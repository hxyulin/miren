use super::call_destinations::CapturedCallDestination;
use super::*;
use crate::symbolic::MemoryProjection;

/// A missing subobject is independent of the allocation's lifetime and retained payload bytes.
#[derive(Clone, Default, Debug)]
pub(super) struct MissingPlaces(Vec<(usize, Vec<Step>)>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Step {
    Field(usize),
    Variant(usize),
}

impl MissingPlaces {
    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub(super) fn check(&self, owner: usize, fields: &[Step]) -> Result<(), String> {
        if self.0.iter().any(|(candidate, missing)| {
            *candidate == owner && (missing.starts_with(fields) || fields.starts_with(missing))
        }) {
            Err("place initialization is unavailable after ownership consumption".into())
        } else {
            Ok(())
        }
    }

    pub(super) fn descendants(
        &self,
        owner: usize,
        prefix: &[Step],
    ) -> Result<Vec<Vec<Step>>, String> {
        if self
            .0
            .iter()
            .any(|(candidate, path)| *candidate == owner && prefix.starts_with(path))
        {
            return Err("place initialization is unavailable after ownership consumption".into());
        }
        Ok(self
            .0
            .iter()
            .filter(|(candidate, path)| *candidate == owner && path.starts_with(prefix))
            .map(|(_, path)| path[prefix.len()..].to_vec())
            .collect())
    }

    pub(super) fn consume(&mut self, owner: usize, fields: Vec<Step>) -> Result<(), String> {
        let retained = self
            .0
            .iter()
            .filter(|(candidate, missing)| *candidate != owner || !missing.starts_with(&fields))
            .map(|(_, path)| 1 + path.len())
            .sum::<usize>();
        if fields.len() > 16 || retained + 1 + fields.len() > MAX_INPUT_VALUES {
            return Err(
                "ownership initialization ledger exceeds its 512-node or depth16 limit".into(),
            );
        }
        self.0
            .retain(|(candidate, missing)| *candidate != owner || !missing.starts_with(&fields));
        self.0.push((owner, fields));
        Ok(())
    }

    pub(super) fn entries(&self) -> &[(usize, Vec<Step>)] {
        &self.0
    }

    pub(super) fn initialize(&mut self, owner: usize, fields: &[Step]) {
        self.0
            .retain(|(candidate, missing)| *candidate != owner || !missing.starts_with(fields));
    }

    pub(super) fn transfer(
        &mut self,
        owner: usize,
        target: usize,
        into: &mut Self,
    ) -> Result<(), String> {
        let mut updated = into.clone();
        for (_, fields) in self.0.iter().filter(|(candidate, _)| *candidate == owner) {
            updated.consume(target, fields.clone())?;
        }
        *into = updated;
        self.initialize(owner, &[]);
        Ok(())
    }
}

pub(super) fn field_footprint(path: &[MemoryProjection]) -> Option<Vec<Step>> {
    path.iter()
        .map(|part| match part {
            MemoryProjection::Field(field) => Some(Step::Field(*field)),
            MemoryProjection::Variant(variant) => Some(Step::Variant(*variant)),
            _ => None,
        })
        .collect()
}

// A dynamic destination suffix can only be disjoint after an unequal fixed prefix.
// This is a refusal check, never a certificate granting a read or a write.
pub(super) fn overlaps_destination(source: &[Step], destination: &[MemoryProjection]) -> bool {
    for (position, projection) in destination.iter().enumerate() {
        let Some(source) = source.get(position) else {
            return true;
        };
        let destination = match projection {
            MemoryProjection::Field(field) => Step::Field(*field),
            MemoryProjection::Variant(variant) => Step::Variant(*variant),
            _ => return true,
        };
        if *source != destination {
            return false;
        }
    }
    true
}

pub(super) fn compiler_field_footprint<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Result<Vec<Step>, String> {
    if place.projection.len() > 16 {
        return Err("ownership consumption field path exceeds depth16 limit".into());
    }
    let mut original = body.local_decls[place.local].ty;
    let mut fields = Vec::new();
    let mut active_variant = None;
    for part in place.projection {
        if let ProjectionElem::Downcast(_, variant) = part {
            let ty::Adt(def, _) = original.kind() else {
                return Err("ownership downcast requires original compiler enum type".into());
            };
            if !def.is_enum()
                || variant.as_usize() >= def.variants().len()
                || active_variant.is_some()
            {
                return Err("ownership downcast has invalid original variant metadata".into());
            }
            active_variant = Some(variant);
            fields.push(Step::Variant(variant.as_usize()));
            continue;
        }
        let ProjectionElem::Field(field, recorded) = part else {
            return Err("ownership consumption requires an owned local or fixed field path".into());
        };
        let selected = match original.kind() {
            ty::Tuple(types) => types.get(field.as_usize()).copied(),
            ty::Closure(_, args) => args.as_closure().upvar_tys().get(field.as_usize()).copied(),
            ty::Adt(def, args) if def.is_enum() => active_variant
                .and_then(|variant| def.variants()[variant].fields.get(field))
                .map(|field| field.ty(tcx, args).skip_norm_wip()),
            ty::Adt(def, args) if def.is_struct() => def
                .non_enum_variant()
                .fields
                .get(field)
                .map(|field| field.ty(tcx, args).skip_norm_wip()),
            _ => None,
        }
        .ok_or("ownership consumption field lacks its exact compiler parent")?;
        if selected != recorded {
            return Err("ownership consumption field differs from original compiler type".into());
        }
        original = selected;
        active_variant = None;
        fields.push(Step::Field(field.as_usize()));
    }
    Ok(fields)
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn owned_field_footprint(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> Result<Vec<Step>, String> {
        if place.projection.len() > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "ownership consumption field path exceeds depth16 limit".into(),
            ));
        }
        compiler_field_footprint(self.tcx, body, place)
    }

    pub(super) fn reject_call_move_overlap(
        &self,
        body: &Body<'tcx>,
        state: &State,
        destination: Place<'tcx>,
        captured: Option<&CapturedCallDestination<'tcx>>,
        operand: &Operand<'tcx>,
    ) -> Result<(), String> {
        let Operand::Move(source) = operand else {
            return Ok(());
        };
        let (allocation, fields) = if source
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Deref))
        {
            let Some((allocation, fields)) = self.coroutine_move_storage(body, state, *source)?
            else {
                return Ok(());
            }; // The ordinary operand consumer refuses unsupported moves.
            (Some(allocation), fields)
        } else {
            (
                state.addresses[source.local.as_usize()],
                self.owned_field_footprint(body, *source)?,
            )
        };
        let overlap = match captured {
            Some(CapturedCallDestination::Tracked(target)) => allocation
                .is_some_and(|allocation| target.overlaps_owned_source(allocation, &fields)),
            None if destination
                .projection
                .iter()
                .any(|part| matches!(part, ProjectionElem::Deref)) =>
            {
                let (target, path, _) = self.memory_path(state, destination)?;
                allocation.is_some() && allocation == target && overlaps_destination(&fields, &path)
            }
            _ => {
                let target_allocation = state.addresses[destination.local.as_usize()];
                let same_owner = match (allocation, target_allocation) {
                    (Some(source), Some(target)) => source == target,
                    (None, None) => source.local == destination.local,
                    _ => false,
                };
                if same_owner {
                    let mut path = Vec::new();
                    for projection in destination.projection {
                        match projection {
                            ProjectionElem::Field(field, _) => {
                                path.push(MemoryProjection::Field(field.as_usize()))
                            }
                            ProjectionElem::Downcast(_, variant) => {
                                path.push(MemoryProjection::Variant(variant.as_usize()))
                            }
                            _ => {
                                return if overlaps_destination(&fields, &path) {
                                    Err(self.categorized_error(UnknownCategory::Semantics,
                                        "call Move input overlaps return storage without a resolved compiler contract".into()))
                                } else {
                                    Ok(())
                                };
                            }
                        }
                    }
                    overlaps_destination(&fields, &path)
                } else {
                    false
                }
            }
        };
        if overlap {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "call Move input overlaps return storage without a resolved compiler contract"
                    .into(),
            ));
        }
        Ok(())
    }

    pub(super) fn evaluate_operand(
        &self,
        id: DefId,
        body: &Body<'tcx>,
        state: &mut State,
        operand: &Operand<'tcx>,
    ) -> Result<Value, String> {
        if let Operand::Move(place) = operand {
            state.constant_receipts.invalidate(*place);
        }
        if let Operand::Move(place) = operand
            && place
                .projection
                .iter()
                .any(|part| matches!(part, ProjectionElem::Deref))
            && let Some(value) = self.consume_coroutine_operand(body, state, *place)?
        {
            return Ok(value);
        }
        let footprint = if let Operand::Move(place) = operand {
            Some((*place, self.owned_field_footprint(body, *place)?))
        } else {
            None
        };
        let value = self.operand(id, body, state, operand)?;
        if !state.memory.owned_regions.is_empty()
            && matches!(operand, Operand::Move(_))
            && owned_boxes::region_occurrences(std::slice::from_ref(&value))?
                .iter()
                .any(|(_, _, kind)| *kind == symbolic::OwnedRegionKind::BorrowedOwner)
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "readonly virtual Box cannot become an executable moved owner".into(),
            ));
        }
        if !state.memory.owned_regions.is_empty()
            && matches!(operand, Operand::Copy(_))
            && !owned_boxes::owner_occurrences(std::slice::from_ref(&value))?.is_empty()
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "executable owned Box Copy needs an exact consuming call certificate".into(),
            ));
        }
        if let Some((place, fields)) = footprint {
            let local = place.local.as_usize();
            if let Some(allocation) = state.addresses[local] {
                state
                    .memory
                    .missing_places
                    .consume(allocation, fields)
                    .map_err(|reason| {
                        self.categorized_error(UnknownCategory::ResourceLimit, reason)
                    })?;
            } else {
                state
                    .missing_places
                    .consume(local, fields)
                    .map_err(|reason| {
                        self.categorized_error(UnknownCategory::ResourceLimit, reason)
                    })?;
            }
        }
        Ok(value)
    }

    pub(super) fn check_local_initialization(
        &self,
        state: &State,
        local: usize,
        fields: &[Step],
    ) -> Result<(), String> {
        let result = if let Some(allocation) = state.addresses[local] {
            state.memory.missing_places.check(allocation, fields)
        } else {
            state.missing_places.check(local, fields)
        };
        result.map_err(|reason| self.categorized_error(UnknownCategory::Semantics, reason))
    }

    pub(super) fn check_place_initialization(
        &self,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        let fields = place
            .projection
            .iter()
            .take_while(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..) | ProjectionElem::Downcast(..)
                )
            })
            .filter_map(|part| match part {
                ProjectionElem::Field(field, _) => Some(Step::Field(field.as_usize())),
                ProjectionElem::Downcast(_, variant) => Some(Step::Variant(variant.as_usize())),
                _ => None,
            })
            .collect::<Vec<_>>();
        self.check_local_initialization(state, place.local.as_usize(), &fields)
    }
}

impl Memory {
    pub(super) fn check_projection_initialization(
        &self,
        allocation: usize,
        projection: &[MemoryProjection],
    ) -> Result<(), String> {
        let fields = field_footprint(projection).unwrap_or_default();
        self.missing_places.check(allocation, &fields)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn call_overlap_is_about_source_storage_not_referenced_targets() {
        assert!(overlaps_destination(&[], &[MemoryProjection::Field(0)]));
        assert!(overlaps_destination(&[Step::Field(0)], &[]));
        assert!(!overlaps_destination(
            &[Step::Field(0)],
            &[MemoryProjection::Field(1)]
        ));
        assert!(overlaps_destination(
            &[Step::Field(0)],
            &[MemoryProjection::Field(0)]
        ));
        assert!(!overlaps_destination(
            &[Step::Variant(0), Step::Field(0)],
            &[MemoryProjection::Variant(1), MemoryProjection::Field(0)]
        ));
    }

    #[test]
    fn consumption_and_repair_keep_siblings_identity_and_branch_state() {
        let mut missing = MissingPlaces::default();
        missing
            .consume(3, vec![Step::Field(0), Step::Field(1)])
            .unwrap();
        assert!(missing.check(3, &[Step::Field(0)]).is_err());
        assert!(
            missing
                .check(3, &[Step::Field(0), Step::Field(1), Step::Field(0)])
                .is_err()
        );
        assert!(missing.check(3, &[Step::Field(1)]).is_ok());
        assert!(missing.check(4, &[]).is_ok());
        let branch = missing.clone();
        missing.initialize(3, &[Step::Field(0)]);
        assert!(missing.check(3, &[]).is_ok());
        assert!(branch.check(3, &[]).is_err());
        missing.consume(3, vec![]).unwrap();
        missing.initialize(3, &[Step::Field(0)]);
        assert!(missing.check(3, &[Step::Field(0)]).is_err());
        missing.initialize(3, &[]);
        assert!(missing.check(3, &[]).is_ok());
    }

    #[test]
    fn addressed_transfer_preserves_projection_specific_consumption() {
        let mut locals = MissingPlaces::default();
        locals.consume(2, vec![Step::Field(0)]).unwrap();
        let mut memory = Memory::from(vec![Some(Value::Unit)]);
        locals.transfer(2, 0, &mut memory.missing_places).unwrap();
        assert!(locals.is_empty());
        assert!(
            memory
                .check_projection_initialization(0, &[MemoryProjection::Field(0)])
                .is_err()
        );
        assert!(
            memory
                .check_projection_initialization(0, &[MemoryProjection::Field(1)])
                .is_ok()
        );
        let mut sibling = memory.clone();
        sibling.missing_places.initialize(0, &[Step::Field(0)]);
        assert!(sibling.check_projection_initialization(0, &[]).is_ok());
        assert!(memory.check_projection_initialization(0, &[]).is_err());
    }
    #[test]
    fn carrier_descendants_do_not_authorize_consumed_reference_handles() {
        let mut missing = MissingPlaces::default();
        missing.consume(7, vec![Step::Field(0)]).unwrap();
        assert_eq!(
            missing.descendants(7, &[]).unwrap(),
            vec![vec![Step::Field(0)]]
        );
        assert!(missing.check(7, &[Step::Field(0)]).is_err());
        assert!(missing.check(7, &[Step::Field(1)]).is_ok());
        assert!(missing.descendants(7, &[Step::Field(0)]).is_err());
        missing.consume(8, vec![]).unwrap();
        assert!(missing.descendants(8, &[]).is_err());
    }

    #[test]
    fn active_variants_and_budget_failures_preserve_distinct_masks() {
        let mut missing = MissingPlaces::default();
        missing
            .consume(0, vec![Step::Variant(1), Step::Field(0)])
            .unwrap();
        assert!(
            missing
                .check(0, &[Step::Variant(1), Step::Field(0)])
                .is_err()
        );
        assert!(
            missing
                .check(0, &[Step::Variant(0), Step::Field(0)])
                .is_ok()
        );
        missing.initialize(0, &[Step::Variant(0), Step::Field(0)]);
        assert!(
            missing
                .check(0, &[Step::Variant(1), Step::Field(0)])
                .is_err()
        );
        let prior = missing.0.clone();
        assert!(missing.consume(0, vec![Step::Field(0); 17]).is_err());
        assert_eq!(missing.0, prior);
        for owner in 1..255 {
            missing.consume(owner, vec![Step::Field(0)]).unwrap();
        }
        let prior = missing.0.clone();
        assert!(
            missing
                .consume(256, vec![Step::Field(0), Step::Field(1)])
                .is_err()
        );
        assert_eq!(missing.0, prior);
    }
}
