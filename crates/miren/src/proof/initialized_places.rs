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
    Element(usize),
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

/// Immutable original compiler types; no Body, values, rights or mutable state are cached.
#[derive(Default)]
pub(super) struct Registry<'tcx> {
    scope: std::rc::Rc<()>,
    types: std::cell::RefCell<Vec<Ty<'tcx>>>,
}

#[derive(Clone)]
pub(super) struct Owner {
    scope: std::rc::Rc<()>,
    slot: usize,
    retired: bool,
    allocation: usize,
}

fn array_element<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    offset: u64,
    min_length: u64,
    from_end: bool,
) -> Result<(Ty<'tcx>, usize), String> {
    let ty::Array(child, count) = original.kind() else {
        return Err("ownership element requires original compiler fixed array type".into());
    };
    let count = count
        .try_to_target_usize(tcx)
        .ok_or("ownership array requires original concrete compiler length")?;
    let valid_offset = if from_end {
        offset <= min_length
    } else {
        offset < min_length
    };
    if min_length > count || !valid_offset {
        return Err("ownership constant index differs from original compiler array bounds".into());
    }
    let index = if from_end {
        count.checked_sub(offset)
    } else {
        Some(offset)
    }
    .filter(|index| *index < count)
    .ok_or("ownership constant index exceeds original compiler array bounds")?;
    Ok((
        *child,
        usize::try_from(index).map_err(|_| "ownership index exceeds host usize")?,
    ))
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
        if let ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } = part
        {
            if active_variant.is_some() {
                return Err("ownership array element requires its selected variant field".into());
            }
            let (child, index) = array_element(tcx, original, offset, min_length, from_end)?;
            original = child;
            fields.push(Step::Element(index));
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
    pub(super) fn initialized_type_count(&self) -> usize {
        self.initialized_types.types.borrow().len()
    }

    pub(super) fn preflight_initialized_owner(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        state.flow.require_unarmed()?;
        let fields = self.owned_field_footprint(body, place)?;
        if !fields.iter().any(|part| matches!(part, Step::Element(_)))
            && !matches!(
                place.ty(&body.local_decls, self.tcx).ty.kind(),
                ty::Array(..)
            )
        {
            return Err(
                "ownership array type issuance requires an actual owned element path".into(),
            );
        }
        self.preflight_owned_type_storage(body, state, place)
    }

    pub(super) fn preflight_owned_type_storage(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        state.flow.require_unarmed()?;
        let original = body.local_decls[place.local].ty;
        let allocation = state.addresses[place.local.as_usize()];
        if let Some(allocation) = allocation {
            if state
                .memory
                .get(allocation)
                .and_then(Option::as_ref)
                .is_none()
            {
                return Err("ownership type evidence requires live retained allocation".into());
            }
            self.check_initialized_owner_type(&state.memory, allocation, original)?;
            if state
                .memory
                .initialized_owners
                .iter()
                .any(|(key, _)| *key == allocation)
            {
                return Ok(());
            }
        }
        let slots = if allocation.is_some() { 1 } else { 2 };
        if state.memory.storage_slots().saturating_add(slots) > memory::MAX_ALLOCATIONS
            || state.memory.initialized_owners.len() >= MAX_INPUT_VALUES
        {
            return Err("ownership original type evidence exceeds retained storage limits".into());
        }
        let types = self.initialized_types.types.borrow();
        if !types.contains(&original) && types.len() >= MAX_INPUT_VALUES {
            return Err("ownership original type evidence exceeds its 512-node limit".into());
        }
        Ok(())
    }

    // Only Body-bearing owned-place operations call this issuer. Numeric paths cannot issue Owner.
    pub(super) fn bind_initialized_owner(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        self.preflight_initialized_owner(body, state, place)?;
        let fields = self.owned_field_footprint(body, place)?;
        if !fields.iter().any(|part| matches!(part, Step::Element(_)))
            && !matches!(
                place.ty(&body.local_decls, self.tcx).ty.kind(),
                ty::Array(..)
            )
        {
            return Err(
                "ownership array type issuance requires an actual owned element path".into(),
            );
        }
        self.bind_owned_type_storage(body, state, place)
    }

    pub(super) fn bind_owned_type_storage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        self.preflight_owned_type_storage(body, state, place)?;
        let allocation = state.addresses[place.local.as_usize()]
            .ok_or("ownership array type issuance requires actual addressed owner")?;
        let original = body.local_decls[place.local].ty;
        self.bind_validated_owned_storage(original, &mut state.memory, allocation)
    }

    pub(super) fn bind_iterator_element_storage(
        &self,
        witness: &array_iterator_constructors::drops::ElementWitness<'tcx>,
        state: &mut State,
        allocation: usize,
    ) -> Result<(), String> {
        let original = witness.element(self, state, allocation)?;
        self.bind_validated_owned_storage(original, &mut state.memory, allocation)
    }

    fn bind_validated_owned_storage(
        &self,
        original: Ty<'tcx>,
        memory: &mut Memory,
        allocation: usize,
    ) -> Result<(), String> {
        if memory.get(allocation).and_then(Option::as_ref).is_none() {
            return Err("ownership type evidence requires live retained allocation".into());
        }
        let mut types = self.initialized_types.types.borrow_mut();
        if let Some((_, owner)) = memory
            .initialized_owners
            .iter()
            .find(|(key, _)| *key == allocation)
        {
            if owner.allocation != allocation
                || owner.retired
                || !std::rc::Rc::ptr_eq(&owner.scope, &self.initialized_types.scope)
                || types.get(owner.slot) != Some(&original)
            {
                return Err(
                    "ownership allocation type evidence differs from original owner".into(),
                );
            }
            return Ok(());
        }
        if memory.initialized_owners.len() >= MAX_INPUT_VALUES {
            return Err("ownership original type evidence exceeds its 512-node limit".into());
        }
        let slot = if let Some(slot) = types.iter().position(|ty| *ty == original) {
            slot
        } else {
            if types.len() >= MAX_INPUT_VALUES {
                return Err("ownership original type evidence exceeds its 512-node limit".into());
            }
            let slot = types.len();
            types.push(original);
            slot
        };
        std::rc::Rc::make_mut(&mut memory.initialized_owners).push((
            allocation,
            Owner {
                scope: self.initialized_types.scope.clone(),
                slot,
                retired: false,
                allocation,
            },
        ));
        Ok(())
    }

    pub(super) fn typed_memory_footprint(
        &self,
        memory: &Memory,
        allocation: usize,
        path: &[MemoryProjection],
    ) -> Result<Option<Vec<Step>>, String> {
        if let Some(fields) = field_footprint(path) {
            return Ok(Some(fields));
        }
        Ok(self
            .typed_memory_evidence(memory, allocation, path)?
            .map(|(fields, _)| fields))
    }

    pub(super) fn typed_memory_evidence(
        &self,
        memory: &Memory,
        allocation: usize,
        path: &[MemoryProjection],
    ) -> Result<Option<(Vec<Step>, Ty<'tcx>)>, String> {
        let Some((_, owner)) = memory
            .initialized_owners
            .iter()
            .find(|(key, _)| *key == allocation)
        else {
            return Ok(None);
        };
        if owner.allocation != allocation {
            return Err("ownership initialization type differs from allocation identity".into());
        }
        if owner.retired || memory.get(allocation).and_then(Option::as_ref).is_none() {
            return Err("ownership initialization type belongs to retired allocation".into());
        }
        if !std::rc::Rc::ptr_eq(&owner.scope, &self.initialized_types.scope) {
            return Err("ownership initialization type belongs to a foreign engine".into());
        }
        if path.len() > 16 {
            return Err("ownership consumption field path exceeds depth16 limit".into());
        }
        let mut original = *self
            .initialized_types
            .types
            .borrow()
            .get(owner.slot)
            .ok_or("ownership original compiler type evidence is unavailable")?;
        let mut fields = Vec::new();
        let mut variant = None;
        for part in path {
            match part {
                MemoryProjection::Field(field) => {
                    original = match original.kind() {
                        ty::Tuple(types) => types.get(*field).copied(),
                        ty::Closure(_, args) => args.as_closure().upvar_tys().get(*field).copied(),
                        ty::Adt(def, args) if def.is_struct() => def
                            .non_enum_variant()
                            .fields
                            .get(rustc_abi::FieldIdx::from_usize(*field))
                            .map(|field| field.ty(self.tcx, args).skip_norm_wip()),
                        ty::Adt(def, args) if def.is_enum() => variant
                            .and_then(|variant: usize| {
                                def.variants()
                                    .get(rustc_abi::VariantIdx::from_usize(variant))
                            })
                            .and_then(|variant| {
                                variant.fields.get(rustc_abi::FieldIdx::from_usize(*field))
                            })
                            .map(|field| field.ty(self.tcx, args).skip_norm_wip()),
                        _ => None,
                    }
                    .ok_or("ownership memory field lacks its original compiler parent")?;
                    variant = None;
                    fields.push(Step::Field(*field));
                }
                MemoryProjection::Variant(selected) => {
                    let ty::Adt(def, _) = original.kind() else {
                        return Ok(None);
                    };
                    if !def.is_enum() || *selected >= def.variants().len() || variant.is_some() {
                        return Err(
                            "ownership memory variant differs from original compiler type".into(),
                        );
                    }
                    variant = Some(*selected);
                    fields.push(Step::Variant(*selected));
                }
                MemoryProjection::Index(value) => {
                    let (expression, bits, signed) = value.integer()?;
                    if signed
                        || bits != u32::from(self.tcx.sess.target.pointer_width)
                        || !expression.belongs_to(&self.terms)
                        || variant.is_some()
                    {
                        return Ok(None);
                    }
                    let Some(symbolic::Constant::BitVec { value: index, .. }) =
                        symbolic::constant(&expression)
                    else {
                        return Ok(None);
                    };
                    let index =
                        u64::try_from(index).map_err(|_| "ownership memory index exceeds u64")?;
                    let (child, index) = array_element(
                        self.tcx,
                        original,
                        index,
                        index
                            .checked_add(1)
                            .ok_or("ownership memory index overflow")?,
                        false,
                    )?;
                    original = child;
                    fields.push(Step::Element(index));
                }
                MemoryProjection::TypedIndex { .. }
                | MemoryProjection::Slice { .. }
                | MemoryProjection::Chunks { .. } => return Ok(None),
            }
        }
        Ok(Some((fields, original)))
    }

    pub(super) fn check_memory_initialization(
        &self,
        memory: &Memory,
        allocation: usize,
        path: &[MemoryProjection],
    ) -> Result<(), String> {
        if self.check_drop_shared_reference(allocation, path, memory, &[])? {
            return Ok(());
        }
        let fields = self
            .typed_memory_footprint(memory, allocation, path)?
            .unwrap_or_default();
        memory.missing_places.check(allocation, &fields)
    }

    pub(super) fn validate_fixed_array_storage(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        if !place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::ConstantIndex { .. }))
            || !place.projection.iter().all(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..)
                        | ProjectionElem::Downcast(..)
                        | ProjectionElem::ConstantIndex { .. }
                )
            })
        {
            return Ok(());
        }
        self.owned_field_footprint(body, place)?;
        let mut value = self.raw_local(state, place.local.as_usize())?;
        for (position, part) in place.projection.iter().enumerate() {
            if let ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } = part
            {
                let prefix = Place {
                    local: place.local,
                    projection: self.tcx.mk_place_elems(&place.projection[..position]),
                };
                let original = prefix.ty(&body.local_decls, self.tcx).ty;
                array_element(self.tcx, original, offset, min_length, from_end)?;
                let ty::Array(_, count) = original.kind() else {
                    unreachable!()
                };
                let count = count.try_to_target_usize(self.tcx).unwrap();
                let matches = match value.clone().materialize()? {
                    Value::Elements(elements) => u64::try_from(elements.len()).ok() == Some(count),
                    Value::Bytes { length, .. } => {
                        let (length, bits, signed) = length.integer()?;
                        !signed
                            && bits == u32::from(self.tcx.sess.target.pointer_width)
                            && length.belongs_to(&self.terms)
                            && symbolic::constant(&length)
                                == Some(symbolic::Constant::BitVec {
                                    value: u128::from(count),
                                    bits,
                                })
                    }
                    _ => false,
                };
                if !matches {
                    return Err(
                        "ownership array backing differs from original compiler length".into(),
                    );
                }
            }
            value = self.place_projection(state, value, part)?;
        }
        Ok(())
    }

    pub(super) fn check_initialized_owner_type(
        &self,
        memory: &Memory,
        allocation: usize,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        if let Some((_, owner)) = memory
            .initialized_owners
            .iter()
            .find(|(key, _)| *key == allocation)
            && (owner.allocation != allocation
                || owner.retired
                || !std::rc::Rc::ptr_eq(&owner.scope, &self.initialized_types.scope)
                || self.initialized_types.types.borrow().get(owner.slot) != Some(&original))
        {
            return Err("ownership allocation type evidence differs from original owner".into());
        }
        Ok(())
    }

    pub(super) fn check_typed_place_initialization(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        if place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::ConstantIndex { .. }))
            && place.projection.iter().all(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..)
                        | ProjectionElem::Downcast(..)
                        | ProjectionElem::ConstantIndex { .. }
                )
            })
        {
            let fields = self.owned_field_footprint(body, place)?;
            if fields.iter().any(|part| matches!(part, Step::Element(_)))
                && let Some(allocation) = state.addresses[place.local.as_usize()]
            {
                self.check_initialized_owner_type(
                    &state.memory,
                    allocation,
                    body.local_decls[place.local].ty,
                )?;
            }
            self.check_local_initialization(state, place.local.as_usize(), &fields)
        } else {
            self.check_place_initialization(state, place)
        }
    }

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
                    if destination
                        .projection
                        .iter()
                        .any(|part| matches!(part, ProjectionElem::ConstantIndex { .. }))
                        && destination.projection.iter().all(|part| {
                            matches!(
                                part,
                                ProjectionElem::Field(..)
                                    | ProjectionElem::Downcast(..)
                                    | ProjectionElem::ConstantIndex { .. }
                            )
                        })
                    {
                        let target = self.owned_field_footprint(body, destination)?;
                        if fields.starts_with(&target) || target.starts_with(&fields) {
                            return Err(self.categorized_error(
                                UnknownCategory::Semantics,
                                concat!(
                                    "call Move input overlaps return storage without a resolved ",
                                    "compiler contract"
                                )
                                .into(),
                            ));
                        }
                        return Ok(());
                    }
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
                let owners = if fields.iter().any(|part| matches!(part, Step::Element(_))) {
                    let owners = state.memory.initialized_owners.clone();
                    self.bind_initialized_owner(body, state, place)?;
                    Some(owners)
                } else {
                    None
                };
                if let Err(reason) = state.memory.missing_places.consume(allocation, fields) {
                    if let Some(owners) = owners {
                        state.memory.initialized_owners = owners;
                    }
                    return Err(self.categorized_error(UnknownCategory::ResourceLimit, reason));
                }
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
    pub(super) fn retire_initialized_owner(&mut self, allocation: usize) {
        if let Some((_, owner)) = std::rc::Rc::make_mut(&mut self.initialized_owners)
            .iter_mut()
            .find(|(key, _)| *key == allocation)
        {
            owner.retired = true;
        }
    }

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

    #[test]
    fn element_masks_keep_siblings_prefixes_and_branch_repair() {
        let mut missing = MissingPlaces::default();
        let first = vec![Step::Field(0), Step::Element(0), Step::Element(1)];
        missing.consume(7, first.clone()).unwrap();
        assert!(missing.check(7, &[Step::Field(0)]).is_err());
        assert!(
            missing
                .check(7, &[Step::Field(0), Step::Element(0)])
                .is_err()
        );
        assert!(
            missing
                .check(7, &[Step::Field(0), Step::Element(1)])
                .is_ok()
        );
        assert!(
            missing
                .check(7, &[Step::Field(0), Step::Element(0), Step::Element(0)])
                .is_ok()
        );
        let mut branch = missing.clone();
        branch.initialize(7, &[Step::Field(0), Step::Element(0), Step::Element(0)]);
        assert!(branch.check(7, &first).is_err());
        branch.initialize(7, &first);
        assert!(branch.check(7, &[]).is_ok());
        assert!(missing.check(7, &[]).is_err());
        let mut addressed = MissingPlaces::default();
        missing.transfer(7, 9, &mut addressed).unwrap();
        assert!(missing.is_empty());
        assert!(addressed.check(9, &first).is_err());
        assert!(addressed.check(7, &first).is_ok());
    }

    #[test]
    fn actual_compiler_array_paths_preserve_owner_namespace_and_masks() {
        struct Check {
            checked: bool,
        }
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                compiler_array_controls(tcx);
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("miren-array-init-{}-{nonce}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("array.rs");
        std::fs::write(
            &source,
            include_str!("../../../../tests/fixtures/array_move_initialization.rs"),
        )
        .unwrap();
        let arguments = vec![
            "rustc".into(),
            source.to_str().unwrap().into(),
            "--crate-type=lib".into(),
            "--edition=2024".into(),
            "-Cpanic=abort".into(),
            "-Copt-level=0".into(),
            "--out-dir".into(),
            directory.to_str().unwrap().into(),
            "--sysroot".into(),
            env!("MIREN_SYSROOT").into(),
        ];
        let mut callback = Check { checked: false };
        rustc_driver::run_compiler(&arguments, &mut callback);
        assert!(callback.checked);
        std::fs::remove_dir_all(&directory).unwrap();
    }

    fn compiler_array_controls<'tcx>(tcx: TyCtxt<'tcx>) {
        let options = || VerificationOptions {
            all_failures: false,
            induction: false,
            startup: false,
            isolated_startup: false,
            async_entry: false,
            limits: miren::AnalysisLimits::default(),
        };
        let config = miren::ContractConfig::default();
        let mut engine = Engine::new(tcx, &config, options());
        let id = tcx
            .mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == "unpack"
            })
            .unwrap()
            .to_def_id();
        let instance = engine
            .resolve_function_item(id, ty::GenericArgs::empty())
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        let moved =
            body.basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter_map(|statement| match &statement.kind {
                    StatementKind::Assign(assignment) => match &assignment.1 {
                        Rvalue::Use(Operand::Move(place), _)
                            if place.projection.iter().any(|part| {
                                matches!(part, ProjectionElem::ConstantIndex { .. })
                            }) =>
                        {
                            Some(*place)
                        }
                        _ => None,
                    },
                    _ => None,
                })
                .collect::<Vec<_>>();
        assert_eq!(moved.len(), 2);
        let first = moved[0];
        let second = moved[1];
        assert_eq!(
            engine.owned_field_footprint(&body, first).unwrap(),
            vec![Step::Element(0)]
        );
        assert_eq!(
            engine.owned_field_footprint(&body, second).unwrap(),
            vec![Step::Element(1)]
        );
        let mut conditions = Vec::new();
        let original = body.local_decls[first.local].ty;
        let value = engine.argument(id, original, &mut conditions).unwrap();
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            addresses: vec![None; body.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            conditions,
            memory: Memory::default(),
            missing_places: MissingPlaces::default(),
        };
        state.locals[first.local.as_usize()] = Some(value);
        let old = engine
            .borrow_typed(&body, &mut state, first, false)
            .unwrap();
        let sibling = engine
            .borrow_typed(&body, &mut state, second, false)
            .unwrap();
        let allocation = state.addresses[first.local.as_usize()].unwrap();
        let moved_value = engine
            .evaluate_operand(id, &body, &mut state, &Operand::Move(first))
            .unwrap();
        let before = format!("{:?}", state.memory.missing_places);
        assert_eq!(
            engine
                .reference_value(&old, &state.memory, &state.conditions)
                .unwrap_err(),
            "place initialization is unavailable after ownership consumption"
        );
        engine
            .reference_value(&sibling, &state.memory, &state.conditions)
            .unwrap();
        engine
            .validate_typed_reference_graph(&sibling, &state, None, &mut Vec::new())
            .unwrap();
        let mut branch = state.clone();
        engine
            .write_typed(&body, &mut branch, first, moved_value)
            .unwrap();
        assert!(branch.memory.missing_places.check(allocation, &[]).is_ok());
        assert_eq!(format!("{:?}", state.memory.missing_places), before);
        let foreign = Engine::new(tcx, &config, options());
        let Value::Reference { projection, .. } = &sibling else {
            panic!("actual tracked sibling")
        };
        assert_eq!(
            foreign
                .check_memory_initialization(&state.memory, allocation, projection)
                .unwrap_err(),
            "ownership initialization type belongs to a foreign engine"
        );
        let mut changed = body.as_ref().clone();
        let ty::Array(child, _) = original.kind() else {
            panic!("actual compiler array")
        };
        changed.local_decls[first.local].ty = Ty::new_array(tcx, *child, 3);
        assert_eq!(
            engine
                .check_typed_place_initialization(&changed, &state, second)
                .unwrap_err(),
            "ownership allocation type evidence differs from original owner"
        );
        changed.local_decls[first.local].ty = Ty::new_array(tcx, tcx.types.u32, 2);
        assert_eq!(
            engine
                .check_typed_place_initialization(&changed, &state, second)
                .unwrap_err(),
            "ownership allocation type evidence differs from original owner"
        );
        let mut wrong_owner = state.clone();
        let other = wrong_owner.memory.len();
        wrong_owner.memory.push(state.memory[allocation].clone());
        std::rc::Rc::make_mut(&mut wrong_owner.memory.initialized_owners)[0].0 = other;
        assert_eq!(
            engine
                .check_memory_initialization(&wrong_owner.memory, other, projection)
                .unwrap_err(),
            "ownership initialization type differs from allocation identity"
        );
        let before = format!("{:?}", state.memory.missing_places);
        for (offset, min_length, from_end) in [(2, 2, false), (0, 3, false), (3, 3, true)] {
            let invalid = Place {
                local: first.local,
                projection: tcx.mk_place_elems(&[ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                }]),
            };
            assert_eq!(
                engine.owned_field_footprint(&body, invalid).unwrap_err(),
                "ownership constant index differs from original compiler array bounds"
            );
        }
        assert_eq!(format!("{:?}", state.memory.missing_places), before);
        let from_end = Place {
            local: first.local,
            projection: tcx.mk_place_elems(&[ProjectionElem::ConstantIndex {
                offset: 1,
                min_length: 1,
                from_end: true,
            }]),
        };
        assert_eq!(
            engine.owned_field_footprint(&body, from_end).unwrap(),
            vec![Step::Element(1)]
        );
        let mut retired = state.clone();
        retired.memory.retire_initialized_owner(allocation);
        retired.memory[allocation] = None;
        assert_eq!(
            engine
                .check_memory_initialization(&retired.memory, allocation, projection)
                .unwrap_err(),
            "ownership initialization type belongs to retired allocation"
        );
        retired.memory[allocation] = state.memory[allocation].clone();
        assert_eq!(
            engine
                .check_memory_initialization(&retired.memory, allocation, projection)
                .unwrap_err(),
            "ownership initialization type belongs to retired allocation"
        );
        assert_eq!(
            engine
                .bind_initialized_owner(&body, &mut retired, second)
                .unwrap_err(),
            "ownership allocation type evidence differs from original owner"
        );
        println!("array-init actual compiler paths and ownership controls complete");
    }
}
