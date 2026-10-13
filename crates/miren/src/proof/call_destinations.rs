//! Destination indices are evaluated before calls; owner contents come from the returned state.
use super::*;
use rustc_middle::mir::Local;
use storage_locations::StorageLocation;

pub(super) struct CapturedDestinationIndices {
    root: Local,
    allocation: Option<usize>,
    indices: Vec<(Local, Value)>,
}

pub(super) enum CapturedCallDestination<'tcx> {
    Owned(CapturedDestinationIndices),
    Tracked(call_destination_locations::CapturedTrackedDestination<'tcx>),
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn capture_call_destination(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<CapturedCallDestination<'tcx>>, String> {
        if place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Deref))
        {
            return self
                .capture_tracked_call_destination(body, state, place)
                .map(|captured| Some(CapturedCallDestination::Tracked(captured)));
        }
        self.capture_destination_indices(body, state, place)
            .map(|captured| captured.map(CapturedCallDestination::Owned))
    }

    pub(super) fn store_call_result(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        captured: Option<&CapturedCallDestination<'tcx>>,
        value: Value,
    ) -> Result<(), String> {
        self.validate_array_iterator_value(place.ty(&body.local_decls, self.tcx).ty, &value)?;
        state.constant_receipts.invalidate(place);
        self.activation_validate(&state.flow, &state.memory)?;
        state.flow.charge_publication(state, place)?;
        if !state.memory.owned_regions.is_empty()
            && super::owned_boxes::region_occurrences(std::slice::from_ref(&value))?
                .iter()
                .any(|(_, _, kind)| *kind == symbolic::OwnedRegionKind::BorrowedOwner)
        {
            return Err("readonly virtual Box cannot be an executable call result".into());
        }
        self.owned_box_type_value(
            place.ty(&body.local_decls, self.tcx).ty,
            &value,
            &state.memory,
        )?;
        match captured {
            Some(CapturedCallDestination::Tracked(captured)) => {
                self.store_tracked_call_result(state, captured, value)
            }
            Some(CapturedCallDestination::Owned(indices)) => {
                self.store_owned_call_result(body, state, place, Some(indices), value)
            }
            None => self.store_owned_call_result(body, state, place, None, value),
        }
    }

    pub(super) fn capture_destination_indices(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<CapturedDestinationIndices>, String> {
        if place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Deref))
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "call destination dereference requires pre-call base-location capture".into(),
            ));
        }
        if !place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Index(_)))
        {
            return Ok(None);
        }
        if place.projection.len() > typed_array_choices::MAX_CHOICE_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "call destination exceeds its owned path budget".into(),
            ));
        }
        if !place.projection.iter().all(|part| {
            matches!(
                part,
                ProjectionElem::Field(..)
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex {
                        from_end: false,
                        ..
                    }
            )
        }) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "indexed call destination requires a direct owned product path".into(),
            ));
        }
        let original = body.local_decls[place.local].ty;
        if self.owned_product_shape(original)?.is_none() {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "indexed call destination requires a complete pure owned root type".into(),
            ));
        }
        let allocation = state.addresses[place.local.as_usize()];
        if let Some(allocation) = allocation {
            StorageLocation::tracked(allocation, true).require_write(&state.memory)?;
        }
        self.validate_owned_product(
            original,
            &self.local(state, place.local.as_usize())?,
            &state.conditions,
        )?;
        let (indices, _) =
            self.capture_owned_destination_path(body, state, original, place.projection)?;
        Ok(Some(CapturedDestinationIndices {
            root: place.local,
            allocation,
            indices,
        }))
    }

    pub(super) fn capture_owned_destination_path(
        &self,
        body: &Body<'tcx>,
        state: &State,
        original: Ty<'tcx>,
        projections: &[rustc_middle::mir::PlaceElem<'tcx>],
    ) -> Result<(Vec<(Local, Value)>, Ty<'tcx>), String> {
        let mut indices: Vec<(Local, Value)> = Vec::new();
        let mut current = original;
        for projection in projections.iter().copied() {
            match projection {
                ProjectionElem::Field(field, recorded) => {
                    let child = match current.kind() {
                        ty::Tuple(fields) => fields.get(field.as_usize()).copied(),
                        ty::Adt(definition, arguments) if definition.is_struct() => definition
                            .non_enum_variant()
                            .fields
                            .get(field)
                            .map(|field| field.ty(self.tcx, arguments).skip_norm_wip()),
                        _ => None,
                    }
                    .ok_or("call destination field differs from its original product type")?;
                    if child != recorded {
                        return Err(
                            "call destination field differs from original compiler type".into()
                        );
                    }
                    current = child;
                }
                ProjectionElem::Index(local) => {
                    if body.local_decls[local].ty != self.tcx.types.usize {
                        return Err("call destination index requires exact compiler usize".into());
                    }
                    let ty::Array(element, count) = current.kind() else {
                        return Err(
                            "captured call destination index requires original fixed array".into(),
                        );
                    };
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("captured call destination array requires compiler length")?;
                    let value = if let Some((_, value)) =
                        indices.iter().find(|(key, _)| *key == local)
                    {
                        value.clone()
                    } else {
                        let value = self.local(state, local.as_usize())?;
                        let (term, bits, signed) = value.integer()?;
                        if signed
                            || bits != u32::from(self.tcx.sess.target.pointer_width)
                            || term.sort() != &Sort::BitVec(bits)
                            || !term.belongs_to(&self.terms)
                        {
                            return Err(
                                "captured call destination index has invalid usize storage".into(),
                            );
                        }
                        indices.push((local, value.clone()));
                        value
                    };
                    self.memory_bounds(
                        &value,
                        &symbolic::integer(
                            &self.terms,
                            u128::from(count),
                            u32::from(self.tcx.sess.target.pointer_width),
                            false,
                        ),
                        &state.conditions,
                    )?;
                    current = *element;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    let ty::Array(element, count) = current.kind() else {
                        return Err(
                            "constant call destination index requires original fixed array".into(),
                        );
                    };
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("constant call destination array requires compiler length")?;
                    if count < min_length || offset >= count {
                        return Err(
                            "constant call destination index is outside its original array".into(),
                        );
                    }
                    current = *element;
                }
                _ => return Err("call destination has an uncertified owned projection".into()),
            }
        }
        Ok((indices, current))
    }

    pub(super) fn destination_index(
        &self,
        state: &State,
        local: Local,
        captured: Option<&CapturedDestinationIndices>,
    ) -> Result<Value, String> {
        match captured {
            Some(captured) => captured
                .indices
                .iter()
                .find(|(key, _)| *key == local)
                .map(|(_, value)| value.clone())
                .ok_or_else(|| "call destination omitted a captured index".into()),
            None => self.local(state, local.as_usize()),
        }
    }

    fn store_owned_call_result(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        indices: Option<&CapturedDestinationIndices>,
        value: Value,
    ) -> Result<(), String> {
        if let Some(captured) = indices {
            if captured.root != place.local
                || captured.allocation != state.addresses[place.local.as_usize()]
            {
                return Err("call destination owner changed during the call".into());
            }
            if let Some(allocation) = captured.allocation {
                StorageLocation::tracked(allocation, true).require_write(&state.memory)?;
            }
            self.validate_owned_product(
                body.local_decls[place.local].ty,
                &self.local(state, place.local.as_usize())?,
                &state.conditions,
            )?;
            self.validate_owned_product(
                place.ty(&body.local_decls, self.tcx).ty,
                &value,
                &state.conditions,
            )?;
        }
        match self.write_with_indices_typed(body, state, place, value.clone(), indices) {
            Err(error) if typed_array_choices::known_owned_write_frontier(&error) => {
                if self.write_owned_array_element(body, state, place, &value, indices)?
                    || (self.known_owned_array_write_candidate(body, place)
                        && self
                            .write_known_owned_array_element(body, state, place, &value, indices)?)
                    || (self.owned_field_array_write_candidate(body, place)
                        && self.write_owned_field_array(body, state, place, &value, indices)?)
                {
                    Ok(())
                } else {
                    Err(error)
                }
            }
            result => result,
        }
    }
}
