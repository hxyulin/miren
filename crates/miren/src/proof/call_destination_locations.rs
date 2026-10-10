//! Retained tracked call-result locations preserve pre-call addresses and current owner contents.
use super::*;
use crate::symbolic::MemoryProjection;
use storage_locations::StorageLocation;

pub(super) struct CapturedTrackedDestination<'tcx> {
    location: StorageLocation,
    original: Ty<'tcx>,
    target: Ty<'tcx>,
    path: Vec<MemoryProjection>,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn capture_tracked_call_destination(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<CapturedTrackedDestination<'tcx>, String> {
        let unsupported = || {
            self.categorized_error(
                UnknownCategory::Semantics,
                "call destination requires an unprojected tracked mutable pure owner".into(),
            )
        };
        let Some((ProjectionElem::Deref, suffix)) = place.projection.split_first() else {
            return Err(unsupported());
        };
        if suffix.len() >= typed_array_choices::MAX_CHOICE_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "tracked call destination exceeds its owned path budget".into(),
            ));
        }
        if !suffix.iter().all(|part| {
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
            return Err(unsupported());
        }
        let ty::Ref(_, original, mutability) = body.local_decls[place.local].ty.kind() else {
            return Err(unsupported());
        };
        if !mutability.is_mut() || self.owned_product_shape(*original)?.is_none() {
            return Err(unsupported());
        }
        let Value::Reference {
            allocation,
            projection,
            mutable,
        } = self.local(state, place.local.as_usize())?
        else {
            return Err(unsupported());
        };
        if !mutable || !projection.is_empty() {
            return Err(unsupported());
        }
        let location = StorageLocation::tracked(allocation, mutable);
        location.require_write(&state.memory)?;
        self.validate_owned_product(*original, location.read(&state.memory)?, &state.conditions)?;
        let (indices, target) =
            self.capture_owned_destination_path(body, state, *original, suffix)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let mut path = Vec::new();
        for projection in suffix {
            path.push(match projection {
                ProjectionElem::Field(field, _) => MemoryProjection::Field(field.as_usize()),
                ProjectionElem::Index(local) => MemoryProjection::Index(Box::new(
                    indices
                        .iter()
                        .find(|(key, _)| key == local)
                        .map(|(_, value)| value.clone())
                        .ok_or("tracked call destination omitted its pre-call index")?,
                )),
                ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => MemoryProjection::Index(Box::new(symbolic::integer(
                    &self.terms,
                    u128::from(*offset),
                    bits,
                    false,
                ))),
                _ => return Err(unsupported()),
            });
        }
        Ok(CapturedTrackedDestination {
            location,
            original: *original,
            target,
            path,
        })
    }

    pub(super) fn store_tracked_call_result(
        &self,
        state: &mut State,
        captured: &CapturedTrackedDestination<'tcx>,
        value: Value,
    ) -> Result<(), String> {
        captured.location.require_write(&state.memory)?;
        let storage = captured.location.read(&state.memory)?;
        self.validate_owned_product_update(
            captured.original,
            storage,
            captured.target,
            &value,
            &state.conditions,
        )?;
        let mut storage = storage.clone();
        self.write_projection(&mut storage, &captured.path, value, &state.conditions)?;
        captured.location.write(&mut state.memory, storage)
    }
}
