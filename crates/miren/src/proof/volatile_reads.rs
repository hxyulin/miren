//! Volatile scalar reads from initialized compiler-typed retained allocations only.
use super::*;
use rustc_span::Symbol;

impl<'tcx> Engine<'tcx> {
    pub(super) fn volatile_load(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Vec<Return>>, String> {
        if !self
            .tcx
            .is_intrinsic(instance.def_id(), Symbol::intern("volatile_load"))
        {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        let [input] = signature.inputs() else {
            return Err("volatile load requires exactly one compiler pointer input".into());
        };
        let ty::RawPtr(pointee, mutability) = input.kind() else {
            return Err("volatile load requires a thin const pointer".into());
        };
        if mutability.is_mut() || signature.output() != *pointee {
            return Err("volatile load compiler input/output types disagree".into());
        }
        let [
            pointer @ Value::TrackedPointer {
                reference,
                address,
                bits,
            },
        ] = values
        else {
            return Err(
                "volatile load requires retained allocation provenance; numeric and \
                        shared static addresses are unsupported"
                    .into(),
            );
        };
        self.validate_tracked_value(pointer, state)?;
        let Value::Reference {
            allocation,
            projection,
            ..
        } = reference.as_ref()
        else {
            return Err("volatile load requires an ordinary retained allocation reference".into());
        };
        if *bits != u32::from(self.tcx.sess.target.pointer_width) || !projection.is_empty() {
            return Err(
                "volatile load requires a whole scalar allocation without projections".into(),
            );
        }
        let layout = self.static_layout(*pointee)?;
        if !self.tracked_addresses.iter().any(|(location, registered)| {
            registered == address
                && location.allocation == *allocation
                && location.pointee == *pointee
                && location.projection.is_empty()
                && location.cursor.is_none()
                && location.extent == layout.size.bytes()
        }) {
            return Err(
                "volatile load lacks exact compiler-typed whole allocation evidence".into(),
            );
        }
        let value = self.reference_value(reference, &state.memory, &state.conditions)?;
        let valid = match &value {
            Value::Bool(_) => *pointee == self.tcx.types.bool,
            Value::Int { bits, signed, .. } => {
                matches!(pointee.kind(), ty::Int(_) | ty::Uint(_))
                    && self.integer_type(*pointee) == Some((*bits, *signed))
            }
            Value::Float { bits, .. } => self.float_type(*pointee) == Some(*bits),
            _ => false,
        };
        if !valid {
            return Err(
                "volatile load requires initialized retained scalar of its exact type".into(),
            );
        }
        // Layout, initialization and liveness do not certify temporal access permission.
        // Do not expose the retained value until an access model supplies that certificate.
        Err(self.categorized_error(UnknownCategory::Semantics, RAW_ACCESS_PERMISSION_GAP.into()))
    }
}
