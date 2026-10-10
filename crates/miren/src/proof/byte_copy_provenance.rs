//! Provenance eligibility for the new finite-copy path, never a storage capability.
use super::*;

#[derive(Clone)]
pub(super) struct IncomingByteRoot {
    pub(super) allocation: usize,
    pub(super) capacity: Value,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn incoming_byte_copy_root(&self, id: DefId, body: &Body<'tcx>) -> bool {
        if !matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) {
            return false;
        }
        let signature = self.tcx.fn_sig(id).instantiate_identity().skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return false;
        }
        let mut roots = 0;
        for local in body.args_iter() {
            match body.local_decls[local].ty.kind() {
                ty::Ref(_, pointee, rustc_hir::Mutability::Mut) => {
                    if !matches!(pointee.kind(), ty::Slice(element)
                        if *element == self.tcx.types.u8)
                    {
                        return false;
                    }
                    roots += 1;
                }
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => {}
                _ => return false,
            }
        }
        roots == 1
    }

    fn byte_copy_transport_type(&self, original: Ty<'tcx>) -> bool {
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
            ty::Tuple(fields) => fields.is_empty(),
            ty::Ref(_, pointee, _) => {
                *pointee == self.tcx.types.u8
                    || matches!(pointee.kind(), ty::Slice(element) | ty::Array(element, _)
                        if *element == self.tcx.types.u8)
            }
            ty::Adt(def, args) => {
                self.tcx.lang_items().get(LangItem::RangeTo) == Some(def.did())
                    && args.type_at(0) == self.tcx.types.usize
            }
            _ => false,
        }
    }

    pub(super) fn byte_copy_call_eligibility(
        &self,
        instance: ty::Instance<'tcx>,
        indirect: bool,
        state: &mut State,
    ) {
        // Restrict every shortcut too: raw inputs/outputs or unsafe/foreign/indirect transport
        // cannot recover the incoming safe slice provenance merely by retaining allocation IDs.
        let item = instance.def_id();
        if indirect
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(self.tcx.def_kind(item), DefKind::Fn | DefKind::AssocFn)
        {
            state.memory.byte_copy_opaque = true;
            return;
        }
        let Ok(signature) = self.call_signature(instance) else {
            state.memory.byte_copy_opaque = true;
            return;
        };
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature
                .inputs()
                .iter()
                .any(|ty| !self.byte_copy_transport_type(*ty))
            || !self.byte_copy_transport_type(signature.output())
        {
            state.memory.byte_copy_opaque = true;
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn byte_copy_current_destination(
        &self,
        reference: &Value,
        state: &State,
    ) -> Result<(usize, Value), String> {
        if state.memory.byte_copy_opaque {
            return Err("finite byte copy needs an unexposed incoming writable origin".into());
        }
        let Value::Reference {
            allocation,
            projection,
            mutable: true,
        } = reference
        else {
            return Err("finite byte copy needs current writable tracked storage".into());
        };
        if projection.len() > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "finite byte copy view exceeds the existing 16-depth budget".into(),
            ));
        }
        if projection.is_empty()
            || projection
                .iter()
                .any(|step| !matches!(step, symbolic::MemoryProjection::Slice { .. }))
        {
            return Err("finite byte copy needs an exact safe slice view".into());
        }
        let origin = state
            .memory
            .incoming_byte_roots
            .iter()
            .find(|origin| origin.allocation == *allocation)
            .ok_or("finite byte copy has no original incoming byte issuer")?;
        let location = storage_locations::StorageLocation::tracked(*allocation, true);
        location.require_write(&state.memory)?;
        let current = location.read(&state.memory)?;
        let Value::Bytes { length, data } = current else {
            return Err("finite byte copy current owner has a different original carrier".into());
        };
        let (capacity, bits, signed) = length.integer()?;
        let (issued, issued_bits, issued_signed) = origin.capacity.integer()?;
        let target_bits = u32::from(self.tcx.sess.target.pointer_width);
        if signed
            || issued_signed
            || bits != target_bits
            || issued_bits != target_bits
            || capacity != issued
            || data.sort() != &Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8)))
        {
            return Err("finite byte copy current extent/type differs from its issuer".into());
        }
        // Both operations reject foreign Terms even when their SMT sorts happen to agree.
        self.terms
            .apply(Op::BvAdd, &[capacity, self.terms.bit_vector(0, bits)?])?;
        self.terms
            .apply(Op::Select, &[data.clone(), self.terms.bit_vector(0, bits)?])?;
        self.validate_tracked_value(reference, state)?;
        Ok((*allocation, current.clone()))
    }
}
