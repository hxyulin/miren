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

    pub(super) fn retain_byte_copy_array_source(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.incoming_byte_roots.is_empty()
            || state.memory.byte_copy_opaque
            || !place.projection.is_empty()
        {
            return Ok(None);
        }
        let Some(declaration) = body.local_decls.get(place.local) else {
            return Err("byte copy source local is outside its current body".into());
        };
        let ty::Array(element, count) = declaration.ty.kind() else {
            return Ok(None);
        };
        if *element != self.tcx.types.u8 {
            return Ok(None);
        }
        let Some(count) = count
            .try_to_target_usize(self.tcx)
            .filter(|count| *count <= 128)
        else {
            return Ok(None);
        };
        state.flow.require_unarmed()?;
        let value = self.local(state, place.local.as_usize())?;
        let Value::Bytes { length, data } = &value else {
            return Err("byte copy array source lacks its current original carrier".into());
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        if !aggregate_validity::byte_array_payload_matches(&self.terms, bits, count, length, data)?
        {
            return Err("byte copy array source has a different original extent or codec".into());
        }
        let index = place.local.as_usize();
        let allocation = if let Some(allocation) = state.addresses[index] {
            storage_locations::StorageLocation::tracked(allocation, false).read(&state.memory)?;
            allocation
        } else {
            if state.memory.storage_slots() >= memory::MAX_ALLOCATIONS {
                return Err("memory allocation budget reached".into());
            }
            let allocation = state.memory.len();
            state.memory.push(Some(value));
            state
                .missing_places
                .transfer(index, allocation, &mut state.memory.missing_places)
                .map_err(|reason| self.categorized_error(UnknownCategory::ResourceLimit, reason))?;
            state.addresses[index] = Some(allocation);
            allocation
        };
        Ok(Some(Value::Reference {
            allocation,
            projection: Vec::new(),
            mutable: false,
        }))
    }

    pub(super) fn byte_copy_local_source(
        &self,
        body: &Body<'tcx>,
        origin: &byte_copy_origins::SourceOrigin,
        raw_source: &Value,
        source: &Value,
        raw_destination: &Value,
        state: &State,
    ) -> Result<(), String> {
        let byte_copy_origins::SourceOrigin::LocalArray { local, count } = origin else {
            return Err("byte copy local source needs its exact original borrow".into());
        };
        let Some(declaration) = body.local_decls.get(*local) else {
            return Err("byte copy original source local is outside its body".into());
        };
        if !matches!(declaration.ty.kind(), ty::Array(element, extent)
            if *element == self.tcx.types.u8
                && extent.try_to_target_usize(self.tcx) == Some(*count))
        {
            return Err("byte copy original array source type or extent changed".into());
        }
        let Value::Reference {
            allocation,
            projection,
            mutable: false,
        } = raw_source
        else {
            return Err("byte copy local source lacks an actual readonly tracked borrow".into());
        };
        let Value::Reference {
            allocation: destination,
            ..
        } = raw_destination
        else {
            return Err("byte copy local source lacks a tracked destination".into());
        };
        if !projection.is_empty()
            || allocation == destination
            || state.addresses.get(local.as_usize()) != Some(&Some(*allocation))
        {
            return Err(
                "byte copy original source allocation differs or overlaps destination".into(),
            );
        }
        self.validate_tracked_value(raw_source, state)?;
        let current =
            storage_locations::StorageLocation::tracked(*allocation, false).read(&state.memory)?;
        let (
            Value::Bytes { length, data },
            Value::Bytes {
                length: seen,
                data: snapshot,
            },
        ) = (current, source)
        else {
            return Err("byte copy local source lacks initialized byte storage".into());
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        if *count > 128
            || length.integer()? != seen.integer()?
            || data != snapshot
            || !aggregate_validity::byte_array_payload_matches(
                &self.terms,
                bits,
                *count,
                length,
                data,
            )?
        {
            return Err(
                "byte copy evaluated snapshot differs from its current original array".into(),
            );
        }
        Ok(())
    }

    fn byte_copy_local_array_output(
        &self,
        instance: ty::Instance<'tcx>,
        signature: &ty::FnSig<'tcx>,
    ) -> bool {
        if !instance.def_id().is_local()
            || !instance.args.is_empty()
            || !self.tcx.is_mir_available(instance.def_id())
            || signature
                .inputs()
                .iter()
                .any(|ty| !matches!(ty.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)))
        {
            return false;
        }
        matches!(signature.output().kind(), ty::Array(element, count)
            if *element == self.tcx.types.u8
                && count.try_to_target_usize(self.tcx).is_some_and(|count| count <= 128))
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
            || (!self.byte_copy_transport_type(signature.output())
                && !self.byte_copy_local_array_output(instance, &signature))
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
