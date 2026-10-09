use super::*;

const MAX_CALL_SIGNATURES: usize = 256;

// A safe Rust body can satisfy an unsafe callable declaration. Preserve every other
// signature component, including its bound variables, instead of rebuilding argument types.
pub(super) fn callable_signature_compatible<'tcx>(
    actual: ty::PolyFnSig<'tcx>,
    expected: ty::PolyFnSig<'tcx>,
) -> bool {
    actual == expected
        || (actual.skip_binder().safety() == rustc_hir::Safety::Safe
            && expected.skip_binder().safety() == rustc_hir::Safety::Unsafe
            && actual.map_bound(|signature| signature.set_safety(rustc_hir::Safety::Unsafe))
                == expected)
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn call_poly_signature(
        &self,
        instance: ty::Instance<'tcx>,
    ) -> Result<ty::PolyFnSig<'tcx>, String> {
        if let Some(signature) = self.call_signatures.borrow().get(&instance) {
            return Ok(*signature);
        }
        let signature = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                self.tcx
                    .fn_sig(instance.def_id())
                    .instantiate(self.tcx, instance.args),
            )
            .map_err(|error| format!("call signature normalization failed: {error:?}"))?;
        let mut signatures = self.call_signatures.borrow_mut();
        if signatures.len() < MAX_CALL_SIGNATURES {
            signatures.insert(instance, signature);
        }
        Ok(signature)
    }

    pub(super) fn call_signature(
        &self,
        instance: ty::Instance<'tcx>,
    ) -> Result<ty::FnSig<'tcx>, String> {
        self.call_poly_signature(instance)
            .map(|sig| sig.skip_binder())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn callable_safety_changes_only_allow_safe_bodies_beneath_unsafe_declarations() {
        let safe: ty::PolyFnSig<'_> = ty::Binder::dummy(ty::FnSig::dummy());
        let unsafe_signature =
            safe.map_bound(|signature| signature.set_safety(rustc_hir::Safety::Unsafe));
        assert!(callable_signature_compatible(safe, safe));
        assert!(callable_signature_compatible(
            unsafe_signature,
            unsafe_signature
        ));
        assert!(callable_signature_compatible(safe, unsafe_signature));
        assert!(!callable_signature_compatible(unsafe_signature, safe));
    }
}
