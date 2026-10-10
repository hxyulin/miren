use super::*;
use rustc_middle::ty::adjustment::PointerCoercion;

#[derive(Clone, PartialEq)]
pub(super) enum Target<'tcx> {
    Known {
        instance: ty::Instance<'tcx>,
        signature: Ty<'tcx>,
    },
    Opaque {
        signature: Ty<'tcx>,
    },
    Choice(super::function_tables::Choice<'tcx>),
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn reify_function_pointer(
        &mut self,
        kind: PointerCoercion,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
    ) -> Result<Value, String> {
        if !matches!(kind, PointerCoercion::ReifyFnPointer(_)) {
            return Err("only known function-item pointer coercions are modeled".into());
        }
        let ty::FnDef(id, args) = source.kind() else {
            return Err("function-pointer coercion needs a concrete function item".into());
        };
        let instance = ty::Instance::resolve_for_fn_ptr(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            *id,
            args.skip_binder(),
        )
        .ok_or_else(|| {
            format!(
                "unresolved function-pointer target {}",
                self.tcx.def_path_str(*id)
            )
        })?;
        if !matches!(instance.def, ty::InstanceKind::Item(_)) {
            return Err(format!(
                "unsupported function-pointer adapter {:?}",
                instance.def
            ));
        }
        let signature = self.call_poly_signature(ty::Instance::new_raw(*id, args.skip_binder()))?;
        let expected = self
            .tcx
            .erase_and_anonymize_regions(Ty::new_fn_ptr(self.tcx, signature));
        let target = self.tcx.erase_and_anonymize_regions(target);
        if !matches!(target.kind(), ty::FnPtr(..))
            || !call_metadata::callable_signature_compatible(
                expected.fn_sig(self.tcx),
                target.fn_sig(self.tcx),
            )
        {
            return Err("function-pointer coercion changes the callable signature".into());
        }
        let entry = Target::Known {
            instance,
            signature: target,
        };
        let id = self.register_function_pointer(entry)?;
        Ok(Value::FunctionPointer { id })
    }

    pub(super) fn known_function_pointer(
        &self,
        value: &Value,
        callable: Ty<'tcx>,
    ) -> Result<ty::Instance<'tcx>, String> {
        let Value::FunctionPointer { id } = value else {
            return Err("indirect call needs a known function-pointer target".into());
        };
        let pointers = self.function_pointers.borrow();
        let target = pointers
            .get(*id)
            .ok_or("function-pointer target is missing")?;
        let Target::Known {
            instance,
            signature,
        } = target
        else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "indirect call through an arbitrary function-pointer input is unsupported".into(),
            ));
        };
        let callable = self.tcx.erase_and_anonymize_regions(callable);
        if callable != *signature {
            return Err("indirect-call signature differs from its known target".into());
        }
        Ok(*instance)
    }
}
