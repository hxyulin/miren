use super::function_pointers::Target;
use super::*;

impl<'tcx> Engine<'tcx> {
    pub(super) fn register_function_pointer(&self, entry: Target<'tcx>) -> Result<usize, String> {
        let mut pointers = self.function_pointers.borrow_mut();
        if let Some(id) = pointers.iter().position(|item| *item == entry) {
            return Ok(id);
        }
        let used = pointers.iter().try_fold(0_usize, |used, entry| {
            used.checked_add(super::function_tables::registry_cost(entry))
        });
        if used
            .and_then(|used| used.checked_add(super::function_tables::registry_cost(&entry)))
            .is_none_or(|next| next > 512)
        {
            return Err(
                "typed function-pointer registry exceeds 512 signatures and targets".into(),
            );
        }
        let id = pointers.len();
        pointers.push(entry);
        Ok(id)
    }

    pub(super) fn opaque_function_pointer_id(&self, signature: Ty<'tcx>) -> Result<usize, String> {
        if !matches!(signature.kind(), ty::FnPtr(..)) {
            return Err(
                "opaque function-pointer input needs a compiler function-pointer type".into(),
            );
        }
        let signature = self.tcx.erase_and_anonymize_regions(signature);
        self.register_function_pointer(Target::Opaque { signature })
    }

    pub(super) fn opaque_function_pointer_input(
        &self,
        signature: Ty<'tcx>,
    ) -> Result<Value, String> {
        let id = self.opaque_function_pointer_id(signature)?;
        // This token covers every valid pointer of this compiler signature. It records no
        // numeric address, target identity, purity, termination, or callback effects. Tokens
        // with the same signature are not evidence that the input pointers compare equal.
        Ok(Value::FunctionPointer { id })
    }

    pub(super) fn function_pointer_input_description(
        &self,
        value: &Value,
    ) -> Result<String, String> {
        let Value::FunctionPointer { id } = value else {
            return Err("function-pointer input description needs a signature witness".into());
        };
        let pointers = self.function_pointers.borrow();
        match pointers
            .get(*id)
            .ok_or("function-pointer input witness is missing")?
        {
            Target::Opaque { signature } => Ok(format!(
                "arbitrary valid function pointer {signature}; target and callback effects unknown"
            )),
            Target::Known {
                instance,
                signature,
            } => Ok(format!(
                "compiler function pointer {signature}; target {}",
                self.tcx.def_path_str(instance.def_id())
            )),
            Target::Choice(_) => Err("function table choice is not an incoming pointer".into()),
        }
    }

    pub(super) fn validate_function_pointer(
        &self,
        value: &Value,
        signature: Ty<'tcx>,
    ) -> Result<(), String> {
        let Value::FunctionPointer { id } = value else {
            return Err("typed function-pointer storage needs a retained signature witness".into());
        };
        let pointers = self.function_pointers.borrow();
        let target = pointers
            .get(*id)
            .ok_or("function-pointer signature witness is missing")?;
        let retained = match target {
            Target::Known { signature, .. } | Target::Opaque { signature } => *signature,
            Target::Choice(choice) => choice.signature(),
        };
        if self.tcx.erase_and_anonymize_regions(signature) != retained {
            return Err("function-pointer storage changes the retained callable signature".into());
        }
        Ok(())
    }
}
