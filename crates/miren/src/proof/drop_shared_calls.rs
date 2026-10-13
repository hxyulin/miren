//! Ordinary shared Drop receivers execute actual Rust bodies without detached owner snapshots.
use super::*;
use rustc_middle::mir::BasicBlock;
use std::rc::Rc;

impl<'tcx> Engine<'tcx> {
    fn shared_drop_signature(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<Option<ty::FnSig<'tcx>>, String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !instance.def_id().is_local()
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || self.tcx.coroutine_kind(instance.def_id()).is_some()
            || self
                .specification(instance)?
                .is_some_and(|spec| spec.trusted)
            || self.foreign_rust_target(instance)?.is_some()
        {
            return Ok(None);
        }
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return Ok(None);
        }
        let [parameter] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Ref(_, original, rustc_hir::Mutability::Not) = parameter.kind() else {
            return Ok(None);
        };
        if !drop_shared_projections::readonly_drop_struct(self.tcx, *original) {
            return Ok(None);
        }
        if !matches!(
            signature.output().kind(),
            ty::Bool
                | ty::Char
                | ty::Int(_)
                | ty::Uint(_)
                | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
        ) {
            return Ok(None);
        }
        Ok(Some(signature))
    }

    pub(super) fn shared_drop_receiver_arguments(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<bool, String> {
        let Some(signature) = self.shared_drop_signature(instance)? else {
            return Ok(false);
        };
        self.validate_shared_drop_argument(signature, values, memory, conditions)
    }

    fn validate_shared_drop_argument(
        &self,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<bool, String> {
        let ty::Ref(_, expected, rustc_hir::Mutability::Not) = signature.inputs()[0].kind() else {
            return Ok(false);
        };
        let [receiver] = values else {
            return Err("shared Drop call argument arity differs".into());
        };
        let Some(original) = self
            .shared_drop_reference_target(receiver, memory, conditions)
            .map_err(|reason| self.drop_shared_error(reason))?
        else {
            return Ok(false);
        };
        if original != *expected {
            return Err("shared Drop receiver original pointee type differs".into());
        }
        Ok(true)
    }

    pub(super) fn shared_drop_receiver_call(
        &mut self,
        source: (ty::Instance<'tcx>, &Rc<Body<'tcx>>, BasicBlock),
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<Return>>, String> {
        if !matches!(state.flow, activation_flow::Flow::Unarmed) {
            return Ok(None);
        }
        let Some(signature) = self.shared_drop_signature(instance)? else {
            return Ok(None);
        };
        if !self.validate_shared_drop_argument(
            signature,
            values,
            &state.memory,
            &state.conditions,
        )? {
            return Ok(None);
        }
        let parameter = signature.inputs()[0];
        let (caller, body, block) = source;
        if !Rc::ptr_eq(body, &self.instantiated_body(caller)?) {
            return Err("shared Drop call requires its actual current caller Body".into());
        }
        let terminator = body
            .basic_blocks
            .get(block)
            .ok_or("shared Drop call block is unavailable")?
            .terminator();
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            return Err("shared Drop receiver route requires an actual Call".into());
        };
        let ty::FnDef(callee, arguments) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("shared Drop receiver route requires original FnDef".into());
        };
        if self.resolve_function_item(*callee, arguments.skip_binder())? != instance
            || args.len() != 1
            || args[0].node.ty(&body.local_decls, self.tcx) != parameter
        {
            return Err("shared Drop actual Call or original receiver signature differs".into());
        }
        if !self.tcx.is_mir_available(instance.def_id()) {
            return Err(self.categorized_error(
                UnknownCategory::MissingCompilerEvidence,
                self.missing_body_reason(instance.def_id()),
            ));
        }
        let callee = self.instantiated_body(instance)?;
        if callee.source.instance != instance.def
            || callee.source.promoted.is_some()
            || callee.coroutine.is_some()
            || callee.arg_count != 1
            || callee.local_decls[rustc_middle::mir::Local::from_usize(1)].ty != parameter
            || callee.return_ty() != signature.output()
        {
            return Err("shared Drop callee original Body or signature differs".into());
        }
        // Contracts remain in the normal call path. Requires/Ensures needing whole snapshots
        // still refuse; NoPanic executes and verifies the actual helper body.
        state
            .flow
            .charge_call_memory(&state.conditions, &state.memory)?;
        self.call_instance_flow(
            &mut state.flow,
            instance,
            values.to_vec(),
            state.conditions.clone(),
            state.memory.clone(),
            (stack, (caller.def_id(), terminator.source_info.span)),
        )
        .map(Some)
    }
}

#[cfg(test)]
#[path = "drop_shared_calls_probe.rs"]
mod probe;
