//! Terminal callee locals are never encoded into a successor Horn state.
use super::*;

impl<'tcx> Engine<'tcx> {
    pub(super) fn validate_terminal_arguments(
        &self,
        frame: &Frame<'tcx>,
        state: &State,
    ) -> Result<(), String> {
        if !state.memory.missing_places.is_empty() {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "inductive return retains unavailable allocation storage".into(),
            ));
        }
        for (owner, _) in state.missing_places.entries() {
            let mut nodes = 0;
            if *owner == 0
                || *owner > frame.body.arg_count
                || state.addresses.get(*owner) != Some(&None)
                || !self.terminal_owned_argument_type(
                    frame.body.local_decls[rustc_middle::mir::Local::from_usize(*owner)].ty,
                    0,
                    &mut nodes,
                )
            {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "inductive return retains an observable consumed source place".into(),
                ));
            }
        }
        Ok(())
    }

    fn terminal_owned_argument_type(
        &self,
        original: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> bool {
        *nodes += 1;
        let env = ty::TypingEnv::fully_monomorphized();
        if depth >= MAX_INPUT_DEPTH
            || *nodes > MAX_STATE_VALUES
            || !original.is_freeze(self.tcx, env)
            || original.needs_drop(self.tcx, env)
        {
            return false;
        }
        match original.kind() {
            ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
            ty::Tuple(fields) => fields
                .iter()
                .all(|field| self.terminal_owned_argument_type(field, depth + 1, nodes)),
            ty::Array(element, count) => {
                // Original child eligibility is required even for an empty array.
                let Some(count) = count.try_to_target_usize(self.tcx) else {
                    return false;
                };
                count <= 128 && self.terminal_owned_argument_type(*element, depth + 1, nodes)
            }
            ty::Adt(definition, args)
                if definition.did().is_local()
                    && self.plain_composite_struct(*definition)
                    && !definition.repr().packed() =>
            {
                definition.non_enum_variant().fields.iter().all(|field| {
                    self.terminal_owned_argument_type(
                        self.tcx
                            .type_of(field.did)
                            .instantiate(self.tcx, args)
                            .skip_norm_wip(),
                        depth + 1,
                        nodes,
                    )
                })
            }
            _ => false,
        }
    }
}
