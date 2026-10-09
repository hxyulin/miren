use super::*;
use crate::symbolic::MemoryProjection;
use rustc_span::Symbol;

impl<'tcx> Engine<'tcx> {
    pub(super) fn isolated_pointer_atomic_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &mut State,
        site: (DefId, Span),
    ) -> Result<Option<Value>, String> {
        if !self.isolated_startup {
            return Ok(None);
        }
        let parent = self.tcx.parent(instance.def_id());
        if !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false }) {
            return Ok(None);
        }
        let receiver_ty = self
            .tcx
            .type_of(parent)
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        if let Some(value) =
            self.isolated_pointer_atomic_store_call(instance, receiver_ty, values, state, site)?
        {
            return Ok(Some(value));
        }
        if let Some(value) = self.pointer_atomic_load(instance, receiver_ty, values, state, site)? {
            return Ok(Some(value));
        }
        self.pointer_atomic_compare_exchange(instance, receiver_ty, values, state, site)
    }

    fn isolated_pointer_atomic_store_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        receiver_ty: Ty<'tcx>,
        values: &[Value],
        state: &mut State,
        site: (DefId, Span),
    ) -> Result<Option<Value>, String> {
        let Some(atomic) = self.tcx.get_diagnostic_item(Symbol::intern("Atomic")) else {
            return Ok(None);
        };
        let ty::Adt(definition, arguments) = receiver_ty.kind() else {
            return Ok(None);
        };
        if definition.did() != atomic
            || instance.def_id().krate != atomic.krate
            || self.tcx.item_name(instance.def_id()) != Symbol::intern("store")
        {
            return Ok(None);
        }
        let pointer_ty = arguments.type_at(0);
        if !self.thin_raw_pointer(pointer_ty) {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        let ([reference_ty, value_ty, ordering_ty], [receiver, value, ordering]) =
            (signature.inputs(), values)
        else {
            return Err("isolated pointer atomic store signature mismatch".into());
        };
        if !signature.output().is_unit()
            || *value_ty != pointer_ty
            || !matches!(reference_ty.kind(), ty::Ref(_, element, mutability)
                if *element == receiver_ty && !mutability.is_mut())
        {
            return Err(
                "isolated pointer atomic store requires its exact primitive signature".into(),
            );
        }
        let safe = self.atomic_order(ordering, *ordering_ty, &["Relaxed", "Release", "SeqCst"])?;
        self.require(
            site.0,
            site.1,
            &state.conditions,
            &safe,
            ObligationKind::PanicSafety,
            "pointer atomic store requires a valid non-acquire ordering".into(),
        )?;
        state.conditions.push(safe);
        self.validate_pointer_atomic_receiver(receiver_ty, pointer_ty, receiver, state)?;
        self.validate_tracked_value(value, state)?;
        self.isolated_pointer_address(value, pointer_ty, state)?;
        if state.memory.startup_invalidated && !matches!(receiver, Value::StaticView { .. }) {
            return Err(
                "isolated pointer atomic store requires valid local backing history".into(),
            );
        }
        if !state.memory.startup_invalidated {
            self.write_isolated_pointer_atomic(
                receiver,
                receiver_ty,
                pointer_ty,
                value.clone(),
                state,
            )?;
        }
        self.record_model(
            instance.def_id(),
            "isolated-entry pointer atomic store; typed backing update",
        );
        Ok(Some(Value::Unit))
    }

    pub(super) fn isolated_pointer_atomic_load(
        &mut self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        state: &State,
    ) -> Result<Option<Value>, String> {
        if !self.isolated_startup || state.memory.startup_invalidated {
            return Ok(None);
        }
        if matches!(receiver, Value::StaticView { .. }) {
            return Ok(None);
        }
        let (_, _, value) =
            self.isolated_pointer_atomic_place(receiver, receiver_ty, pointer_ty, state)?;
        Ok(Some(value))
    }

    fn isolated_pointer_atomic_place(
        &self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        state: &State,
    ) -> Result<(usize, Vec<MemoryProjection>, Value), String> {
        let Value::Reference {
            allocation,
            projection,
            ..
        } = receiver
        else {
            return Err("isolated pointer atomic needs allocation-backed storage".into());
        };
        let mut allocation = *allocation;
        let mut path = projection.clone();
        let mut value = self.reference_value(receiver, &state.memory, &state.conditions)?;
        let mut ty = receiver_ty;
        let atomic = self
            .tcx
            .get_diagnostic_item(Symbol::intern("Atomic"))
            .ok_or("pointer atomic storage compiler identity unavailable")?;
        for _ in 0..8 {
            if let Value::Reference {
                allocation: inner,
                projection,
                ..
            } = &value
            {
                allocation = *inner;
                path = projection.clone();
                value = self.reference_value(&value, &state.memory, &state.conditions)?;
            }
            if ty == pointer_ty {
                return Ok((allocation, path, value));
            }
            let wrapper = self.pointer_atomic_wrapper(ty, atomic.krate)?;
            let Value::Adt { fields, .. } = value else {
                return Err("isolated pointer atomic wrapper is not initialized".into());
            };
            let [(_, inner)] = fields.as_slice() else {
                return Err("isolated pointer atomic wrapper has invalid field count".into());
            };
            value = inner.clone();
            path.push(MemoryProjection::Field(0));
            ty = wrapper.field_ty;
        }
        Err("isolated pointer atomic storage exceeds the wrapper budget".into())
    }

    pub(super) fn isolated_pointer_atomic_update(
        &mut self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        pointers: (&Value, &Value),
        succeeds: &Term,
        state: &mut State,
    ) -> Result<(), String> {
        let (old, replacement) = pointers;
        let fails = symbolic::not(succeeds);
        let success_possible =
            self.feasible(&[state.conditions.clone(), vec![succeeds.clone()]].concat())?;
        let failure_possible = self.feasible(&[state.conditions.clone(), vec![fails]].concat())?;
        let value = if !success_possible {
            old.clone()
        } else if !failure_possible {
            replacement.clone()
        } else {
            let Value::RawPointer {
                address: before,
                bits,
            } = self.isolated_pointer_address(old, pointer_ty, state)?
            else {
                return Err("isolated pointer old address normalization failed".into());
            };
            let Value::RawPointer {
                address: after,
                bits: width,
            } = self.isolated_pointer_address(replacement, pointer_ty, state)?
            else {
                return Err("isolated pointer replacement address normalization failed".into());
            };
            if bits != width {
                return Err("isolated pointer atomic update has inconsistent widths".into());
            }
            // Retain only selected address bits when the result can have different origins.
            // The actual observed old pointer remains intact in the returned CAS result.
            Value::RawPointer {
                address: self
                    .terms
                    .apply(Op::Ite, &[succeeds.clone(), after, before])?,
                bits,
            }
        };
        self.write_isolated_pointer_atomic(receiver, receiver_ty, pointer_ty, value, state)
    }

    pub(super) fn isolated_pointer_address(
        &mut self,
        value: &Value,
        pointer_ty: Ty<'tcx>,
        state: &mut State,
    ) -> Result<Value, String> {
        let width = u32::from(self.tcx.sess.target.pointer_width);
        self.validate_tracked_value(value, state)?;
        if let Value::RawPointer { address, bits } | Value::TrackedPointer { address, bits, .. } =
            value
        {
            if *bits != width || *address.sort() != Sort::BitVec(width) {
                return Err("isolated pointer atomic address has an inconsistent width".into());
            }
            return Ok(Value::RawPointer {
                address: address.clone(),
                bits: *bits,
            });
        }
        if matches!(value, Value::StaticView { .. }) {
            self.static_stored_address(pointer_ty, value, state)?;
            let Value::Int {
                expression,
                bits,
                signed: false,
            } = self.expose_static_address(pointer_ty, self.tcx.types.usize, value, state)?
            else {
                return Err("isolated static pointer address normalization failed".into());
            };
            return Ok(Value::RawPointer {
                address: expression,
                bits,
            });
        }
        Err("isolated pointer atomic needs an initialized thin address handle".into())
    }

    fn write_isolated_pointer_atomic(
        &self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        value: Value,
        state: &mut State,
    ) -> Result<(), String> {
        if matches!(receiver, Value::StaticView { .. }) {
            self.isolated_pointer_atomic_store(receiver, receiver_ty, pointer_ty, value, state)?;
        } else {
            let (allocation, path, _) =
                self.isolated_pointer_atomic_place(receiver, receiver_ty, pointer_ty, state)?;
            let mut storage = state.memory[allocation]
                .clone()
                .ok_or("isolated pointer atomic backing allocation is retired")?;
            self.write_projection(&mut storage, &path, value, &state.conditions)?;
            state.memory[allocation] = Some(storage);
        }
        Ok(())
    }
}
