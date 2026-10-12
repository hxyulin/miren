use super::*;
use rustc_span::Symbol;
use symbolic::MemoryProjection;

impl<'tcx> Engine<'tcx> {
    pub(super) fn unchecked_slice_iterator_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &mut State,
    ) -> Result<Option<Return>, String> {
        let callee = instance.def_id();
        if self.tcx.item_name(callee) != Symbol::intern("__iterator_get_unchecked") {
            return Ok(None);
        }
        let Some(iterator_trait) = self.tcx.get_diagnostic_item(Symbol::intern("Iterator")) else {
            return Ok(None);
        };
        let parent = self.tcx.parent(callee);
        if callee.krate != iterator_trait.krate
            || !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            || self
                .tcx
                .impl_trait_ref(parent)
                .instantiate(self.tcx, instance.args)
                .skip_norm_wip()
                .def_id
                != iterator_trait
        {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        let [receiver_ty, index_ty] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Ref(_, iterator_ty, receiver_mutability) = receiver_ty.kind() else {
            return Ok(None);
        };
        let Some(mutable) = self.slice_iterator_kind(*iterator_ty) else {
            return Ok(None);
        };
        let ty::Adt(_, args) = iterator_ty.kind() else {
            return Ok(None);
        };
        let ty::Ref(_, element, result_mutability) = signature.output().kind() else {
            return Ok(None);
        };
        let iterator_element = args
            .types()
            .next()
            .ok_or("unchecked slice iterator has no compiler element type")?;
        if !receiver_mutability.is_mut()
            || *index_ty != self.tcx.types.usize
            || *element != iterator_element
            || result_mutability.is_mut() != mutable
        {
            return Err(
                "unchecked slice iterator signature does not match its compiler type".into(),
            );
        }
        if self.induction {
            return Err("unchecked iterator access needs retained finite access history".into());
        }
        let [receiver, offset] = values else {
            return Err("unchecked slice iterator arguments are missing".into());
        };
        if !matches!(receiver, Value::Reference { mutable: true, .. }) {
            return Err("unchecked iteration needs a retained writable iterator receiver".into());
        }
        self.validate_tracked_value(receiver, state)?;
        let iterator = self.snapshot(receiver, &state.memory, &state.conditions, 0)?;
        let Value::SliceIterator {
            source,
            front,
            back,
            mutable: actual,
            mut unchecked,
        } = iterator
        else {
            return Err("unchecked slice iterator needs a retained cursor and source".into());
        };
        if actual != mutable {
            return Err("unchecked iterator mutability differs from its compiler type".into());
        }
        if !matches!(
            &*source,
            Value::Reference { .. } | Value::StaticSlice { .. }
        ) {
            return Err(
                "unchecked iterator needs retained source liveness; snapshots are insufficient"
                    .into(),
            );
        }
        self.validate_tracked_value(&source, state)?;
        let storage = self.snapshot(&source, &state.memory, &state.conditions, 0)?;
        let length = match &storage {
            Value::Bytes { length, .. } => (**length).clone(),
            Value::Elements(elements) => self.iterator_index(elements.len() as u128),
            Value::StaticSlice { elements, .. } => self.iterator_index(elements.len() as u128),
            _ => return Err("unchecked iterator backing storage is unsupported".into()),
        };
        let ordered =
            symbolic::binary(&self.terms, "le", (*front).clone(), (*back).clone())?.boolean()?;
        let backed =
            symbolic::binary(&self.terms, "le", (*back).clone(), length.clone())?.boolean()?;
        let safe = self.terms.apply(Op::And, &[ordered, backed])?;
        if self.feasible(&[state.conditions.clone(), vec![symbolic::not(&safe)]].concat())? {
            return Err("unchecked iterator cursor bounds are not established".into());
        }
        let remaining = symbolic::binary(&self.terms, "sub", (*back).clone(), (*front).clone())?;
        self.memory_bounds(offset, &remaining, &state.conditions)?;
        let index = symbolic::binary(&self.terms, "add", (*front).clone(), offset.clone())?;
        self.memory_bounds(&index, &length, &state.conditions)?;
        let item = if let Value::Reference {
            allocation,
            projection,
            mutable: writable,
        } = &*source
        {
            if mutable && !writable {
                return Err("unchecked mutable iterator needs writable source backing".into());
            }
            let mut projection = projection.clone();
            projection.push(MemoryProjection::Index(Box::new(index.clone())));
            Value::Reference {
                allocation: *allocation,
                projection,
                mutable,
            }
        } else if !mutable {
            match &storage {
                Value::Elements(elements) => {
                    self.fixed_element(elements, &index, &state.conditions)?
                }
                Value::StaticSlice { elements, .. } => {
                    self.fixed_element(elements, &index, &state.conditions)?
                }
                Value::Bytes { data, .. } => Value::Int {
                    expression: self
                        .terms
                        .apply(Op::Select, &[data.clone(), index.integer()?.0])?,
                    bits: 8,
                    signed: false,
                },
                _ => return Err("unchecked shared iterator element storage is unsupported".into()),
            }
        } else {
            return Err("unchecked mutable iterator needs retained allocation backing".into());
        };
        if mutable {
            if unchecked.len() >= 256 {
                return Err(
                    "unchecked mutable iterator exceeds its 256-element access budget".into(),
                );
            }
            for issued in &unchecked {
                let equal = symbolic::binary(&self.terms, "eq", issued.clone(), index.clone())?
                    .boolean()?;
                if self.feasible(&[state.conditions.clone(), vec![equal]].concat())? {
                    return Err("unchecked mutable iterator indices may overlap".into());
                }
            }
            unchecked.push(index);
        }
        let iterator = Value::SliceIterator {
            source,
            front,
            back,
            mutable,
            unchecked,
        };
        self.store_iterator(receiver, iterator, &mut state.memory, &state.conditions)?;
        self.record_model(
            callee,
            "core unchecked slice iteration; proven bounds and distinct mutable indices",
        );
        Ok(Some(Return {
            flow: activation_flow::Flow::Unarmed,
            value: item,
            conditions: state.conditions.clone(),
            memory: state.memory.clone(),
        }))
    }
}
