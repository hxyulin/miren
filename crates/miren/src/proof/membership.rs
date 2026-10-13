use super::*;
use rustc_span::Symbol;

const MAX_MEMBERSHIP_ELEMENTS: usize = 128;

impl<'tcx> Engine<'tcx> {
    fn core_slice_contains_trait(&self) -> Option<DefId> {
        let iterator = self.tcx.get_diagnostic_item(Symbol::intern("SliceIter"))?;
        let slice = self.tcx.parent(self.tcx.parent(iterator));
        let cmp = self.tcx.module_children(slice).iter().find_map(|child| {
            let id = child.res.opt_def_id()?;
            (child.ident.name == Symbol::intern("cmp")
                && id.krate == iterator.krate
                && self.tcx.def_kind(id) == DefKind::Mod)
                .then_some(id)
        })?;
        self.tcx.module_children(cmp).iter().find_map(|child| {
            let id = child.res.opt_def_id()?;
            (child.ident.name == Symbol::intern("SliceContains")
                && id.krate == iterator.krate
                && self.tcx.def_kind(id) == DefKind::Trait)
                .then_some(id)
        })
    }

    pub(super) fn slice_membership(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        raw_values: &[Value],
        state: &State,
        stack: &[DefId],
        call: &readonly_byte_origins::CallOccurrence<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let site = call.site()?;
        let callee = instance.def_id();
        if !self
            .tcx
            .lang_items()
            .get(LangItem::SliceLen)
            .is_some_and(|id| id.krate == callee.krate)
        {
            return Ok(None);
        }
        let parent = self.tcx.parent(callee);
        let name = self.tcx.item_name(callee);
        let slice_first = name == Symbol::intern("contains")
            && matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false })
            && matches!(
                self.tcx
                    .type_of(parent)
                    .instantiate(self.tcx, instance.args)
                    .skip_norm_wip()
                    .kind(),
                ty::Slice(_)
            );
        let element_first = name == Symbol::intern("slice_contains")
            && matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            && self.core_slice_contains_trait().is_some_and(|id| {
                self.tcx
                    .impl_trait_ref(parent)
                    .instantiate(self.tcx, instance.args)
                    .skip_norm_wip()
                    .def_id
                    == id
            });
        if !slice_first && !element_first {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        if !signature.output().is_bool() {
            return Ok(None);
        }
        let [first, second] = signature.inputs() else {
            return Ok(None);
        };
        let (slice_ty, needle_ty) = if slice_first {
            (*first, *second)
        } else {
            (*second, *first)
        };
        let (ty::Ref(_, slice, slice_mut), ty::Ref(_, element, needle_mut)) =
            (slice_ty.kind(), needle_ty.kind())
        else {
            return Ok(None);
        };
        if slice_mut.is_mut()
            || needle_mut.is_mut()
            || !matches!(slice.kind(), ty::Slice(item) if item == element)
        {
            return Ok(None);
        }
        let exact_niche = matches!(element.kind(), ty::Adt(def, args)
            if self.tcx.lang_items().get(LangItem::Option) == Some(def.did())
                && args.len() == 1
                && matches!(args.type_at(0).kind(), ty::Adt(payload, payload_args)
                    if self.tcx.is_diagnostic_item(Symbol::intern("NonZero"), payload.did())
                        && payload_args.len() == 1
                        && nonzero_options::readonly_niche_integer_type(
                            self.tcx, payload_args.type_at(0))
                            .is_some()));
        if exact_niche {
            state.flow.require_unarmed()?;
        }
        // New niche admission inventories original MIR before selected instantiation.
        if !exact_niche {
            self.instantiated_body(instance)?;
        }
        let [raw_first, raw_second] = raw_values else {
            return Err("slice membership requires two tracked arguments".into());
        };
        for (expected, value) in [(*first, raw_first), (*second, raw_second)] {
            self.validate_tracked_value(value, state)?;
            self.validate_readonly_slice_value(expected, value, &state.memory, &state.conditions)?;
        }
        let [first, second] = values else {
            return Err("slice membership requires two modeled arguments".to_owned());
        };
        let (slice, needle) = if slice_first {
            (first, second)
        } else {
            (second, first)
        };
        let slice = slice.materialize()?;
        if matches!(slice, Value::CompositeSlice { .. }) {
            if exact_niche {
                if matches!(element.kind(), ty::Adt(_, option)
                    if matches!(option.type_at(0).kind(), ty::Adt(_, nonzero)
                        if nonzero.type_at(0) == self.tcx.types.u8))
                {
                    let inputs = readonly_byte_origins::Inputs {
                        selected: instance,
                        slice_first,
                        raw: raw_values,
                        slice: &slice,
                        needle,
                    };
                    let origin = readonly_byte_origins::observe(self, call, &inputs, state)?;
                    origin.validate_current(self, call, state)?;
                    // These invocation-local facts grant no raw read or derived reference rights.
                    // The existing independently checked byte-membership refusal still applies.
                }
                let member =
                    self.exact_niche_membership(*element, instance, &slice, needle, state)?;
                self.record_model(
                    callee,
                    if matches!(element.kind(), ty::Adt(_, args)
                        if matches!(args.type_at(0).kind(), ty::Adt(_, payload)
                            if payload.type_at(0) == self.tcx.types.u16))
                    {
                        "exact checked core Option<NonZeroU16> slice membership"
                    } else {
                        "exact checked core Option<NonZeroU32> slice membership"
                    },
                );
                return Ok(Some(vec![Return {
                    value: Value::Bool(member),
                    conditions: state.conditions.clone(),
                    memory: state.memory.clone(),
                    flow: state.flow.clone(),
                }]));
            }
            let Some(plan) = self.pure_comparison_shape(*element)? else {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported".into(),
                ));
            };
            let length = self.composite_slice_length(&slice, &state.conditions)?;
            self.validate_owned_product(*element, needle, &state.conditions)?;
            let shape = self
                .owned_product_shape(*element)?
                .ok_or("composite membership needle has no exact compiler product")?;
            let needle = self.prepare_typed_product(*element, &shape, needle, 0)?;
            self.certify_pure_comparison(*element, instance)?;
            let (length, bits, _) = length.integer()?;
            let index = self.fresh(Sort::BitVec(bits));
            let item = self.composite_slice_logical_item(&slice, *element, &index)?;
            let equal = self.pure_comparison_equal(&plan, &item, &needle)?;
            let inside = self
                .terms
                .apply(Op::BvUnsignedLt, &[index.clone(), length])?;
            let predicate = self.terms.apply(Op::And, &[inside, equal])?;
            let member = self
                .terms
                .quantify(miren::smt::Quantifier::Exists, &index, &predicate)?;
            self.record_model(
                callee,
                concat!(
                    "full-domain pure composite slice membership; ",
                    "scoped existential structural numeric equality",
                ),
            );
            return Ok(Some(vec![Return {
                flow: activation_flow::Flow::Unarmed,
                value: Value::Bool(member),
                conditions: state.conditions.clone(),
                memory: state.memory.clone(),
            }]));
        }
        if matches!(slice, Value::ScalarSlice { .. }) {
            // Source and needle validity are established under the original free conditions.
            let length = self.scalar_slice_length(&slice, &state.conditions)?;
            self.validate_scalar_slice_needle(*element, needle, &state.conditions)?;
            let (length, bits, _) = length.integer()?;
            let index = self.fresh(Sort::BitVec(bits));
            let item = self.scalar_slice_logical_item(&slice, *element, &index)?;
            let equal = symbolic::binary(&self.terms, "eq", item, needle.clone())?.boolean()?;
            let inside = self
                .terms
                .apply(Op::BvUnsignedLt, &[index.clone(), length])?;
            let predicate = self.terms.apply(Op::And, &[inside, equal])?;
            let member = self
                .terms
                .quantify(miren::smt::Quantifier::Exists, &index, &predicate)?;
            self.record_model(
                callee,
                concat!(
                    "full-domain primitive scalar slice membership; ",
                    "scoped existential numeric equality"
                ),
            );
            return Ok(Some(vec![Return {
                flow: activation_flow::Flow::Unarmed,
                value: Value::Bool(member),
                conditions: state.conditions.clone(),
                memory: state.memory.clone(),
            }]));
        }
        if !(element.is_bool()
            || self.integer_type(*element).is_some()
            || self.float_type(*element).is_some())
        {
            let Value::Elements(elements) = &slice else {
                return Err("custom membership needs fixed modeled element storage".to_owned());
            };
            if elements.len() > MAX_MEMBERSHIP_ELEMENTS {
                return Err("slice membership exceeds the 128-element model budget".to_owned());
            }
            let [first, second] = raw_values else {
                return Err("custom membership requires two tracked arguments".to_owned());
            };
            let (slice, needle) = if slice_first {
                (first, second)
            } else {
                (second, first)
            };
            return self
                .custom_membership(
                    instance,
                    (*element, elements.len()),
                    (slice, needle),
                    state,
                    stack,
                    site,
                )
                .map(Some);
        }
        let mut member = self.terms.boolean(false);
        match &slice {
            Value::MutableU16 { .. } | Value::OwnedRegion { .. } | Value::OwnedSnapshot(_) => {
                return Err("owned regions require their private typed protocol".into());
            }
            Value::Elements(elements) => {
                if elements.len() > MAX_MEMBERSHIP_ELEMENTS {
                    return Err("slice membership exceeds the 128-element model budget".to_owned());
                }
                for item in elements {
                    let equal = symbolic::binary(&self.terms, "eq", item.clone(), needle.clone())?
                        .boolean()?;
                    member = self.terms.apply(Op::Or, &[member, equal])?;
                }
            }
            Value::Bytes { length, data } if *element == self.tcx.types.u8 => {
                let (length_term, bits, _) = length.integer()?;
                let limit = self
                    .terms
                    .bit_vector(MAX_MEMBERSHIP_ELEMENTS as u128, bits)?;
                let outside = self
                    .terms
                    .apply(Op::BvUnsignedGt, &[length_term.clone(), limit])?;
                if self.feasible(&[state.conditions.clone(), vec![outside]].concat())? {
                    return Err("byte membership needs a proven length at most 128".to_owned());
                }
                let count = match symbolic::constant(&length_term) {
                    Some(symbolic::Constant::BitVec { value, .. }) => value as usize,
                    _ => MAX_MEMBERSHIP_ELEMENTS,
                };
                for index in 0..count {
                    let index = self.terms.bit_vector(index as u128, bits)?;
                    let item = Value::Int {
                        expression: self
                            .terms
                            .apply(Op::Select, &[data.clone(), index.clone()])?,
                        bits: 8,
                        signed: false,
                    };
                    let equal =
                        symbolic::binary(&self.terms, "eq", item, needle.clone())?.boolean()?;
                    let inside = self
                        .terms
                        .apply(Op::BvUnsignedLt, &[index, length_term.clone()])?;
                    let equal = self.terms.apply(Op::And, &[inside, equal])?;
                    member = self.terms.apply(Op::Or, &[member, equal])?;
                }
            }
            Value::CompositeSlice { .. } => unreachable!("composite membership refused above"),
            Value::ScalarSlice { .. } => unreachable!("certified scalar membership handled above"),
            Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Bytes { .. }
            | Value::Adt { .. }
            | Value::Enum { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::Reference { .. }
            | Value::SliceIterator { .. }
            | Value::Tuple(_)
            | Value::MetadataPointer(_)
            | Value::StaticText
            | Value::FormatArguments
            | Value::RawPointer { .. }
            | Value::RawSlice { .. }
            | Value::TrackedPointer { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::MaybeUninit { .. }
            | Value::Uninitialized
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => {
                return Err("slice membership storage is not modeled".to_owned());
            }
        }
        self.record_model(
            callee,
            "bounded primitive slice membership; exact equality per element",
        );
        Ok(Some(vec![Return {
            flow: activation_flow::Flow::Unarmed,
            value: Value::Bool(member),
            conditions: state.conditions.clone(),
            memory: state.memory.clone(),
        }]))
    }

    fn custom_membership(
        &mut self,
        instance: ty::Instance<'tcx>,
        shape: (Ty<'tcx>, usize),
        sources: (&Value, &Value),
        state: &State,
        stack: &[DefId],
        site: (DefId, Span),
    ) -> Result<Vec<Return>, String> {
        let (element, count) = shape;
        let (slice, needle) = sources;
        let method = self
            .tcx
            .get_diagnostic_item(Symbol::intern("cmp_partialeq_eq"))
            .ok_or("compiler PartialEq method identity is unavailable")?;
        let args = self.tcx.mk_args(&[element.into(), element.into()]);
        let equality = self.resolve_function_item(method, args)?;
        let iterator = Value::SliceIterator {
            unchecked: Vec::new(),
            source: Box::new(slice.clone()),
            front: Box::new(self.iterator_index(0)),
            back: Box::new(self.iterator_index(count as u128)),
            mutable: false,
        };
        let mut pending = vec![(iterator, state.conditions.clone(), state.memory.clone())];
        let mut returns = Vec::new();
        self.record_model(
            instance.def_id(),
            "fixed custom membership; ordered checked PartialEq calls and short-circuit effects",
        );
        while let Some((iterator, conditions, memory)) = pending.pop() {
            for iteration in
                self.iterator_step(iterator, self.iterator_index(0), false, conditions, memory)?
            {
                let Some(item) = iteration.item else {
                    returns.push(Return {
                        flow: activation_flow::Flow::Unarmed,
                        value: Value::Bool(self.terms.boolean(false)),
                        conditions: iteration.conditions,
                        memory: iteration.memory,
                    });
                    continue;
                };
                for result in self.call_instance(
                    equality,
                    vec![item, needle.clone()],
                    iteration.conditions,
                    iteration.memory,
                    stack,
                    site,
                )? {
                    let equal = result.value.boolean()?;
                    let mut found = result.conditions.clone();
                    found.push(equal.clone());
                    if self.feasible(&found)? {
                        returns.push(Return {
                            flow: activation_flow::Flow::Unarmed,
                            value: Value::Bool(self.terms.boolean(true)),
                            conditions: found,
                            memory: result.memory.clone(),
                        });
                    }
                    let mut absent = result.conditions;
                    absent.push(symbolic::not(&equal));
                    if self.feasible(&absent)? {
                        pending.push((iteration.iterator.clone(), absent, result.memory));
                    }
                }
            }
        }
        Ok(returns)
    }
}
