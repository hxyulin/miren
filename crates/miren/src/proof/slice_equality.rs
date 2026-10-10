use super::*;
use rustc_span::Symbol;

const MAX_SLICE_EQUALITY_ELEMENTS: usize = 128;

impl<'tcx> Engine<'tcx> {
    pub(super) fn slice_equality(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        raw_values: &[Value],
        state: &State,
        stack: &[DefId],
        site: (DefId, Span),
    ) -> Result<Option<Vec<Return>>, String> {
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        let name = self.tcx.item_name(callee);
        if !matches!(name.as_str(), "eq" | "ne")
            || !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            || !self
                .tcx
                .get_diagnostic_item(Symbol::intern("cmp_partialeq_eq"))
                .is_some_and(|method| {
                    self.tcx.parent(method)
                        == self
                            .tcx
                            .impl_trait_ref(parent)
                            .instantiate(self.tcx, instance.args)
                            .skip_norm_wip()
                            .def_id
                })
        {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        let [left, right] = signature.inputs() else {
            return Ok(None);
        };
        let (ty::Ref(_, left, left_mut), ty::Ref(_, right, right_mut)) =
            (left.kind(), right.kind())
        else {
            return Ok(None);
        };
        let (left_element, right_element) = match (left.kind(), right.kind()) {
            (ty::Slice(left), ty::Slice(right))
            | (ty::Array(left, _), ty::Slice(right))
            | (ty::Slice(left), ty::Array(right, _)) => (*left, *right),
            _ => return Ok(None),
        };
        if left_mut.is_mut() || right_mut.is_mut() || !signature.output().is_bool() {
            return Ok(None);
        }
        self.instantiated_body(instance)?;
        let [raw_left, raw_right] = raw_values else {
            return Err("slice equality requires two tracked arguments".into());
        };
        for (expected, value) in [
            (signature.inputs()[0], raw_left),
            (signature.inputs()[1], raw_right),
        ] {
            self.validate_tracked_value(value, state)?;
            self.validate_readonly_slice_value(expected, value, &state.memory, &state.conditions)?;
        }
        let [left, right] = values else {
            return Err("slice equality requires two modeled arguments".into());
        };
        let left = left.materialize()?;
        let right = right.materialize()?;
        let composite = if matches!(left, Value::CompositeSlice { .. })
            || matches!(right, Value::CompositeSlice { .. })
        {
            if !matches!(
                (&left, &right),
                (Value::CompositeSlice { .. }, Value::CompositeSlice { .. })
            ) || left_element != right_element
            {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "mixed composite slice equality is unsupported".into(),
                ));
            }
            let Some(plan) = self.pure_comparison_shape(left_element)? else {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "whole composite slice equality is unsupported".into(),
                ));
            };
            // Full free source/extent certification precedes body checks and all shortcuts.
            let left_length = self.composite_slice_length(&left, &state.conditions)?;
            let right_length = self.composite_slice_length(&right, &state.conditions)?;
            self.certify_pure_comparison(left_element, instance)?;
            Some((plan, left_length, right_length))
        } else {
            None
        };
        let left_length = if let Some((_, length, _)) = &composite {
            length.clone()
        } else {
            self.equality_slice_length(&left, &state.conditions)?
        };
        let right_length = if let Some((_, _, length)) = &composite {
            length.clone()
        } else {
            self.equality_slice_length(&right, &state.conditions)?
        };
        let same_length =
            symbolic::binary(&self.terms, "eq", left_length.clone(), right_length)?.boolean()?;
        let negate = name == Symbol::intern("ne");
        let mut returns = Vec::new();
        let mismatch = [state.conditions.clone(), vec![symbolic::not(&same_length)]].concat();
        if self.feasible(&mismatch)? {
            returns.push(Return {
                value: Value::Bool(self.terms.boolean(negate)),
                conditions: mismatch,
                memory: state.memory.clone(),
            });
        }
        let conditions = [state.conditions.clone(), vec![same_length]].concat();
        self.record_model(
            callee,
            "slice equality; length check before element comparisons",
        );
        if !self.feasible(&conditions)? {
            return Ok(Some(returns));
        }
        let (length, bits, _) = left_length.integer()?;
        if let Some((plan, _, _)) = composite {
            let index = self.fresh(Sort::BitVec(bits));
            let left_item = self.composite_slice_logical_item(&left, left_element, &index)?;
            let right_item = self.composite_slice_logical_item(&right, right_element, &index)?;
            let equal = self.pure_comparison_equal(&plan, &left_item, &right_item)?;
            let inside = self
                .terms
                .apply(Op::BvUnsignedLt, &[index.clone(), length])?;
            let predicate = self.terms.apply(Op::Or, &[symbolic::not(&inside), equal])?;
            let equal = self
                .terms
                .quantify(miren::smt::Quantifier::Forall, &index, &predicate)?;
            self.record_model(
                callee,
                concat!(
                    "full-domain pure composite slice equality; ",
                    "scoped universal structural numeric equality",
                ),
            );
            returns.push(Return {
                value: Value::Bool(if negate { symbolic::not(&equal) } else { equal }),
                conditions,
                memory: state.memory.clone(),
            });
            return Ok(Some(returns));
        }
        if matches!(
            (&left, &right),
            (Value::ScalarSlice { .. }, Value::ScalarSlice { .. })
        ) {
            if left_element != right_element || self.scalar_slice_element(left_element)?.is_none() {
                return Err(
                    "full-domain slice equality requires identical primitive compiler types".into(),
                );
            }
            // Both source extents were certified under free conditions before length mismatch.
            let index = self.fresh(Sort::BitVec(bits));
            let left_item = self.scalar_slice_logical_item(&left, left_element, &index)?;
            let right_item = self.scalar_slice_logical_item(&right, right_element, &index)?;
            let item = symbolic::binary(&self.terms, "eq", left_item, right_item)?.boolean()?;
            let inside = self
                .terms
                .apply(Op::BvUnsignedLt, &[index.clone(), length])?;
            let predicate = self.terms.apply(Op::Or, &[symbolic::not(&inside), item])?;
            let equal = self
                .terms
                .quantify(miren::smt::Quantifier::Forall, &index, &predicate)?;
            self.record_model(
                callee,
                "full-domain primitive scalar slice equality; scoped universal numeric equality",
            );
            returns.push(Return {
                value: Value::Bool(if negate { symbolic::not(&equal) } else { equal }),
                conditions,
                memory: state.memory.clone(),
            });
            return Ok(Some(returns));
        }
        let limit = self
            .terms
            .bit_vector(MAX_SLICE_EQUALITY_ELEMENTS as u128, bits)?;
        let outside = self
            .terms
            .apply(Op::BvUnsignedGt, &[length.clone(), limit])?;
        if self.feasible(&[conditions.clone(), vec![outside]].concat())? {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "slice equality needs a proven length at most 128".into(),
            ));
        }
        let primitive = left_element == right_element
            && (left_element.is_bool()
                || left_element.is_char()
                || self.integer_type(left_element).is_some()
                || self.float_type(left_element).is_some());
        if !primitive {
            let Value::Elements(elements) = &left else {
                return Err("custom slice equality needs fixed modeled element storage".into());
            };
            let state = State {
                missing_places: initialized_places::MissingPlaces::default(),
                conditions,
                ..state.clone()
            };
            returns.extend(self.custom_sequence_equality(
                instance,
                (left_element, right_element, elements.len(), negate),
                raw_values,
                &state,
                stack,
                site,
            )?);
            return Ok(Some(returns));
        }
        let count = match (&left, &right) {
            (Value::Elements(elements), _) | (_, Value::Elements(elements)) => elements.len(),
            _ => match symbolic::constant(&length) {
                Some(symbolic::Constant::BitVec { value, .. }) => value as usize,
                _ => MAX_SLICE_EQUALITY_ELEMENTS,
            },
        };
        let mut equal = self.terms.boolean(true);
        for index in 0..count {
            let index_term = self.terms.bit_vector(index as u128, bits)?;
            let inside = self
                .terms
                .apply(Op::BvUnsignedLt, &[index_term, length.clone()])?;
            let selected_conditions = [conditions.clone(), vec![inside.clone()]].concat();
            if !self.feasible(&selected_conditions)? {
                continue;
            }
            let left =
                self.slice_equality_item(&left, left_element, index, bits, &selected_conditions)?;
            let right =
                self.slice_equality_item(&right, right_element, index, bits, &selected_conditions)?;
            let item = symbolic::binary(&self.terms, "eq", left, right)?.boolean()?;
            let item = self.terms.apply(Op::Or, &[symbolic::not(&inside), item])?;
            equal = self.terms.apply(Op::And, &[equal, item])?;
        }
        self.record_model(
            callee,
            "bounded primitive slice equality; exact numeric comparisons",
        );
        returns.push(Return {
            value: Value::Bool(if negate { symbolic::not(&equal) } else { equal }),
            conditions,
            memory: state.memory.clone(),
        });
        Ok(Some(returns))
    }

    fn equality_slice_length(&self, source: &Value, conditions: &[Term]) -> Result<Value, String> {
        match source {
            Value::CompositeSlice { .. } => Err("composite equality is unsupported".into()),
            Value::ScalarSlice { .. } => self.scalar_slice_length(source, conditions),
            Value::Bytes { length, .. } => Ok((**length).clone()),
            Value::Elements(fields) => Ok(self.iterator_index(fields.len() as u128)),
            Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
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
            | Value::Input(_)
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
            | Value::Unit => Err("slice equality needs byte or element storage".into()),
        }
    }

    fn slice_equality_item(
        &self,
        value: &Value,
        element: Ty<'tcx>,
        index: usize,
        bits: u32,
        conditions: &[Term],
    ) -> Result<Value, String> {
        match value {
            Value::CompositeSlice { .. } => Err("composite equality is unsupported".into()),
            Value::ScalarSlice { .. } => {
                self.scalar_slice_select(value, &self.iterator_index(index as u128), conditions)
            }
            Value::Elements(elements) => elements
                .get(index)
                .cloned()
                .ok_or_else(|| "slice equality index exceeds modeled element storage".into()),
            Value::Bytes { data, .. } if element == self.tcx.types.u8 => Ok(Value::Int {
                expression: self.terms.apply(
                    Op::Select,
                    &[data.clone(), self.terms.bit_vector(index as u128, bits)?],
                )?,
                bits: 8,
                signed: false,
            }),
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
            | Value::Unit => Err("slice equality needs modeled element storage".into()),
        }
    }
}
