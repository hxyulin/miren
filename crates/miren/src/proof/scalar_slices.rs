//! Logical initialized readonly slice observations; no byte or raw access grant.
use super::*;

use symbolic::ScalarSliceElement;

fn scalar_slice_sort(element: ScalarSliceElement) -> Result<Sort, String> {
    match element {
        ScalarSliceElement::Bool => Ok(Sort::Bool),
        ScalarSliceElement::Integer { bits, .. } if matches!(bits, 8 | 16 | 32 | 64 | 128) => {
            Ok(Sort::BitVec(bits))
        }
        ScalarSliceElement::Float { bits } if matches!(bits, 32 | 64) => Ok(Sort::BitVec(bits)),
        ScalarSliceElement::Char => Ok(Sort::BitVec(32)),
        ScalarSliceElement::Integer { .. } | ScalarSliceElement::Float { .. } => {
            Err("scalar slice descriptor has an unsupported primitive width".into())
        }
    }
}

fn validate_slice_terms(
    context: &Context,
    pointer_bits: u32,
    element: ScalarSliceElement,
    length: &Value,
    data: &Term,
) -> Result<(), String> {
    let (term, bits, signed) = length.integer()?;
    if bits != pointer_bits
        || signed
        || term.sort() != &Sort::BitVec(pointer_bits)
        || !term.belongs_to(context)
    {
        return Err("scalar slice length requires unsigned target usize in its context".into());
    }
    let expected = Sort::Array(
        Box::new(Sort::BitVec(pointer_bits)),
        Box::new(scalar_slice_sort(element)?),
    );
    if data.sort() != &expected || !data.belongs_to(context) {
        return Err(
            "scalar slice data does not match its certified element sort or context".into(),
        );
    }
    Ok(())
}

fn validate_cursor_terms(
    context: &Context,
    pointer_bits: u32,
    front: &Value,
    back: &Value,
) -> Result<(), String> {
    for bound in [front, back] {
        let (term, width, signed) = bound.integer()?;
        if width != pointer_bits
            || signed
            || term.sort() != &Sort::BitVec(pointer_bits)
            || !term.belongs_to(context)
        {
            return Err("scalar slice cursor requires target usize bounds".into());
        }
    }
    Ok(())
}

fn decode_scalar_element(
    context: &Context,
    element: ScalarSliceElement,
    selected: Term,
) -> Result<Value, String> {
    if selected.sort() != &scalar_slice_sort(element)? || !selected.belongs_to(context) {
        return Err("scalar slice selection has inconsistent element sort or context".into());
    }
    match element {
        ScalarSliceElement::Bool => Ok(Value::Bool(selected)),
        ScalarSliceElement::Integer { bits, signed } => Ok(Value::Int {
            expression: selected,
            bits,
            signed,
        }),
        ScalarSliceElement::Float { bits } => {
            Ok(symbolic::float_from_bits(context, selected, bits))
        }
        ScalarSliceElement::Char => Ok(Value::Int {
            // Only the constructor's already-valid incoming typed observation can use
            // this encoding. The seed is neither physical bytes nor a stored initializer.
            expression: characters::valid_char_observation(context, &selected)?,
            bits: 32,
            signed: false,
        }),
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn scalar_slice_element(
        &self,
        element: Ty<'tcx>,
    ) -> Result<Option<ScalarSliceElement>, String> {
        let shape = match element.kind() {
            ty::Bool => ScalarSliceElement::Bool,
            ty::Char => ScalarSliceElement::Char,
            ty::Int(_) | ty::Uint(_) => {
                let (bits, signed) = self
                    .integer_type(element)
                    .ok_or("primitive slice width unavailable")?;
                ScalarSliceElement::Integer { bits, signed }
            }
            ty::Float(ty::FloatTy::F32) => ScalarSliceElement::Float { bits: 32 },
            ty::Float(ty::FloatTy::F64) => ScalarSliceElement::Float { bits: 64 },
            _ => return Ok(None),
        };
        let env = ty::TypingEnv::fully_monomorphized();
        let layout = self.static_layout(element)?;
        let bytes = match shape {
            ScalarSliceElement::Bool => 1,
            ScalarSliceElement::Char => 4,
            ScalarSliceElement::Integer { bits, .. } | ScalarSliceElement::Float { bits } => {
                u64::from(bits / 8)
            }
        };
        if bytes == 0
            || layout.size.bytes() != bytes
            || layout.align.abi.bytes() == 0
            || !layout.align.abi.bytes().is_power_of_two()
            || !element.is_freeze(self.tcx, env)
            || !self.tcx.type_is_copy_modulo_regions(env, element)
            || element.needs_drop(self.tcx, env)
        {
            return Err("scalar slice element has an inconsistent compiler layout".into());
        }
        scalar_slice_sort(shape)?;
        Ok(Some(shape))
    }

    pub(super) fn scalar_slice_input(
        &mut self,
        element: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        if self.building_mutable_input {
            return Err("mutable scalar slice input requires a mutation and alias model".into());
        }
        let shape = self
            .scalar_slice_element(element)?
            .ok_or("incoming scalar slice requires an exact primitive element")?;
        if self
            .input_values
            .checked_add(2)
            .is_none_or(|count| count > MAX_INPUT_VALUES)
        {
            return Err("input shape exceeds the 512-value budget".into());
        }
        self.input_values += 2;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max =
            ((1_u128 << (bits - 1)) - 1) / u128::from(self.static_layout(element)?.size.bytes());
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let id = if let Some(id) = self.scalar_slice_types.iter().position(|ty| *ty == element) {
            id
        } else {
            let id = self.scalar_slice_types.len();
            self.scalar_slice_types.push(element);
            id
        };
        Ok(Value::ScalarSlice {
            id,
            element: shape,
            length: Box::new(Value::Int {
                expression: length,
                bits,
                signed: false,
            }),
            data: self.fresh(Sort::Array(
                Box::new(Sort::BitVec(bits)),
                Box::new(scalar_slice_sort(shape)?),
            )),
        })
    }

    pub(super) fn scalar_slice_length(
        &self,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::ScalarSlice {
            id,
            element,
            length,
            data,
        } = value
        else {
            return Err("expected an initialized readonly scalar slice".into());
        };
        let ty = *self
            .scalar_slice_types
            .get(*id)
            .ok_or("scalar slice compiler type descriptor is absent")?;
        if self.scalar_slice_element(ty)? != Some(*element) {
            return Err("scalar slice compiler type differs from its logical element tag".into());
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        validate_slice_terms(&self.terms, bits, *element, length, data)?;
        let bytes = match element {
            ScalarSliceElement::Bool => 1,
            ScalarSliceElement::Char => 4,
            ScalarSliceElement::Integer { bits, .. } | ScalarSliceElement::Float { bits } => {
                u128::from(bits / 8)
            }
        };
        let max = ((1_u128 << (bits - 1)) - 1) / bytes;
        let bounded = self.terms.apply(
            Op::BvUnsignedLe,
            &[length.integer()?.0, self.terms.bit_vector(max, bits)?],
        )?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&bounded));
        if self.feasible(&invalid)? {
            return Err("scalar slice lacks its valid target allocation extent".into());
        }
        Ok((**length).clone())
    }

    pub(super) fn scalar_slice_select(
        &self,
        value: &Value,
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let length = self.scalar_slice_length(value, conditions)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (expression, width, signed) = index.integer()?;
        if width != bits
            || signed
            || expression.sort() != &Sort::BitVec(bits)
            || !expression.belongs_to(&self.terms)
        {
            return Err("scalar slice index requires exact target usize".into());
        }
        self.memory_bounds(index, &length, conditions)?;
        let Value::ScalarSlice { element, data, .. } = value else {
            unreachable!()
        };
        let selected = self.terms.apply(Op::Select, &[data.clone(), expression])?;
        decode_scalar_element(&self.terms, *element, selected)
    }

    /// Pure logical observation after the consumer has certified the original source and
    /// allocation extent under free path conditions. This grants no checked memory access;
    /// an open logical binder must never be passed to memory_bounds or feasibility here.
    pub(super) fn scalar_slice_logical_item(
        &self,
        value: &Value,
        original: Ty<'tcx>,
        index: &Term,
    ) -> Result<Value, String> {
        let Value::ScalarSlice {
            id,
            element,
            length,
            data,
        } = value
        else {
            return Err(
                "logical scalar observation requires a certified readonly descriptor".into(),
            );
        };
        if self.scalar_slice_types.get(*id) != Some(&original)
            || self.scalar_slice_element(original)? != Some(*element)
        {
            return Err(
                "logical scalar observation differs from its original compiler type".into(),
            );
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        validate_slice_terms(&self.terms, bits, *element, length, data)?;
        if index.sort() != &Sort::BitVec(bits) || !index.belongs_to(&self.terms) {
            return Err(
                "logical scalar observation requires a target-usize index in its context".into(),
            );
        }
        let selected = self
            .terms
            .apply(Op::Select, &[data.clone(), index.clone()])?;
        decode_scalar_element(&self.terms, *element, selected)
    }

    pub(super) fn validate_scalar_slice_needle(
        &self,
        original: Ty<'tcx>,
        needle: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let element = self
            .scalar_slice_element(original)?
            .ok_or("scalar slice comparison requires an exact primitive compiler type")?;
        let valid = match element {
            ScalarSliceElement::Bool => match needle {
                Value::Bool(term) => term.sort() == &Sort::Bool && term.belongs_to(&self.terms),
                _ => false,
            },
            ScalarSliceElement::Integer { bits, signed } => match needle {
                Value::Int {
                    expression,
                    bits: actual_bits,
                    signed: actual_signed,
                } => {
                    bits == *actual_bits
                        && signed == *actual_signed
                        && expression.sort() == &Sort::BitVec(bits)
                        && expression.belongs_to(&self.terms)
                }
                _ => false,
            },
            ScalarSliceElement::Char => {
                self.prove_char_value(needle, conditions)?;
                true
            }
            ScalarSliceElement::Float { bits } => match needle {
                Value::Float {
                    expression,
                    bits: actual_bits,
                    ..
                } => {
                    let (exponent, significand) = if bits == 32 { (8, 24) } else { (11, 53) };
                    bits == *actual_bits
                        && expression.sort()
                            == &Sort::Float {
                                exponent,
                                significand,
                            }
                        && expression.belongs_to(&self.terms)
                }
                _ => false,
            },
        };
        if !valid {
            return Err(
                "scalar slice comparison needle differs from its exact primitive type".into(),
            );
        }
        Ok(())
    }

    pub(super) fn scalar_slice_region(
        &self,
        value: &Value,
        offset: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let capacity = self.scalar_slice_length(value, conditions)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [offset, length] {
            let (expression, width, signed) = bound.integer()?;
            if width != bits
                || signed
                || expression.sort() != &Sort::BitVec(bits)
                || !expression.belongs_to(&self.terms)
            {
                return Err("scalar slice region requires exact target usize bounds".into());
            }
        }
        let within =
            symbolic::binary(&self.terms, "le", offset.clone(), capacity.clone())?.boolean()?;
        let available = symbolic::binary(&self.terms, "sub", capacity, offset.clone())?;
        let fits = symbolic::binary(&self.terms, "le", length.clone(), available)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[within, fits])?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&safe));
        if self.feasible(&invalid)? {
            return Err("scalar slice view lacks proven region bounds".into());
        }
        let Value::ScalarSlice {
            id, element, data, ..
        } = value
        else {
            unreachable!()
        };
        Ok(Value::ScalarSlice {
            id: *id,
            element: *element,
            length: Box::new(length.clone()),
            data: self
                .terms
                .apply(Op::ArrayOffset, &[data.clone(), offset.integer()?.0])?,
        })
    }
    pub(super) fn validate_scalar_slice_value(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
        memory: &[Option<Value>],
        conditions: &[Term],
    ) -> Result<(), String> {
        if !contains_scalar_slice(value, memory, &mut Vec::new()) {
            return Ok(());
        }
        self.scalar_slice_typed_depth(expected, value, memory, conditions, 0)
    }

    fn scalar_slice_typed_depth(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
        memory: &[Option<Value>],
        conditions: &[Term],
        depth: usize,
    ) -> Result<(), String> {
        if !contains_scalar_slice(value, memory, &mut Vec::new()) {
            return Ok(());
        }
        if depth >= 32 {
            return Err("scalar slice typed carrier nesting limit reached".into());
        }
        match value {
            Value::ScalarSlice { id, element, .. } => {
                let ty::Slice(ty) = expected.kind() else {
                    return Err(
                        "scalar slice descriptor requires its exact compiler slice type".into(),
                    );
                };
                if self.scalar_slice_types.get(*id) != Some(ty)
                    || self.scalar_slice_element(*ty)? != Some(*element)
                {
                    return Err(
                        "scalar slice descriptor differs from its compiler element type".into(),
                    );
                }
                self.scalar_slice_length(value, conditions)?;
            }
            Value::Reference { mutable, .. } => {
                let ty::Ref(_, pointee, permission) = expected.kind() else {
                    return Err(
                        "scalar slice reference carrier requires its compiler reference type"
                            .into(),
                    );
                };
                let stored = self.reference_value(value, memory, conditions)?;
                if matches!(stored, Value::ScalarSlice { .. }) && (*mutable || permission.is_mut())
                {
                    return Err("readonly scalar slice cannot supply a mutable reference".into());
                }
                self.scalar_slice_typed_depth(*pointee, &stored, memory, conditions, depth + 1)?;
            }
            Value::Tuple(values) => {
                if let ty::Tuple(types) = expected.kind() {
                    if types.len() != values.len() {
                        return Err("scalar slice tuple carrier arity mismatch".into());
                    }
                    for (ty, value) in types.iter().zip(values) {
                        self.scalar_slice_typed_depth(ty, value, memory, conditions, depth + 1)?;
                    }
                } else {
                    return Err("scalar slice tuple carrier requires compiler tuple type".into());
                }
            }
            Value::Elements(values) => {
                if let ty::Array(ty, count) = expected.kind() {
                    if count.try_to_target_usize(self.tcx) != Some(values.len() as u64) {
                        return Err("scalar slice array carrier count mismatch".into());
                    }
                    for value in values {
                        self.scalar_slice_typed_depth(*ty, value, memory, conditions, depth + 1)?;
                    }
                } else {
                    return Err("scalar slice element carrier requires compiler array type".into());
                }
            }
            Value::Adt { fields, .. } if matches!(expected.kind(), ty::Closure(..)) => {
                let types = self
                    .closure_capture_types(expected, value)?
                    .ok_or("closure carrier compiler type is missing")?;
                for (ty, (_, capture)) in types.iter().zip(fields) {
                    self.scalar_slice_typed_depth(ty, capture, memory, conditions, depth + 1)?;
                }
            }
            Value::Adt {
                name,
                variant,
                fields,
                discriminant,
                is_option,
            } => {
                if let ty::Adt(def, args) = expected.kind() {
                    if def.is_union() || *name != self.tcx.def_path_str(def.did()) {
                        return Err("scalar slice ADT carrier compiler identity mismatch".into());
                    }
                    if *variant >= def.variants().len() {
                        return Err("scalar slice carrier variant mismatch".into());
                    }
                    let index = rustc_abi::VariantIdx::from_usize(*variant);
                    let expected_tag = if def.is_enum() {
                        def.discriminant_for_variant(self.tcx, index).val
                    } else {
                        0
                    };
                    if *is_option
                        != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                        || *discriminant != expected_tag
                    {
                        return Err("scalar slice ADT carrier variant metadata mismatch".into());
                    }
                    let Some(layout) = def.variants().iter().nth(*variant) else {
                        return Err("scalar slice carrier variant mismatch".into());
                    };
                    if fields.len() != layout.fields.len() {
                        return Err("scalar slice ADT carrier arity mismatch".into());
                    }
                    for (field, (name, value)) in layout.fields.iter().zip(fields) {
                        if field.name.as_str() != name {
                            return Err("scalar slice carrier field identity mismatch".into());
                        }
                        let ty = field.ty(self.tcx, args).skip_norm_wip();
                        self.scalar_slice_typed_depth(ty, value, memory, conditions, depth + 1)?;
                    }
                } else {
                    return Err("scalar slice ADT carrier requires compiler ADT type".into());
                }
            }
            Value::Enum {
                discriminant,
                variants,
                is_option,
            } => {
                let ty::Adt(def, _) = expected.kind() else {
                    return Err("scalar slice enum carrier requires compiler enum type".into());
                };
                if !def.is_enum()
                    || variants.len() != def.variants().len()
                    || *is_option
                        != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                {
                    return Err("scalar slice enum carrier variant inventory mismatch".into());
                }
                let (term, bits, signed) = discriminant.integer()?;
                if self.integer_type(expected.discriminant_ty(self.tcx)) != Some((bits, signed))
                    || term.sort() != &Sort::BitVec(bits)
                    || !term.belongs_to(&self.terms)
                {
                    return Err("scalar slice enum carrier tag metadata mismatch".into());
                }
                for (index, variant) in variants.iter().enumerate() {
                    if !matches!(variant, Value::Adt { variant, .. } if *variant == index) {
                        return Err("scalar slice enum carrier variant order mismatch".into());
                    }
                    self.scalar_slice_typed_depth(
                        expected,
                        variant,
                        memory,
                        conditions,
                        depth + 1,
                    )?;
                }
            }
            Value::SliceIterator {
                source,
                front,
                back,
                mutable,
                unchecked,
            } => {
                let stored = self.reference_value(source, memory, conditions)?;
                // The discovery walk visits whole allocations; a projected finite source
                // may share its parent with an unrelated scalar-slice field.
                if !contains_scalar_slice(&stored, memory, &mut Vec::new()) {
                    return Ok(());
                }
                let ty::Adt(def, args) = expected.kind() else {
                    return Err("scalar slice cursor requires exact compiler Iter type".into());
                };
                if self
                    .tcx
                    .get_diagnostic_item(rustc_span::Symbol::intern("SliceIter"))
                    != Some(def.did())
                    || *mutable
                    || !unchecked.is_empty()
                    || !matches!(source.as_ref(), Value::Reference { mutable: false, .. })
                {
                    return Err(
                        "scalar slice cursor requires an immutable retained core Iter".into(),
                    );
                }
                let element = args
                    .types()
                    .next()
                    .ok_or("scalar slice cursor lacks its compiler element argument")?;
                self.scalar_slice_typed_depth(
                    Ty::new_slice(self.tcx, element),
                    &stored,
                    memory,
                    conditions,
                    depth + 1,
                )?;
                let length = self.scalar_slice_length(&stored, conditions)?;
                let bits = u32::from(self.tcx.sess.target.pointer_width);
                validate_cursor_terms(&self.terms, bits, front, back)?;
                let ordered =
                    symbolic::binary(&self.terms, "le", (**front).clone(), (**back).clone())?
                        .boolean()?;
                let inside =
                    symbolic::binary(&self.terms, "le", (**back).clone(), length)?.boolean()?;
                let safe = self.terms.apply(Op::And, &[ordered, inside])?;
                let mut invalid = conditions.to_vec();
                invalid.push(symbolic::not(&safe));
                if self.feasible(&invalid)? {
                    return Err("scalar slice cursor lacks ordered live source bounds".into());
                }
            }
            Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Bytes { .. }
            | Value::MaybeUninit { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::MetadataPointer(_)
            | Value::StaticText
            | Value::FormatArguments
            | Value::RawPointer { .. }
            | Value::RawSlice { .. }
            | Value::TrackedPointer { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::Uninitialized
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => {
                return Err("unsupported scalar slice typed carrier".into());
            }
        }
        Ok(())
    }

    pub(super) fn readonly_scalar_slice_range(
        &mut self,
        instance: ty::Instance<'tcx>,
        raw_values: &[Value],
        state: &State,
        site: (DefId, Span),
    ) -> Result<Option<Vec<Return>>, String> {
        use rustc_span::Symbol;
        use symbolic::MemoryProjection;
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        let Some(trait_id) = self.tcx.get_diagnostic_item(Symbol::intern("SliceIndex")) else {
            return Ok(None);
        };
        if self.tcx.item_name(callee) != Symbol::intern("index")
            || callee.krate != trait_id.krate
            || !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            || self
                .tcx
                .impl_trait_ref(parent)
                .instantiate(self.tcx, instance.args)
                .skip_norm_wip()
                .def_id
                != trait_id
        {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.safety() != rustc_hir::Safety::Safe
        {
            return Ok(None);
        }
        let [range_ty, receiver_ty] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Adt(def, args) = range_ty.kind() else {
            return Ok(None);
        };
        let range_kind = [
            LangItem::Range,
            LangItem::RangeTo,
            LangItem::RangeFrom,
            LangItem::RangeFull,
        ]
        .into_iter()
        .position(|item| self.tcx.lang_items().get(item) == Some(def.did()));
        let Some(kind) = range_kind else {
            return Ok(None);
        };
        if kind != 3 && args.type_at(0) != self.tcx.types.usize {
            return Ok(None);
        }
        let ty::Ref(_, slice, permission) = receiver_ty.kind() else {
            return Ok(None);
        };
        let ty::Slice(element) = slice.kind() else {
            return Ok(None);
        };
        let output_matches = match signature.output().kind() {
            ty::Ref(_, output, permission) => *output == *slice && !permission.is_mut(),
            _ => false,
        };
        if permission.is_mut() || self.scalar_slice_element(*element)?.is_none() || !output_matches
        {
            return Ok(None);
        }
        let [
            range,
            reference @ Value::Reference {
                allocation,
                projection,
                mutable: false,
            },
        ] = raw_values
        else {
            return Ok(None);
        };
        let storage = self.reference_value(reference, &state.memory, &state.conditions)?;
        if !matches!(storage, Value::ScalarSlice { .. }) {
            return Ok(None);
        }
        self.validate_scalar_slice_value(
            *receiver_ty,
            reference,
            &state.memory,
            &state.conditions,
        )?;
        // A missing selected core body never becomes a successful modeled operation.
        self.instantiated_body(instance)?;
        let range = range.clone().materialize()?;
        let expected_fields = match kind {
            0 => 2,
            1 | 2 => 1,
            3 => 0,
            _ => unreachable!(),
        };
        if !matches!(&range,
            Value::Adt {
                name, variant: 0, discriminant: 0, is_option: false, fields
            } if *name == self.tcx.def_path_str(def.did()) && fields.len() == expected_fields)
        {
            return Err("readonly scalar range requires exact compiler range storage".into());
        }
        let capacity = self.scalar_slice_length(&storage, &state.conditions)?;
        let start = if matches!(kind, 0 | 2) {
            range.field("start")?
        } else {
            self.iterator_index(0)
        };
        let end = if matches!(kind, 0 | 1) {
            range.field("end")?
        } else {
            capacity.clone()
        };
        for bound in [&start, &end] {
            let (term, bits, signed) = bound.integer()?;
            if bits != u32::from(self.tcx.sess.target.pointer_width)
                || signed
                || term.sort() != &Sort::BitVec(bits)
                || !term.belongs_to(&self.terms)
            {
                return Err("readonly scalar range bounds require exact target usize".into());
            }
        }
        let ordered = symbolic::binary(&self.terms, "le", start.clone(), end.clone())?.boolean()?;
        let inside = symbolic::binary(&self.terms, "le", end.clone(), capacity)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[ordered, inside])?;
        self.require(
            site.0,
            site.1,
            &state.conditions,
            &safe,
            ObligationKind::PanicSafety,
            "readonly scalar range requires start <= end <= slice length".into(),
        )?;
        let mut conditions = state.conditions.clone();
        conditions.push(safe);
        let mut projection = projection.clone();
        projection.push(MemoryProjection::Slice {
            offset: Box::new(start.clone()),
            length: Box::new(symbolic::binary(&self.terms, "sub", end, start)?),
        });
        self.record_model(
            callee,
            "checked core readonly scalar range; retained caller allocation and projections",
        );
        Ok(Some(vec![Return {
            value: Value::Reference {
                allocation: *allocation,
                projection,
                mutable: false,
            },
            conditions,
            memory: state.memory.clone(),
        }]))
    }
}

fn contains_scalar_slice(
    value: &Value,
    memory: &[Option<Value>],
    visited: &mut Vec<usize>,
) -> bool {
    match value {
        Value::ScalarSlice { .. } => true,
        Value::Reference { allocation, .. }
        | Value::Cell { allocation }
        | Value::LocalAtomic { allocation, .. } => {
            if visited.contains(allocation) {
                return false;
            }
            visited.push(*allocation);
            memory
                .get(*allocation)
                .and_then(Option::as_ref)
                .is_some_and(|value| contains_scalar_slice(value, memory, visited))
        }
        Value::Adt { fields, .. } => fields
            .iter()
            .any(|(_, value)| contains_scalar_slice(value, memory, visited)),
        Value::Enum { variants, .. } | Value::Tuple(variants) => variants
            .iter()
            .any(|value| contains_scalar_slice(value, memory, visited)),
        Value::Elements(values) => values
            .iter()
            .any(|value| contains_scalar_slice(value, memory, visited)),
        Value::MaybeUninit { payload, .. } => payload
            .as_ref()
            .is_some_and(|value| contains_scalar_slice(value, memory, visited)),
        Value::TrackedPointer { reference, .. } => {
            contains_scalar_slice(reference, memory, visited)
        }
        Value::RawSlice { source, .. }
        | Value::SliceIterator { source, .. }
        | Value::MetadataPointer(source)
        | Value::TraitObject { source, .. }
        | Value::DebugReference { source, .. } => contains_scalar_slice(source, memory, visited),
        Value::StaticSlice {
            source, elements, ..
        } => {
            contains_scalar_slice(source, memory, visited)
                || elements
                    .iter()
                    .any(|value| contains_scalar_slice(value, memory, visited))
        }
        Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Bytes { .. }
        | Value::Atomic { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::RawPointer { .. }
        | Value::StaticView { .. }
        | Value::Uninitialized
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Unit => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cursor_bounds_reject_signed_wrong_width_and_foreign_context_terms() {
        let context = Context::default();
        let foreign = Context::default();
        for bits in [32, 64] {
            let front = symbolic::integer(&context, 0, bits, false);
            let back = symbolic::integer(&context, 129, bits, false);
            assert!(validate_cursor_terms(&context, bits, &front, &back).is_ok());
            for malformed in [
                symbolic::integer(&context, 0, bits, true),
                symbolic::integer(&context, 0, 16, false),
                symbolic::integer(&foreign, 0, bits, false),
                Value::Bool(context.boolean(false)),
            ] {
                assert!(validate_cursor_terms(&context, bits, &malformed, &back).is_err());
                assert!(validate_cursor_terms(&context, bits, &front, &malformed).is_err());
            }
        }
    }

    #[test]
    fn logical_scalar_slices_require_exact_length_element_sort_and_context() {
        let context = Context::default();
        let foreign = Context::default();
        for pointer_bits in [32, 64] {
            let length = symbolic::integer(&context, 0, pointer_bits, false);
            for element in [
                ScalarSliceElement::Bool,
                ScalarSliceElement::Integer {
                    bits: 16,
                    signed: true,
                },
                ScalarSliceElement::Integer {
                    bits: 128,
                    signed: false,
                },
                ScalarSliceElement::Float { bits: 32 },
                ScalarSliceElement::Float { bits: 64 },
                ScalarSliceElement::Char,
            ] {
                let item = match scalar_slice_sort(element).unwrap() {
                    Sort::Bool => context.boolean(true),
                    Sort::BitVec(bits) => context.bit_vector(1, bits).unwrap(),
                    other => panic!("unexpected primitive sort {other:?}"),
                };
                let data = context
                    .apply(
                        Op::ConstArray {
                            index_bits: pointer_bits,
                        },
                        std::slice::from_ref(&item),
                    )
                    .unwrap();
                assert!(
                    validate_slice_terms(&context, pointer_bits, element, &length, &data).is_ok()
                );
                assert!(
                    validate_slice_terms(&foreign, pointer_bits, element, &length, &data).is_err()
                );
                assert!(
                    validate_slice_terms(
                        &context,
                        pointer_bits,
                        element,
                        &symbolic::integer(&context, 0, pointer_bits, true),
                        &data
                    )
                    .is_err()
                );
                assert!(
                    validate_slice_terms(
                        &context,
                        pointer_bits,
                        element,
                        &symbolic::integer(&context, 0, 16, false),
                        &data
                    )
                    .is_err()
                );
                let bad_data = context
                    .apply(
                        Op::ConstArray { index_bits: 16 },
                        std::slice::from_ref(&item),
                    )
                    .unwrap();
                assert!(
                    validate_slice_terms(&context, pointer_bits, element, &length, &bad_data)
                        .is_err()
                );
                let bad_item = context.bit_vector(0, 7).unwrap();
                let bad_data = context
                    .apply(
                        Op::ConstArray {
                            index_bits: pointer_bits,
                        },
                        &[bad_item],
                    )
                    .unwrap();
                assert!(
                    validate_slice_terms(&context, pointer_bits, element, &length, &bad_data)
                        .is_err()
                );
                assert!(decode_scalar_element(&context, element, item.clone()).is_ok());
                assert!(decode_scalar_element(&foreign, element, item).is_err());
            }
        }
        for element in [
            ScalarSliceElement::Integer {
                bits: 7,
                signed: false,
            },
            ScalarSliceElement::Float { bits: 16 },
        ] {
            assert!(scalar_slice_sort(element).is_err());
        }
        let surrogate = context.bit_vector(0xd800, 32).unwrap();
        let decoded = decode_scalar_element(&context, ScalarSliceElement::Char, surrogate).unwrap();
        assert_eq!(
            symbolic::constant(&decoded.integer().unwrap().0),
            Some(symbolic::Constant::BitVec { value: 0, bits: 32 })
        );
        let nan = context.bit_vector(0x7fc0_1234, 32).unwrap();
        let Value::Float {
            raw_bits: Some(raw),
            ..
        } = decode_scalar_element(
            &context,
            ScalarSliceElement::Float { bits: 32 },
            nan.clone(),
        )
        .unwrap()
        else {
            panic!("float storage bits were lost");
        };
        assert_eq!(raw, nan);
    }

    #[test]
    fn even_empty_scalar_slices_keep_their_original_source_lifetime() {
        let context = Context::default();
        let descriptor = Value::ScalarSlice {
            id: 0,
            element: ScalarSliceElement::Char,
            length: Box::new(symbolic::integer(&context, 0, 64, false)),
            data: context
                .apply(
                    Op::ConstArray { index_bits: 64 },
                    &[context.bit_vector(0xd800, 32).unwrap()],
                )
                .unwrap(),
        };
        let reference = Value::Reference {
            allocation: 0,
            projection: Vec::new(),
            mutable: false,
        };
        let mut state = State {
            locals: Vec::new(),
            addresses: Vec::new(),
            conditions: Vec::new(),
            memory: vec![Some(descriptor.clone())].into(),
        };
        assert!(
            Engine::validate_reference_graph(&reference, &state, None, &mut Vec::new()).is_ok()
        );
        assert!(!descriptor.contains_mutable());
        assert_eq!(descriptor.owned_iterator_size(), None);
        let copied_handle = reference.clone();
        state.memory[0] = None;
        for handle in [&reference, &copied_handle] {
            let error = Engine::validate_reference_graph(handle, &state, None, &mut Vec::new())
                .unwrap_err();
            assert!(error.contains("dead or uninitialized"));
        }
    }
}
