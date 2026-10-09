use super::*;

const MAX_DEPTH: usize = 16;
const MAX_NODES: usize = 256;
const MAX_SHAPES: usize = 128;
const MAX_ARRAY_ELEMENTS: u64 = 128;

impl<'tcx> Engine<'tcx> {
    fn maybe_uninit_shape(&self, wrapper: Ty<'tcx>) -> Result<(Ty<'tcx>, usize, usize), String> {
        let env = ty::TypingEnv::fully_monomorphized();
        let ty::Adt(def, args) = wrapper.kind() else {
            return Err("MaybeUninit certificate needs its compiler union type".into());
        };
        if self.tcx.lang_items().get(LangItem::MaybeUninit) != Some(def.did())
            || !def.is_union()
            || !def.repr().transparent()
            || args.len() != 1
            || def.non_enum_variant().fields.len() != 2
        {
            return Err(
                "MaybeUninit certificate has an unsupported union identity or shape".into(),
            );
        }
        // Do not let normalization erase restricted scalar-pattern validity.
        let mut original_nodes = 0;
        self.maybe_uninit_pure_type(args.type_at(0), 0, &mut original_nodes)?;
        let payload = self
            .tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(args.type_at(0)))
            .map_err(|e| format!("MaybeUninit payload normalization failed: {e:?}"))?;
        let mut nodes = 0;
        self.maybe_uninit_pure_type(payload, 0, &mut nodes)?;
        let wrapper_layout = self.static_layout(wrapper)?;
        let payload_layout = self.static_layout(payload)?;
        if wrapper_layout.size != payload_layout.size
            || wrapper_layout.align != payload_layout.align
            || wrapper.needs_drop(self.tcx, env)
        {
            return Err(
                "MaybeUninit certificate does not preserve the exact payload layout".into(),
            );
        }
        let mut unit = None;
        let mut initialized = None;
        for (index, field) in def.non_enum_variant().fields.iter().enumerate() {
            let field_ty = self
                .tcx
                .try_normalize_erasing_regions(env, field.ty(self.tcx, args))
                .map_err(|e| format!("MaybeUninit field normalization failed: {e:?}"))?;
            if wrapper_layout.fields.offset(index).bytes() != 0 {
                return Err("MaybeUninit field is not at the payload origin".into());
            }
            if field_ty.is_unit() {
                unit = Some(index);
                continue;
            }
            let ty::Adt(drop, drop_args) = field_ty.kind() else {
                return Err("MaybeUninit value field lacks core ManuallyDrop identity".into());
            };
            if self.tcx.lang_items().get(LangItem::ManuallyDrop) != Some(drop.did())
                || !drop.is_struct()
                || !drop.repr().transparent()
                || drop_args.len() != 1
                || drop_args.type_at(0) != payload
                || drop.non_enum_variant().fields.len() != 1
            {
                return Err("MaybeUninit value field has a mismatched ManuallyDrop shape".into());
            }
            let inner = self
                .tcx
                .try_normalize_erasing_regions(
                    env,
                    drop.non_enum_variant().fields.raw[0].ty(self.tcx, drop_args),
                )
                .map_err(|e| format!("ManuallyDrop field normalization failed: {e:?}"))?;
            let layout = self.static_layout(field_ty)?;
            if inner != payload
                || layout.size != payload_layout.size
                || layout.align != payload_layout.align
                || layout.fields.offset(0).bytes() != 0
            {
                return Err("ManuallyDrop certificate changes the payload type or layout".into());
            }
            initialized = Some(index);
        }
        Ok((
            payload,
            unit.ok_or("MaybeUninit unit field is missing")?,
            initialized.ok_or("MaybeUninit initialized field is missing")?,
        ))
    }

    fn maybe_uninit_pure_type(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<(), String> {
        *nodes += 1;
        if matches!(ty.kind(), ty::Pat(..)) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "MaybeUninit payload contains a restricted scalar pattern".into(),
            ));
        }
        let env = ty::TypingEnv::fully_monomorphized();
        if depth > MAX_DEPTH
            || *nodes > MAX_NODES
            || !ty.is_freeze(self.tcx, env)
            || !self.tcx.type_is_copy_modulo_regions(env, ty)
            || ty.needs_drop(self.tcx, env)
        {
            return Err("MaybeUninit payload exceeds the bounded Copy Freeze value domain".into());
        }
        match ty.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => {
                self.static_layout(ty)?;
                Ok(())
            }
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.maybe_uninit_pure_type(field, depth + 1, nodes)?;
                }
                self.static_layout(ty)?;
                Ok(())
            }
            ty::Array(element, length) => {
                let count = self.maybe_uninit_array_count(*length)?;
                // Even an empty array must have an eligible element type, including raw
                // restricted-pattern checks before any normalization.
                let mut element_nodes = 0;
                self.maybe_uninit_pure_type(*element, depth + 1, &mut element_nodes)?;
                for _ in 0..count {
                    self.maybe_uninit_pure_type(*element, depth + 1, nodes)?;
                }
                self.static_layout(ty)?;
                Ok(())
            }
            _ => Err("MaybeUninit payload requires primitive or pure tuple types".into()),
        }
    }

    fn maybe_uninit_array_count(&self, length: ty::Const<'tcx>) -> Result<u64, String> {
        let count = length
            .try_to_target_usize(self.tcx)
            .ok_or("MaybeUninit array requires an exact compiler constant length")?;
        if count > MAX_ARRAY_ELEMENTS {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "MaybeUninit array exceeds the 128-element budget".into(),
            ));
        }
        Ok(count)
    }

    fn maybe_uninit_payload_value(
        &self,
        ty: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let valid = |term: &Term, sort: Sort| term.belongs_to(&self.terms) && term.sort() == &sort;
        match (ty.kind(), value) {
            (ty::Bool, Value::Bool(term)) if valid(term, Sort::Bool) => Ok(()),
            (ty::Char, Value::Int { .. }) => self.prove_char_value(value, conditions),
            (
                ty::Int(_) | ty::Uint(_),
                Value::Int {
                    expression,
                    bits,
                    signed,
                },
            ) if self.integer_type(ty) == Some((*bits, *signed))
                && valid(expression, Sort::BitVec(*bits)) =>
            {
                Ok(())
            }
            (
                ty::Float(_),
                Value::Float {
                    expression,
                    bits,
                    raw_bits,
                },
            ) => {
                let sort = match bits {
                    32 => Sort::Float {
                        exponent: 8,
                        significand: 24,
                    },
                    64 => Sort::Float {
                        exponent: 11,
                        significand: 53,
                    },
                    _ => return Err("MaybeUninit floating payload has an invalid width".into()),
                };
                if self.float_type(ty) != Some(*bits)
                    || !valid(expression, sort)
                    || raw_bits
                        .as_ref()
                        .is_some_and(|raw| !valid(raw, Sort::BitVec(*bits)))
                {
                    return Err(
                        "MaybeUninit floating payload has invalid type, sort or context".into(),
                    );
                }
                Ok(())
            }
            (ty::Tuple(fields), Value::Unit) if fields.is_empty() => Ok(()),
            (ty::Tuple(fields), Value::Tuple(values)) if fields.len() == values.len() => {
                for (field, value) in fields.iter().zip(values) {
                    self.maybe_uninit_payload_value(field, value, conditions)?;
                }
                Ok(())
            }
            (ty::Array(element, count), Value::Elements(values)) => {
                let count = self.maybe_uninit_array_count(*count)?;
                if values.len() as u64 != count {
                    return Err(
                        "MaybeUninit initialized array has a mismatched element count".into(),
                    );
                }
                for value in values.iter() {
                    self.maybe_uninit_payload_value(*element, value, conditions)?;
                }
                Ok(())
            }
            (ty::Array(element, count), Value::Bytes { length, data })
                if *element == self.tcx.types.u8 =>
            {
                let count = self.maybe_uninit_array_count(*count)?;
                let pointer_bits = u32::from(self.tcx.sess.target.pointer_width);
                validate_byte_payload(&self.terms, pointer_bits, count, length, data)
            }

            _ => {
                Err("MaybeUninit initialized payload does not match its exact compiler type".into())
            }
        }
    }

    pub(super) fn maybe_uninit_aggregate(
        &mut self,
        wrapper: Ty<'tcx>,
        active: usize,
        operand_types: &[Ty<'tcx>],
        values: &[Value],
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Adt(def, args) = wrapper.kind() else {
            return Ok(None);
        };
        if self.tcx.lang_items().get(LangItem::MaybeUninit) != Some(def.did()) {
            return Ok(None);
        }
        let (payload_ty, unit, initialized) = self.maybe_uninit_shape(wrapper)?;
        let [value] = values else {
            return Err("MaybeUninit union construction requires one operand".into());
        };
        let [operand_ty] = operand_types else {
            return Err("MaybeUninit union operand type is missing".into());
        };
        let field = def
            .non_enum_variant()
            .fields
            .raw
            .get(active)
            .ok_or("MaybeUninit union active field is invalid")?;
        let field_ty = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                field.ty(self.tcx, args),
            )
            .map_err(|e| format!("MaybeUninit active field normalization failed: {e:?}"))?;
        if *operand_ty != field_ty {
            return Err(
                "MaybeUninit union operand type differs from its declared active field".into(),
            );
        }
        let payload = if active == unit
            && (matches!(value, Value::Unit)
                || matches!(value, Value::Tuple(fields) if fields.is_empty()))
        {
            None
        } else if active == initialized {
            let Value::Adt {
                name,
                variant,
                fields,
                is_option,
                ..
            } = value
            else {
                return Err(
                    "MaybeUninit construction lacks initialized ManuallyDrop storage".into(),
                );
            };
            let ty::Adt(drop, _) = operand_ty.kind() else {
                return Err("MaybeUninit value wrapper is not an ADT".into());
            };
            if *variant != 0
                || *is_option
                || *name != self.tcx.def_path_str(drop.did())
                || fields.len() != 1
            {
                return Err(
                    "MaybeUninit construction has mismatched retained ManuallyDrop storage".into(),
                );
            }
            let (field_name, payload) = fields.first().ok_or("ManuallyDrop payload is missing")?;
            if *field_name != drop.non_enum_variant().fields.raw[0].name.as_str() {
                return Err(
                    "ManuallyDrop retained field does not match its compiler identity".into(),
                );
            }
            self.maybe_uninit_payload_value(payload_ty, payload, conditions)?;
            Some(Box::new(payload.clone()))
        } else {
            return Err("MaybeUninit construction has an incompatible active field value".into());
        };
        let id = if let Some(id) = self.maybe_uninit_types.iter().position(|ty| *ty == wrapper) {
            id
        } else {
            if self.maybe_uninit_types.len() >= MAX_SHAPES {
                return Err("MaybeUninit type descriptor budget reached".into());
            }
            let id = self.maybe_uninit_types.len();
            self.maybe_uninit_types.push(wrapper);
            id
        };
        Ok(Some(Value::MaybeUninit { id, payload }))
    }

    pub(super) fn maybe_uninit_payload_type(&self, id: usize) -> Result<Ty<'tcx>, String> {
        let wrapper = *self
            .maybe_uninit_types
            .get(id)
            .ok_or("MaybeUninit type descriptor is missing")?;
        Ok(self.maybe_uninit_shape(wrapper)?.0)
    }

    pub(super) fn validate_maybe_uninit_value(
        &self,
        ty: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        if !contains_wrapper(value) {
            return Ok(());
        }
        let mut nodes = 0;
        self.validate_maybe_uninit_context(ty, value, conditions, 0, &mut nodes)
    }

    fn validate_maybe_uninit_context(
        &self,
        ty: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
        depth: usize,
        nodes: &mut usize,
    ) -> Result<(), String> {
        // Existing unrelated representations stay in their own validation domains. Every
        // aggregate is traversed so a nested wrapper cannot escape compiler type checking.
        *nodes += 1;
        if depth > 32 || *nodes > 4096 {
            return Err("MaybeUninit contextual validation budget reached".into());
        }
        match value {
            Value::MaybeUninit { id, payload } => {
                let original = self
                    .maybe_uninit_types
                    .get(*id)
                    .ok_or("MaybeUninit type descriptor is missing")?;
                if *original != ty {
                    return Err(
                        "MaybeUninit retained wrapper differs from the exact compiler type".into(),
                    );
                }
                let payload_ty = self.maybe_uninit_payload_type(*id)?;
                if let Some(value) = payload {
                    self.maybe_uninit_payload_value(payload_ty, value, conditions)?;
                }
                Ok(())
            }
            Value::Tuple(values) => {
                let ty::Tuple(fields) = ty.kind() else {
                    if values.iter().any(contains_wrapper) {
                        return Err(
                            "nested MaybeUninit tuple has a mismatched compiler type".into()
                        );
                    }
                    return Ok(());
                };
                if fields.len() != values.len() {
                    return Err("nested MaybeUninit tuple has a mismatched arity".into());
                }
                for (field, value) in fields.iter().zip(values) {
                    self.validate_maybe_uninit_context(field, value, conditions, depth + 1, nodes)?;
                }
                Ok(())
            }
            Value::Elements(values) => {
                let ty::Array(element, length) = ty.kind() else {
                    if values.iter().any(contains_wrapper) {
                        return Err(
                            "nested MaybeUninit array has a mismatched compiler type".into()
                        );
                    }
                    return Ok(());
                };
                if length.try_to_target_usize(self.tcx) != Some(values.len() as u64) {
                    return Err("nested MaybeUninit array has a mismatched length".into());
                }
                for value in values.iter() {
                    self.validate_maybe_uninit_context(
                        *element,
                        value,
                        conditions,
                        depth + 1,
                        nodes,
                    )?;
                }
                Ok(())
            }
            Value::Adt { fields, .. }
                if matches!(ty.kind(), ty::Closure(..))
                    && fields.iter().any(|(_, value)| contains_wrapper(value)) =>
            {
                let types = self
                    .closure_capture_types(ty, value)?
                    .ok_or("closure carrier compiler type is missing")?;
                for (ty, (_, capture)) in types.iter().zip(fields) {
                    self.validate_maybe_uninit_context(ty, capture, conditions, depth + 1, nodes)?;
                }
                Ok(())
            }
            Value::Adt {
                name,
                variant,
                fields,
                discriminant,
                is_option,
            } if fields.iter().any(|(_, value)| contains_wrapper(value)) => {
                let ty::Adt(def, args) = ty.kind() else {
                    return Err("nested MaybeUninit ADT lacks its compiler type".into());
                };
                if def.is_union() || self.tcx.def_path_str(def.did()) != *name {
                    return Err(
                        "nested MaybeUninit ADT has an incompatible compiler identity".into(),
                    );
                }
                let index = rustc_abi::VariantIdx::from_usize(*variant);
                let variant = def
                    .variants()
                    .get(index)
                    .ok_or("nested MaybeUninit ADT has an invalid variant")?;
                let expected_discriminant = if def.is_enum() {
                    def.discriminant_for_variant(self.tcx, index).val
                } else {
                    0
                };
                if *is_option != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                    || *discriminant != expected_discriminant
                {
                    return Err("nested MaybeUninit ADT has incompatible variant metadata".into());
                }
                if variant.fields.len() != fields.len() {
                    return Err("nested MaybeUninit ADT has mismatched fields".into());
                }
                for (field, (name, value)) in variant.fields.iter().zip(fields.iter()) {
                    if field.name.as_str() != name {
                        return Err("nested MaybeUninit ADT field identity differs".into());
                    }
                    let field_ty = self
                        .tcx
                        .try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            field.ty(self.tcx, args),
                        )
                        .map_err(|e| {
                            format!("nested MaybeUninit field normalization failed: {e:?}")
                        })?;
                    self.validate_maybe_uninit_context(
                        field_ty,
                        value,
                        conditions,
                        depth + 1,
                        nodes,
                    )?;
                }
                Ok(())
            }
            Value::Enum { variants, .. } if variants.iter().any(contains_wrapper) => {
                Err("symbolic enum carriers of MaybeUninit require typed variant selection".into())
            }
            _ if contains_wrapper(value) => {
                Err("MaybeUninit contextual carrier is unsupported".into())
            }
            _ => Ok(()),
        }
    }

    fn unique_zero_byte_payload(&self, ty: Ty<'tcx>) -> Result<Option<Value>, String> {
        if self.static_layout(ty)?.size.bytes() != 0 {
            return Ok(None);
        }
        match ty.kind() {
            ty::Tuple(fields) if fields.is_empty() => Ok(Some(Value::Unit)),
            ty::Tuple(fields) => {
                let mut values = Vec::new();
                for field in fields.iter() {
                    let Some(value) = self.unique_zero_byte_payload(field)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Ok(Some(Value::Tuple(values)))
            }
            ty::Array(element, length) => {
                let count = self.maybe_uninit_array_count(*length)?;
                if *element == self.tcx.types.u8 && count == 0 {
                    let bits = u32::from(self.tcx.sess.target.pointer_width);
                    return Ok(Some(Value::Bytes {
                        length: Box::new(symbolic::integer(&self.terms, 0, bits, false)),
                        data: self.terms.apply(
                            Op::ConstArray { index_bits: bits },
                            &[self.terms.bit_vector(0, 8)?],
                        )?,
                    }));
                }
                let mut values = Vec::new();
                for _ in 0..count {
                    let Some(value) = self.unique_zero_byte_payload(*element)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Ok(Some(Value::Elements(values.into())))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn maybe_uninit_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Adt(def, _) = source.kind() else {
            return Ok(None);
        };
        if self.tcx.lang_items().get(LangItem::MaybeUninit) != Some(def.did()) {
            return Ok(None);
        }
        self.validate_maybe_uninit_value(source, value, conditions)?;
        let (payload_ty, _, _) = self.maybe_uninit_shape(source)?;
        if target != payload_ty {
            return Err("MaybeUninit extraction changes the exact compiler payload type".into());
        }
        let Value::MaybeUninit { payload, .. } = value else {
            return Err("MaybeUninit extraction lacks certified wrapper state".into());
        };
        let Some(payload) = payload else {
            return self
                .unique_zero_byte_payload(target)?
                .map(Some)
                .ok_or_else(|| {
                    self.categorized_error(
                        UnknownCategory::Semantics,
                        "MaybeUninit payload is not initialized".into(),
                    )
                });
        };
        self.maybe_uninit_payload_value(target, payload, conditions)?;
        Ok(Some((**payload).clone()))
    }
}

fn contains_wrapper(value: &Value) -> bool {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            Value::MaybeUninit { .. } => return true,
            Value::Tuple(values) => pending.extend(values),
            Value::Enum {
                discriminant,
                variants,
                ..
            } => {
                pending.push(discriminant);
                pending.extend(variants);
            }
            Value::Elements(values) => pending.extend(values.iter()),
            Value::Adt { fields, .. } => pending.extend(fields.iter().map(|(_, value)| value)),
            Value::StaticSlice {
                source, elements, ..
            } => {
                pending.push(source);
                pending.extend(elements);
            }
            Value::TrackedPointer { reference, .. } => pending.push(reference),
            Value::RawSlice { source, length } => {
                pending.push(source);
                pending.push(length);
            }
            Value::SliceIterator {
                source,
                front,
                back,
                unchecked,
                ..
            } => {
                pending.extend([source.as_ref(), front.as_ref(), back.as_ref()]);
                pending.extend(unchecked);
            }
            Value::MetadataPointer(source)
            | Value::TraitObject { source, .. }
            | Value::DebugReference { source, .. } => pending.push(source),
            Value::Uninitialized
            | Value::StaticView { .. }
            | Value::RawPointer { .. }
            | Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::ScalarSlice { .. }
            | Value::Bytes { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::Reference { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => {}
        }
    }
    false
}

fn validate_byte_payload(
    context: &Context,
    pointer_bits: u32,
    count: u64,
    length: &Value,
    data: &Term,
) -> Result<(), String> {
    let (length, bits, signed) = length.integer()?;
    if bits != pointer_bits
        || signed
        || !length.belongs_to(context)
        || length.sort() != &Sort::BitVec(pointer_bits)
        || symbolic::constant(&length)
            != Some(symbolic::Constant::BitVec {
                value: u128::from(count),
                bits: pointer_bits,
            })
        || !data.belongs_to(context)
        || data.sort()
            != &Sort::Array(
                Box::new(Sort::BitVec(pointer_bits)),
                Box::new(Sort::BitVec(8)),
            )
    {
        return Err(
            "MaybeUninit initialized byte array has invalid length, sort or context".into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initialized_byte_arrays_require_exact_length_sort_and_context() {
        let context = Context::default();
        let foreign = Context::default();
        for bits in [32, 64] {
            let length = symbolic::integer(&context, 3, bits, false);
            let data = context
                .apply(
                    Op::ConstArray { index_bits: bits },
                    &[context.bit_vector(7, 8).unwrap()],
                )
                .unwrap();
            assert!(validate_byte_payload(&context, bits, 3, &length, &data).is_ok());
            assert!(validate_byte_payload(&context, bits, 2, &length, &data).is_err());
            assert!(
                validate_byte_payload(
                    &context,
                    bits,
                    3,
                    &symbolic::integer(&context, 3, bits, true),
                    &data
                )
                .is_err()
            );
            let wrong_width = Value::Int {
                expression: context.bit_vector(3, 8).unwrap(),
                bits,
                signed: false,
            };
            assert!(validate_byte_payload(&context, bits, 3, &wrong_width, &data).is_err());
            let symbolic_length = Value::Int {
                expression: context.symbol(bits, Sort::BitVec(bits)).unwrap(),
                bits,
                signed: false,
            };
            assert!(validate_byte_payload(&context, bits, 3, &symbolic_length, &data).is_err());
            assert!(
                validate_byte_payload(
                    &context,
                    bits,
                    3,
                    &symbolic::integer(&foreign, 3, bits, false),
                    &data
                )
                .is_err()
            );
            let wrong_element = context
                .apply(
                    Op::ConstArray { index_bits: bits },
                    &[context.bit_vector(7, 16).unwrap()],
                )
                .unwrap();
            assert!(validate_byte_payload(&context, bits, 3, &length, &wrong_element).is_err());
            let wrong_index = context
                .apply(
                    Op::ConstArray { index_bits: 8 },
                    &[context.bit_vector(7, 8).unwrap()],
                )
                .unwrap();
            assert!(validate_byte_payload(&context, bits, 3, &length, &wrong_index).is_err());
            let foreign_data = foreign
                .apply(
                    Op::ConstArray { index_bits: bits },
                    &[foreign.bit_vector(7, 8).unwrap()],
                )
                .unwrap();
            assert!(validate_byte_payload(&context, bits, 3, &length, &foreign_data).is_err());
        }
    }
}
