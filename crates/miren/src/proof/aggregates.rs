use super::*;
use rustc_index::IndexVec;

const MAX_ARRAY_BYTES: u64 = 128;
pub(super) const MAX_ARRAY_ELEMENTS: usize = 16;
const MAX_INPUT_ELEMENTS: usize = 256;
pub(super) const MAX_ENUM_VARIANTS: usize = 64;
pub(super) const MAX_FIELDLESS_ENUM_VARIANTS: usize = 256;

pub(super) fn known_repeat_cost(count: usize) -> Option<usize> {
    count.saturating_sub(1).checked_add(2)
}

// This budget belongs only to the new Repeat admission, not generic aggregate consumers.
pub(super) struct RepeatWork {
    used: usize,
}

impl RepeatWork {
    pub(super) fn new() -> Self {
        Self { used: 0 }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn repeat_charge(&self, work: &mut RepeatWork, count: usize) -> Result<(), String> {
        work.used = work.used.saturating_add(count);
        if work.used > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "known Repeat exceeds existing 512-node work budget".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn repeat_type_work(
        &self,
        original: Ty<'tcx>,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
        work: &mut RepeatWork,
    ) -> Result<Ty<'tcx>, String> {
        self.repeat_charge(work, 1)?;
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "known Repeat original type exceeds depth16".into(),
            ));
        }
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => {}
            ty::Param(parameter) => {
                let selected = arguments
                    .get(parameter.index as usize)
                    .and_then(|argument| argument.as_type())
                    .ok_or("known Repeat original Param mapping differs")?;
                return self.repeat_type_work(selected, arguments, depth + 1, work);
            }
            ty::Tuple(fields) => {
                self.repeat_charge(work, fields.len())?;
                for field in fields.iter() {
                    self.repeat_type_work(field, arguments, depth + 1, work)?;
                }
            }
            ty::Adt(_, args) => self.repeat_argument_work(args, depth + 1, work)?,
            ty::Array(element, count) => {
                self.repeat_charge(work, 1)?;
                count
                    .try_to_target_usize(self.tcx)
                    .ok_or("known Repeat original array extent is not literal")?;
                self.repeat_type_work(*element, arguments, depth + 1, work)?;
            }
            ty::FnPtr(..) => {
                let signature = original.fn_sig(self.tcx);
                if !signature.bound_vars().is_empty() {
                    return Err("known Repeat bound callable variables are unsupported".into());
                }
                self.repeat_signature_work(signature.skip_binder(), arguments, depth + 1, work)?;
            }
            _ => return Err("known Repeat original type grammar is unsupported".into()),
        }
        Ok(original)
    }

    pub(super) fn repeat_argument_work(
        &self,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
        work: &mut RepeatWork,
    ) -> Result<(), String> {
        self.repeat_charge(work, arguments.len())?;
        for argument in arguments.iter() {
            match argument.kind() {
                ty::GenericArgKind::Type(original) => {
                    self.repeat_type_work(original, arguments, depth, work)?;
                }
                ty::GenericArgKind::Lifetime(_) => {}
                ty::GenericArgKind::Const(_) => {
                    return Err("known Repeat const substitution is unsupported".into());
                }
            }
        }
        Ok(())
    }

    pub(super) fn repeat_signature_work(
        &self,
        signature: ty::FnSig<'tcx>,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
        work: &mut RepeatWork,
    ) -> Result<(), String> {
        let arity = signature.inputs().len();
        if !(1..=2).contains(&arity)
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return Err(
                "known Repeat needs a safe Rust integer callable with one or two args".into(),
            );
        }
        self.repeat_charge(work, arity + 1)?;
        let result = signature.output();
        let primitive = arity == 1
            && signature.inputs()[0] == result
            && matches!(
                result.kind(),
                ty::Bool | ty::Char | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
            );
        for original in signature.inputs().iter().chain(std::iter::once(&result)) {
            let selected = self.repeat_type_work(*original, arguments, depth, work)?;
            if !primitive && !matches!(selected.kind(), ty::Int(_) | ty::Uint(_)) {
                return Err("known Repeat signature needs exact original integer types".into());
            }
        }
        Ok(())
    }

    pub(super) fn repeat_place_type(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        work: &mut RepeatWork,
    ) -> Result<Ty<'tcx>, String> {
        let declaration = body
            .local_decls
            .get(place.local)
            .ok_or("known Repeat local is outside its original Body")?;
        self.repeat_charge(work, place.projection.len())?;
        if place.projection.len() > MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "known Repeat place exceeds depth16".into(),
            ));
        }
        let mut original = declaration.ty;
        self.repeat_type_work(original, self.tcx.mk_args(&[]), 0, work)?;
        let mut variant = None;
        for part in place.projection {
            match part {
                ProjectionElem::Downcast(_, index) => {
                    let ty::Adt(def, _) = original.kind() else {
                        return Err("known Repeat downcast lacks original enum".into());
                    };
                    if !def.is_enum()
                        || index.as_usize() >= def.variants().len()
                        || variant.is_some()
                    {
                        return Err("known Repeat original variant differs".into());
                    }
                    variant = Some(index);
                }
                ProjectionElem::Field(index, recorded) => {
                    self.repeat_type_work(recorded, self.tcx.mk_args(&[]), 0, work)?;
                    let selected = match original.kind() {
                        ty::Tuple(fields) => fields.get(index.as_usize()).copied(),
                        ty::Adt(def, args) => {
                            let fields = if def.is_struct() {
                                &def.non_enum_variant().fields
                            } else if def.is_enum() {
                                &def.variants()[variant
                                    .ok_or("known Repeat enum field lacks original downcast")?]
                                .fields
                            } else {
                                return Err("known Repeat union field is unsupported".into());
                            };
                            let field = fields
                                .get(index)
                                .ok_or("known Repeat field exceeds original inventory")?;
                            // Bound raw field Param expansion before field.ty substitutes.
                            let raw = self
                                .tcx
                                .type_of(field.did)
                                .instantiate_identity()
                                .skip_norm_wip();
                            self.repeat_type_work(raw, args, 0, work)?;
                            Some(field.ty(self.tcx, args).skip_norm_wip())
                        }
                        _ => None,
                    }
                    .ok_or("known Repeat field lacks original compiler parent")?;
                    if selected != recorded {
                        return Err(
                            "known Repeat FieldTy differs from original compiler type".into()
                        );
                    }
                    original = selected;
                    variant = None;
                }
                _ => return Err("known Repeat needs an owned local or fixed field path".into()),
            }
        }
        if variant.is_some() {
            return Err("known Repeat dangling downcast is unsupported".into());
        }
        self.owned_field_footprint(body, place)?;
        Ok(original)
    }

    pub(super) fn known_repeat_assignment(
        &self,
        executing: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Rvalue::Repeat(operand, length) = rvalue else {
            return Ok(None);
        };
        let candidate = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let Some(declaration) = body.local_decls.get(place.local) else {
                    return Err("known Repeat operand local is outside its Body".into());
                };
                if let Some(ProjectionElem::Field(_, recorded)) = place.projection.last() {
                    *recorded
                } else {
                    declaration.ty
                }
            }
            Operand::Constant(constant) => constant.const_.ty(),
            Operand::RuntimeChecks(_) => return Ok(None),
        };
        if !matches!(candidate.kind(), ty::FnPtr(..)) {
            return Ok(None);
        }
        let mut work = RepeatWork::new();
        let cached = self.bodies.borrow();
        self.repeat_charge(&mut work, cached.len())?;
        let mut matches = cached
            .iter()
            .filter(|(_, candidate)| std::ptr::eq(candidate.as_ref(), body));
        let (instance, original) = matches
            .next()
            .ok_or("known Repeat requires an authenticated current cached Body")?;
        if matches.next().is_some()
            || *instance != executing
            || body.source.instance != instance.def
        {
            return Err("known Repeat cached full Instance/Body association differs".into());
        }
        let instance = *instance;
        let original = original.clone();
        drop(cached);
        self.repeat_argument_work(instance.args, 0, &mut work)?;
        self.repeat_charge(&mut work, original.local_decls.len())?;
        self.repeat_charge(&mut work, original.basic_blocks.len())?;
        for block in original.basic_blocks.iter() {
            self.repeat_charge(&mut work, block.statements.len())?;
        }
        let found = original.basic_blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                std::ptr::eq(&statement.kind, occurrence)
                    && matches!(&statement.kind, StatementKind::Assign(assignment)
                        if assignment.0 == destination && std::ptr::eq(&assignment.1, rvalue))
            })
        });
        if !found {
            return Err("known Repeat is not its actual cached Assign occurrence".into());
        }
        let destination_ty = self.repeat_place_type(body, destination, &mut work)?;
        let source_ty = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.repeat_place_type(body, *place, &mut work)?
            }
            Operand::Constant(constant) => {
                let original = constant.const_.ty();
                self.repeat_type_work(original, self.tcx.mk_args(&[]), 0, &mut work)?;
                original
            }
            Operand::RuntimeChecks(_) => {
                return Err("known Repeat cannot authenticate runtime-check operand".into());
            }
        };
        let ty::Array(element, extent) = destination_ty.kind() else {
            return Err("known Repeat destination needs its original array type".into());
        };
        let count = length
            .try_to_target_usize(self.tcx)
            .ok_or("known Repeat length is not literal target usize")?;
        let count = usize::try_from(count).map_err(|_| "known Repeat length exceeds host usize")?;
        if count > MAX_ARRAY_BYTES as usize
            || *element != source_ty
            || extent != length
            || !matches!(source_ty.kind(), ty::FnPtr(..))
        {
            return Err("known Repeat original element/count exceeds its exact domain".into());
        }
        let env = ty::TypingEnv::fully_monomorphized();
        if !self.tcx.type_is_copy_modulo_regions(env, source_ty)
            || !source_ty.is_freeze(self.tcx, env)
        {
            return Err("known Repeat original FnPtr needs Copy and Freeze".into());
        }
        self.tcx
            .layout_of(env.as_query_input(destination_ty))
            .map_err(|error| format!("known Repeat array layout is unavailable: {error:?}"))?;
        let cost = known_repeat_cost(count).ok_or("known Repeat construction cost overflow")?;
        if cost > symbolic::MAX_REPEAT_VALUES {
            return Err("known Repeat exceeds existing 256-value construction budget".into());
        }
        let value = self.evaluate_operand(executing.def_id(), body, state, operand)?;
        self.validate_repeat_target(&value, source_ty, &mut work)?;
        Ok(Some(Value::Elements(vec![value; count].into())))
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn enum_input(
        &mut self,
        id: DefId,
        ty: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        let ty::Adt(def, args) = ty.kind() else {
            return Err("expected an enum type".to_owned());
        };
        let fieldless = def
            .variants()
            .iter()
            .all(|variant| variant.fields.is_empty());
        let maximum = if fieldless {
            MAX_FIELDLESS_ENUM_VARIANTS
        } else {
            MAX_ENUM_VARIANTS
        };
        if def.variants().is_empty() || def.variants().len() > maximum {
            return Err(format!("enum inputs need between 1 and {maximum} variants"));
        }
        let (bits, signed) = self
            .integer_type(ty.discriminant_ty(self.tcx))
            .ok_or("unsupported enum discriminant type")?;
        let discriminant = Value::Int {
            expression: self.fresh(Sort::BitVec(bits)),
            bits,
            signed,
        };
        let mut variants = Vec::new();
        let mut valid = Vec::new();
        for (index, variant) in def.variants().iter_enumerated() {
            if self.input_values >= MAX_INPUT_VALUES {
                return Err("input shape exceeds the 512-value budget".to_owned());
            }
            self.input_values += 1;
            let tag = def.discriminant_for_variant(self.tcx, index).val;
            valid.push(
                symbolic::binary(
                    &self.terms,
                    "eq",
                    discriminant.clone(),
                    symbolic::integer(&self.terms, tag, bits, signed),
                )?
                .boolean()?,
            );
            let fields = variant
                .fields
                .iter()
                .map(|field| {
                    let ty = self
                        .tcx
                        .try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            field.ty(self.tcx, args),
                        )
                        .map_err(|error| format!("input field normalization failed: {error:?}"))?;
                    self.argument(id, ty, conditions).map_err(|error| {
                        format!(
                            "input variant {} field {}: {error}",
                            variant.name, field.name
                        )
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            variants.push(self.constructed(ty, index.as_usize(), fields)?);
        }
        conditions.push(self.terms.apply(Op::Or, &valid)?);
        Ok(Value::Enum {
            discriminant: Box::new(discriminant),
            variants,
            is_option: self.tcx.lang_items().get(LangItem::Option) == Some(def.did()),
        })
    }

    pub(super) fn struct_input(
        &mut self,
        id: DefId,
        ty: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        let ty::Adt(def, args) = ty.kind() else {
            return Err("expected a struct type".to_owned());
        };
        let fields = def
            .non_enum_variant()
            .fields
            .iter()
            .map(|field| {
                let ty = self
                    .tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        field.ty(self.tcx, args),
                    )
                    .map_err(|error| format!("input field normalization failed: {error:?}"))?;
                Ok((
                    field.name.as_str().to_owned(),
                    self.argument(id, ty, conditions)
                        .map_err(|error| format!("input field {}: {error}", field.name))?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Value::Adt {
            name: self.tcx.def_path_str(def.did()),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: fields.into(),
        })
    }

    pub(super) fn element_input(
        &mut self,
        id: DefId,
        ty: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        let ty::Array(element, count) = ty.kind() else {
            return Err("expected a fixed array input".to_owned());
        };
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("unknown input array length")?;
        if count > MAX_INPUT_ELEMENTS as u64 {
            return Err("fixed array input exceeds 256 elements".to_owned());
        }
        Ok(Value::Elements(
            (0..count)
                .map(|index| {
                    self.argument(id, *element, conditions)
                        .map_err(|error| format!("input array element {index}: {error}"))
                })
                .collect::<Result<_, _>>()?,
        ))
    }

    pub(super) fn aggregate(
        &mut self,
        id: DefId,
        body: &Body<'tcx>,
        state: &mut State,
        kind: &AggregateKind<'tcx>,
        operands: &IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
    ) -> Result<Value, String> {
        let values = operands
            .iter()
            .map(|value| self.evaluate_operand(id, body, state, value))
            .collect::<Result<Vec<_>, _>>()?;
        let pin = matches!(kind, AggregateKind::Adt(def, ..)
            if self.tcx.lang_items().get(LangItem::Pin) == Some(*def));
        for (operand, value) in operands.iter().zip(&values) {
            if !pin
                || !self.validate_coroutine_reference_transport(
                    operand.ty(&body.local_decls, self.tcx),
                    value,
                    state,
                    None,
                )?
            {
                self.validate_tracked_value(value, state)?;
            }
        }
        if let AggregateKind::Adt(def, variant, args, _, Some(active)) = kind {
            let operand_types = operands
                .iter()
                .map(|operand| operand.ty(&body.local_decls, self.tcx))
                .collect::<Vec<_>>();
            if variant.as_usize() != 0 {
                return Err("union aggregate has an invalid variant".into());
            }
            let wrapper = Ty::new_adt(self.tcx, self.tcx.adt_def(*def), args);
            if let Some(value) = self.maybe_uninit_aggregate(
                wrapper,
                active.as_usize(),
                &operand_types,
                &values,
                &state.conditions,
            )? {
                self.record_model(
                    id,
                    "compiler-certified MaybeUninit construction; explicit payload initialization",
                );
                return Ok(value);
            }
        }
        match kind {
            AggregateKind::RawPtr(pointee, mutability) => {
                self.raw_slice_aggregate(id, *pointee, mutability.is_mut(), values, state)
            }
            AggregateKind::Coroutine(id, args) => self.construct_coroutine(*id, args, values),
            AggregateKind::Array(element) if *element == self.tcx.types.u8 => {
                if values.len() as u64 > MAX_ARRAY_BYTES {
                    return Err("byte array model size limit reached".to_owned());
                }
                let bits = u32::from(self.tcx.sess.target.pointer_width);
                let mut data = self.terms.apply(
                    Op::ConstArray { index_bits: bits },
                    &[self.terms.bit_vector(0, 8)?],
                )?;
                for (index, value) in values.iter().enumerate() {
                    let (expression, width, signed) = value.integer()?;
                    if width != 8 || signed {
                        return Err("non-byte array element".to_owned());
                    }
                    data = self.terms.apply(
                        Op::Store,
                        &[
                            data.clone(),
                            self.terms.bit_vector(index as u128, bits)?,
                            expression.clone(),
                        ],
                    )?;
                }
                Ok(Value::Bytes {
                    length: Box::new(symbolic::integer(
                        &self.terms,
                        values.len() as u128,
                        bits,
                        false,
                    )),
                    data,
                })
            }
            AggregateKind::Closure(id, _) => Ok(Value::Adt {
                name: self.tcx.def_path_str(*id),
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields: values
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| (index.to_string(), value))
                    .collect(),
            }),
            AggregateKind::Array(_) => {
                if values.len() > MAX_ARRAY_ELEMENTS {
                    return Err("fixed array element model size limit reached".to_owned());
                }
                Ok(Value::Elements(values.into()))
            }
            AggregateKind::Adt(id, variant, _, _, active) if active.is_none() => {
                let def = self.tcx.adt_def(*id);
                if !def.is_struct() && !def.is_enum() {
                    return Err("only struct and enum aggregates are modeled".to_owned());
                }
                let layout = def.variant(*variant);
                if layout.fields.len() != values.len() {
                    return Err("ADT field count mismatch".to_owned());
                }
                Ok(Value::Adt {
                    name: self.tcx.def_path_str(*id),
                    variant: variant.as_usize(),
                    is_option: self.tcx.lang_items().get(LangItem::Option) == Some(*id),
                    discriminant: if def.is_enum() {
                        def.discriminant_for_variant(self.tcx, *variant).val
                    } else {
                        0
                    },
                    fields: layout
                        .fields
                        .iter()
                        .zip(values)
                        .map(|(field, value)| (field.name.as_str().to_owned(), value))
                        .collect(),
                })
            }
            _ => Err("unsupported aggregate kind".to_owned()),
        }
    }

    pub(super) fn fixed_element(
        &self,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        self.fixed_element_with_type(elements, index, conditions, None)
    }

    pub(super) fn fixed_element_with_type(
        &self,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
        original: Option<Ty<'tcx>>,
    ) -> Result<Value, String> {
        self.fixed_element_with_source(elements, index, conditions, original, None)
    }

    pub(super) fn fixed_element_with_source(
        &self,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
        original: Option<Ty<'tcx>>,
        source: Option<function_tables::TableSource<'_, 'tcx>>,
    ) -> Result<Value, String> {
        let (expression, bits, signed) = index.integer()?;
        if signed || bits != u32::from(self.tcx.sess.target.pointer_width) {
            return Err("fixed array index type mismatch".to_owned());
        }
        if let Some(symbolic::Constant::BitVec {
            value,
            bits: constant_bits,
        }) = symbolic::constant(&expression)
            && constant_bits == bits
        {
            return usize::try_from(value)
                .ok()
                .and_then(|position| elements.get(position))
                .cloned()
                .ok_or_else(|| "array read lacks a proven bounds check".to_owned());
        }
        let scalar_choice = symbolic::select_element(&self.terms, elements, index);
        if scalar_choice.is_ok() {
            let bound = symbolic::binary(
                &self.terms,
                "lt",
                index.clone(),
                symbolic::integer(&self.terms, elements.len() as u128, bits, false),
            )?
            .boolean()?;
            let mut outside = conditions.to_vec();
            outside.push(symbolic::not(&bound));
            if self.feasible(&outside)? {
                return Err("array read lacks a proven bounds check".to_owned());
            }
            return scalar_choice;
        }
        for (position, element) in elements.iter().enumerate() {
            let equal = symbolic::binary(
                &self.terms,
                "eq",
                index.clone(),
                symbolic::integer(&self.terms, position as u128, bits, false),
            )?
            .boolean()?;
            let mut different = conditions.to_vec();
            different.push(symbolic::not(&equal));
            if !self.feasible(&different)? {
                return Ok(element.clone());
            }
        }
        let bound = symbolic::binary(
            &self.terms,
            "lt",
            index.clone(),
            symbolic::integer(&self.terms, elements.len() as u128, bits, false),
        )?
        .boolean()?;
        let mut outside = conditions.to_vec();
        outside.push(symbolic::not(&bound));
        if self.feasible(&outside)? {
            return Err("array read lacks a proven bounds check".to_owned());
        }
        if let Some(original) = original
            && let Some(selected) =
                self.function_table_choice(original, elements, index, conditions, source)?
        {
            return Ok(selected);
        }
        if let Some(original) = original
            && let Some(selected) =
                self.typed_owned_array_choice(original, elements, index, conditions)?
        {
            return Ok(selected);
        }
        if let Some(original) = original
            && let Some(source) = source
            && let Some(selected) = self.shared_trait_object_choice(
                original,
                elements,
                index,
                conditions,
                source.state,
            )?
        {
            return Ok(selected);
        }
        symbolic::select_element(&self.terms, elements, index).map_err(|_| {
            "non-scalar array index is not uniquely determined on this path".to_owned()
        })
    }

    pub(super) fn constant_element(
        &self,
        state: &State,
        value: Value,
        offset: u64,
        min_length: u64,
        from_end: bool,
    ) -> Result<Value, String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = match &value {
            Value::ScalarSlice { .. } => self.scalar_slice_length(&value, &state.conditions)?,
            Value::CompositeSlice { .. } => {
                self.composite_slice_length(&value, &state.conditions)?
            }
            Value::Bytes { length, .. } => length.as_ref().clone(),
            Value::Elements(elements) => {
                symbolic::integer(&self.terms, elements.len() as u128, bits, false)
            }
            Value::StaticSlice { elements, .. } => {
                symbolic::integer(&self.terms, elements.len() as u128, bits, false)
            }
            _ => return Err("constant indexing needs a modeled array or slice".to_owned()),
        };
        let required = if from_end {
            min_length.max(offset)
        } else {
            min_length
        };
        let long_enough = symbolic::binary(
            &self.terms,
            "ge",
            length.clone(),
            symbolic::integer(&self.terms, u128::from(required), bits, false),
        )?
        .boolean()?;
        let mut too_short = state.conditions.clone();
        too_short.push(symbolic::not(&long_enough));
        if self.feasible(&too_short)? {
            return Err("constant index lacks a proven minimum length".to_owned());
        }
        let offset = symbolic::integer(&self.terms, u128::from(offset), bits, false);
        let index = if from_end {
            symbolic::binary(&self.terms, "sub", length.clone(), offset)?
        } else {
            offset
        };
        match value {
            value @ Value::CompositeSlice { .. } => {
                self.composite_slice_select(&value, &index, &state.conditions)
            }
            value @ Value::ScalarSlice { .. } => {
                self.scalar_slice_select(&value, &index, &state.conditions)
            }
            Value::Elements(elements) => self.fixed_element(&elements, &index, &state.conditions),
            Value::StaticSlice { elements, .. } => {
                let selected = self.fixed_element(&elements, &index, &state.conditions)?;
                self.static_view_projection(&selected, ProjectionElem::Deref, state)
            }
            Value::Bytes { data, .. } => {
                let inside =
                    symbolic::binary(&self.terms, "lt", index.clone(), length)?.boolean()?;
                let mut outside = state.conditions.clone();
                outside.push(symbolic::not(&inside));
                if self.feasible(&outside)? {
                    return Err("constant byte index lacks a proven bounds check".to_owned());
                }
                let (expression, _, _) = index.integer()?;
                Ok(Value::Int {
                    expression: self
                        .terms
                        .apply(Op::Select, &[data.clone(), expression.clone()])?,
                    bits: 8,
                    signed: false,
                })
            }
            _ => Err("constant indexing needs a modeled array or slice".to_owned()),
        }
    }

    pub(super) fn repeated_array(
        &self,
        id: DefId,
        body: &Body<'tcx>,
        state: &mut State,
        operand: &Operand<'tcx>,
        length: ty::Const<'tcx>,
    ) -> Result<Value, String> {
        let count = length
            .try_to_target_usize(self.tcx)
            .ok_or("unevaluated repeat length")?;
        if !operand
            .ty(body, self.tcx)
            .is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err("repeated interior mutable storage is not modeled".to_owned());
        }
        let value = self.evaluate_operand(id, body, state, operand)?;
        if operand.ty(body, self.tcx) != self.tcx.types.u8 {
            if count > MAX_ARRAY_BYTES {
                return Err("array repeat exceeds the 128-element limit".to_owned());
            }
            let size = value
                .owned_repeat_size()
                .ok_or("repeat operand needs a small owned value")?;
            let copies = value
                .owned_repeat_clone_size()
                .and_then(|size| size.checked_mul(count.saturating_sub(1) as usize))
                .ok_or("owned repeat clone cost exceeds the model budget")?;
            if size
                .checked_add(copies)
                .and_then(|size| size.checked_add(1))
                .is_none_or(|size| size > symbolic::MAX_REPEAT_VALUES)
            {
                return Err("owned repeat exceeds the 256-value budget".to_owned());
            }
            return Ok(Value::Elements(vec![value; count as usize].into()));
        }
        let (expression, width, signed) = value.integer()?;
        if width != 8 || signed {
            return Err("byte repeat operand has incompatible scalar storage".to_owned());
        }
        let array = Ty::new_array(self.tcx, self.tcx.types.u8, count);
        self.tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(array))
            .map_err(|error| {
                format!("byte repeat requires a valid target array layout: {error:?}")
            })?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        Ok(Value::Bytes {
            length: Box::new(symbolic::integer(&self.terms, count as u128, bits, false)),
            data: self
                .terms
                .apply(Op::ConstArray { index_bits: bits }, &[expression])?,
        })
    }
}
