use super::*;
use rustc_span::Symbol;

impl<'tcx> Engine<'tcx> {
    fn is_core_align_of_val(&self, callee: DefId) -> bool {
        let Some(anchor) = self.tcx.get_diagnostic_item(Symbol::intern("mem_align_of")) else {
            return false;
        };
        let module = self.tcx.parent(anchor);
        if self.tcx.crate_name(anchor.krate) != Symbol::intern("core")
            || callee.krate != anchor.krate
            || self.tcx.parent(callee) != module
            || self.tcx.item_name(callee) != Symbol::intern("align_of_val")
            || self.tcx.def_kind(anchor) != DefKind::Fn
            || self.tcx.def_kind(module) != DefKind::Mod
        {
            return false;
        }
        self.tcx.module_children(module).iter().any(|child| {
            let Some(id) = child.res.opt_def_id() else {
                return false;
            };
            id == callee
                && child.ident.name == Symbol::intern("align_of_val")
                && id.krate == anchor.krate
                && self.tcx.parent(id) == module
                && self.tcx.def_kind(id) == DefKind::Fn
                && self.tcx.visibility(id).is_public()
        })
    }

    pub(super) fn layout_intrinsic(
        &mut self,
        instance: ty::Instance<'tcx>,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
        state: &mut State,
        location: (DefId, Span),
    ) -> Result<Option<Value>, String> {
        let callee = instance.def_id();
        if self.is_core_align_of_val(callee) {
            let ty = instance.args.type_at(0);
            let ty::Slice(element) = ty.kind() else {
                return Ok(None);
            };
            let [value] = values else {
                return Err("dynamic alignment requires one shared slice argument".into());
            };
            let storage = value.materialize()?;
            if !matches!(
                storage,
                Value::ScalarSlice { .. } | Value::CompositeSlice { .. }
            ) {
                return Ok(None);
            }
            if signature.safety() != rustc_hir::Safety::Safe
                || signature.abi() != rustc_abi::ExternAbi::Rust
                || signature.c_variadic()
                || signature.output() != self.tcx.types.usize
                || !matches!(signature.inputs(), [input]
                    if matches!(input.kind(), ty::Ref(_, pointee, mutability)
                        if *pointee == ty && !mutability.is_mut()))
            {
                return Err("dynamic alignment requires the exact safe shared-slice API".into());
            }
            self.validate_readonly_slice_value(ty, &storage, &state.memory, &state.conditions)?;
            self.readonly_slice_length(&storage, &state.conditions)?;
            self.instantiated_body(instance)?;
            let bits = u32::from(self.tcx.sess.target.pointer_width);
            let alignment = self.static_layout(*element)?.align.abi.bytes();
            if !alignment.is_power_of_two() || u128::from(alignment) > (u128::MAX >> (128 - bits)) {
                return Err("dynamic slice alignment does not fit target usize".into());
            }
            self.record_model(
                callee,
                "readonly slice alignment; exact compiler element ABI alignment",
            );
            return Ok(Some(symbolic::integer(
                &self.terms,
                u128::from(alignment),
                bits,
                false,
            )));
        }
        if self
            .tcx
            .is_intrinsic(callee, Symbol::intern("assert_zero_valid"))
        {
            if !signature.inputs().is_empty() || !signature.output().is_unit() || !values.is_empty()
            {
                return Err("zero-validity intrinsic signature mismatch".into());
            }
            let ty = instance.args.type_at(0);
            let valid = self
                .tcx
                .check_validity_requirement((
                    rustc_middle::ty::layout::ValidityRequirement::Zero,
                    ty::TypingEnv::fully_monomorphized().as_query_input(ty),
                ))
                .map_err(|error| format!("zero-validity layout unavailable: {error:?}"))?;
            let safe = self.terms.boolean(valid);
            self.require(
                location.0,
                location.1,
                &state.conditions,
                &safe,
                ObligationKind::PanicSafety,
                format!("compiler zero-initialization validity guard for {ty:?}"),
            )?;
            state.conditions.push(safe);
            self.record_model(
                callee,
                "compiler zero-initialization validity query; guard only",
            );
            return Ok(Some(Value::Unit));
        }
        if self
            .tcx
            .is_intrinsic(callee, Symbol::intern("assert_inhabited"))
        {
            if self
                .tcx
                .lang_items()
                .get(LangItem::MaybeUninit)
                .map(|id| id.krate)
                != Some(callee.krate)
                || !signature.inputs().is_empty()
                || !values.is_empty()
                || !signature.output().is_unit()
                || signature.safety() != rustc_hir::Safety::Safe
                || signature.abi() != rustc_abi::ExternAbi::Rust
                || signature.c_variadic()
            {
                return Err(
                    "inhabitance intrinsic has an unsupported compiler identity or signature"
                        .into(),
                );
            }
            let payload = instance.args.type_at(0);
            let inhabited = self
                .tcx
                .check_validity_requirement((
                    rustc_middle::ty::layout::ValidityRequirement::Inhabited,
                    ty::TypingEnv::fully_monomorphized().as_query_input(payload),
                ))
                .map_err(|error| format!("compiler inhabitance query unavailable: {error:?}"))?;
            let safe = self.terms.boolean(inhabited);
            self.require(
                location.0,
                location.1,
                &state.conditions,
                &safe,
                ObligationKind::PanicSafety,
                format!("compiler inhabitance guard for {payload:?}"),
            )?;
            state.conditions.push(safe);
            self.record_model(callee, "compiler inhabitance query; guard only");
            return Ok(Some(Value::Unit));
        }
        let reference_api = self
            .tcx
            .is_diagnostic_item(Symbol::intern("mem_size_of_val"), callee);
        if !reference_api && !self.tcx.is_intrinsic(callee, Symbol::intern("size_of_val")) {
            return Ok(None);
        }
        let ty = instance.args.type_at(0);
        let matching_pointer = match signature.inputs() {
            [input] => match input.kind() {
                ty::RawPtr(pointee, _) => !reference_api && *pointee == ty,
                ty::Ref(_, pointee, _) => reference_api && *pointee == ty,
                _ => false,
            },
            _ => false,
        };
        if signature.output() != self.tcx.types.usize || !matching_pointer {
            return Err("dynamic-size intrinsic signature mismatch".into());
        }
        let [value] = values else {
            return Err("dynamic-size intrinsic requires one pointer".into());
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let size = if ty.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized()) {
            symbolic::integer(
                &self.terms,
                u128::from(self.static_layout(ty)?.size.bytes()),
                bits,
                false,
            )
        } else {
            let ty::Slice(element) = ty.kind() else {
                return Err("dynamic size requires a sized type or modeled slice metadata".into());
            };
            let length = match value.materialize()? {
                storage @ Value::CompositeSlice { .. } if reference_api => {
                    if signature.safety() != rustc_hir::Safety::Safe
                        || signature.abi() != rustc_abi::ExternAbi::Rust
                        || signature.c_variadic()
                    {
                        return Err("composite dynamic size requires a safe fixed Rust API".into());
                    }
                    self.validate_readonly_slice_value(
                        ty,
                        &storage,
                        &state.memory,
                        &state.conditions,
                    )?;
                    self.instantiated_body(instance)?;
                    self.readonly_slice_length(&storage, &state.conditions)?
                }
                storage @ Value::ScalarSlice { .. } => {
                    self.validate_readonly_slice_value(
                        ty,
                        &storage,
                        &state.memory,
                        &state.conditions,
                    )?;
                    self.scalar_slice_length(&storage, &state.conditions)?
                }
                Value::Bytes { length, .. } => *length,
                Value::Elements(elements) => {
                    symbolic::integer(&self.terms, elements.len() as u128, bits, false)
                }
                Value::StaticSlice { elements, .. } => {
                    symbolic::integer(&self.terms, elements.len() as u128, bits, false)
                }
                _ => return Err("dynamic slice size requires retained length metadata".into()),
            };
            let stride = self.static_layout(*element)?.size.bytes();
            symbolic::binary(
                &self.terms,
                "mul",
                length,
                symbolic::integer(&self.terms, u128::from(stride), bits, false),
            )?
        };
        self.record_model(
            callee,
            "compiler-sized value or slice length times compiler element size",
        );
        Ok(Some(size))
    }

    pub(super) fn byte_array_scalar_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
    ) -> Result<Option<Value>, String> {
        // Character and pattern types restrict valid encodings; only primitive integers
        // accept every initialized bit pattern.
        let scalar = match target.kind() {
            ty::Int(_) | ty::Uint(_) => self.integer_type(target),
            _ => None,
        };
        let Some(bits) = self
            .float_type(target)
            .or_else(|| scalar.map(|(bits, _)| bits))
        else {
            return Ok(None);
        };
        let ty::Array(element, count) = source.kind() else {
            return Ok(None);
        };
        if *element != self.tcx.types.u8
            || count.try_to_target_usize(self.tcx) != Some(u64::from(bits / 8))
            || self.static_layout(source)?.size != self.static_layout(target)?.size
        {
            return Ok(None);
        }
        let Value::Bytes { data, .. } = value else {
            return Err("byte-to-scalar transmute requires initialized byte storage".into());
        };
        let count = bits / 8;
        let little = self.tcx.data_layout.endian == rustc_abi::Endian::Little;
        let mut expression = None;
        for position in 0..count {
            let index = if little {
                count - 1 - position
            } else {
                position
            };
            let byte = self.terms.apply(
                Op::Select,
                &[
                    data.clone(),
                    self.terms.bit_vector(
                        u128::from(index),
                        u32::from(self.tcx.sess.target.pointer_width),
                    )?,
                ],
            )?;
            expression = Some(match expression {
                Some(previous) => self.terms.apply(Op::Concat, &[previous, byte])?,
                None => byte,
            });
        }
        let expression = expression.ok_or("empty scalar byte encoding")?;
        Ok(Some(match scalar {
            Some((bits, signed)) => Value::Int {
                expression,
                bits,
                signed,
            },
            None => symbolic::float_from_bits(&self.terms, expression, bits),
        }))
    }
}
