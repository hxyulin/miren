use super::*;
use rustc_span::Symbol;

impl<'tcx> Engine<'tcx> {
    pub(super) fn layout_intrinsic(
        &mut self,
        instance: ty::Instance<'tcx>,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
        state: &mut State,
        location: (DefId, Span),
    ) -> Result<Option<Value>, String> {
        let callee = instance.def_id();
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
                Value::Bytes { length, .. } => *length,
                Value::Elements(elements) | Value::StaticSlice { elements, .. } => {
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
