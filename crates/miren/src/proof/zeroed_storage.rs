use super::*;
use rustc_span::Symbol;

const MAX_ZERO_DEPTH: usize = 16;
const MAX_ZERO_VALUES: usize = 256;
const MAX_ZERO_ELEMENTS: u64 = 128;

impl<'tcx> Engine<'tcx> {
    pub(super) fn zeroed_storage(
        &mut self,
        instance: ty::Instance<'tcx>,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
        state: &mut State,
        location: (DefId, Span),
    ) -> Result<Option<Value>, String> {
        let callee = instance.def_id();
        if !self
            .tcx
            .is_diagnostic_item(Symbol::intern("mem_zeroed"), callee)
        {
            return Ok(None);
        }
        let payload = instance.args.type_at(0);
        if !signature.inputs().is_empty() || !values.is_empty() || signature.output() != payload {
            return Err("zeroed storage signature mismatch".into());
        }
        let valid = self
            .tcx
            .check_validity_requirement((
                rustc_middle::ty::layout::ValidityRequirement::Zero,
                ty::TypingEnv::fully_monomorphized().as_query_input(payload),
            ))
            .map_err(|error| format!("zeroed storage validity layout unavailable: {error:?}"))?;
        let safe = self.terms.boolean(valid);
        self.require(
            location.0,
            location.1,
            &state.conditions,
            &safe,
            ObligationKind::PanicSafety,
            format!("compiler zero-initialization validity guard for {payload:?}"),
        )?;
        state.conditions.push(safe);
        // The pinned core function panics before returning an invalid zeroed value. This
        // placeholder is only written into an infeasible continuation, never read by execution.
        if !valid {
            self.record_model(callee, "zeroed storage rejected by compiler validity guard");
            return Ok(Some(Value::Unit));
        }
        let mut remaining = MAX_ZERO_VALUES;
        let value = self.zeroed_payload(payload, 0, &mut remaining)?;
        self.record_model(
            callee,
            "initialized zeroed payload with checked compiler validity and closed type layout",
        );
        Ok(Some(value))
    }

    fn zeroed_payload(
        &self,
        payload: Ty<'tcx>,
        depth: usize,
        remaining: &mut usize,
    ) -> Result<Value, String> {
        if depth >= MAX_ZERO_DEPTH || *remaining == 0 {
            return Err("zeroed storage exceeds the depth or 256-value budget".into());
        }
        *remaining -= 1;
        self.static_layout(payload)?;
        match payload.kind() {
            ty::Bool => Ok(Value::Bool(self.terms.boolean(false))),
            ty::Int(_) | ty::Uint(_) | ty::Char => {
                let (bits, signed) = self
                    .integer_type(payload)
                    .ok_or("zeroed storage scalar width unavailable")?;
                Ok(symbolic::integer(&self.terms, 0, bits, signed))
            }
            ty::Float(_) => {
                let bits = self
                    .float_type(payload)
                    .ok_or("zeroed storage float width unavailable")?;
                Ok(symbolic::float_from_bits(
                    &self.terms,
                    self.terms.bit_vector(0, bits)?,
                    bits,
                ))
            }
            ty::Tuple(fields) if fields.is_empty() => Ok(Value::Unit),
            ty::Tuple(fields) => Ok(Value::Tuple(
                fields
                    .iter()
                    .map(|field| self.zeroed_payload(field, depth + 1, remaining))
                    .collect::<Result<_, _>>()?,
            )),
            ty::Array(element, length) => {
                let count = length
                    .try_to_target_usize(self.tcx)
                    .ok_or("zeroed storage array length unavailable")?;
                if *element == self.tcx.types.u8 {
                    let bits = u32::from(self.tcx.sess.target.pointer_width);
                    return Ok(Value::Bytes {
                        length: Box::new(symbolic::integer(
                            &self.terms,
                            u128::from(count),
                            bits,
                            false,
                        )),
                        data: self.terms.apply(
                            Op::ConstArray { index_bits: bits },
                            &[self.terms.bit_vector(0, 8)?],
                        )?,
                    });
                }
                if count > MAX_ZERO_ELEMENTS {
                    return Err("zeroed storage array exceeds 128 elements".into());
                }
                Ok(Value::Elements(
                    (0..count)
                        .map(|_| self.zeroed_payload(*element, depth + 1, remaining))
                        .collect::<Result<_, _>>()?,
                ))
            }
            ty::Adt(def, args) if def.is_struct() => {
                let fields = def
                    .non_enum_variant()
                    .fields
                    .iter()
                    .map(|field| {
                        let field = self
                            .tcx
                            .try_normalize_erasing_regions(
                                ty::TypingEnv::fully_monomorphized(),
                                field.ty(self.tcx, args),
                            )
                            .map_err(|error| {
                                format!("zeroed storage field normalization failed: {error:?}")
                            })?;
                        self.zeroed_payload(field, depth + 1, remaining)
                    })
                    .collect::<Result<_, _>>()?;
                self.constructed(payload, 0, fields)
            }
            ty::Adt(def, _) if def.is_enum() => {
                let layout = self.static_layout(payload)?;
                if def.variants().len() > 64
                    || def
                        .variants()
                        .iter()
                        .any(|variant| !variant.fields.is_empty())
                    || !matches!(
                        layout.variants,
                        rustc_abi::Variants::Multiple {
                            tag_encoding: rustc_abi::TagEncoding::Direct,
                            ..
                        }
                    )
                {
                    return Err("zeroed enum needs bounded fieldless direct-tag layout".into());
                }
                let mut zero_variant = None;
                for (index, _) in def.variants().iter_enumerated() {
                    if def.discriminant_for_variant(self.tcx, index).val == 0
                        && zero_variant.replace(index).is_some()
                    {
                        return Err("zeroed enum has ambiguous zero discriminant".into());
                    }
                }
                let variant = zero_variant.ok_or("zeroed enum has no zero discriminant")?;
                self.constructed(payload, variant.as_usize(), Vec::new())
            }
            // Do not infer a selected union field or an enum discriminant from layout validity.
            // MaybeUninit is a union: accepting its container never initializes its payload.
            _ => Err(format!(
                "zeroed storage payload is not modeled: {payload:?}"
            )),
        }
    }
}
