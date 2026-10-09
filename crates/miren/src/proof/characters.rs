use super::*;

pub(super) fn unicode_scalar(context: &Context, value: &Term) -> Result<Term, String> {
    if value.sort() != &Sort::BitVec(32) || !value.belongs_to(context) {
        return Err("char representation requires an unsigned 32-bit term in its context".into());
    }
    let within = context.apply(
        Op::BvUnsignedLe,
        &[value.clone(), context.bit_vector(0x10ffff, 32)?],
    )?;
    let below = context.apply(
        Op::BvUnsignedLt,
        &[value.clone(), context.bit_vector(0xd800, 32)?],
    )?;
    let above = context.apply(
        Op::BvUnsignedGt,
        &[value.clone(), context.bit_vector(0xdfff, 32)?],
    )?;
    context.apply(Op::And, &[within, context.apply(Op::Or, &[below, above])?])
}

pub(super) fn valid_char_observation(context: &Context, raw: &Term) -> Result<Term, String> {
    // Identity on every Unicode scalar, mapping every invalid encoding to a valid scalar.
    // This covers all valid char observations without restoring an initializer/history.
    context.apply(
        Op::Ite,
        &[
            unicode_scalar(context, raw)?,
            raw.clone(),
            context.bit_vector(0, 32)?,
        ],
    )
}

pub(super) fn validate_float_encoding(
    context: &Context,
    value: &Value,
    width: u32,
) -> Result<(), String> {
    let Value::Float {
        expression,
        bits,
        raw_bits,
    } = value
    else {
        return Err("scalar bit formation requires a compiler float value".into());
    };
    let (exponent, significand) = match width {
        32 => (8, 24),
        64 => (11, 53),
        _ => return Err("scalar bit formation requires an exact primitive float width".into()),
    };
    if *bits != width
        || expression.sort()
            != &(Sort::Float {
                exponent,
                significand,
            })
        || !expression.belongs_to(context)
    {
        return Err("scalar bit formation has inconsistent float metadata".into());
    }
    let raw = raw_bits
        .as_ref()
        .ok_or("float result has no tracked storage encoding")?;
    if raw.sort() != &Sort::BitVec(width) || !raw.belongs_to(context) {
        return Err("scalar bit formation has inconsistent float storage encoding".into());
    }
    Ok(())
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn restricted_scalar_target(&self, target: Ty<'tcx>) -> bool {
        let mut base = target;
        for _ in 0..16 {
            match base.kind() {
                ty::Pat(inner, _) => base = *inner,
                ty::Char => return true,
                ty::Int(_) | ty::Uint(_) => return base != target,
                _ => return false,
            }
        }
        matches!(base.kind(), ty::Pat(..))
    }

    pub(super) fn prove_scalar_target(
        &self,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        self.prove_scalar_target_at(target, value, conditions, 0)
    }

    fn prove_scalar_target_at(
        &self,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
        depth: usize,
    ) -> Result<(), String> {
        if depth >= 16 {
            return Err("scalar target refinement exceeds the 16-level budget".into());
        }
        match target.kind() {
            ty::Pat(base, pattern) => {
                self.prove_scalar_target_at(*base, value, conditions, depth + 1)?;
                if self.static_layout(target)?.size != self.static_layout(*base)?.size
                    || self.static_layout(target)?.align != self.static_layout(*base)?.align
                {
                    return Err("scalar pattern changes the compiler representation".into());
                }
                let valid = self.input_pattern(*pattern, value, 0)?;
                let mut invalid = conditions.to_vec();
                invalid.push(symbolic::not(&valid));
                if self.feasible(&invalid)? {
                    return Err(self.categorized_error(
                        UnknownCategory::Semantics,
                        "scalar formation requires a proven compiler scalar pattern".into(),
                    ));
                }
                Ok(())
            }
            ty::Char => self.prove_char_value(value, conditions),
            ty::Int(_) | ty::Uint(_) => {
                let (expression, bits, signed) = value.integer()?;
                if self.integer_type(target) != Some((bits, signed))
                    || expression.sort() != &Sort::BitVec(bits)
                    || !expression.belongs_to(&self.terms)
                    || self.static_layout(target)?.size.bits() != u64::from(bits)
                {
                    return Err("scalar formation does not match its exact compiler type".into());
                }
                Ok(())
            }
            _ => Err("scalar formation requires a primitive integer or char base".into()),
        }
    }

    pub(super) fn prove_char_value(
        &self,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let (expression, bits, signed) = value.integer()?;
        let layout = self.static_layout(self.tcx.types.char)?;
        if bits != 32 || signed || layout.size.bits() != 32 {
            return Err("char value does not match the compiler scalar representation".into());
        }
        let valid = unicode_scalar(&self.terms, &expression)?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&valid));
        if self.feasible(&invalid)? {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "char formation requires a proven Unicode scalar value".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn char_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        if (source == self.tcx.types.u32 || source == self.tcx.types.i32 || source.is_char())
            && target.is_char()
        {
            if self.static_layout(source)?.size != self.static_layout(target)?.size
                || self.static_layout(source)?.align != self.static_layout(target)?.align
            {
                return Err("char transmute changes the compiler scalar layout".into());
            }
            let (expression, bits, signed) = value.integer()?;
            if bits != 32
                || signed != (source == self.tcx.types.i32)
                || expression.sort() != &Sort::BitVec(32)
                || !expression.belongs_to(&self.terms)
            {
                return Err("char transmute source does not match its exact compiler type".into());
            }
            let value = symbolic::cast(&self.terms, value.clone(), 32, false)?;
            self.prove_char_value(&value, conditions)?;
            return Ok(Some(value));
        }
        if source.is_char()
            && matches!(target.kind(), ty::Int(_) | ty::Uint(_))
            && self
                .integer_type(target)
                .is_some_and(|(bits, _)| bits == 32)
        {
            self.prove_char_value(value, conditions)?;
            let (bits, signed) = self
                .integer_type(target)
                .ok_or("char output integer type unavailable")?;
            return symbolic::cast(&self.terms, value.clone(), bits, signed).map(Some);
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn char_observations_cover_valid_scalars_without_invalid_encodings() {
        let context = Context::default();
        for value in [
            0,
            0xff,
            0xd7ff,
            0xe000,
            0x10ffff,
            0xd800,
            0xdfff,
            0x110000,
            u32::MAX,
        ] {
            let raw = context.bit_vector(u128::from(value), 32).unwrap();
            let observed = valid_char_observation(&context, &raw).unwrap();
            let valid = value <= 0x10ffff && !(0xd800..=0xdfff).contains(&value);
            assert_eq!(
                symbolic::constant(&observed),
                Some(symbolic::Constant::BitVec {
                    value: if valid { u128::from(value) } else { 0 },
                    bits: 32
                })
            );
        }
        let raw = context.symbol(0, Sort::BitVec(32)).unwrap();
        let observed = valid_char_observation(&context, &raw).unwrap();
        let unchanged = context
            .apply(Op::Equal, &[raw.clone(), observed.clone()])
            .unwrap();
        let identity = context
            .apply(
                Op::Or,
                &[
                    symbolic::not(&unicode_scalar(&context, &raw).unwrap()),
                    unchanged,
                ],
            )
            .unwrap();
        let guarantee = context
            .apply(
                Op::And,
                &[identity, unicode_scalar(&context, &observed).unwrap()],
            )
            .unwrap();
        let query = Query::new(
            &context.declarations(),
            &[],
            &symbolic::not(&guarantee).smt(200_000).unwrap(),
        );
        assert!(matches!(
            Solver::default().check_query(&query),
            Answer::Unsat
        ));
        let valid_float =
            symbolic::float_from_bits(&context, context.bit_vector(0xe000, 32).unwrap(), 32);
        assert!(validate_float_encoding(&context, &valid_float, 32).is_ok());
        let foreign = Context::default();
        let Value::Float { expression, .. } = &valid_float else {
            unreachable!()
        };
        for raw in [
            foreign.bit_vector(0xe000, 32).unwrap(),
            context.bit_vector(0xe000, 64).unwrap(),
        ] {
            let forged = Value::Float {
                expression: expression.clone(),
                bits: 32,
                raw_bits: Some(raw),
            };
            assert!(validate_float_encoding(&context, &forged, 32).is_err());
        }
        let forged = Value::Float {
            expression: context.symbol(1, Sort::BitVec(32)).unwrap(),
            bits: 32,
            raw_bits: Some(context.bit_vector(0xe000, 32).unwrap()),
        };
        assert!(validate_float_encoding(&context, &forged, 32).is_err());

        assert!(valid_char_observation(&context, &foreign.bit_vector(3, 32).unwrap()).is_err());
        assert!(valid_char_observation(&context, &context.bit_vector(3, 64).unwrap()).is_err());
    }
}
