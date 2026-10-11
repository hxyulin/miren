//! Exact producer authority for mutable floating storage, independent of numeric equality.
use super::*;

const MAX_PAIR_DEPTH: usize = 16;

pub(super) const ENABLE_MUTABLE_FLOAT: bool = true;

#[derive(Default)]
pub(super) struct Registry {
    active: bool,
    pairs: Vec<Pair>,
    bindings: BTreeMap<u32, Term>,
    exhausted: bool,
}

struct Pair {
    expression: Term,
    raw: Term,
    bits: u32,
    depth: usize,
}

impl Registry {
    pub(super) fn activate(&mut self) {
        self.active = true;
    }

    fn depth(&self, context: &Context, value: &Value, width: u32) -> Result<usize, String> {
        if !self.active {
            return Err("mutable float producer namespace was not issued".into());
        }
        characters::validate_float_encoding(context, value, width)?;
        let Value::Float {
            expression,
            raw_bits: Some(raw),
            ..
        } = value
        else {
            return Err("mutable float requires an exact encoded pair".into());
        };
        let Value::Float {
            expression: decoded,
            ..
        } = symbolic::float_from_bits(context, raw.clone(), width)
        else {
            unreachable!("float decoding returns a float");
        };
        if *expression == decoded {
            return Ok(0);
        }
        self.pairs
            .iter()
            .find(|pair| pair.bits == width && pair.expression == *expression && pair.raw == *raw)
            .map(|pair| pair.depth)
            .ok_or_else(|| {
                if self.exhausted {
                    "mutable float producer certificate exceeds existing storage/depth budget"
                        .into()
                } else {
                    "mutable float requires exact issued producer-pair authority".into()
                }
            })
    }

    fn record(&mut self, context: &Context, value: &Value, depth: usize) {
        // Losing optional metadata must not change successful readonly producer behavior.
        // A mutable consumer still requires an exact entry and refuses missing authority.
        if depth > MAX_PAIR_DEPTH
            || self.pairs.len().saturating_add(self.bindings.len()) >= MAX_INPUT_VALUES
        {
            self.exhausted = true;
            return;
        }
        let Value::Float {
            expression,
            bits,
            raw_bits: Some(raw),
        } = value
        else {
            return;
        };
        if characters::validate_float_encoding(context, value, *bits).is_err()
            || self.pairs.iter().any(|pair| {
                pair.bits == *bits && pair.expression == *expression && pair.raw == *raw
            })
        {
            return;
        }
        self.pairs.push(Pair {
            expression: expression.clone(),
            raw: raw.clone(),
            bits: *bits,
            depth,
        });
    }

    pub(super) fn materialized(
        &mut self,
        context: &Context,
        value: &Value,
        symbol: u32,
        binding: &Term,
    ) {
        // Called exclusively by the actual fresh-symbol materialization issuer.
        if !self.active {
            return;
        }
        if self
            .pairs
            .len()
            .saturating_add(self.bindings.len())
            .saturating_add(2)
            > MAX_INPUT_VALUES
        {
            self.exhausted = true;
            return;
        }
        let Value::Float {
            expression,
            bits,
            raw_bits: Some(raw),
        } = value
        else {
            return;
        };
        if raw.symbol_index() != Some(symbol)
            || characters::validate_float_encoding(context, value, *bits).is_err()
        {
            return;
        }
        let Value::Float {
            expression: decoded,
            ..
        } = symbolic::float_from_bits(context, raw.clone(), *bits)
        else {
            unreachable!("float decoding returns a float")
        };
        let Ok(expected) = context.apply(Op::Equal, &[decoded, expression.clone()]) else {
            return;
        };
        if expected != *binding {
            return;
        }
        self.record(context, value, 0);
        self.bindings.insert(symbol, binding.clone());
    }

    pub(super) fn selected(
        &mut self,
        context: &Context,
        condition: &Term,
        left: &Value,
        right: &Value,
    ) -> Option<Value> {
        if !self.active {
            return None;
        }
        let Value::Float {
            expression: a,
            bits,
            raw_bits: Some(raw_a),
        } = left
        else {
            return None;
        };
        let Value::Float {
            expression: b,
            bits: other,
            raw_bits: Some(raw_b),
        } = right
        else {
            return None;
        };
        if bits != other || condition.sort() != &Sort::Bool || !condition.belongs_to(context) {
            return None;
        }
        let depth = self
            .depth(context, left, *bits)
            .ok()?
            .max(self.depth(context, right, *bits).ok()?)
            .saturating_add(1);
        let result = Value::Float {
            expression: context
                .apply(Op::Ite, &[condition.clone(), a.clone(), b.clone()])
                .ok()?,
            bits: *bits,
            raw_bits: Some(
                context
                    .apply(Op::Ite, &[condition.clone(), raw_a.clone(), raw_b.clone()])
                    .ok()?,
            ),
        };
        self.record(context, &result, depth);
        Some(result)
    }

    pub(super) fn negated(&mut self, context: &Context, input: &Value, result: &Value) {
        if !self.active {
            return;
        }
        let Value::Float { bits, .. } = input else {
            return;
        };
        let Ok(depth) = self.depth(context, input, *bits) else {
            return;
        };
        let Ok(expected) = symbolic::float_negate(context, input.clone()) else {
            return;
        };
        if same_pair(&expected, result) {
            self.record(context, result, depth.saturating_add(1));
        }
    }

    pub(super) fn absolute(&mut self, context: &Context, input: &Value, result: &Value) {
        if !self.active {
            return;
        }
        let Value::Float {
            expression,
            bits,
            raw_bits: Some(raw),
        } = input
        else {
            return;
        };
        let Ok(depth) = self.depth(context, input, *bits) else {
            return;
        };
        let expected = (|| -> Result<Value, String> {
            Ok(Value::Float {
                expression: context.apply(Op::FpAbs, std::slice::from_ref(expression))?,
                bits: *bits,
                raw_bits: Some(context.apply(
                    Op::BvAnd,
                    &[
                        raw.clone(),
                        context.bit_vector((1_u128 << (bits - 1)) - 1, *bits)?,
                    ],
                )?),
            })
        })();
        if expected
            .as_ref()
            .is_ok_and(|expected| same_pair(expected, result))
        {
            self.record(context, result, depth.saturating_add(1));
        }
    }
}

fn same_pair(left: &Value, right: &Value) -> bool {
    matches!((left, right), (
        Value::Float { expression: a, bits, raw_bits: Some(raw) },
        Value::Float { expression: b, bits: other, raw_bits: Some(other_raw) }
    ) if bits == other && a == b && raw == other_raw)
}

fn float_decoding_relation(
    context: &Context,
    expression: &Term,
    raw: &Term,
    width: u32,
) -> Result<Term, String> {
    let (exponent, significand) = match width {
        32 => (8, 24),
        64 => (11, 53),
        _ => return Err("float decoding relation requires an exact primitive float width".into()),
    };
    if expression.sort()
        != &(Sort::Float {
            exponent,
            significand,
        })
        || !expression.belongs_to(context)
        || raw.sort() != &Sort::BitVec(width)
        || !raw.belongs_to(context)
    {
        return Err("float decoding relation has inconsistent numeric/storage metadata".into());
    }
    let Value::Float {
        expression: decoded,
        ..
    } = symbolic::float_from_bits(context, raw.clone(), width)
    else {
        unreachable!("float decoding returns a float")
    };
    context.apply(Op::Equal, &[decoded, expression.clone()])
}

impl<'tcx> Engine<'tcx> {
    fn checked_float_decoding_relation(
        &self,
        expression: &Term,
        raw: &Term,
        width: u32,
    ) -> Result<Term, String> {
        float_decoding_relation(&self.terms, expression, raw, width)
    }

    pub(super) fn validate_float_pair(&self, value: &Value, width: u32) -> Result<(), String> {
        if self
            .float_pairs
            .bindings
            .iter()
            .any(|(symbol, binding)| self.float_encodings.get(symbol) != Some(binding))
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "mutable float producer binding changed or is unavailable".into(),
            ));
        }
        self.float_pairs
            .depth(&self.terms, value, width)
            .map(|_| ())
            .map_err(|detail| {
                let category = if detail
                    == "mutable float producer certificate exceeds existing storage/depth budget"
                {
                    UnknownCategory::ResourceLimit
                } else {
                    UnknownCategory::Semantics
                };
                self.categorized_error(category, detail)
            })
    }

    pub(super) fn prove_float_pair(
        &self,
        value: &Value,
        width: u32,
        conditions: &[Term],
    ) -> Result<(), String> {
        self.validate_float_pair(value, width)?;
        let Value::Float {
            expression,
            raw_bits: Some(raw),
            ..
        } = value
        else {
            return Err("mutable float requires tracked raw encoding".into());
        };
        let equal = self.checked_float_decoding_relation(expression, raw, width)?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&equal));
        if self.feasible(&invalid)? {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "mutable float requires proven numeric/storage correspondence".into(),
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_decoding_relation_preserves_nan_payloads_and_signed_zero() {
        for (width, encodings) in [
            (32, [0, 0x80000000, 0x7fc00017, 0x7fc00018]),
            (
                64,
                [
                    0,
                    0x8000000000000000,
                    0x7ff8000000000017,
                    0x7ff8000000000018,
                ],
            ),
        ] {
            let context = Context::default();
            for encoding in encodings {
                let raw = context.bit_vector(encoding, width).unwrap();
                let Value::Float { expression, .. } =
                    symbolic::float_from_bits(&context, raw.clone(), width)
                else {
                    unreachable!()
                };
                let expected = context
                    .apply(Op::Equal, &[expression.clone(), expression.clone()])
                    .unwrap();
                assert_eq!(
                    float_decoding_relation(&context, &expression, &raw, width).unwrap(),
                    expected
                );
                let numeric = context.symbol(99, expression.sort().clone()).unwrap();
                let expected = context
                    .apply(Op::Equal, &[expression.clone(), numeric.clone()])
                    .unwrap();
                assert_eq!(
                    float_decoding_relation(&context, &numeric, &raw, width).unwrap(),
                    expected
                );
            }
        }
    }

    #[test]
    fn checked_decoding_relation_refuses_metadata_before_allocating_terms() {
        let context = Context::default();
        let foreign = Context::default();
        let raw = context.symbol(0, Sort::BitVec(32)).unwrap();
        let wrong_raw = context.symbol(1, Sort::BitVec(64)).unwrap();
        let boolean = context.symbol(2, Sort::Bool).unwrap();
        let Value::Float { expression, .. } = symbolic::float_from_bits(&context, raw.clone(), 32)
        else {
            unreachable!()
        };
        let foreign_raw = foreign.symbol(0, Sort::BitVec(32)).unwrap();
        let foreign_numeric = foreign.symbol(1, expression.sort().clone()).unwrap();
        let marker = context.symbol(3, Sort::Bool).unwrap();
        for (numeric, storage, width) in [
            (&expression, &raw, 16),
            (&expression, &raw, 64),
            (&expression, &wrong_raw, 32),
            (&boolean, &raw, 32),
            (&expression, &boolean, 32),
            (&foreign_numeric, &raw, 32),
            (&expression, &foreign_raw, 32),
        ] {
            assert!(float_decoding_relation(&context, numeric, storage, width).is_err());
        }
        assert_eq!(context.symbol(4, Sort::Bool).unwrap().id(), marker.id() + 1);
    }

    #[test]
    fn readonly_namespace_metadata_does_not_allocate_context_nodes() {
        fn next_id(observe: bool) -> usize {
            let context = Context::default();
            let mut registry = Registry::default();
            let raw = context.symbol(0, Sort::BitVec(32)).unwrap();
            let value = symbolic::float_from_bits(&context, raw.clone(), 32);
            let negated = symbolic::float_negate(&context, value.clone()).unwrap();
            let Value::Float {
                expression,
                raw_bits: Some(raw),
                ..
            } = &negated
            else {
                unreachable!()
            };
            let absolute = Value::Float {
                expression: context
                    .apply(Op::FpAbs, std::slice::from_ref(expression))
                    .unwrap(),
                bits: 32,
                raw_bits: Some(
                    context
                        .apply(
                            Op::BvAnd,
                            &[raw.clone(), context.bit_vector(0x7fffffff, 32).unwrap()],
                        )
                        .unwrap(),
                ),
            };
            let condition = context.symbol(1, Sort::Bool).unwrap();
            if observe {
                registry.negated(&context, &value, &negated);
                registry.absolute(&context, &negated, &absolute);
                assert!(
                    registry
                        .selected(&context, &condition, &value, &absolute)
                        .is_none()
                );
                registry.materialized(&context, &value, 0, &condition);
                assert!(registry.depth(&context, &negated, 32).is_err());
                assert!(registry.pairs.is_empty() && registry.bindings.is_empty());
            }
            context.apply(Op::Not, &[condition]).unwrap().id()
        }
        assert_eq!(next_id(false), next_id(true));
    }

    #[test]
    fn copied_nan_payloads_require_the_exact_decoded_pair() {
        let context = Context::default();
        let mut registry = Registry::default();
        registry.activate();
        let original =
            symbolic::float_from_bits(&context, context.bit_vector(0x7fc00017, 32).unwrap(), 32);
        assert_eq!(registry.depth(&context, &original, 32).unwrap(), 0);
        let mut forged = original.clone();
        if let Value::Float { raw_bits, .. } = &mut forged {
            *raw_bits = Some(context.bit_vector(0x7fc00018, 32).unwrap());
        }
        assert!(registry.depth(&context, &forged, 32).is_err());
        let negated = symbolic::float_negate(&context, original.clone()).unwrap();
        assert!(registry.depth(&context, &negated, 32).is_err());
        registry.negated(&context, &original, &negated);
        assert_eq!(registry.depth(&context, &negated, 32).unwrap(), 1);
        registry.negated(&context, &forged, &negated);
        assert_eq!(registry.pairs.len(), 1);
        let condition = context.symbol(0, Sort::Bool).unwrap();
        let choice = registry
            .selected(&context, &condition, &original, &negated)
            .unwrap();
        assert_eq!(registry.depth(&context, &choice, 32).unwrap(), 2);
        let mut swapped = choice.clone();
        if let Value::Float { raw_bits, .. } = &mut swapped {
            let Value::Float {
                raw_bits: Some(a), ..
            } = &original
            else {
                unreachable!()
            };
            let Value::Float {
                raw_bits: Some(b), ..
            } = &negated
            else {
                unreachable!()
            };
            *raw_bits = Some(
                context
                    .apply(Op::Ite, &[condition, b.clone(), a.clone()])
                    .unwrap(),
            );
        }
        assert!(registry.depth(&context, &swapped, 32).is_err());
        let foreign = Context::default();
        assert!(registry.depth(&foreign, &original, 32).is_err());
        assert!(registry.depth(&context, &original, 64).is_err());
    }

    #[test]
    fn issuer_metadata_is_bounded_without_changing_readonly_values() {
        let context = Context::default();
        let mut registry = Registry::default();
        registry.activate();
        let original =
            symbolic::float_from_bits(&context, context.symbol(0, Sort::BitVec(32)).unwrap(), 32);
        let mut current = original.clone();
        for depth in 1..=MAX_PAIR_DEPTH {
            let result = symbolic::float_negate(&context, current.clone()).unwrap();
            registry.negated(&context, &current, &result);
            assert!(registry.depth(&context, &result, 32).unwrap() <= depth);
            current = result;
        }
        let beyond_depth = symbolic::float_negate(&context, current.clone()).unwrap();
        registry.negated(&context, &current, &beyond_depth);
        assert!(
            registry
                .depth(&context, &beyond_depth, 32)
                .unwrap_err()
                .contains("exceeds existing storage/depth budget")
        );
        assert_eq!(registry.depth(&context, &original, 32).unwrap(), 0);
        // Unique numeric arithmetic pairs fill the optional metadata capacity; none are
        // registered by shape, and extra readonly materializations remain ordinary values.
        let Value::Float {
            expression: numeric,
            ..
        } = symbolic::binary(&context, "add", original.clone(), original.clone()).unwrap()
        else {
            unreachable!()
        };
        for i in 0..MAX_INPUT_VALUES {
            let raw = context.symbol((i + 1) as u32, Sort::BitVec(32)).unwrap();
            let value = Value::Float {
                expression: numeric.clone(),
                bits: 32,
                raw_bits: Some(raw),
            };
            let Value::Float {
                expression,
                raw_bits: Some(raw),
                ..
            } = &value
            else {
                unreachable!()
            };
            let Value::Float {
                expression: decoded,
                ..
            } = symbolic::float_from_bits(&context, raw.clone(), 32)
            else {
                unreachable!()
            };
            let binding = context
                .apply(Op::Equal, &[decoded, expression.clone()])
                .unwrap();
            registry.materialized(&context, &value, (i + 1) as u32, &binding);
        }
        assert!(!registry.pairs.is_empty());
        assert!(registry.pairs.len().saturating_add(registry.bindings.len()) <= MAX_INPUT_VALUES);
        assert!(!registry.bindings.is_empty());
        let extra_raw = context.symbol(900, Sort::BitVec(32)).unwrap();
        let Value::Float {
            expression: decoded,
            ..
        } = symbolic::float_from_bits(&context, extra_raw.clone(), 32)
        else {
            unreachable!()
        };
        let extra = Value::Float {
            expression: numeric,
            bits: 32,
            raw_bits: Some(extra_raw.clone()),
        };
        let Value::Float { expression, .. } = &extra else {
            unreachable!()
        };
        let binding = context
            .apply(Op::Equal, &[decoded, expression.clone()])
            .unwrap();
        registry.materialized(&context, &extra, 900, &binding);
        assert!(
            registry
                .depth(&context, &extra, 32)
                .unwrap_err()
                .contains("exceeds existing storage/depth budget")
        );
        assert_eq!(registry.depth(&context, &original, 32).unwrap(), 0);
    }
}
