use super::{Context, Op, Sort, Term, Value};

const MAX_DEPTH: usize = 16;
const MAX_NODES: usize = 512;

pub(super) fn aggregate_choice(
    context: &Context,
    elements: &[Value],
    index: &Value,
) -> Result<Option<Value>, String> {
    if !matches!(
        elements.first(),
        Some(Value::Tuple(_) | Value::Elements(_) | Value::Unit)
    ) {
        return Ok(None);
    }
    let (index, bits, signed) = index.integer()?;
    if signed || index.sort() != &Sort::BitVec(bits) || !index.belongs_to(context) {
        return Err("tuple array choice requires an unsigned index in its context".into());
    }
    if bits < usize::BITS && elements.len() > (1_usize << bits) {
        return Err("tuple array choice exceeds the index capacity".into());
    }
    let mut nodes = 0;
    let mut pure = true;
    for value in elements {
        pure &= validate(context, value, 0, &mut nodes)?;
    }
    if !pure {
        // Leave existing unique/singleton handle selection to the ordinary selector. This
        // domain never synthesizes conditional reference or other identity-bearing values.
        return Ok(None);
    }
    let mut result = elements.last().cloned().ok_or("empty tuple array choice")?;
    for (position, value) in elements.iter().enumerate().rev().skip(1) {
        let condition = context.apply(
            Op::Equal,
            &[index.clone(), context.bit_vector(position as u128, bits)?],
        )?;
        result = merge(context, &condition, value, &result)?;
    }
    Ok(Some(result))
}

fn validate(
    context: &Context,
    value: &Value,
    depth: usize,
    nodes: &mut usize,
) -> Result<bool, String> {
    *nodes += 1;
    if depth > MAX_DEPTH || *nodes > MAX_NODES {
        return Err("tuple array choice exceeds its depth or node budget".into());
    }
    let valid = |term: &Term, sort: Sort| term.belongs_to(context) && term.sort() == &sort;
    match value {
        Value::OwnedRegion { .. } | Value::OwnedSnapshot(_) => {
            Err("owned regions require their private typed protocol".into())
        }
        Value::Bool(term) if valid(term, Sort::Bool) => Ok(true),
        Value::Int {
            expression, bits, ..
        } if matches!(*bits, 8 | 16 | 32 | 64 | 128) && valid(expression, Sort::BitVec(*bits)) => {
            Ok(true)
        }
        Value::Float {
            expression,
            bits,
            raw_bits,
        } => {
            let sort = match bits {
                32 => Sort::Float {
                    exponent: 8,
                    significand: 24,
                },
                64 => Sort::Float {
                    exponent: 11,
                    significand: 53,
                },
                _ => return Err("tuple array choice has an unsupported float width".into()),
            };
            if !valid(expression, sort)
                || raw_bits
                    .as_ref()
                    .is_some_and(|raw| !valid(raw, Sort::BitVec(*bits)))
            {
                return Err("tuple array choice float has an invalid sort or context".into());
            }
            Ok(true)
        }
        Value::Tuple(fields) => {
            let mut pure = true;
            for field in fields {
                pure &= validate(context, field, depth + 1, nodes)?;
            }
            Ok(pure)
        }
        Value::Elements(elements) => {
            let mut pure = true;
            for element in elements.iter() {
                pure &= validate(context, element, depth + 1, nodes)?;
            }
            Ok(pure)
        }
        Value::Unit => Ok(true),
        Value::Bool(_) | Value::Int { .. } => {
            Err("tuple array choice primitive has an invalid width, sort or context".into())
        }
        Value::Uninitialized
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::RawPointer { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Input(_)
        | Value::Bytes { .. }
        | Value::Adt { .. }
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function => Ok(false),
    }
}

fn merge(
    context: &Context,
    condition: &Term,
    selected: &Value,
    otherwise: &Value,
) -> Result<Value, String> {
    match (selected, otherwise) {
        (Value::Unit, Value::Unit) => Ok(Value::Unit),
        (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => Ok(Value::Tuple(
            a.iter()
                .zip(b)
                .map(|(a, b)| merge(context, condition, a, b))
                .collect::<Result<_, _>>()?,
        )),
        (Value::Elements(a), Value::Elements(b)) if a.len() == b.len() => Ok(Value::Elements(
            a.iter()
                .zip(b.iter())
                .map(|(a, b)| merge(context, condition, a, b))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        )),
        _ => scalar_conditional(context, condition, selected, otherwise),
    }
}

pub(super) fn scalar_conditional(
    context: &Context,
    condition: &Term,
    selected: &Value,
    otherwise: &Value,
) -> Result<Value, String> {
    for value in [selected, otherwise] {
        if !matches!(
            value,
            Value::Bool(_) | Value::Int { .. } | Value::Float { .. }
        ) || !validate(context, value, 0, &mut 0)?
        {
            return Err("conditional scalar requires certified primitive values".into());
        }
    }
    let ite =
        |a: &Term, b: &Term| context.apply(Op::Ite, &[condition.clone(), a.clone(), b.clone()]);
    match (selected, otherwise) {
        (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(ite(a, b)?)),
        (
            Value::Int {
                expression: a,
                bits,
                signed,
            },
            Value::Int {
                expression: b,
                bits: b_bits,
                signed: b_signed,
            },
        ) if bits == b_bits && signed == b_signed => Ok(Value::Int {
            expression: ite(a, b)?,
            bits: *bits,
            signed: *signed,
        }),
        (
            Value::Float {
                expression: a,
                bits,
                raw_bits,
            },
            Value::Float {
                expression: b,
                bits: b_bits,
                raw_bits: b_raw,
            },
        ) if bits == b_bits => Ok(Value::Float {
            expression: ite(a, b)?,
            bits: *bits,
            raw_bits: raw_bits
                .as_ref()
                .zip(b_raw.as_ref())
                .map(|(a, b)| ite(a, b))
                .transpose()?,
        }),
        _ => Err(
            "tuple array choice requires exactly matching primitive tuple or fixed-array shapes"
                .into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{integer, select_element};

    #[test]
    fn shared_scalar_conditionals_preserve_selection_terms_and_float_certificates() {
        let context = Context::default();
        let foreign = Context::default();
        let condition = context.symbol(801, Sort::Bool).unwrap();
        let old = integer(&context, 3, 16, false);
        let selected = integer(&context, 9, 16, false);
        let result = scalar_conditional(&context, &condition, &selected, &old).unwrap();
        assert_eq!(
            result.integer().unwrap().0,
            context
                .apply(
                    Op::Ite,
                    &[
                        condition.clone(),
                        selected.integer().unwrap().0,
                        old.integer().unwrap().0
                    ],
                )
                .unwrap()
        );
        assert!(
            scalar_conditional(
                &context,
                &condition,
                &selected,
                &integer(&context, 3, 16, true)
            )
            .is_err()
        );
        assert!(scalar_conditional(&context, &foreign.boolean(true), &selected, &old).is_err());
        assert!(
            scalar_conditional(
                &context,
                &context.bit_vector(1, 8).unwrap(),
                &selected,
                &old
            )
            .is_err()
        );
        assert!(scalar_conditional(&context, &condition, &Value::Unit, &Value::Unit).is_err());
        let selected = crate::symbolic::float(&context, 0x80000000, 32);
        let old = crate::symbolic::float(&context, 0x7fc00001, 32);
        assert!(matches!(
            scalar_conditional(&context, &condition, &selected, &old).unwrap(),
            Value::Float {
                raw_bits: Some(_),
                ..
            }
        ));
        let Value::Float {
            expression, bits, ..
        } = old
        else {
            panic!("float fixture");
        };
        let old = Value::Float {
            expression,
            bits,
            raw_bits: None,
        };
        assert!(matches!(
            scalar_conditional(&context, &condition, &selected, &old).unwrap(),
            Value::Float { raw_bits: None, .. }
        ));
    }

    #[test]
    fn nested_array_choices_preserve_carriers_correlations_and_identity_fallback() {
        let context = Context::default();
        let foreign = Context::default();
        let index = Value::Int {
            expression: context.symbol(901, Sort::BitVec(8)).unwrap(),
            bits: 8,
            signed: false,
        };
        let array = |values: Vec<Value>| Value::Elements(values.into());
        let a = array(vec![
            integer(&context, 3, 16, false),
            Value::Tuple(vec![crate::symbolic::float(&context, 0x80000000, 32)]),
        ]);
        let b = array(vec![
            integer(&context, 7, 16, false),
            Value::Tuple(vec![crate::symbolic::float(&context, 0x7fc00015, 32)]),
        ]);
        let selected = select_element(&context, &[a.clone(), b.clone()], &index).unwrap();
        let Value::Elements(values) = selected else {
            panic!("selected array must retain its carrier");
        };
        let condition = context
            .apply(
                Op::Equal,
                &[
                    index.integer().unwrap().0,
                    context.bit_vector(0, 8).unwrap(),
                ],
            )
            .unwrap();
        assert_eq!(
            values[0].integer().unwrap().0,
            context
                .apply(
                    Op::Ite,
                    &[
                        condition.clone(),
                        context.bit_vector(3, 16).unwrap(),
                        context.bit_vector(7, 16).unwrap(),
                    ]
                )
                .unwrap()
        );
        let Value::Tuple(fields) = &values[1] else {
            panic!("nested tuple carrier");
        };
        let Value::Float {
            raw_bits: Some(raw),
            ..
        } = &fields[0]
        else {
            panic!("selected float must retain certified bits");
        };
        assert_eq!(
            *raw,
            context
                .apply(
                    Op::Ite,
                    &[
                        condition,
                        context.bit_vector(0x80000000, 32).unwrap(),
                        context.bit_vector(0x7fc00015, 32).unwrap(),
                    ]
                )
                .unwrap()
        );
        assert!(select_element(&context, &[a.clone(), array(vec![])], &index).is_err());
        assert!(select_element(&context, &[a.clone(), Value::Tuple(vec![])], &index).is_err());
        assert!(
            select_element(
                &context,
                &[array(vec![integer(&foreign, 3, 16, false)])],
                &index
            )
            .is_err()
        );
        assert!(
            matches!(select_element(&context, &[array(vec![]), array(vec![])], &index),
            Ok(Value::Elements(values)) if values.is_empty())
        );
        let handle = array(vec![Value::Reference {
            allocation: 0,
            projection: vec![],
            mutable: false,
        }]);
        assert!(
            aggregate_choice(&context, std::slice::from_ref(&handle), &index)
                .unwrap()
                .is_none()
        );
        assert!(select_element(&context, std::slice::from_ref(&handle), &index).is_ok());
        assert!(select_element(&context, &[handle.clone(), handle.clone()], &index).is_err());
        let malformed = array(vec![handle, integer(&foreign, 1, 16, false)]);
        assert!(aggregate_choice(&context, &[malformed], &index).is_err());
        assert!(select_element(&context, &[array(vec![Value::Unit; MAX_NODES])], &index).is_err());
        let mut deep = Value::Unit;
        for _ in 0..=MAX_DEPTH {
            deep = array(vec![deep]);
        }
        assert!(select_element(&context, &[deep], &index).is_err());
        // One absent raw-bit certificate prevents inventing one for the merged result.
        let mut no_raw = crate::symbolic::float(&context, 0, 32);
        if let Value::Float { raw_bits, .. } = &mut no_raw {
            *raw_bits = None;
        }
        let selected = select_element(
            &context,
            &[
                array(vec![no_raw]),
                array(vec![crate::symbolic::float(&context, 1, 32)]),
            ],
            &index,
        )
        .unwrap();
        assert!(matches!(selected, Value::Elements(values)
            if matches!(&values[0], Value::Float { raw_bits: None, .. })));
    }

    #[test]
    fn aggregate_choices_reject_forged_shapes_contexts_and_unbounded_trees() {
        let context = Context::default();
        let foreign = Context::default();
        let index = integer(&context, 0, 8, false);
        let good = Value::Tuple(vec![integer(&context, 3, 16, false), Value::Unit]);
        let wrong_sign = Value::Tuple(vec![integer(&context, 3, 16, true), Value::Unit]);
        assert!(select_element(&context, &[good.clone(), wrong_sign], &index).is_err());
        let wrong_shape = Value::Tuple(vec![integer(&context, 3, 16, false)]);
        assert!(select_element(&context, &[good.clone(), wrong_shape], &index).is_err());
        let wrong_context = Value::Tuple(vec![integer(&foreign, 3, 16, false), Value::Unit]);
        assert!(select_element(&context, &[wrong_context], &index).is_err());
        let forged_width = Value::Tuple(vec![Value::Int {
            expression: context.bit_vector(3, 8).unwrap(),
            bits: 16,
            signed: false,
        }]);
        assert!(select_element(&context, &[forged_width], &index).is_err());
        let foreign_index = integer(&foreign, 0, 8, false);
        assert!(select_element(&context, std::slice::from_ref(&good), &foreign_index).is_err());
        assert!(
            select_element(
                &context,
                std::slice::from_ref(&good),
                &integer(&context, 0, 8, true)
            )
            .is_err()
        );
        assert!(select_element(&context, &vec![good.clone(); 257], &index).is_err());
        let oversized = Value::Tuple(vec![Value::Unit; MAX_NODES]);
        assert!(select_element(&context, &[oversized], &index).is_err());
        let mut deep = Value::Unit;
        for _ in 0..=MAX_DEPTH {
            deep = Value::Tuple(vec![deep]);
        }
        assert!(select_element(&context, &[deep], &index).is_err());
        let unsupported = Value::Tuple(vec![Value::Reference {
            allocation: 0,
            projection: vec![],
            mutable: false,
        }]);
        assert!(
            aggregate_choice(&context, std::slice::from_ref(&unsupported), &index)
                .unwrap()
                .is_none()
        );
        assert!(select_element(&context, std::slice::from_ref(&unsupported), &index).is_ok());
        assert!(select_element(&context, &[unsupported.clone(), unsupported], &index).is_err());
        let uninitialized = Value::Tuple(vec![Value::MaybeUninit {
            id: 0,
            payload: None,
        }]);
        let initialized = Value::Tuple(vec![Value::MaybeUninit {
            id: 0,
            payload: Some(Box::new(integer(&context, 7, 16, false))),
        }]);
        assert!(
            aggregate_choice(&context, std::slice::from_ref(&initialized), &index)
                .unwrap()
                .is_none()
        );
        assert!(select_element(&context, &[uninitialized, initialized], &index).is_err());
        let mut float = crate::symbolic::float(&context, 0x80000000, 32);
        if let Value::Float { raw_bits, .. } = &mut float {
            *raw_bits = Some(context.bit_vector(0, 64).unwrap());
        }
        assert!(select_element(&context, &[Value::Tuple(vec![float])], &index).is_err());
        let mut float = crate::symbolic::float(&context, 0x80000000, 32);
        if let Value::Float { raw_bits, .. } = &mut float {
            *raw_bits = Some(foreign.bit_vector(0, 32).unwrap());
        }
        assert!(select_element(&context, &[Value::Tuple(vec![float])], &index).is_err());
        let float = crate::symbolic::float(&foreign, 0x80000000, 32);
        assert!(select_element(&context, &[Value::Tuple(vec![float])], &index).is_err());
        let empty_adt = Value::Adt {
            name: "DropZst".into(),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![].into(),
        };
        assert!(
            aggregate_choice(&context, &[Value::Tuple(vec![empty_adt])], &index)
                .unwrap()
                .is_none()
        );
        let selected = select_element(&context, &[good], &index).unwrap();
        assert!(matches!(selected, Value::Tuple(fields) if fields.len() == 2));
    }
}
