use super::{Context, Op, Sort, Term, Value};

const MAX_DEPTH: usize = 16;
const MAX_NODES: usize = 512;

pub(super) fn tuple_choice(
    context: &Context,
    elements: &[Value],
    index: &Value,
) -> Result<Option<Value>, String> {
    if !matches!(elements.first(), Some(Value::Tuple(_) | Value::Unit)) {
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
        Value::Unit => Ok(true),
        Value::Bool(_) | Value::Int { .. } => {
            Err("tuple array choice primitive has an invalid width, sort or context".into())
        }
        Value::Uninitialized
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
        | Value::Elements(_)
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
    let ite =
        |a: &Term, b: &Term| context.apply(Op::Ite, &[condition.clone(), a.clone(), b.clone()]);
    match (selected, otherwise) {
        (Value::Unit, Value::Unit) => Ok(Value::Unit),
        (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => Ok(Value::Tuple(
            a.iter()
                .zip(b)
                .map(|(a, b)| merge(context, condition, a, b))
                .collect::<Result<_, _>>()?,
        )),
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
        _ => Err("tuple array choice requires exactly matching primitive tuple shapes".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{integer, select_element};

    #[test]
    fn tuple_choices_reject_forged_shapes_contexts_and_unbounded_trees() {
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
            tuple_choice(&context, std::slice::from_ref(&unsupported), &index)
                .unwrap()
                .is_none()
        );
        assert!(select_element(&context, std::slice::from_ref(&unsupported), &index).is_ok());
        assert!(select_element(&context, &[unsupported.clone(), unsupported], &index).is_err());
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
            tuple_choice(&context, &[Value::Tuple(vec![empty_adt])], &index)
                .unwrap()
                .is_none()
        );
        let selected = select_element(&context, &[good], &index).unwrap();
        assert!(matches!(selected, Value::Tuple(fields) if fields.len() == 2));
    }
}
