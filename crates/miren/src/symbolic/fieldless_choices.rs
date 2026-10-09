use super::{Context, MAX_REPEAT_VALUES, Sort, Value, select_element};
use std::collections::HashSet;

pub(super) fn fieldless_enum_choice(
    context: &Context,
    elements: &[Value],
    index: &Value,
) -> Result<Option<Value>, String> {
    if elements.is_empty() || elements.len() > MAX_REPEAT_VALUES {
        return Ok(None);
    }
    let Value::Enum {
        discriminant,
        variants,
        is_option,
    } = &elements[0]
    else {
        return Ok(None);
    };
    if variants.is_empty() || variants.len() > MAX_REPEAT_VALUES {
        return Ok(None);
    }
    let (index_expression, index_bits, _) = index.integer()?;
    if index_expression.sort() != &Sort::BitVec(index_bits) || !index_expression.belongs_to(context)
    {
        return Err("fieldless enum choice index requires its declared context and width".into());
    }
    if index_bits < usize::BITS && elements.len() > (1_usize << index_bits) {
        return Ok(None);
    }
    let (_, bits, signed) = discriminant.integer()?;
    if !(1..=128).contains(&bits) {
        return Err("fieldless enum choice discriminants exceed their represented width".into());
    }
    let mask = u128::MAX >> (128 - bits);
    let mut represented_tags = HashSet::new();
    let Some((name, _, _, _)) = fieldless_variant(&variants[0]) else {
        return Ok(None);
    };
    for (position, variant) in variants.iter().enumerate() {
        let Some((variant_name, number, option, tag)) = fieldless_variant(variant) else {
            return Ok(None);
        };
        if variant_name != name || number != position || option != *is_option {
            return Ok(None);
        }
        if !represented_tags.insert(tag & mask) {
            return Ok(None);
        }
    }
    let mut choices = Vec::with_capacity(elements.len());
    for element in elements {
        let Value::Enum {
            discriminant: choice,
            variants: choice_variants,
            is_option: choice_option,
        } = element
        else {
            return Ok(None);
        };
        let (expression, choice_bits, choice_signed) = choice.integer()?;
        if expression.sort() != &Sort::BitVec(choice_bits) || !expression.belongs_to(context) {
            return Err("fieldless enum choice requires its declared context and width".into());
        }
        if choice_bits != bits
            || choice_signed != signed
            || choice_option != is_option
            || choice_variants.len() != variants.len()
            || choice_variants.iter().zip(variants).any(|(left, right)| {
                fieldless_variant(left).is_none()
                    || fieldless_variant(left) != fieldless_variant(right)
            })
        {
            return Ok(None);
        }
        choices.push((**choice).clone());
    }
    Ok(Some(Value::Enum {
        discriminant: Box::new(select_element(context, &choices, index)?),
        variants: variants.clone(),
        is_option: *is_option,
    }))
}

fn fieldless_variant(value: &Value) -> Option<(&str, usize, bool, u128)> {
    if let Value::Adt {
        name,
        variant,
        is_option,
        discriminant,
        fields,
    } = value
        && fields.is_empty()
    {
        return Some((name, *variant, *is_option, *discriminant));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{AdtFields, integer};

    fn variant(name: &str, number: usize, tag: u128) -> Value {
        Value::Adt {
            name: name.into(),
            variant: number,
            discriminant: tag,
            is_option: false,
            fields: AdtFields::default(),
        }
    }

    fn choice(context: &Context, symbol: u32) -> Value {
        Value::Enum {
            discriminant: Box::new(Value::Int {
                expression: context.symbol(symbol, Sort::BitVec(8)).unwrap(),
                bits: 8,
                signed: true,
            }),
            variants: vec![variant("Press", 0, u128::MAX), variant("Press", 1, 7)],
            is_option: false,
        }
    }

    #[test]
    fn fieldless_choices_preserve_signed_metadata_and_every_variant() {
        let context = Context::default();
        let values = [choice(&context, 0), choice(&context, 1)];
        let index = Value::Int {
            expression: context.symbol(2, Sort::BitVec(32)).unwrap(),
            bits: 32,
            signed: false,
        };
        let result = fieldless_enum_choice(&context, &values, &index)
            .unwrap()
            .unwrap();
        let Value::Enum {
            discriminant,
            variants,
            is_option,
        } = result
        else {
            panic!("expected retained enum choice");
        };
        assert!(!is_option);
        assert_eq!(discriminant.integer().unwrap().1, 8);
        assert!(discriminant.integer().unwrap().2);
        assert_eq!(
            fieldless_variant(&variants[0]),
            Some(("Press", 0, false, u128::MAX))
        );
        assert_eq!(
            fieldless_variant(&variants[1]),
            Some(("Press", 1, false, 7))
        );
    }

    #[test]
    fn incompatible_variant_inventories_payloads_and_contexts_are_rejected() {
        let context = Context::default();
        let original = choice(&context, 0);
        let index = integer(&context, 0, 32, false);
        for mutation in 0..7 {
            let mut changed = choice(&context, 1);
            let Value::Enum {
                discriminant,
                variants,
                is_option,
            } = &mut changed
            else {
                panic!("expected enum test value");
            };
            match mutation {
                0 => variants[1] = variant("Other", 1, 7),
                1 => variants[1] = variant("Press", 0, 7),
                2 => variants[1] = variant("Press", 1, 8),
                3 => *is_option = true,
                4 => variants.pop().map(|_| ()).unwrap(),
                5 => {
                    let Value::Adt { fields, .. } = &mut variants[1] else {
                        panic!("expected enum variant");
                    };
                    fields.push(("value".into(), integer(&context, 0, 8, false)));
                }
                6 => **discriminant = integer(&context, 0, 8, false),
                _ => unreachable!("bounded mutation selector"),
            }
            assert!(
                fieldless_enum_choice(&context, &[original.clone(), changed], &index)
                    .unwrap()
                    .is_none()
            );
        }
        let mut malformed = choice(&context, 1);
        let Value::Enum { discriminant, .. } = &mut malformed else {
            panic!("expected enum test value");
        };
        **discriminant = Value::Int {
            expression: context.bit_vector(0, 16).unwrap(),
            bits: 8,
            signed: true,
        };
        assert!(fieldless_enum_choice(&context, &[original.clone(), malformed], &index).is_err());
        let foreign = choice(&Context::default(), 0);
        assert!(fieldless_enum_choice(&context, &[original.clone(), foreign], &index).is_err());
        let singleton = [original.clone()];
        let foreign_index = integer(&Context::default(), 0, 32, false);
        assert!(fieldless_enum_choice(&context, &singleton, &foreign_index).is_err());
        let forged_index = Value::Int {
            expression: context.bit_vector(0, 16).unwrap(),
            bits: 32,
            signed: false,
        };
        assert!(fieldless_enum_choice(&context, &singleton, &forged_index).is_err());
        let mut truncated_collision = original;
        let Value::Enum { variants, .. } = &mut truncated_collision else {
            panic!("expected enum test value");
        };
        // -1 is legitimately sign-extended, but a second tag 255 represents the same i8 bits.
        variants[1] = variant("Press", 1, 255);
        assert!(
            fieldless_enum_choice(&context, &[truncated_collision], &index)
                .unwrap()
                .is_none()
        );
    }
}
