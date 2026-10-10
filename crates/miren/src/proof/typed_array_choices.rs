//! Owned finite choices certified by the actual MIR array-prefix type.
use super::*;
use composite_slices::CompositeShape;
use symbolic::ScalarSliceElement;

const MAX_CHOICE_NODES: usize = 512;
const MAX_CHOICE_DEPTH: usize = 16;

impl<'tcx> Engine<'tcx> {
    pub(super) fn typed_struct_array_choice(
        &self,
        original: Ty<'tcx>,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Array(element, count) = original.kind() else {
            return Ok(None);
        };
        if count.try_to_target_usize(self.tcx) != Some(elements.len() as u64) {
            return Err("typed struct array choice inventory differs from compiler length".into());
        }
        let Some(shape) = self.owned_struct_choice_shape(*element)? else {
            return Ok(None);
        };
        if !contains_struct(&shape) {
            return Ok(None);
        }
        let (term, bits, signed) = index.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("typed struct array choice requires exact target usize".into());
        }
        let mut columns: Vec<Vec<Value>> = Vec::new();
        let mut nodes = 0;
        for value in elements {
            let mut leaves = Vec::new();
            flatten(&self.terms, &shape, value, 0, &mut nodes, &mut leaves)?;
            for (position, (kind, leaf)) in leaves.into_iter().enumerate() {
                if kind == ScalarSliceElement::Char {
                    self.prove_char_value(&leaf, conditions)?;
                }
                if columns.len() <= position {
                    columns.push(Vec::new());
                }
                columns[position].push(leaf);
            }
        }
        let selected = columns
            .iter()
            .map(|values| symbolic::select_element(&self.terms, values, index))
            .collect::<Result<Vec<_>, _>>()?;
        let mut cursor = 0;
        let result = rebuild(&shape, &selected, &mut cursor)?;
        if cursor != selected.len() {
            return Err("typed struct array choice omitted leaf values".into());
        }
        Ok(Some(result))
    }
}

fn contains_struct(shape: &CompositeShape) -> bool {
    match shape {
        CompositeShape::Struct { .. } => true,
        CompositeShape::Tuple(fields) | CompositeShape::Array(fields) => {
            fields.iter().any(contains_struct)
        }
        CompositeShape::Primitive(_) => false,
    }
}

fn flatten(
    context: &Context,
    shape: &CompositeShape,
    value: &Value,
    depth: usize,
    nodes: &mut usize,
    leaves: &mut Vec<(ScalarSliceElement, Value)>,
) -> Result<(), String> {
    if depth >= MAX_CHOICE_DEPTH || *nodes >= MAX_CHOICE_NODES {
        return Err("typed struct array choice exceeds its depth or candidate node budget".into());
    }
    *nodes += 1;
    let valid = |term: &Term, sort: Sort| term.sort() == &sort && term.belongs_to(context);
    match (shape, value) {
        (CompositeShape::Primitive(kind), value) => {
            let correct = match (kind, value) {
                (ScalarSliceElement::Bool, Value::Bool(term)) => valid(term, Sort::Bool),
                (
                    ScalarSliceElement::Integer { bits, signed },
                    Value::Int {
                        expression,
                        bits: actual,
                        signed: actual_signed,
                    },
                ) => {
                    bits == actual
                        && signed == actual_signed
                        && valid(expression, Sort::BitVec(*bits))
                }
                (
                    ScalarSliceElement::Char,
                    Value::Int {
                        expression,
                        bits: 32,
                        signed: false,
                    },
                ) => valid(expression, Sort::BitVec(32)),
                (
                    ScalarSliceElement::Float { bits },
                    Value::Float {
                        expression,
                        bits: actual,
                        raw_bits,
                    },
                ) => {
                    let (exponent, significand) = match bits {
                        32 => (8, 24),
                        64 => (11, 53),
                        _ => return Err("typed struct choice float width is invalid".into()),
                    };
                    bits == actual
                        && valid(
                            expression,
                            Sort::Float {
                                exponent,
                                significand,
                            },
                        )
                        && raw_bits
                            .as_ref()
                            .is_none_or(|raw| valid(raw, Sort::BitVec(*bits)))
                }
                _ => false,
            };
            if !correct {
                return Err("typed struct choice primitive differs from compiler shape".into());
            }
            leaves.push((*kind, value.clone()));
        }
        (CompositeShape::Tuple(fields), Value::Unit) if fields.is_empty() => {}
        (CompositeShape::Tuple(fields), Value::Tuple(values)) if fields.len() == values.len() => {
            for (field, value) in fields.iter().zip(values) {
                flatten(context, field, value, depth + 1, nodes, leaves)?;
            }
        }
        (CompositeShape::Array(fields), Value::Elements(values))
            if fields.len() == values.len() =>
        {
            for (field, value) in fields.iter().zip(values.iter()) {
                flatten(context, field, value, depth + 1, nodes, leaves)?;
            }
        }
        (
            CompositeShape::Struct { name, fields },
            Value::Adt {
                name: actual,
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: values,
            },
        ) if name == actual && fields.len() == values.len() => {
            for ((name, field), (actual, value)) in fields.iter().zip(values.iter()) {
                if name != actual {
                    return Err(
                        "typed struct choice field identity differs from compiler shape".into(),
                    );
                }
                flatten(context, field, value, depth + 1, nodes, leaves)?;
            }
        }
        _ => return Err("typed struct choice value differs from exact compiler shape".into()),
    }
    Ok(())
}

fn rebuild(shape: &CompositeShape, leaves: &[Value], cursor: &mut usize) -> Result<Value, String> {
    Ok(match shape {
        CompositeShape::Primitive(_) => {
            let value = leaves
                .get(*cursor)
                .ok_or("typed struct choice leaf missing")?
                .clone();
            *cursor += 1;
            value
        }
        CompositeShape::Tuple(fields) if fields.is_empty() => Value::Unit,
        CompositeShape::Tuple(fields) => Value::Tuple(
            fields
                .iter()
                .map(|field| rebuild(field, leaves, cursor))
                .collect::<Result<_, _>>()?,
        ),
        CompositeShape::Array(fields) => Value::Elements(
            fields
                .iter()
                .map(|field| rebuild(field, leaves, cursor))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        ),
        CompositeShape::Struct { name, fields } => Value::Adt {
            name: name.clone(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: fields
                .iter()
                .map(|(name, field)| Ok((name.clone(), rebuild(field, leaves, cursor)?)))
                .collect::<Result<Vec<_>, String>>()?
                .into(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_candidate_schema_rejects_corruption_and_preserves_nominal_zero_values() {
        let context = Context::default();
        let foreign = Context::default();
        let shape = CompositeShape::Struct {
            name: "fixture::Pair".into(),
            fields: vec![
                (
                    "value".into(),
                    CompositeShape::Primitive(ScalarSliceElement::Integer {
                        bits: 16,
                        signed: false,
                    }),
                ),
                (
                    "marker".into(),
                    CompositeShape::Struct {
                        name: "fixture::Zero".into(),
                        fields: vec![],
                    },
                ),
            ],
        };
        let zero = Value::Adt {
            name: "fixture::Zero".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![].into(),
        };
        let value = |term| Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![
                (
                    "value".into(),
                    Value::Int {
                        expression: term,
                        bits: 16,
                        signed: false,
                    },
                ),
                ("marker".into(), zero.clone()),
            ]
            .into(),
        };
        let correct = value(context.bit_vector(7, 16).unwrap());
        let mut leaves = Vec::new();
        flatten(&context, &shape, &correct, 0, &mut 0, &mut leaves).unwrap();
        assert_eq!(leaves.len(), 1);
        let rebuilt = rebuild(&shape, &[leaves[0].1.clone()], &mut 0).unwrap();
        assert_eq!(format!("{correct:?}"), format!("{rebuilt:?}"));
        assert!(
            flatten(
                &context,
                &shape,
                &value(foreign.bit_vector(7, 16).unwrap()),
                0,
                &mut 0,
                &mut Vec::new()
            )
            .is_err()
        );
        let Value::Adt { fields, .. } = correct.clone() else {
            unreachable!()
        };
        for invalid in [
            Value::Adt {
                name: "fixture::Other".into(),
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 1,
                discriminant: 0,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 1,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 0,
                is_option: true,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: vec![].into(),
            },
        ] {
            assert!(flatten(&context, &shape, &invalid, 0, &mut 0, &mut Vec::new()).is_err());
        }
        let Value::Adt { mut fields, .. } = correct.clone() else {
            unreachable!()
        };
        fields = fields.iter().cloned().rev().collect::<Vec<_>>().into();
        let reordered = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields,
        };
        assert!(flatten(&context, &shape, &reordered, 0, &mut 0, &mut Vec::new()).is_err());
        let Value::Adt { fields, .. } = correct.clone() else {
            unreachable!()
        };
        let mut renamed = fields.iter().cloned().collect::<Vec<_>>();
        renamed[0].0 = "wrong".into();
        let renamed = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: renamed.into(),
        };
        assert!(flatten(&context, &shape, &renamed, 0, &mut 0, &mut Vec::new()).is_err());
        let mut signed = fields.iter().cloned().collect::<Vec<_>>();
        let Value::Int { signed: sign, .. } = &mut signed[0].1 else {
            unreachable!()
        };
        *sign = true;
        let signed = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: signed.into(),
        };
        assert!(flatten(&context, &shape, &signed, 0, &mut 0, &mut Vec::new()).is_err());
        let mut exhausted = MAX_CHOICE_NODES;
        assert!(
            flatten(
                &context,
                &shape,
                &correct,
                0,
                &mut exhausted,
                &mut Vec::new()
            )
            .is_err()
        );
    }
}
