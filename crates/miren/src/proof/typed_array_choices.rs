//! Owned finite choices certified by the actual MIR array-prefix type.
use super::*;
use composite_slices::CompositeShape;
use symbolic::ScalarSliceElement;

#[derive(Clone, Debug)]
enum OwnedChoiceShape {
    Primitive(ScalarSliceElement),
    Tuple(Vec<OwnedChoiceShape>),
    Array(Vec<OwnedChoiceShape>),
    Struct {
        name: String,
        fields: Vec<(String, OwnedChoiceShape)>,
    },
    ByteArray(usize),
}

const MAX_CHOICE_NODES: usize = 512;
const MAX_CHOICE_DEPTH: usize = 16;

impl<'tcx> Engine<'tcx> {
    pub(super) fn typed_owned_array_choice(
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
        let shape = self.annotate_owned_shape(*element, &shape)?;
        if !contains_owned_choice(&shape) {
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
            flatten(&self.terms, bits, &shape, value, 0, &mut nodes, &mut leaves)?;
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
        let result = rebuild(&self.terms, bits, &shape, &selected, &mut cursor)?;
        if cursor != selected.len() {
            return Err("typed struct array choice omitted leaf values".into());
        }
        Ok(Some(result))
    }
    fn annotate_owned_shape(
        &self,
        original: Ty<'tcx>,
        certified: &CompositeShape,
    ) -> Result<OwnedChoiceShape, String> {
        match (original.kind(), certified) {
            (ty::Array(element, count), CompositeShape::Array(fields)) => {
                let count = count
                    .try_to_target_usize(self.tcx)
                    .ok_or("owned array annotation requires concrete compiler count")?;
                if count != fields.len() as u64 {
                    return Err("owned array annotation differs from certified count".into());
                }
                if *element == self.tcx.types.u8 {
                    return certified_byte_array_annotation(count, fields);
                }
                Ok(OwnedChoiceShape::Array(
                    fields
                        .iter()
                        .map(|field| self.annotate_owned_shape(*element, field))
                        .collect::<Result<_, _>>()?,
                ))
            }
            (ty::Tuple(types), CompositeShape::Tuple(fields)) if types.len() == fields.len() => {
                Ok(OwnedChoiceShape::Tuple(
                    types
                        .iter()
                        .zip(fields)
                        .map(|(ty, field)| self.annotate_owned_shape(ty, field))
                        .collect::<Result<_, _>>()?,
                ))
            }
            (ty::Adt(def, args), CompositeShape::Struct { name, fields })
                if self.plain_composite_struct(*def)
                    && self.tcx.def_path_str(def.did()) == *name
                    && def.non_enum_variant().fields.len() == fields.len() =>
            {
                let fields = def
                    .non_enum_variant()
                    .fields
                    .iter()
                    .zip(fields)
                    .map(|(field, (name, shape))| {
                        if field.name.as_str() != name {
                            return Err("owned struct annotation field identity mismatch".into());
                        }
                        Ok((
                            name.clone(),
                            self.annotate_owned_shape(
                                field.ty(self.tcx, args).skip_norm_wip(),
                                shape,
                            )?,
                        ))
                    })
                    .collect::<Result<_, String>>()?;
                Ok(OwnedChoiceShape::Struct {
                    name: name.clone(),
                    fields,
                })
            }
            (_, CompositeShape::Primitive(kind))
                if self.scalar_slice_element(original)? == Some(*kind) =>
            {
                Ok(OwnedChoiceShape::Primitive(*kind))
            }
            _ => Err("owned choice annotation differs from original compiler type".into()),
        }
    }
}

// The caller first checks the ORIGINAL compiler array element is exactly core u8. In
// particular, an empty certified shape alone never supplies that element-type evidence.
fn certified_byte_array_annotation(
    count: u64,
    fields: &[CompositeShape],
) -> Result<OwnedChoiceShape, String> {
    if count != fields.len() as u64
        || fields.iter().any(|field| {
            !matches!(
                field,
                CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 8,
                    signed: false
                })
            )
        })
    {
        return Err("owned byte array annotation differs from certified primitive shape".into());
    }
    Ok(OwnedChoiceShape::ByteArray(fields.len()))
}

fn contains_owned_choice(shape: &OwnedChoiceShape) -> bool {
    match shape {
        OwnedChoiceShape::Struct { .. } | OwnedChoiceShape::ByteArray(_) => true,
        OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
            fields.iter().any(contains_owned_choice)
        }
        OwnedChoiceShape::Primitive(_) => false,
    }
}

fn validate_owned_bytes(
    context: &Context,
    pointer_bits: u32,
    count: usize,
    length: &Value,
    data: &Term,
) -> Result<(), String> {
    if !aggregate_validity::byte_array_payload_matches(
        context,
        pointer_bits,
        count as u64,
        length,
        data,
    )? {
        return Err("owned byte array choice has invalid length, sort or context".into());
    }
    Ok(())
}

fn flatten(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
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
        (OwnedChoiceShape::ByteArray(count), value) => {
            let bytes = match value {
                Value::Elements(values) if values.len() == *count => values.to_vec(),
                Value::Bytes { data, length } => {
                    validate_owned_bytes(context, pointer_bits, *count, length, data)?;
                    (0..*count)
                        .map(|position| {
                            Ok(Value::Int {
                                expression: context.apply(
                                    Op::Select,
                                    &[
                                        data.clone(),
                                        context.bit_vector(position as u128, pointer_bits)?,
                                    ],
                                )?,
                                bits: 8,
                                signed: false,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?
                }
                _ => return Err("owned byte array choice has incorrect carrier or count".into()),
            };
            for byte in &bytes {
                flatten(
                    context,
                    pointer_bits,
                    &OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                        bits: 8,
                        signed: false,
                    }),
                    byte,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (OwnedChoiceShape::Primitive(kind), value) => {
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
        (OwnedChoiceShape::Tuple(fields), Value::Unit) if fields.is_empty() => {}
        (OwnedChoiceShape::Tuple(fields), Value::Tuple(values)) if fields.len() == values.len() => {
            for (field, value) in fields.iter().zip(values) {
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (OwnedChoiceShape::Array(fields), Value::Elements(values))
            if fields.len() == values.len() =>
        {
            for (field, value) in fields.iter().zip(values.iter()) {
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (
            OwnedChoiceShape::Struct { name, fields },
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
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        _ => return Err("typed struct choice value differs from exact compiler shape".into()),
    }
    Ok(())
}

fn rebuild(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    leaves: &[Value],
    cursor: &mut usize,
) -> Result<Value, String> {
    Ok(match shape {
        OwnedChoiceShape::ByteArray(count) => {
            let mut data = context.apply(
                Op::ConstArray {
                    index_bits: pointer_bits,
                },
                &[context.bit_vector(0, 8)?],
            )?;
            for position in 0..*count {
                let byte = leaves
                    .get(*cursor)
                    .ok_or("owned byte array choice leaf missing")?;
                *cursor += 1;
                let (byte, bits, signed) = byte.integer()?;
                if bits != 8 || signed {
                    return Err("owned byte array choice selected leaf is not u8".into());
                }
                data = context.apply(
                    Op::Store,
                    &[
                        data,
                        context.bit_vector(position as u128, pointer_bits)?,
                        byte,
                    ],
                )?;
            }
            Value::Bytes {
                data,
                length: Box::new(symbolic::integer(
                    context,
                    *count as u128,
                    pointer_bits,
                    false,
                )),
            }
        }
        OwnedChoiceShape::Primitive(_) => {
            let value = leaves
                .get(*cursor)
                .ok_or("typed struct choice leaf missing")?
                .clone();
            *cursor += 1;
            value
        }
        OwnedChoiceShape::Tuple(fields) if fields.is_empty() => Value::Unit,
        OwnedChoiceShape::Tuple(fields) => Value::Tuple(
            fields
                .iter()
                .map(|field| rebuild(context, pointer_bits, field, leaves, cursor))
                .collect::<Result<_, _>>()?,
        ),
        OwnedChoiceShape::Array(fields) => Value::Elements(
            fields
                .iter()
                .map(|field| rebuild(context, pointer_bits, field, leaves, cursor))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        ),
        OwnedChoiceShape::Struct { name, fields } => Value::Adt {
            name: name.clone(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: fields
                .iter()
                .map(|(name, field)| {
                    Ok((
                        name.clone(),
                        rebuild(context, pointer_bits, field, leaves, cursor)?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?
                .into(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_candidates_require_typed_annotations_exact_carriers_and_expanded_budgets() {
        let context = Context::default();
        let foreign = Context::default();
        let u8_shape = CompositeShape::Primitive(ScalarSliceElement::Integer {
            bits: 8,
            signed: false,
        });
        assert!(certified_byte_array_annotation(1, &[]).is_err());
        assert!(
            certified_byte_array_annotation(
                1,
                &[CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 16,
                    signed: false
                })]
            )
            .is_err()
        );
        let shape = certified_byte_array_annotation(3, &vec![u8_shape; 3]).unwrap();
        let empty = certified_byte_array_annotation(0, &[]).unwrap();
        for bits in [32, 64] {
            let data = context
                .apply(
                    Op::ConstArray { index_bits: bits },
                    &[context.bit_vector(7, 8).unwrap()],
                )
                .unwrap();
            let length = symbolic::integer(&context, 3, bits, false);
            let bytes = Value::Bytes {
                data: data.clone(),
                length: Box::new(length.clone()),
            };
            let elements =
                Value::Elements(vec![symbolic::integer(&context, 7, 8, false); 3].into());
            let mut byte_leaves = Vec::new();
            let mut element_leaves = Vec::new();
            let mut byte_nodes = 0;
            let mut element_nodes = 0;
            flatten(
                &context,
                bits,
                &shape,
                &bytes,
                0,
                &mut byte_nodes,
                &mut byte_leaves,
            )
            .unwrap();
            flatten(
                &context,
                bits,
                &shape,
                &elements,
                0,
                &mut element_nodes,
                &mut element_leaves,
            )
            .unwrap();
            assert_eq!(byte_nodes, 4);
            assert_eq!(element_nodes, byte_nodes);
            assert_eq!(format!("{byte_leaves:?}"), format!("{element_leaves:?}"));
            let selected = byte_leaves
                .into_iter()
                .map(|(_, value)| value)
                .collect::<Vec<_>>();
            let result = rebuild(&context, bits, &shape, &selected, &mut 0).unwrap();
            let Value::Bytes {
                data: result_data,
                length: result_len,
            } = result
            else {
                panic!("selected owned byte array must retain the byte carrier");
            };
            validate_owned_bytes(&context, bits, 3, &result_len, &result_data).unwrap();
            for position in 0..3 {
                assert_eq!(
                    symbolic::constant(
                        &context
                            .apply(
                                Op::Select,
                                &[
                                    result_data.clone(),
                                    context.bit_vector(position, bits).unwrap(),
                                ]
                            )
                            .unwrap()
                    ),
                    Some(symbolic::Constant::BitVec { value: 7, bits: 8 })
                );
            }
            let empty_bytes = Value::Bytes {
                data: data.clone(),
                length: Box::new(symbolic::integer(&context, 0, bits, false)),
            };
            flatten(
                &context,
                bits,
                &empty,
                &empty_bytes,
                0,
                &mut 0,
                &mut Vec::new(),
            )
            .unwrap();
            assert!(
                flatten(
                    &context,
                    bits,
                    &OwnedChoiceShape::Array(vec![]),
                    &empty_bytes,
                    0,
                    &mut 0,
                    &mut Vec::new()
                )
                .is_err()
            );
            assert!(
                flatten(
                    &context,
                    bits,
                    &empty,
                    &Value::Unit,
                    0,
                    &mut 0,
                    &mut Vec::new()
                )
                .is_err()
            );
            for invalid_length in [
                symbolic::integer(&context, 2, bits, false),
                symbolic::integer(&context, 3, bits, true),
                symbolic::integer(&foreign, 3, bits, false),
                Value::Int {
                    expression: context.symbol(100 + bits, Sort::BitVec(bits)).unwrap(),
                    bits,
                    signed: false,
                },
            ] {
                assert!(validate_owned_bytes(&context, bits, 3, &invalid_length, &data).is_err());
            }
            for invalid_data in [
                foreign
                    .apply(
                        Op::ConstArray { index_bits: bits },
                        &[foreign.bit_vector(7, 8).unwrap()],
                    )
                    .unwrap(),
                context
                    .apply(
                        Op::ConstArray {
                            index_bits: bits / 2,
                        },
                        &[context.bit_vector(7, 8).unwrap()],
                    )
                    .unwrap(),
                context
                    .apply(
                        Op::ConstArray { index_bits: bits },
                        &[context.bit_vector(7, 16).unwrap()],
                    )
                    .unwrap(),
            ] {
                assert!(validate_owned_bytes(&context, bits, 3, &length, &invalid_data).is_err());
            }
            for candidate in [&bytes, &elements] {
                let mut exhausted = MAX_CHOICE_NODES - 3;
                assert!(
                    flatten(
                        &context,
                        bits,
                        &shape,
                        candidate,
                        0,
                        &mut exhausted,
                        &mut Vec::new()
                    )
                    .is_err()
                );
            }
            let signed = Value::Elements(vec![symbolic::integer(&context, 7, 8, true); 3].into());
            assert!(flatten(&context, bits, &shape, &signed, 0, &mut 0, &mut Vec::new()).is_err());
        }
    }

    #[test]
    fn typed_candidate_schema_rejects_corruption_and_preserves_nominal_zero_values() {
        let context = Context::default();
        let foreign = Context::default();
        let shape = OwnedChoiceShape::Struct {
            name: "fixture::Pair".into(),
            fields: vec![
                (
                    "value".into(),
                    OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                        bits: 16,
                        signed: false,
                    }),
                ),
                (
                    "marker".into(),
                    OwnedChoiceShape::Struct {
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
        flatten(&context, 64, &shape, &correct, 0, &mut 0, &mut leaves).unwrap();
        assert_eq!(leaves.len(), 1);
        let rebuilt = rebuild(&context, 64, &shape, &[leaves[0].1.clone()], &mut 0).unwrap();
        assert_eq!(format!("{correct:?}"), format!("{rebuilt:?}"));
        assert!(
            flatten(
                &context,
                64,
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
            assert!(flatten(&context, 64, &shape, &invalid, 0, &mut 0, &mut Vec::new()).is_err());
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
        assert!(flatten(&context, 64, &shape, &reordered, 0, &mut 0, &mut Vec::new()).is_err());
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
        assert!(flatten(&context, 64, &shape, &renamed, 0, &mut 0, &mut Vec::new()).is_err());
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
        assert!(flatten(&context, 64, &shape, &signed, 0, &mut 0, &mut Vec::new()).is_err());
        let mut exhausted = MAX_CHOICE_NODES;
        assert!(
            flatten(
                &context,
                64,
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
