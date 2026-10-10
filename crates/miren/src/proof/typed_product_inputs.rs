//! Bounded preparation of closed or issued compiler-certified deferred owned products.
use super::*;
use symbolic::input::{InputKind, InputShape, InputValue};
use typed_array_choices::{MAX_CHOICE_DEPTH, MAX_CHOICE_NODES, OwnedChoiceShape, rebuild};

const MAX_RESERVED_SLOTS: u32 = 262_144;

#[derive(Clone, Copy, Debug)]
struct DescriptorStats {
    slots: u32,
    height: usize,
    expanded: usize,
    observable: bool,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn prepare_typed_product(
        &self,
        original: Ty<'tcx>,
        shape: &OwnedChoiceShape,
        value: &Value,
        used: usize,
    ) -> Result<Value, String> {
        let mut cost = 0;
        product_cost(shape, 0, &mut cost)?;
        if cost > MAX_CHOICE_NODES.saturating_sub(used) {
            return Err(
                "typed struct array choice exceeds its depth or candidate node budget".into(),
            );
        }
        self.prepare_product_depth(original, shape, value, 0)
    }

    fn prepare_product_depth(
        &self,
        original: Ty<'tcx>,
        shape: &OwnedChoiceShape,
        value: &Value,
        depth: usize,
    ) -> Result<Value, String> {
        if depth >= MAX_CHOICE_DEPTH {
            return Err("deferred product exceeds its depth budget".into());
        }
        if let Value::Input(input) = value {
            let mut nodes = 0;
            self.descriptor_type(original, &input.shape, depth, &mut nodes)?;
            let mut nodes = 0;
            let stats = descriptor_stats(&input.shape, input.shape.slots == 0, depth, &mut nodes)?;
            validate_envelope(&self.terms, input, stats)?;
            if stats.observable || product_observable(shape) {
                self.validate_issued_product(original, input)?;
                let materialized = input.materialize()?;
                return self.prepare_product_depth(original, shape, &materialized, depth);
            }
            let mut cursor = 0;
            return rebuild(
                &self.terms,
                u32::from(self.tcx.sess.target.pointer_width),
                shape,
                &[],
                &mut cursor,
            );
        }
        Ok(match (original.kind(), shape, value) {
            (ty::Tuple(types), OwnedChoiceShape::Tuple(fields), Value::Tuple(values))
                if types.len() == fields.len() && fields.len() == values.len() =>
            {
                Value::Tuple(
                    types
                        .iter()
                        .zip(fields)
                        .zip(values)
                        .map(|((ty, field), value)| {
                            self.prepare_product_depth(ty, field, value, depth + 1)
                        })
                        .collect::<Result<_, _>>()?,
                )
            }
            (ty::Array(element, _), OwnedChoiceShape::Array(fields), Value::Elements(values))
                if fields.len() == values.len() =>
            {
                Value::Elements(
                    fields
                        .iter()
                        .zip(values.iter())
                        .map(|(field, value)| {
                            self.prepare_product_depth(*element, field, value, depth + 1)
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into(),
                )
            }
            (
                ty::Adt(def, args),
                OwnedChoiceShape::Struct { name, fields },
                Value::Adt {
                    name: actual,
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: values,
                },
            ) if name == actual
                && def.non_enum_variant().fields.len() == fields.len()
                && fields.len() == values.len() =>
            {
                let fields = def
                    .non_enum_variant()
                    .fields
                    .iter()
                    .zip(fields)
                    .zip(values.iter())
                    .map(|((field, (name, shape)), (actual, value))| {
                        if field.name.as_str() != name || actual != name {
                            return Err("deferred product field identity mismatch".into());
                        }
                        Ok((
                            name.clone(),
                            self.prepare_product_depth(
                                field.ty(self.tcx, args).skip_norm_wip(),
                                shape,
                                value,
                                depth + 1,
                            )?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Value::Adt {
                    name: name.clone(),
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: fields.into(),
                }
            }
            (
                _,
                OwnedChoiceShape::Primitive(_),
                Value::Bool(_) | Value::Int { .. } | Value::Float { .. },
            ) => value.clone(),
            (ty::Tuple(types), OwnedChoiceShape::Tuple(fields), Value::Unit)
                if types.is_empty() && fields.is_empty() =>
            {
                Value::Unit
            }
            (ty::Array(_, _), OwnedChoiceShape::ByteArray(count), Value::Elements(values))
                if *count == values.len()
                    && values
                        .iter()
                        .all(|value| matches!(value, Value::Int { .. })) =>
            {
                value.clone()
            }
            (ty::Array(_, _), OwnedChoiceShape::ByteArray(_), Value::Bytes { length, .. })
                if matches!(length.as_ref(), Value::Int { .. }) =>
            {
                value.clone()
            }
            _ => return Err("typed struct choice value differs from exact compiler shape".into()),
        })
    }

    fn descriptor_type(
        &self,
        original: Ty<'tcx>,
        shape: &InputShape,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<(), String> {
        charge(depth, nodes)?;
        let mismatch =
            || "deferred product descriptor differs from original compiler type".to_owned();
        match (original.kind(), &shape.kind) {
            (ty::Bool, InputKind::Bool) => Ok(()),
            (ty::Int(_) | ty::Uint(_), InputKind::Integer { bits, signed })
                if self.integer_type(original) == Some((*bits, *signed)) =>
            {
                Ok(())
            }
            (ty::Float(_), InputKind::Float { bits })
                if self.float_type(original) == Some(*bits) =>
            {
                Ok(())
            }
            (ty::Tuple(types), InputKind::Unit) if types.is_empty() => Ok(()),
            (ty::Tuple(types), InputKind::Tuple(fields))
                if !types.is_empty() && types.len() == fields.len() =>
            {
                for (ty, field) in types.iter().zip(fields) {
                    self.descriptor_type(ty, field, depth + 1, nodes)?;
                }
                Ok(())
            }
            (
                ty::Array(element, count),
                InputKind::Array {
                    element: field,
                    count: actual,
                },
            ) if count.try_to_target_usize(self.tcx) == Some(*actual as u64) => {
                // The original inner type is checked even when there are no actual elements.
                self.descriptor_type(*element, field, depth + 1, nodes)
            }
            (
                ty::Array(element, count),
                InputKind::Bytes {
                    count: actual,
                    pointer_bits,
                },
            ) if *element == self.tcx.types.u8
                && count.try_to_target_usize(self.tcx) == Some(*actual)
                && *pointer_bits == u32::from(self.tcx.sess.target.pointer_width) =>
            {
                Ok(())
            }
            (ty::Adt(def, args), InputKind::Struct { name, fields })
                if self.plain_composite_struct(*def)
                    && self.tcx.def_path_str(def.did()) == *name
                    && def.non_enum_variant().fields.len() == fields.len() =>
            {
                for (field, (name, shape)) in def.non_enum_variant().fields.iter().zip(fields) {
                    if field.name.as_str() != name {
                        return Err(mismatch());
                    }
                    self.descriptor_type(
                        field.ty(self.tcx, args).skip_norm_wip(),
                        shape,
                        depth + 1,
                        nodes,
                    )?;
                }
                Ok(())
            }
            _ => Err(mismatch()),
        }
    }
}

fn charge(depth: usize, nodes: &mut usize) -> Result<(), String> {
    if depth >= MAX_CHOICE_DEPTH || *nodes >= MAX_CHOICE_NODES {
        return Err("deferred product descriptor exceeds its depth or node budget".into());
    }
    *nodes += 1;
    Ok(())
}

fn product_cost(shape: &OwnedChoiceShape, depth: usize, nodes: &mut usize) -> Result<(), String> {
    charge(depth, nodes)?;
    match shape {
        OwnedChoiceShape::Primitive(_) => {}
        OwnedChoiceShape::ByteArray(count) => {
            if *count > MAX_CHOICE_NODES.saturating_sub(*nodes) {
                return Err("deferred product exceeds its expanded byte budget".into());
            }
            *nodes += count;
        }
        OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
            for field in fields {
                product_cost(field, depth + 1, nodes)?;
            }
        }
        OwnedChoiceShape::Struct { fields, .. } => {
            for (_, field) in fields {
                product_cost(field, depth + 1, nodes)?;
            }
        }
    }
    Ok(())
}

fn product_observable(shape: &OwnedChoiceShape) -> bool {
    match shape {
        OwnedChoiceShape::Primitive(_) => true,
        OwnedChoiceShape::ByteArray(count) => *count != 0,
        OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
            fields.iter().any(product_observable)
        }
        OwnedChoiceShape::Struct { fields, .. } => {
            fields.iter().any(|(_, field)| product_observable(field))
        }
    }
}

fn validate_envelope(
    context: &Context,
    input: &InputValue,
    stats: DescriptorStats,
) -> Result<(), String> {
    if input.seed.sort() != &Sort::Bool
        || !input.seed.belongs_to(context)
        || input
            .start
            .checked_add(stats.slots)
            .is_none_or(|end| end > MAX_RESERVED_SLOTS)
        || input
            .start
            .checked_add(stats.height as u32)
            .is_none_or(|end| end > MAX_RESERVED_SLOTS)
    {
        return Err("deferred product input seed or reserved range is invalid".into());
    }
    Ok(())
}

fn descriptor_stats(
    shape: &InputShape,
    zero: bool,
    depth: usize,
    nodes: &mut usize,
) -> Result<DescriptorStats, String> {
    charge(depth, nodes)?;
    let leaf = |observable| DescriptorStats {
        slots: u32::from(!zero),
        height: 1,
        expanded: 1,
        observable,
    };
    let child =
        |shape: &InputShape, nodes: &mut usize| descriptor_stats(shape, zero, depth + 1, nodes);
    let stats = match &shape.kind {
        InputKind::Bool => leaf(true),
        InputKind::Integer {
            bits: 8 | 16 | 32 | 64 | 128,
            ..
        } => leaf(true),
        InputKind::Float { bits: 32 | 64 } => leaf(true),
        InputKind::Unit => leaf(false),
        InputKind::Bytes {
            count,
            pointer_bits,
        } if *count <= 128 && matches!(pointer_bits, 32 | 64) => DescriptorStats {
            expanded: 1 + *count as usize,
            observable: *count != 0,
            ..leaf(false)
        },
        InputKind::Tuple(fields) => {
            if fields.len() > MAX_CHOICE_NODES.saturating_sub(*nodes) {
                return Err("deferred product descriptor exceeds its field budget".into());
            }
            let stats = fields
                .iter()
                .map(|field| child(field, nodes))
                .collect::<Result<Vec<_>, _>>()?;
            combine_stats(&stats, zero)?
        }
        InputKind::Struct { fields, .. } => {
            if fields.len() > MAX_CHOICE_NODES.saturating_sub(*nodes) {
                return Err("deferred product descriptor exceeds its field budget".into());
            }
            let stats = fields
                .iter()
                .map(|(_, field)| child(field, nodes))
                .collect::<Result<Vec<_>, _>>()?;
            combine_stats(&stats, zero)?
        }
        InputKind::Array { element, count } if *count <= 128 => {
            let element = child(element, nodes)?;
            DescriptorStats {
                slots: if zero {
                    0
                } else {
                    element
                        .slots
                        .checked_mul(*count as u32)
                        .and_then(|n| n.checked_add(1))
                        .ok_or("deferred slot overflow")?
                },
                height: element.height + 1,
                expanded: element
                    .expanded
                    .checked_mul(*count)
                    .and_then(|n| n.checked_add(1))
                    .ok_or("deferred expansion overflow")?,
                observable: *count != 0 && element.observable,
            }
        }
        _ => return Err("deferred product descriptor kind is unsupported".into()),
    };
    if stats.slots != shape.slots
        || stats.height != shape.height
        || stats.expanded > MAX_CHOICE_NODES
        || (zero && stats.observable)
    {
        return Err("deferred product descriptor has invalid slots, height or expansion".into());
    }
    Ok(stats)
}

fn combine_stats(fields: &[DescriptorStats], zero: bool) -> Result<DescriptorStats, String> {
    let mut result = DescriptorStats {
        slots: u32::from(!zero),
        height: 1,
        expanded: 1,
        observable: false,
    };
    for field in fields {
        result.slots = result
            .slots
            .checked_add(field.slots)
            .ok_or("deferred slot overflow")?;
        result.height = result.height.max(field.height + 1);
        result.expanded = result
            .expanded
            .checked_add(field.expanded)
            .ok_or("deferred expansion overflow")?;
        result.observable |= field.observable;
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    fn unit(zero: bool) -> Rc<InputShape> {
        Rc::new(InputShape {
            kind: InputKind::Unit,
            slots: u32::from(!zero),
            height: 1,
        })
    }

    #[test]
    fn closed_descriptor_metadata_checks_modes_seeds_counts_and_reserved_arithmetic() {
        let context = Context::default();
        let foreign = Context::default();
        for zero in [false, true] {
            let shape = Rc::new(InputShape {
                kind: InputKind::Struct {
                    name: "Nominal".into(),
                    fields: vec![("unit".into(), unit(zero))],
                },
                slots: if zero { 0 } else { 2 },
                height: 2,
            });
            let stats = descriptor_stats(&shape, zero, 0, &mut 0).unwrap();
            assert!(!stats.observable);
            assert_eq!(stats.expanded, 2);
            let input = InputValue {
                shape: shape.clone(),
                start: 0,
                seed: context.boolean(false),
            };
            validate_envelope(&context, &input, stats).unwrap();
            assert!(
                validate_envelope(
                    &context,
                    &InputValue {
                        seed: foreign.boolean(false),
                        ..input.clone()
                    },
                    stats
                )
                .is_err()
            );
            assert!(
                validate_envelope(
                    &context,
                    &InputValue {
                        seed: context.bit_vector(0, 8).unwrap(),
                        ..input.clone()
                    },
                    stats
                )
                .is_err()
            );
            assert!(
                validate_envelope(
                    &context,
                    &InputValue {
                        start: u32::MAX,
                        ..input
                    },
                    stats
                )
                .is_err()
            );
            let wrong = InputShape {
                slots: 7,
                ..shape.as_ref().clone()
            };
            assert!(descriptor_stats(&wrong, zero, 0, &mut 0).is_err());
            let wrong = InputShape {
                height: 1,
                ..shape.as_ref().clone()
            };
            assert!(descriptor_stats(&wrong, zero, 0, &mut 0).is_err());
        }
        let hidden = Rc::new(InputShape {
            kind: InputKind::Integer {
                bits: 32,
                signed: false,
            },
            slots: 0,
            height: 1,
        });
        assert!(descriptor_stats(&hidden, true, 0, &mut 0).is_err());
        let scalar = Rc::new(InputShape {
            slots: 1,
            ..hidden.as_ref().clone()
        });
        assert!(
            descriptor_stats(&scalar, false, 0, &mut 0)
                .unwrap()
                .observable
        );
        let empty = InputShape {
            kind: InputKind::Array {
                element: scalar,
                count: 0,
            },
            slots: 1,
            height: 2,
        };
        assert!(
            !descriptor_stats(&empty, false, 0, &mut 0)
                .unwrap()
                .observable
        );
        let unsupported = InputShape {
            kind: InputKind::FunctionPointer { id: 0 },
            slots: 1,
            height: 1,
        };
        assert!(descriptor_stats(&unsupported, false, 0, &mut 0).is_err());
    }

    #[test]
    fn closed_expansion_counts_occurrences_and_preserves_nominal_reconstruction() {
        let context = Context::default();
        let child = Rc::new(InputShape {
            kind: InputKind::Tuple(vec![unit(true), unit(true), unit(true)]),
            slots: 0,
            height: 2,
        });
        let repeated = InputShape {
            kind: InputKind::Array {
                element: child.clone(),
                count: 128,
            },
            slots: 0,
            height: 3,
        };
        assert!(descriptor_stats(&repeated, true, 0, &mut 0).is_err());
        let repeated = InputShape {
            kind: InputKind::Array {
                element: child,
                count: 127,
            },
            slots: 0,
            height: 3,
        };
        assert_eq!(
            descriptor_stats(&repeated, true, 0, &mut 0)
                .unwrap()
                .expanded,
            509
        );
        let too_many = InputShape {
            kind: InputKind::Tuple(vec![unit(true); 513]),
            slots: 0,
            height: 2,
        };
        assert!(descriptor_stats(&too_many, true, 0, &mut 0).is_err());
        let shape = OwnedChoiceShape::Struct {
            name: "Token<7>".into(),
            fields: vec![
                ("empty".into(), OwnedChoiceShape::Array(Vec::new())),
                ("unit".into(), OwnedChoiceShape::Tuple(Vec::new())),
            ],
        };
        let mut cost = 0;
        product_cost(&shape, 0, &mut cost).unwrap();
        assert_eq!(cost, 3);
        assert!(!product_observable(&shape));
        let value = rebuild(&context, 64, &shape, &[], &mut 0).unwrap();
        let Value::Adt {
            name,
            variant,
            discriminant,
            is_option,
            fields,
        } = value
        else {
            panic!("closed nominal product lost its ADT identity");
        };
        assert_eq!(name, "Token<7>");
        assert_eq!((variant, discriminant, is_option), (0, 0, false));
        assert_eq!(fields.len(), 2);
        assert!(matches!(fields[0].1, Value::Elements(_)));
        assert!(product_observable(&OwnedChoiceShape::ByteArray(1)));
        assert!(!product_observable(&OwnedChoiceShape::ByteArray(0)));
    }
}
