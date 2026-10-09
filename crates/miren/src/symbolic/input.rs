use super::{Sort, Term, Value};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct InputShape {
    pub kind: InputKind,
    pub slots: u32,
    pub height: usize,
}

#[derive(Clone, Debug)]
pub struct InputVariant {
    pub discriminant: u128,
    pub fields: Vec<(String, Rc<InputShape>)>,
}

#[derive(Clone, Debug)]
pub enum InputKind {
    Bool,
    Integer {
        bits: u32,
        signed: bool,
    },
    Float {
        bits: u32,
    },
    Unit,
    FunctionPointer {
        id: usize,
    },
    Bytes {
        count: u64,
        pointer_bits: u32,
    },
    Tuple(Vec<Rc<InputShape>>),
    Struct {
        name: String,
        fields: Vec<(String, Rc<InputShape>)>,
    },
    Enum {
        name: String,
        bits: u32,
        signed: bool,
        is_option: bool,
        variants: Vec<InputVariant>,
    },
    Array {
        element: Rc<InputShape>,
        count: usize,
    },
}

#[derive(Clone, Debug)]
pub struct InputValue {
    pub shape: Rc<InputShape>,
    pub start: u32,
    pub seed: Term,
}

impl InputValue {
    fn child(&self, shape: &Rc<InputShape>, start: u32) -> Result<Value, String> {
        let child = Self {
            shape: shape.clone(),
            start,
            seed: self.seed.clone(),
        };
        match &shape.kind {
            InputKind::Bool
            | InputKind::Integer { .. }
            | InputKind::Float { .. }
            | InputKind::Unit
            | InputKind::FunctionPointer { .. }
            | InputKind::Bytes { .. } => child.materialize(),
            InputKind::Tuple(_)
            | InputKind::Struct { .. }
            | InputKind::Enum { .. }
            | InputKind::Array { .. } => Ok(Value::Input(child)),
        }
    }

    pub fn materialize(&self) -> Result<Value, String> {
        let context = self.seed.context();
        let symbol = |sort| context.symbol(self.start, sort);
        let mut start = self
            .start
            .checked_add(1)
            .ok_or("lazy input symbol range overflow")?;
        match &self.shape.kind {
            InputKind::Bool => Ok(Value::Bool(symbol(Sort::Bool)?)),
            InputKind::Integer { bits, signed } => Ok(Value::Int {
                expression: symbol(Sort::BitVec(*bits))?,
                bits: *bits,
                signed: *signed,
            }),
            InputKind::Float { bits } => Ok(super::float_from_bits(
                context,
                symbol(Sort::BitVec(*bits))?,
                *bits,
            )),
            InputKind::Unit => Ok(Value::Unit),
            InputKind::FunctionPointer { id } => Ok(Value::FunctionPointer { id: *id }),
            InputKind::Bytes {
                count,
                pointer_bits,
            } => Ok(Value::Bytes {
                length: Box::new(super::integer(
                    context,
                    u128::from(*count),
                    *pointer_bits,
                    false,
                )),
                data: symbol(Sort::Array(
                    Box::new(Sort::BitVec(*pointer_bits)),
                    Box::new(Sort::BitVec(8)),
                ))?,
            }),
            InputKind::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|shape| {
                        let value = self.child(shape, start)?;
                        start = start
                            .checked_add(shape.slots)
                            .ok_or("lazy input symbol range overflow")?;
                        Ok(value)
                    })
                    .collect::<Result<_, String>>()?;
                Ok(Value::Tuple(fields))
            }
            InputKind::Struct { name, fields } => {
                let fields = fields
                    .iter()
                    .map(|(name, shape)| {
                        let value = self.child(shape, start)?;
                        start = start
                            .checked_add(shape.slots)
                            .ok_or("lazy input symbol range overflow")?;
                        Ok((name.clone(), value))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(Value::Adt {
                    name: name.clone(),
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields: fields.into(),
                })
            }
            InputKind::Enum {
                name,
                bits,
                signed,
                is_option,
                variants,
            } => {
                let tags = variants
                    .iter()
                    .map(|variant| super::integer(context, variant.discriminant, *bits, *signed))
                    .collect::<Vec<_>>();
                let selector = Value::Int {
                    // Root descriptors reserve self.start as the Boolean context seed.
                    // The first variant wrapper's otherwise unused slot holds the selector.
                    expression: context.symbol(start, Sort::BitVec(*bits))?,
                    bits: *bits,
                    signed: false,
                };
                let discriminant = super::select_element(context, &tags, &selector)?;
                let variants = variants
                    .iter()
                    .enumerate()
                    .map(|(position, variant)| {
                        start = start
                            .checked_add(1)
                            .ok_or("lazy input symbol range overflow")?;
                        let fields = variant
                            .fields
                            .iter()
                            .map(|(name, shape)| {
                                let value = self.child(shape, start)?;
                                start = start
                                    .checked_add(shape.slots)
                                    .ok_or("lazy input symbol range overflow")?;
                                Ok((name.clone(), value))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok(Value::Adt {
                            name: name.clone(),
                            variant: position,
                            is_option: *is_option,
                            discriminant: variant.discriminant,
                            fields: fields.into(),
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(Value::Enum {
                    discriminant: Box::new(discriminant),
                    variants,
                    is_option: *is_option,
                })
            }
            InputKind::Array { element, count } => {
                let elements = (0..*count)
                    .map(|_| {
                        let value = self.child(element, start)?;
                        start = start
                            .checked_add(element.slots)
                            .ok_or("lazy input symbol range overflow")?;
                        Ok(value)
                    })
                    .collect::<Result<_, String>>()?;
                Ok(Value::Elements(elements))
            }
        }
    }
}

impl Value {
    pub fn materialize(&self) -> Result<Value, String> {
        match self {
            Self::Uninitialized => Err("read of an uninitialized coroutine saved local".to_owned()),
            Self::Input(input) => input.materialize(),
            value => Ok(value.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::Context;

    #[test]
    fn enum_array_occurrences_and_variant_payloads_keep_disjoint_symbols() {
        let scalar = Rc::new(InputShape {
            kind: InputKind::Integer {
                bits: 16,
                signed: false,
            },
            slots: 1,
            height: 1,
        });
        let element = Rc::new(InputShape {
            kind: InputKind::Enum {
                name: "Cases".into(),
                bits: 16,
                signed: true,
                is_option: false,
                variants: vec![
                    InputVariant {
                        discriminant: u128::MAX,
                        fields: vec![("0".into(), scalar.clone())],
                    },
                    InputVariant {
                        discriminant: 300,
                        fields: vec![("0".into(), scalar)],
                    },
                ],
            },
            slots: 5,
            height: 3,
        });
        let shape = Rc::new(InputShape {
            kind: InputKind::Array { element, count: 2 },
            slots: 11,
            height: 4,
        });
        let context = Context::default();
        let input = InputValue {
            shape,
            start: 0,
            seed: context.symbol(0, Sort::Bool).unwrap(),
        };
        let Value::Elements(elements) = input.materialize().unwrap() else {
            panic!("expected lazy input array");
        };
        let mut identifiers = Vec::new();
        for element in &elements {
            let Value::Enum {
                discriminant,
                variants,
                ..
            } = element.materialize().unwrap()
            else {
                panic!("expected lazy enum occurrence");
            };
            let selector = discriminant.integer().unwrap().0.symbols();
            assert_eq!(selector.len(), 1);
            identifiers.extend(selector);
            for variant in variants {
                let Value::Adt { fields, .. } = variant else {
                    panic!("expected enum payload variant");
                };
                identifiers.extend(fields[0].1.integer().unwrap().0.symbols());
            }
        }
        assert_eq!(identifiers, [2, 3, 5, 7, 8, 10]);
        let mut distinct = identifiers.clone();
        distinct.sort_unstable();
        distinct.dedup();
        assert_eq!(distinct.len(), identifiers.len());
        assert!(input.materialize().is_ok());
    }
}
