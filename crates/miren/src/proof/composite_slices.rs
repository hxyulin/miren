//! Typed incoming aggregate slice observations, without physical or mutable access rights.
use super::*;
use scalar_slices::{decode_scalar_element, scalar_slice_sort};
use symbolic::ScalarSliceElement;

const MAX_SHAPE_NODES: usize = 512;
const MAX_SHAPE_DEPTH: usize = 16;
const MAX_TYPE_ARRAY: u64 = 128;

#[derive(Clone, Debug)]
pub(super) enum CompositeShape {
    Primitive(ScalarSliceElement),
    Tuple(Vec<CompositeShape>),
    Array(Vec<CompositeShape>),
}

#[derive(Clone, Debug)]
pub(super) struct CompositeType<'tcx> {
    pub(super) ty: Ty<'tcx>,
    shape: CompositeShape,
    leaves: Vec<ScalarSliceElement>,
    bytes: u64,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn composite_slice_shape(
        &self,
        ty: Ty<'tcx>,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        if !matches!(ty.kind(), ty::Tuple(_) | ty::Array(..)) {
            return Ok(None);
        }
        let mut nodes = 0;
        let Some(shape) = self.composite_shape_depth(ty, 0, &mut nodes)? else {
            return Ok(None);
        };
        let bytes = self.static_layout(ty)?.size.bytes();
        if bytes == 0 {
            return Ok(None);
        }
        let mut leaves = Vec::new();
        shape.leaves(&mut leaves);
        Ok(Some(CompositeType {
            ty,
            shape,
            leaves,
            bytes,
        }))
    }

    fn composite_shape_depth(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<CompositeShape>, String> {
        if depth >= MAX_SHAPE_DEPTH || *nodes >= MAX_SHAPE_NODES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "composite slice type exceeds its depth or expanded node budget".into(),
            ));
        }
        *nodes += 1;
        // Original kinds are inspected before any normalization: Pat and identity-bearing
        // wrappers remain unsupported even beneath zero-length arrays.
        let env = ty::TypingEnv::fully_monomorphized();
        if !ty.is_freeze(self.tcx, env)
            || !self.tcx.type_is_copy_modulo_regions(env, ty)
            || ty.needs_drop(self.tcx, env)
        {
            return Ok(None);
        }
        let layout = self.static_layout(ty)?;
        if layout.align.abi.bytes() == 0 || !layout.align.abi.bytes().is_power_of_two() {
            return Err("composite slice type has inconsistent compiler alignment".into());
        }
        if let Some(leaf) = self.scalar_slice_element(ty)? {
            return Ok(Some(CompositeShape::Primitive(leaf)));
        }
        match ty.kind() {
            ty::Tuple(fields) => {
                let mut shapes = Vec::new();
                for field in fields.iter() {
                    let Some(shape) = self.composite_shape_depth(field, depth + 1, nodes)? else {
                        return Ok(None);
                    };
                    shapes.push(shape);
                }
                Ok(Some(CompositeShape::Tuple(shapes)))
            }
            ty::Array(element, count) => {
                let Some(count) = count.try_to_target_usize(self.tcx) else {
                    return Ok(None);
                };
                if count > MAX_TYPE_ARRAY {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "composite slice type array exceeds the 128-element shape budget".into(),
                    ));
                }
                // Certify the original element even for N=0, then charge every actual
                // occurrence independently. A zero array's type probe is conservative.
                let Some(first) = self.composite_shape_depth(*element, depth + 1, nodes)? else {
                    return Ok(None);
                };
                let mut shapes = Vec::new();
                if count > 0 {
                    shapes.push(first);
                    for _ in 1..count {
                        let Some(shape) = self.composite_shape_depth(*element, depth + 1, nodes)?
                        else {
                            return Ok(None);
                        };
                        shapes.push(shape);
                    }
                }
                Ok(Some(CompositeShape::Array(shapes)))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn composite_slice_input(
        &mut self,
        root: DefId,
        ty: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        if self.building_mutable_input {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "mutable composite slice input is unsupported".into(),
            ));
        }
        let descriptor = self.composite_slice_shape(ty)?.ok_or_else(|| {
            self.categorized_error(
                UnknownCategory::Semantics,
                "composite slice requires a nonzero-sized pure tuple or array element".into(),
            )
        })?;
        let count = descriptor.leaves.len() + 1;
        if self
            .input_values
            .checked_add(count)
            .is_none_or(|n| n > MAX_INPUT_VALUES)
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "composite slice input exceeds the 512-value budget".into(),
            ));
        }
        self.input_values += count;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max = ((1_u128 << (bits - 1)) - 1) / u128::from(descriptor.bytes);
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let leaves = descriptor
            .leaves
            .iter()
            .map(|leaf| {
                Ok(self.fresh(Sort::Array(
                    Box::new(Sort::BitVec(bits)),
                    Box::new(scalar_slice_sort(*leaf)?),
                )))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let id = if let Some(id) = self.composite_slice_types.iter().position(|d| d.ty == ty) {
            id
        } else {
            let id = self.composite_slice_types.len();
            self.composite_slice_types.push(descriptor);
            id
        };
        self.record_model(
            root,
            "readonly composite slice; exact compiler shape and independent primitive leaf arrays",
        );
        Ok(Value::CompositeSlice {
            id,
            length: Box::new(Value::Int {
                expression: length,
                bits,
                signed: false,
            }),
            leaves,
        })
    }

    pub(super) fn composite_slice_length(
        &self,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::CompositeSlice { id, length, leaves } = value else {
            return Err("expected initialized readonly composite slice".into());
        };
        let descriptor = self
            .composite_slice_types
            .get(*id)
            .ok_or("composite slice compiler descriptor is absent")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        validate_terms(&self.terms, bits, &descriptor.leaves, length, leaves)?;
        let max = ((1_u128 << (bits - 1)) - 1) / u128::from(descriptor.bytes);
        let safe = self.terms.apply(
            Op::BvUnsignedLe,
            &[length.integer()?.0, self.terms.bit_vector(max, bits)?],
        )?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
            return Err("composite slice lacks valid target allocation extent".into());
        }
        Ok((**length).clone())
    }

    pub(super) fn composite_slice_select(
        &self,
        source: &Value,
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let length = self.composite_slice_length(source, conditions)?;
        let (term, bits, signed) = index.integer()?;
        if bits != u32::from(self.tcx.sess.target.pointer_width)
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("composite slice index requires exact target usize".into());
        }
        self.memory_bounds(index, &length, conditions)?;
        let Value::CompositeSlice { id, leaves, .. } = source else {
            unreachable!()
        };
        let descriptor = &self.composite_slice_types[*id];
        let mut cursor = 0;
        let value = descriptor
            .shape
            .observe(&self.terms, leaves, &term, &mut cursor)?;
        if cursor != leaves.len() {
            return Err("composite observation omitted primitive leaf storage".into());
        }
        Ok(value)
    }

    pub(super) fn composite_slice_region(
        &self,
        source: &Value,
        offset: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let capacity = self.composite_slice_length(source, conditions)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for value in [offset, length] {
            let (term, width, signed) = value.integer()?;
            if width != bits
                || signed
                || term.sort() != &Sort::BitVec(bits)
                || !term.belongs_to(&self.terms)
            {
                return Err("composite slice region requires exact target usize".into());
            }
        }
        let within =
            symbolic::binary(&self.terms, "le", offset.clone(), capacity.clone())?.boolean()?;
        let available = symbolic::binary(&self.terms, "sub", capacity, offset.clone())?;
        let fits = symbolic::binary(&self.terms, "le", length.clone(), available)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[within, fits])?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
            return Err("composite slice view lacks proven region bounds".into());
        }
        let Value::CompositeSlice { id, leaves, .. } = source else {
            unreachable!()
        };
        Ok(Value::CompositeSlice {
            id: *id,
            length: Box::new(length.clone()),
            leaves: leaves
                .iter()
                .map(|data| {
                    self.terms
                        .apply(Op::ArrayOffset, &[data.clone(), offset.integer()?.0])
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

fn validate_terms(
    context: &Context,
    pointer_bits: u32,
    types: &[ScalarSliceElement],
    length: &Value,
    leaves: &[Term],
) -> Result<(), String> {
    let (term, bits, signed) = length.integer()?;
    if bits != pointer_bits
        || signed
        || term.sort() != &Sort::BitVec(bits)
        || !term.belongs_to(context)
        || leaves.len() != types.len()
    {
        return Err("composite slice length or leaf inventory metadata mismatch".into());
    }
    for (data, leaf) in leaves.iter().zip(types) {
        let expected = Sort::Array(
            Box::new(Sort::BitVec(bits)),
            Box::new(scalar_slice_sort(*leaf)?),
        );
        if data.sort() != &expected || !data.belongs_to(context) {
            return Err("composite slice leaf has incorrect sort or analysis context".into());
        }
    }
    Ok(())
}

impl CompositeShape {
    fn leaves(&self, output: &mut Vec<ScalarSliceElement>) {
        match self {
            Self::Primitive(leaf) => output.push(*leaf),
            Self::Tuple(fields) | Self::Array(fields) => {
                for field in fields {
                    field.leaves(output);
                }
            }
        }
    }

    fn observe(
        &self,
        context: &Context,
        leaves: &[Term],
        index: &Term,
        cursor: &mut usize,
    ) -> Result<Value, String> {
        match self {
            Self::Primitive(leaf) => {
                let data = leaves
                    .get(*cursor)
                    .ok_or("composite leaf storage missing")?;
                *cursor += 1;
                decode_scalar_element(
                    context,
                    *leaf,
                    context.apply(Op::Select, &[data.clone(), index.clone()])?,
                )
            }
            Self::Tuple(fields) | Self::Array(fields) => {
                let values = fields
                    .iter()
                    .map(|field| field.observe(context, leaves, index, cursor))
                    .collect::<Result<Vec<_>, _>>()?;
                match self {
                    Self::Tuple(_) if values.is_empty() => Ok(Value::Unit),
                    Self::Tuple(_) => Ok(Value::Tuple(values)),
                    Self::Array(_) => Ok(Value::Elements(values.into())),
                    Self::Primitive(_) => unreachable!(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composite_metadata_rejects_foreign_sorts_lengths_and_leaf_inventories() {
        let context = Context::default();
        let kinds = [
            ScalarSliceElement::Integer {
                bits: 16,
                signed: false,
            },
            ScalarSliceElement::Bool,
        ];
        let length = symbolic::integer(&context, 2, 64, false);
        let leaves: Vec<_> = kinds
            .iter()
            .enumerate()
            .map(|(i, leaf)| {
                context
                    .symbol(
                        i as u32,
                        Sort::Array(
                            Box::new(Sort::BitVec(64)),
                            Box::new(scalar_slice_sort(*leaf).unwrap()),
                        ),
                    )
                    .unwrap()
            })
            .collect();
        assert!(validate_terms(&context, 64, &kinds, &length, &leaves).is_ok());
        assert!(validate_terms(&context, 64, &kinds, &length, &leaves[..1]).is_err());
        let mut swapped = leaves.clone();
        swapped.swap(0, 1);
        assert!(validate_terms(&context, 64, &kinds, &length, &swapped).is_err());
        assert!(validate_terms(&context, 32, &kinds, &length, &leaves).is_err());
        let signed = symbolic::integer(&context, 2, 64, true);
        assert!(validate_terms(&context, 64, &kinds, &signed, &leaves).is_err());
        let other = Context::default();
        let foreign = symbolic::integer(&other, 2, 64, false);
        assert!(validate_terms(&context, 64, &kinds, &foreign, &leaves).is_err());
        let foreign_leaf = other.symbol(0, leaves[0].sort().clone()).unwrap();
        let bad = [foreign_leaf, leaves[1].clone()];
        assert!(validate_terms(&context, 64, &kinds, &length, &bad).is_err());
    }

    #[test]
    fn composite_occurrences_reconstruct_distinct_slots_and_stable_selected_values() {
        let context = Context::default();
        let kind = ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        };
        let shape = CompositeShape::Tuple(vec![
            CompositeShape::Primitive(kind),
            CompositeShape::Array(vec![
                CompositeShape::Primitive(kind),
                CompositeShape::Primitive(kind),
            ]),
            CompositeShape::Tuple(Vec::new()),
        ]);
        let mut types = Vec::new();
        shape.leaves(&mut types);
        assert_eq!(types, vec![kind; 3]);
        let leaves: Vec<_> = (0..3)
            .map(|i| {
                context
                    .symbol(
                        i,
                        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(16))),
                    )
                    .unwrap()
            })
            .collect();
        let index = context.symbol(3, Sort::BitVec(64)).unwrap();
        let mut cursor = 0;
        let first = shape
            .observe(&context, &leaves, &index, &mut cursor)
            .unwrap();
        assert_eq!(cursor, 3);
        let Value::Tuple(fields) = &first else {
            panic!("tuple reconstruction")
        };
        let Value::Elements(inner) = &fields[1] else {
            panic!("array reconstruction")
        };
        let terms = [&fields[0], &inner[0], &inner[1]].map(|v| v.integer().unwrap().0);
        for (i, term) in terms.iter().enumerate() {
            assert_eq!(
                term.symbols(),
                std::collections::BTreeSet::from([i as u32, 3])
            );
        }
        assert_ne!(terms[0], terms[1]);
        assert_ne!(terms[1], terms[2]);
        assert!(matches!(fields[2], Value::Unit));
        let mut cursor = 0;
        let Value::Tuple(second) = shape
            .observe(&context, &leaves, &index, &mut cursor)
            .unwrap()
        else {
            panic!("stable reconstruction")
        };
        assert_eq!(
            fields[0].integer().unwrap().0,
            second[0].integer().unwrap().0
        );
        let mut cursor = 0;
        assert!(
            shape
                .observe(&context, &leaves[..2], &index, &mut cursor)
                .is_err()
        );
    }
}
