//! Namespace evidence for lazy inputs actually issued by this Engine.
use super::*;
use std::rc::Rc;
use symbolic::input::{InputKind, InputShape, InputValue};

pub(super) struct IssuedInput<'tcx> {
    pub(super) original: Ty<'tcx>,
    pub(super) reservation: InputReservation,
}

pub(super) struct InputReservation {
    pub(super) shape: Rc<InputShape>,
    pub(super) seed: Term,
    pub(super) start: u32,
    pub(super) end: u32,
}

struct ProductQuery<'a, 'tcx> {
    root: &'a IssuedInput<'tcx>,
    expected: Ty<'tcx>,
    input: &'a InputValue,
}

impl InputReservation {
    fn validate(&self, context: &Context, input: &InputValue) -> Result<(), String> {
        if self.seed.sort() != &Sort::Bool
            || !self.seed.belongs_to(context)
            || self.seed.symbol_index() != Some(self.start)
            || input.seed != self.seed
            || self.shape.slots == 0
            || self.start.checked_add(self.shape.slots) != Some(self.end)
            || self.end > 262_144
            || input.start < self.start
            || input
                .start
                .checked_add(input.shape.slots)
                .is_none_or(|end| end > self.end)
            || input.shape.slots == 0
        {
            return Err("deferred product does not match an issued input reservation".into());
        }
        Ok(())
    }

    fn exact_node(&self, input: &InputValue, shape: &Rc<InputShape>, start: u32) -> bool {
        input.seed == self.seed && input.start == start && Rc::ptr_eq(&input.shape, shape)
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn validate_issued_product(
        &self,
        original: Ty<'tcx>,
        input: &InputValue,
    ) -> Result<(), String> {
        let missing = || {
            self.categorized_error(
                UnknownCategory::Semantics,
                "deferred owned products with scalar leaves need a source reservation certificate"
                    .into(),
            )
        };
        let Some(root) = self
            .input_reservations
            .iter()
            .find(|root| root.reservation.seed == input.seed)
        else {
            return Err(missing());
        };
        root.reservation.validate(&self.terms, input)?;
        // Namespace issuance alone is not purity. Certify the complete original root,
        // including raw field types and unused array elements, before ancestor descent.
        if self.owned_product_shape(root.original)?.is_none() {
            return Err(missing());
        }
        let query = ProductQuery {
            root,
            expected: original,
            input,
        };
        if !self.issued_product_path(
            &query,
            root.original,
            &root.reservation.shape,
            root.reservation.start,
            0,
        )? {
            return Err(missing());
        }
        Ok(())
    }

    fn issued_product_path(
        &self,
        query: &ProductQuery<'_, 'tcx>,
        original: Ty<'tcx>,
        shape: &Rc<InputShape>,
        start: u32,
        depth: usize,
    ) -> Result<bool, String> {
        let ProductQuery {
            root,
            expected,
            input,
        } = query;
        if depth >= typed_array_choices::MAX_CHOICE_DEPTH {
            return Err("issued input path exceeds its depth budget".into());
        }
        if root.reservation.exact_node(input, shape, start) {
            return Ok(original == *expected);
        }
        let first = start
            .checked_add(1)
            .ok_or("issued input path offset overflow")?;
        match (original.kind(), &shape.kind) {
            (
                ty::Array(element_ty, count),
                InputKind::Array {
                    element,
                    count: actual,
                },
            ) if count.try_to_target_usize(self.tcx) == Some(*actual as u64) => {
                let Some(child) = array_child_start(first, element.slots, *actual, input.start)?
                else {
                    return Ok(false);
                };
                self.issued_product_path(query, *element_ty, element, child, depth + 1)
            }
            (ty::Tuple(types), InputKind::Tuple(fields)) if types.len() == fields.len() => {
                let mut offset = first;
                for (ty, field) in types.iter().zip(fields) {
                    let end = offset
                        .checked_add(field.slots)
                        .ok_or("issued input field overflow")?;
                    if (offset..end).contains(&input.start) {
                        return self.issued_product_path(query, ty, field, offset, depth + 1);
                    }
                    offset = end;
                }
                Ok(false)
            }
            (ty::Adt(def, args), InputKind::Struct { name, fields })
                if self.plain_composite_struct(*def)
                    && self.tcx.def_path_str(def.did()) == *name
                    && def.non_enum_variant().fields.len() == fields.len() =>
            {
                let mut offset = first;
                for (field, (name, shape)) in def.non_enum_variant().fields.iter().zip(fields) {
                    if field.name.as_str() != name {
                        return Err("issued input path field identity mismatch".into());
                    }
                    let end = offset
                        .checked_add(shape.slots)
                        .ok_or("issued input field overflow")?;
                    if (offset..end).contains(&input.start) {
                        return self.issued_product_path(
                            query,
                            field.ty(self.tcx, args).skip_norm_wip(),
                            shape,
                            offset,
                            depth + 1,
                        );
                    }
                    offset = end;
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }
}

fn array_child_start(
    first: u32,
    slots: u32,
    count: usize,
    target: u32,
) -> Result<Option<u32>, String> {
    if slots == 0 {
        return Err("issued input array child has zero slots".into());
    }
    let Some(delta) = target.checked_sub(first) else {
        return Ok(None);
    };
    let position = delta / slots;
    if u64::from(position) >= count as u64 {
        return Ok(None);
    }
    let start = first
        .checked_add(
            position
                .checked_mul(slots)
                .ok_or("issued input array overflow")?,
        )
        .ok_or("issued input array overflow")?;
    start
        .checked_add(slots)
        .ok_or("issued input array overflow")?;
    Ok(Some(start))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar() -> Rc<InputShape> {
        Rc::new(InputShape {
            kind: InputKind::Integer {
                bits: 16,
                signed: false,
            },
            slots: 1,
            height: 1,
        })
    }

    #[test]
    fn issued_namespaces_preserve_copies_and_distinguish_shared_shapes_and_offsets() {
        let context = Context::default();
        let leaf = scalar();
        let shape = Rc::new(InputShape {
            kind: InputKind::Tuple(vec![leaf.clone(), leaf.clone()]),
            slots: 3,
            height: 2,
        });
        let first = InputReservation {
            shape: shape.clone(),
            seed: context.symbol(0, Sort::Bool).unwrap(),
            start: 0,
            end: 3,
        };
        let second = InputReservation {
            shape: shape.clone(),
            seed: context.symbol(3, Sort::Bool).unwrap(),
            start: 3,
            end: 6,
        };
        let input = InputValue {
            shape: leaf.clone(),
            start: 1,
            seed: first.seed.clone(),
        };
        first.validate(&context, &input).unwrap();
        assert!(first.exact_node(&input, &leaf, 1));
        assert!(first.exact_node(&input.clone(), &leaf, 1));
        assert_eq!(
            input.materialize().unwrap().integer().unwrap().0,
            input.clone().materialize().unwrap().integer().unwrap().0
        );
        let sibling = InputValue {
            start: 2,
            ..input.clone()
        };
        assert!(!first.exact_node(&sibling, &leaf, 1));
        assert_ne!(
            input.materialize().unwrap().integer().unwrap().0,
            sibling.materialize().unwrap().integer().unwrap().0
        );
        let other = InputValue {
            start: 4,
            seed: second.seed.clone(),
            ..input.clone()
        };
        second.validate(&context, &other).unwrap();
        assert!(second.exact_node(&other, &leaf, 4));
        assert!(first.validate(&context, &other).is_err());
        assert_ne!(
            input.materialize().unwrap().integer().unwrap().0,
            other.materialize().unwrap().integer().unwrap().0
        );
        let fake = InputValue {
            shape: Rc::new(leaf.as_ref().clone()),
            ..input.clone()
        };
        assert!(!first.exact_node(&fake, &leaf, 1));
        let foreign = Context::default();
        assert!(
            first
                .validate(
                    &context,
                    &InputValue {
                        seed: foreign.symbol(0, Sort::Bool).unwrap(),
                        ..input.clone()
                    }
                )
                .is_err()
        );
        assert!(
            first
                .validate(
                    &context,
                    &InputValue {
                        seed: context.boolean(false),
                        ..input.clone()
                    }
                )
                .is_err()
        );
        assert!(
            first
                .validate(
                    &context,
                    &InputValue {
                        start: u32::MAX,
                        ..input.clone()
                    }
                )
                .is_err()
        );
        let invalid = InputReservation { end: 2, ..first };
        assert!(invalid.validate(&context, &input).is_err());
    }

    #[test]
    fn issued_array_paths_bound_occurrences_without_enumerating_or_creating_empty_children() {
        assert_eq!(array_child_start(1, 3, 64, 1).unwrap(), Some(1));
        assert_eq!(array_child_start(1, 3, 64, 2).unwrap(), Some(1));
        assert_eq!(array_child_start(1, 3, 64, 190).unwrap(), Some(190));
        assert_eq!(array_child_start(1, 3, 64, 191).unwrap(), Some(190));
        assert_eq!(array_child_start(1, 3, 64, 193).unwrap(), None);
        assert_eq!(array_child_start(1, 3, 64, 0).unwrap(), None);
        assert_eq!(array_child_start(1, 3, 0, 1).unwrap(), None);
        assert!(array_child_start(1, 0, 1, 1).is_err());
        assert!(array_child_start(u32::MAX - 1, 3, 1, u32::MAX - 1).is_err());
    }
}
