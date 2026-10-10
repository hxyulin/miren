//! Retained initialized enum tags remain separate from consumed payload observations.
use super::*;
use crate::symbolic::MemoryProjection;
use initialized_places::Step;

struct TagSchema {
    name: String,
    option: bool,
    variants: Vec<(u128, Vec<String>)>,
}

fn matches_variant(value: &Value, schema: &TagSchema, expected: Option<usize>) -> bool {
    let Value::Adt {
        name,
        variant,
        is_option,
        discriminant,
        fields,
    } = value
    else {
        return false;
    };
    let Some((tag, names)) = schema.variants.get(*variant) else {
        return false;
    };
    *name == schema.name
        && *is_option == schema.option
        && *discriminant == *tag
        && expected.is_none_or(|expected| expected == *variant)
        && fields.len() == names.len()
        && fields
            .iter()
            .zip(names)
            .all(|((name, _), expected)| name == expected)
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn retained_enum_tag(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        bits: u32,
        signed: bool,
    ) -> Result<Option<Value>, String> {
        let original = place.ty(&body.local_decls, self.tcx).ty;
        let ty::Adt(definition, _) = original.kind() else {
            return Ok(None);
        };
        if !definition.is_enum()
            || !place.projection.iter().all(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..) | ProjectionElem::Downcast(..)
                )
            })
        {
            return Ok(None);
        }
        let footprint = self.owned_field_footprint(body, place)?;
        let local = place.local.as_usize();
        let descendants = if let Some(allocation) = state.addresses[local] {
            state
                .memory
                .missing_places
                .descendants(allocation, &footprint)
        } else {
            state.missing_places.descendants(local, &footprint)
        }
        .map_err(|reason| self.categorized_error(UnknownCategory::Semantics, reason))?;
        if descendants.is_empty() {
            return Ok(None);
        }
        if descendants
            .iter()
            .any(|path| !matches!(path.as_slice(), [Step::Variant(_), Step::Field(_), ..]))
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "enum tag observation requires exact retained payload consumption".into(),
            ));
        }
        if self.integer_type(original.discriminant_ty(self.tcx)) != Some((bits, signed)) {
            return Err("enum tag differs from original compiler discriminant type".into());
        }
        let mut nodes = 1usize;
        for variant in definition.variants() {
            nodes = nodes
                .checked_add(1 + variant.fields.len())
                .ok_or("enum tag metadata size overflow")?;
            if nodes > typed_array_choices::MAX_CHOICE_NODES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "enum tag metadata exceeds the existing 512-node budget".into(),
                ));
            }
        }
        let schema = TagSchema {
            name: self.tcx.def_path_str(definition.did()),
            option: self.tcx.lang_items().get(LangItem::Option) == Some(definition.did()),
            variants: definition
                .variants()
                .iter_enumerated()
                .map(|(index, variant)| {
                    (
                        definition.discriminant_for_variant(self.tcx, index).val,
                        variant
                            .fields
                            .iter()
                            .map(|field| field.name.to_string())
                            .collect(),
                    )
                })
                .collect(),
        };
        // No initialized whole-value load or payload snapshot is performed.
        let mut value = self.raw_local(state, local)?;
        for projection in place.projection {
            let projection = match projection {
                ProjectionElem::Field(field, _) => MemoryProjection::Field(field.as_usize()),
                ProjectionElem::Downcast(_, variant) => {
                    MemoryProjection::Variant(variant.as_usize())
                }
                _ => return Err("enum tag path changed after certification".into()),
            };
            value = self.memory_projection(value, &projection, &state.conditions)?;
        }
        let value = value.materialize()?;
        let invalid = || {
            self.categorized_error(
                UnknownCategory::Semantics,
                "retained enum tag differs from exact original compiler metadata".into(),
            )
        };
        match value {
            value @ Value::Adt { .. } => {
                if !matches_variant(&value, &schema, None) {
                    return Err(invalid());
                }
                let Value::Adt { discriminant, .. } = value else {
                    unreachable!()
                };
                Ok(Some(symbolic::integer(
                    &self.terms,
                    discriminant,
                    bits,
                    signed,
                )))
            }
            Value::Enum {
                discriminant,
                variants,
                is_option,
            } => {
                if is_option != schema.option
                    || variants.len() != schema.variants.len()
                    || !variants
                        .iter()
                        .enumerate()
                        .all(|(index, variant)| matches_variant(variant, &schema, Some(index)))
                {
                    return Err(invalid());
                }
                let (term, width, sign) = discriminant.integer()?;
                if (width, sign) != (bits, signed)
                    || term.sort() != &Sort::BitVec(bits)
                    || !term.belongs_to(&self.terms)
                {
                    return Err(invalid());
                }
                let legal = schema.variants.iter().try_fold(
                    self.terms.boolean(false),
                    |legal, (tag, _)| {
                        let expected = symbolic::integer(&self.terms, *tag, bits, signed);
                        let equal =
                            symbolic::binary(&self.terms, "eq", (*discriminant).clone(), expected)?
                                .boolean()?;
                        self.terms.apply(Op::Or, &[legal, equal])
                    },
                )?;
                let mut conditions = state.conditions.clone();
                conditions.push(symbolic::not(&legal));
                if self.feasible(&conditions)? {
                    return Err(invalid());
                }
                Ok(Some(*discriminant))
            }
            _ => Err(invalid()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nominal_tags_reject_forged_inventory_without_observing_payloads() {
        let schema = TagSchema {
            name: "Choice".into(),
            option: false,
            variants: vec![(7, vec!["first".into(), "second".into()]), (9, Vec::new())],
        };
        let value = Value::Adt {
            name: "Choice".into(),
            variant: 0,
            discriminant: 7,
            is_option: false,
            fields: vec![
                ("first".into(), Value::Uninitialized),
                ("second".into(), Value::Unit),
            ]
            .into(),
        };
        assert!(matches_variant(&value, &schema, Some(0)));
        assert!(!matches_variant(&value, &schema, Some(1)));
        for change in 0..7 {
            let mut changed = value.clone();
            let Value::Adt {
                name,
                variant,
                discriminant,
                is_option,
                fields,
            } = &mut changed
            else {
                unreachable!()
            };
            match change {
                0 => *name = "Other".into(),
                1 => *variant = 2,
                2 => *discriminant = 9,
                3 => *is_option = true,
                4 => fields[0].0 = "renamed".into(),
                5 => *fields = vec![("first".into(), Value::Unit)].into(),
                6 => {
                    *fields = vec![
                        ("second".into(), Value::Unit),
                        ("first".into(), Value::Unit),
                    ]
                    .into()
                }
                _ => unreachable!(),
            }
            assert!(!matches_variant(&changed, &schema, None), "change {change}");
        }
        assert!(!matches_variant(&Value::Uninitialized, &schema, None));
    }
}
