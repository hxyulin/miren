//! Integer-repr fieldless enums retain their exact represented tag bits.
use super::*;
use rustc_abi::{BackendRepr, Primitive, Scalar, TagEncoding, Variants};

impl<'tcx> Engine<'tcx> {
    pub(super) fn fieldless_enum_integer_transmute(
        &mut self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Adt(def, _) = source.kind() else {
            return Ok(None);
        };
        if !def.is_enum() || self.integer_type(target).is_none() {
            return Ok(None);
        }
        if def.repr().int.is_none()
            || def.repr().c()
            || source.discriminant_ty(self.tcx) != target
            || def.variants().is_empty()
            || def.variants().len() > 256
            || def
                .variants()
                .iter()
                .any(|variant| !variant.fields.is_empty())
            || source.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err(
                "enum transmute needs a bounded non-Drop fieldless exact integer repr".into(),
            );
        }
        let (bits, signed) = self
            .integer_type(target)
            .ok_or("enum target integer type")?;
        let layout = self.static_layout(source)?;
        let integer_layout = self.static_layout(target)?;
        let Variants::Multiple {
            tag,
            tag_encoding: TagEncoding::Direct,
            tag_field,
            variants,
        } = &layout.variants
        else {
            return Err("enum transmute requires a compiler direct initialized scalar tag".into());
        };
        if layout.size != integer_layout.size
            || layout.align.abi != integer_layout.align.abi
            || layout.fields.offset(tag_field.as_usize()).bytes() != 0
            || layout.backend_repr != BackendRepr::Scalar(*tag)
            || !matches!(tag, Scalar::Initialized { value: Primitive::Int(width, actual_signed), .. }
                if width.size().bits() == u64::from(bits) && *actual_signed == signed)
            || variants.len() != def.variants().len()
            || variants.iter().any(|variant| {
                !variant.field_offsets.is_empty() || variant.size != integer_layout.size
            })
        {
            return Err(
                "enum transmute lacks matching direct primitive size, alignment and tag".into(),
            );
        }
        let Scalar::Initialized { valid_range, .. } = tag else {
            return Err("enum transmute requires an initialized tag validity range".into());
        };
        let mask = integer_mask(bits);
        let tags = def
            .variants()
            .iter_enumerated()
            .map(|(index, _)| def.discriminant_for_variant(self.tcx, index).val)
            .collect::<Vec<_>>();
        if tags.iter().any(|tag| !valid_range.contains(*tag & mask)) {
            return Err(
                "enum represented tag is outside the compiler scalar validity range".into(),
            );
        }
        let name = self.tcx.def_path_str(def.did());
        let is_option = self.tcx.lang_items().get(LangItem::Option) == Some(def.did());
        let (expression, valid) =
            fieldless_enum_bits(&self.terms, value, &name, &tags, bits, signed, is_option)?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&valid)]].concat())? {
            return Err("enum transmute symbolic tag lacks proven exact variant membership".into());
        }
        Ok(Some(Value::Int {
            expression,
            bits,
            signed,
        }))
    }
}

fn integer_mask(bits: u32) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn fieldless_enum_bits(
    terms: &Context,
    value: &Value,
    name: &str,
    tags: &[u128],
    bits: u32,
    signed: bool,
    is_option: bool,
) -> Result<(Term, Term), String> {
    if !(1..=128).contains(&bits) || tags.is_empty() || tags.len() > 256 {
        return Err("enum transmute requires bounded tag width and inventory".into());
    }
    let mask = integer_mask(bits);
    let mut represented = Vec::new();
    for tag in tags {
        let tag = *tag & mask;
        if represented.contains(&tag) {
            return Err("enum represented tags must be distinct".into());
        }
        represented.push(tag);
    }
    let validate_variant = |value: &Value, position: usize| -> Result<(), String> {
        let Value::Adt {
            name: actual_name,
            variant,
            is_option: actual_option,
            discriminant,
            fields,
        } = value
        else {
            return Err("enum transmute needs exact compiler variant storage".into());
        };
        if actual_name != name
            || *variant != position
            || *actual_option != is_option
            || *discriminant != tags[position]
            || !fields.is_empty()
        {
            return Err(
                "enum transmute variant identity or exact tag disagrees with compiler".into(),
            );
        }
        Ok(())
    };
    let expression = if let Value::Adt { variant, .. } = value {
        if *variant >= tags.len() {
            return Err("enum variant is outside compiler inventory".into());
        }
        validate_variant(value, *variant)?;
        terms.bit_vector(represented[*variant], bits)?
    } else if let Value::Enum {
        discriminant,
        variants,
        is_option: actual_option,
    } = value
    {
        if *actual_option != is_option || variants.len() != tags.len() {
            return Err("enum transmute requires the complete exact compiler inventory".into());
        }
        for (position, variant) in variants.iter().enumerate() {
            validate_variant(variant, position)?;
        }
        let (expression, actual_bits, actual_signed) = discriminant.integer()?;
        if actual_bits != bits
            || actual_signed != signed
            || expression.sort() != &Sort::BitVec(bits)
            || !expression.belongs_to(terms)
        {
            return Err("enum transmute symbolic tag has wrong type, sort or context".into());
        }
        expression
    } else {
        return Err("enum transmute source has no certified fieldless variant value".into());
    };
    let membership = represented
        .iter()
        .map(|tag| {
            terms.apply(
                Op::Equal,
                &[expression.clone(), terms.bit_vector(*tag, bits)?],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((expression, terms.apply(Op::Or, &membership)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use miren::smt::Constant;
    const NEGATIVE: u128 = (-7_i128) as u128;
    fn variant(position: usize, tag: u128) -> Value {
        Value::Adt {
            name: "fixture::Sparse".into(),
            variant: position,
            is_option: false,
            discriminant: tag,
            fields: vec![].into(),
        }
    }
    fn value(expression: Term, bits: u32, signed: bool) -> Value {
        Value::Enum {
            discriminant: Box::new(Value::Int {
                expression,
                bits,
                signed,
            }),
            variants: vec![variant(0, NEGATIVE), variant(1, 9)],
            is_option: false,
        }
    }
    fn select(terms: &Context, value: &Value) -> Result<(Term, Term), String> {
        fieldless_enum_bits(
            terms,
            value,
            "fixture::Sparse",
            &[NEGATIVE, 9],
            8,
            true,
            false,
        )
    }
    #[test]
    fn exact_inventory_rejects_forged_variant_metadata() {
        let terms = Context::default();
        let original = variant(0, NEGATIVE);
        select(&terms, &original).unwrap();
        for change in 0..5 {
            let mut forged = original.clone();
            let Value::Adt {
                name,
                variant,
                is_option,
                discriminant,
                fields,
            } = &mut forged
            else {
                unreachable!()
            };
            match change {
                0 => *name = "other::Sparse".into(),
                1 => *variant = 3,
                2 => *is_option = true,
                3 => *discriminant = 249,
                4 => fields.push(("payload".into(), Value::Unit)),
                _ => unreachable!(),
            }
            assert!(select(&terms, &forged).is_err());
        }
        let mut partial = value(terms.bit_vector(9, 8).unwrap(), 8, true);
        if let Value::Enum { variants, .. } = &mut partial {
            variants.pop();
        }
        assert!(select(&terms, &partial).is_err());
    }
    #[test]
    fn symbolic_tags_reject_foreign_context_sort_width_and_sign() {
        let terms = Context::default();
        let foreign = Context::default();
        for forged in [
            value(foreign.bit_vector(9, 8).unwrap(), 8, true),
            value(terms.bit_vector(9, 16).unwrap(), 8, true),
            value(terms.boolean(true), 8, true),
            value(terms.bit_vector(9, 8).unwrap(), 16, true),
            value(terms.bit_vector(9, 8).unwrap(), 8, false),
        ] {
            assert!(select(&terms, &forged).is_err());
        }
    }
    #[test]
    fn sparse_membership_retains_holes_and_exact_signed_bits() {
        let terms = Context::default();
        for tag in [249, 9] {
            let (_, membership) =
                select(&terms, &value(terms.bit_vector(tag, 8).unwrap(), 8, true)).unwrap();
            assert_eq!(membership.constant(), Some(Constant::Bool(true)));
        }
        let (_, membership) =
            select(&terms, &value(terms.bit_vector(0, 8).unwrap(), 8, true)).unwrap();
        assert_eq!(membership.constant(), Some(Constant::Bool(false)));
        assert!(
            fieldless_enum_bits(
                &terms,
                &variant(0, u128::MAX),
                "fixture::Sparse",
                &[u128::MAX, 255],
                8,
                true,
                false
            )
            .is_err()
        );
        let (bits, _) = select(&terms, &variant(0, NEGATIVE)).unwrap();
        assert_eq!(bits.constant(), Some(Constant::BitVec(249)));
    }
}
