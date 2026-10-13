use super::*;
use rustc_abi::{BackendRepr, FieldIdx, Primitive, Scalar, TagEncoding, Variants};

impl<'tcx> Engine<'tcx> {
    pub(super) fn integer_nonzero_option_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
    ) -> Result<Option<Value>, String> {
        if !matches!(source.kind(), ty::Int(_) | ty::Uint(_)) {
            return Ok(None);
        }
        let ty::Adt(option, option_args) = target.kind() else {
            return Ok(None);
        };
        if self.tcx.lang_items().get(LangItem::Option) != Some(option.did()) {
            return Ok(None);
        }
        let nonzero_ty = option_args.type_at(0);
        let ty::Adt(nonzero, nonzero_args) = nonzero_ty.kind() else {
            return Ok(None);
        };
        if !self
            .tcx
            .is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), nonzero.did())
            || nonzero.did().krate != option.did().krate
            || !nonzero.is_struct()
            || nonzero_args.type_at(0) != source
        {
            return Ok(None);
        }
        if !option.is_enum()
            || option_args.len() != 1
            || nonzero_args.len() != 1
            || option.variants().len() != 2
            || nonzero.non_enum_variant().fields.len() != 1
        {
            return Err("optional NonZero compiler field shape mismatch".into());
        }
        let none = rustc_abi::VariantIdx::from_usize(0);
        let some = rustc_abi::VariantIdx::from_usize(1);
        if !option.variant(none).fields.is_empty()
            || option.variant(some).fields.len() != 1
            || option.variant(none).name.as_str() != "None"
            || option.variant(some).name.as_str() != "Some"
        {
            return Err("optional NonZero compiler variant shape mismatch".into());
        }
        let env = ty::TypingEnv::fully_monomorphized();
        if self
            .tcx
            .try_normalize_erasing_regions(
                env,
                option.variant(some).fields[FieldIdx::from_usize(0)].ty(self.tcx, option_args),
            )
            .map_err(|error| format!("optional NonZero field normalization failed: {error:?}"))?
            != nonzero_ty
        {
            return Err("optional NonZero payload identity mismatch".into());
        }
        let inner_ty = self.nonzero_integer_inner(nonzero_ty, source)?;
        let (bits, signed) = self
            .integer_type(source)
            .ok_or("optional NonZero primitive integer type")?;
        let source_layout = self.static_layout(source)?;
        let option_layout = self.static_layout(target)?;
        let nonzero_layout = self.static_layout(nonzero_ty)?;
        let inner_layout = self.static_layout(inner_ty)?;
        let field = FieldIdx::from_usize(0);
        if !nonzero_integer_scalar(source_layout.backend_repr, bits, signed, 0)
            || !nonzero_integer_scalar(option_layout.backend_repr, bits, signed, 0)
            || !nonzero_integer_scalar(nonzero_layout.backend_repr, bits, signed, 1)
            || !nonzero_integer_scalar(inner_layout.backend_repr, bits, signed, 1)
            || [option_layout, nonzero_layout, inner_layout]
                .iter()
                .any(|layout| {
                    layout.size != source_layout.size || layout.align.abi != source_layout.align.abi
                })
            || nonzero_layout.fields.offset(0).bytes() != 0
            || inner_layout.fields.offset(0).bytes() != 0
        {
            return Err(
                "optional NonZero requires equal-width initialized zero-only scalar layout".into(),
            );
        }
        let Variants::Multiple {
            tag,
            tag_encoding:
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                },
            tag_field,
            ref variants,
        } = option_layout.variants
        else {
            return Err("optional NonZero requires compiler niche encoding".into());
        };
        if untagged_variant != some
            || niche_variants.start != none
            || niche_variants.last != none
            || niche_start != 0
            || tag_field != field
            || option_layout.fields.offset(tag_field.as_usize()).bytes() != 0
            || variants.len() != 2
            || !variants[none].field_offsets.is_empty()
            || variants[some].size != source_layout.size
            || variants[some].field_offsets.len() != 1
            || variants[some].field_offsets[field].bytes() != 0
            || !nonzero_integer_scalar(BackendRepr::Scalar(tag), bits, signed, 0)
        {
            return Err("optional NonZero requires exactly None at the zero niche".into());
        }
        let (expression, actual_bits, actual_signed) = value.integer()?;
        if actual_bits != bits
            || actual_signed != signed
            || expression.sort() != &Sort::BitVec(bits)
            || !expression.belongs_to(&self.terms)
        {
            return Err("optional NonZero input scalar type or context mismatch".into());
        }
        // The payload reuses the source bits without adding a nonzero path constraint.
        // Existing enum downcast checks make it usable only on the selected Some branch.
        let inner_value = self.constructed(inner_ty, 0, vec![value.clone()])?;
        let payload = self.constructed(nonzero_ty, 0, vec![inner_value])?;
        let variants = vec![
            self.constructed(target, 0, vec![])?,
            self.constructed(target, 1, vec![payload])?,
        ];
        let (tag_bits, tag_signed) = self
            .integer_type(target.discriminant_ty(self.tcx))
            .ok_or("optional NonZero discriminant type is unsupported")?;
        let tags = [
            option.discriminant_for_variant(self.tcx, none).val,
            option.discriminant_for_variant(self.tcx, some).val,
        ];
        let zero = self
            .terms
            .apply(Op::Equal, &[expression, self.terms.bit_vector(0, bits)?])?;
        let discriminant = Value::Int {
            expression: self.terms.apply(
                Op::Ite,
                &[
                    zero,
                    self.terms.bit_vector(tags[0], tag_bits)?,
                    self.terms.bit_vector(tags[1], tag_bits)?,
                ],
            )?,
            bits: tag_bits,
            signed: tag_signed,
        };
        Ok(Some(Value::Enum {
            discriminant: Box::new(discriminant),
            variants,
            is_option: true,
        }))
    }

    pub(super) fn nonzero_integer_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        if !matches!(target.kind(), ty::Int(_) | ty::Uint(_)) {
            return Ok(None);
        }
        let ty::Adt(nonzero, args) = source.kind() else {
            return Ok(None);
        };
        if !self
            .tcx
            .is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), nonzero.did())
            || args.len() != 1
            || args.type_at(0) != target
        {
            return Ok(None);
        }
        let inner_ty = self.nonzero_integer_inner(source, target)?;
        let (bits, signed) = self
            .integer_type(target)
            .ok_or("NonZero primitive integer type")?;
        let primitive = self.static_layout(target)?;
        let outer = self.static_layout(source)?;
        let inner = self.static_layout(inner_ty)?;
        if !nonzero_integer_scalar(primitive.backend_repr, bits, signed, 0)
            || !nonzero_integer_scalar(outer.backend_repr, bits, signed, 1)
            || !nonzero_integer_scalar(inner.backend_repr, bits, signed, 1)
            || [outer, inner].iter().any(|layout| {
                layout.size != primitive.size
                    || layout.align.abi != primitive.align.abi
                    || layout.fields.offset(0).bytes() != 0
            })
        {
            return Err(
                "NonZero transmute requires exact initialized primitive scalar layout".into(),
            );
        }
        let outer_name = self.tcx.def_path_str(nonzero.did());
        let ty::Adt(inner_def, _) = inner_ty.kind() else {
            return Err("NonZero compiler inner ADT missing".into());
        };
        let inner_name = self.tcx.def_path_str(inner_def.did());
        let value = if let Value::Input(input) = value {
            input.materialize()?
        } else {
            value.clone()
        };
        let Value::Adt {
            name,
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields,
        } = &value
        else {
            return Err("NonZero transmute requires exact modeled outer storage".into());
        };
        let [
            (
                _,
                Value::Adt {
                    name: actual_inner,
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields: inner_fields,
                },
            ),
        ] = fields.as_slice()
        else {
            return Err("NonZero transmute requires exact modeled inner storage".into());
        };
        let [(field_name, scalar)] = inner_fields.as_slice() else {
            return Err("NonZero transmute requires one modeled scalar".into());
        };
        if *name != outer_name
            || *actual_inner != inner_name
            || fields[0].0
                != nonzero.non_enum_variant().fields[FieldIdx::from_usize(0)]
                    .name
                    .as_str()
            || field_name
                != inner_def.non_enum_variant().fields[FieldIdx::from_usize(0)]
                    .name
                    .as_str()
        {
            return Err("NonZero transmute modeled storage identity mismatch".into());
        }
        let (expression, actual_bits, actual_signed) = scalar.integer()?;
        if actual_bits != bits
            || actual_signed != signed
            || expression.sort() != &Sort::BitVec(bits)
            || !expression.belongs_to(&self.terms)
        {
            return Err("NonZero transmute modeled scalar type or context mismatch".into());
        }
        let zero = self
            .terms
            .apply(Op::Equal, &[expression, self.terms.bit_vector(0, bits)?])?;
        if self.feasible(&[conditions.to_vec(), vec![zero]].concat())? {
            return Err("NonZero transmute lacks proven nonzero source validity".into());
        }
        Ok(Some(scalar.clone()))
    }

    fn nonzero_integer_inner(
        &self,
        nonzero_ty: Ty<'tcx>,
        primitive: Ty<'tcx>,
    ) -> Result<Ty<'tcx>, String> {
        let ty::Adt(nonzero, nonzero_args) = nonzero_ty.kind() else {
            return Err("NonZero requires a compiler ADT".into());
        };
        if !self
            .tcx
            .is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), nonzero.did())
            || !nonzero.is_struct()
            || nonzero_args.len() != 1
            || nonzero_args.type_at(0) != primitive
            || nonzero.non_enum_variant().fields.len() != 1
            || !matches!(primitive.kind(), ty::Int(_) | ty::Uint(_))
        {
            return Err("NonZero primitive compiler identity mismatch".into());
        }
        let env = ty::TypingEnv::fully_monomorphized();
        let inner_ty = self
            .tcx
            .try_normalize_erasing_regions(
                env,
                nonzero.non_enum_variant().fields[FieldIdx::from_usize(0)]
                    .ty(self.tcx, nonzero_args),
            )
            .map_err(|error| format!("optional NonZero field normalization failed: {error:?}"))?;
        let ty::Adt(inner, inner_args) = inner_ty.kind() else {
            return Err("optional NonZero requires compiler scalar inner storage".into());
        };
        if inner.did().krate != nonzero.did().krate
            || !inner.is_struct()
            || inner.non_enum_variant().fields.len() != 1
        {
            return Err("optional NonZero inner field shape mismatch".into());
        }
        let scalar_ty = self
            .tcx
            .try_normalize_erasing_regions(
                env,
                inner.non_enum_variant().fields[FieldIdx::from_usize(0)].ty(self.tcx, inner_args),
            )
            .map_err(|error| format!("optional NonZero field normalization failed: {error:?}"))?;
        if !matches!(scalar_ty.kind(), ty::Pat(base, _) if *base == primitive) {
            return Err("optional NonZero inner integer identity mismatch".into());
        }
        Ok(inner_ty)
    }
}

pub(super) fn nonzero_integer_scalar(
    repr: BackendRepr,
    bits: u32,
    signed: bool,
    start: u128,
) -> bool {
    let max = if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    };
    matches!(repr, BackendRepr::Scalar(Scalar::Initialized {
        value: Primitive::Int(integer, actual_signed), valid_range,
    }) if integer.size().bits() == u64::from(bits) && actual_signed == signed
        && valid_range.start == start && valid_range.end == max)
}

// Exact original primitive admission for the readonly niche prototype. Char/Pat and other
// same-width types are not certificates. Byte-sized membership remains a separate body route.
pub(super) fn readonly_niche_unsigned_bits(original: Ty<'_>) -> Option<u32> {
    match original.kind() {
        ty::Uint(ty::UintTy::U8) => Some(8),
        ty::Uint(ty::UintTy::U16) => Some(16),
        ty::Uint(ty::UintTy::U32) => Some(32),
        _ => None,
    }
}

/// Exact readonly payload domains; discriminant and index signedness are separate facts.
pub(super) fn readonly_niche_integer_type(original: Ty<'_>) -> Option<(u32, bool)> {
    match original.kind() {
        ty::Int(ty::IntTy::I8) => Some((8, true)),
        ty::Int(ty::IntTy::I16) => Some((16, true)),
        ty::Int(ty::IntTy::I32) => Some((32, true)),
        _ => readonly_niche_unsigned_bits(original).map(|bits| (bits, false)),
    }
}
