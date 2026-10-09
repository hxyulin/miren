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
        if !matches!(scalar_ty.kind(), ty::Pat(base, _) if *base == source) {
            return Err("optional NonZero inner integer identity mismatch".into());
        }
        let (bits, signed) = self
            .integer_type(source)
            .ok_or("optional NonZero primitive integer type")?;
        let source_layout = self.static_layout(source)?;
        let option_layout = self.static_layout(target)?;
        let nonzero_layout = self.static_layout(nonzero_ty)?;
        let inner_layout = self.static_layout(inner_ty)?;
        let max = if bits == 128 {
            u128::MAX
        } else {
            (1_u128 << bits) - 1
        };
        let scalar = |layout: rustc_abi::BackendRepr, start| {
            matches!(layout,
            BackendRepr::Scalar(Scalar::Initialized {
                value: Primitive::Int(integer, actual_signed), valid_range,
            }) if integer.size().bits() == u64::from(bits) && actual_signed == signed
                && valid_range.start == start && valid_range.end == max)
        };
        let field = FieldIdx::from_usize(0);
        if !scalar(source_layout.backend_repr, 0)
            || !scalar(option_layout.backend_repr, 0)
            || !scalar(nonzero_layout.backend_repr, 1)
            || !scalar(inner_layout.backend_repr, 1)
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
            || !scalar(BackendRepr::Scalar(tag), 0)
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
}
