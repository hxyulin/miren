//! Pure-owned boundary certification for an explicit ordinary-storage frame premise.
use super::*;
use rustc_abi::{BackendRepr, VariantIdx};
use rustc_middle::ty::TypeVisitableExt;

impl<'tcx> Engine<'tcx> {
    pub(super) fn certify_trusted_owned_inputs(
        &mut self,
        signature: &ty::FnSig<'tcx>,
        values: &[Value],
        conditions: &[Term],
    ) -> Result<(), String> {
        let mut type_budget = 512;
        let mut value_budget = 512;
        for (ty, value) in signature.inputs().iter().zip(values) {
            self.trusted_owned_type(*ty, 0, &mut type_budget)?;
            self.trusted_owned_value(*ty, value, conditions, 0, &mut value_budget)?;
        }
        Ok(())
    }

    fn trusted_owned_type(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        budget: &mut usize,
    ) -> Result<(), String> {
        if matches!(ty.kind(), ty::Pat(_, _)) {
            return Err("owned inputs with restricted pattern validity are unsupported".into());
        }
        if ty.has_escaping_bound_vars() {
            return Err(
                "owned boundary types with escaping bound variables are unsupported".into(),
            );
        }
        if depth >= 16 || *budget == 0 {
            return Err("owned summary input type budget exceeded".into());
        }
        *budget -= 1;
        let env = ty::TypingEnv::fully_monomorphized();
        if !ty.is_freeze(self.tcx, env) || ty.needs_drop(self.tcx, env) {
            return Err("owned storage effect inputs must be non-Drop Freeze values".into());
        }
        if ty.is_bool() || self.integer_type(ty).is_some() || self.float_type(ty).is_some() {
            return Ok(());
        }
        match ty.kind() {
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.trusted_owned_type(field, depth + 1, budget)?;
                }
            }
            ty::Array(element, length) => {
                let count = length
                    .try_to_target_usize(self.tcx)
                    .ok_or("owned array length is unknown")?;
                if count > 256 {
                    return Err("owned array exceeds the 256-element budget".into());
                }
                self.trusted_owned_type(*element, depth + 1, budget)?;
            }
            ty::Adt(def, args) if def.is_struct() || def.is_enum() => {
                let count = def.variants().len();
                let fieldless = def
                    .variants()
                    .iter()
                    .all(|variant| variant.fields.is_empty());
                let limit = if def.is_enum() && fieldless {
                    1024
                } else {
                    256
                };
                if count == 0 || count > limit {
                    return Err(format!(
                        "owned enum inventory {} has {count} variants; limit {limit}",
                        self.tcx.def_path_str(def.did())
                    ));
                }
                if def.is_struct() {
                    self.trusted_owned_struct_layout(ty)?;
                }
                for variant in def.variants() {
                    for field in &variant.fields {
                        let field_ty = self.trusted_owned_field(field.ty(self.tcx, args))?;
                        self.trusted_owned_type(field_ty, depth + 1, budget)?;
                    }
                }
            }
            _ => {
                return Err(concat!(
                    "owned storage effect inputs exclude references, ",
                    "pointers, callbacks and opaque types"
                )
                .into());
            }
        }
        Ok(())
    }

    fn trusted_owned_struct_layout(&self, ty: Ty<'tcx>) -> Result<(), String> {
        let ty::Adt(def, args) = ty.kind() else {
            return Err("owned scalar container requires an ADT".into());
        };
        let layout = self.static_layout(ty)?;
        let mut fields = Vec::new();
        for (position, field) in def.non_enum_variant().fields.iter().enumerate() {
            let field_ty = self.trusted_owned_field(field.ty(self.tcx, args))?;
            let field_layout = self.static_layout(field_ty)?;
            if field_layout.size.bytes() != 0 {
                fields.push((
                    layout.fields.offset(position).bytes(),
                    field_layout.backend_repr,
                ));
            }
        }
        fields.sort_by_key(|(offset, _)| *offset);
        let valid = trusted_owned_scalar_fields(layout.backend_repr, &fields);
        if !valid {
            return Err(
                "owned scalar wrapper has unsupported validity beyond its typed fields".into(),
            );
        }
        Ok(())
    }

    fn trusted_owned_field(
        &self,
        ty: ty::Unnormalized<'tcx, Ty<'tcx>>,
    ) -> Result<Ty<'tcx>, String> {
        for (position, argument) in ty.skip_norm_wip().walk().enumerate() {
            if position >= 512 {
                return Err("owned raw field type exceeds the inspection budget".into());
            }
            if let ty::GenericArgKind::Type(field) = argument.kind()
                && matches!(field.kind(), ty::Pat(_, _))
            {
                return Err("owned inputs with restricted pattern validity are unsupported".into());
            }
        }
        self.tcx
            .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), ty)
            .map_err(|error| format!("owned field normalization failed: {error:?}"))
    }

    fn trusted_owned_value(
        &mut self,
        ty: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
        depth: usize,
        budget: &mut usize,
    ) -> Result<(), String> {
        if depth >= 16 || *budget == 0 {
            return Err("owned summary input value budget exceeded".into());
        }
        *budget -= 1;
        if ty.is_bool() {
            let Value::Bool(expression) = value else {
                return Err("owned bool value shape mismatch".into());
            };
            return self.trusted_owned_term(expression, &Sort::Bool);
        }
        if let Some((bits, signed)) = self.integer_type(ty) {
            let (expression, actual_bits, actual_signed) = value.integer()?;
            if bits != actual_bits || signed != actual_signed {
                return Err("owned integer metadata does not match compiler type".into());
            }
            return self.trusted_owned_term(&expression, &Sort::BitVec(bits));
        }
        if let Some(bits) = self.float_type(ty) {
            let Value::Float {
                expression,
                bits: actual,
                raw_bits,
            } = value
            else {
                return Err("owned float value shape mismatch".into());
            };
            if *actual != bits {
                return Err("owned float width mismatch".into());
            }
            let (exponent, significand) = if bits == 32 { (8, 24) } else { (11, 53) };
            self.trusted_owned_term(
                expression,
                &Sort::Float {
                    exponent,
                    significand,
                },
            )?;
            if let Some(raw) = raw_bits {
                self.trusted_owned_term(raw, &Sort::BitVec(bits))?;
            }
            return Ok(());
        }
        match ty.kind() {
            ty::Tuple(fields) => {
                if fields.is_empty() && matches!(value, Value::Unit) {
                    return Ok(());
                }
                let Value::Tuple(values) = value else {
                    return Err("owned tuple value shape mismatch".into());
                };
                if fields.len() != values.len() {
                    return Err("owned tuple arity mismatch".into());
                }
                for (field, value) in fields.iter().zip(values) {
                    self.trusted_owned_value(field, value, conditions, depth + 1, budget)?;
                }
            }
            ty::Array(element, length) => {
                let count = length
                    .try_to_target_usize(self.tcx)
                    .ok_or("owned array length unavailable")?;
                if let Value::Bytes { data, length } = value {
                    if *element != self.tcx.types.u8 {
                        return Err("owned bytes require a u8 array".into());
                    }
                    let bits = u32::from(self.tcx.sess.target.pointer_width);
                    self.trusted_owned_term(
                        data,
                        &Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8))),
                    )?;
                    let (length, actual_bits, signed) = length.integer()?;
                    if actual_bits != bits || signed {
                        return Err("owned byte length must be target usize".into());
                    }
                    self.trusted_owned_term(&length, &Sort::BitVec(bits))?;
                    let expected = self.terms.bit_vector(u128::from(count), bits)?;
                    let equal = self.terms.apply(Op::Equal, &[length, expected])?;
                    if self
                        .feasible(&[conditions.to_vec(), vec![symbolic::not(&equal)]].concat())?
                    {
                        return Err("owned byte array length lacks exact compiler bound".into());
                    }
                } else {
                    let Value::Elements(values) = value else {
                        return Err(concat!(
                            "owned array needs exact retained finite values; ",
                            "lazy inputs are unsupported"
                        )
                        .into());
                    };
                    if values.len() as u64 != count {
                        return Err("owned array length mismatch".into());
                    }
                    for value in values {
                        self.trusted_owned_value(*element, value, conditions, depth + 1, budget)?;
                    }
                }
            }
            ty::Adt(def, _) if def.is_struct() || def.is_enum() => {
                if let Value::Adt { variant, .. } = value {
                    self.trusted_owned_variant(ty, value, *variant, conditions, depth, budget)?;
                } else if let Value::Enum {
                    discriminant,
                    variants,
                    is_option,
                } = value
                {
                    if !def.is_enum()
                        || variants.len() != def.variants().len()
                        || *is_option
                            != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                    {
                        return Err("owned symbolic enum requires exact complete inventory".into());
                    }
                    let (bits, signed) = self
                        .integer_type(ty.discriminant_ty(self.tcx))
                        .ok_or("owned enum discriminant type unavailable")?;
                    let (expression, actual_bits, actual_signed) = discriminant.integer()?;
                    if bits != actual_bits || signed != actual_signed {
                        return Err("owned enum tag type mismatch".into());
                    }
                    self.trusted_owned_term(&expression, &Sort::BitVec(bits))?;
                    let mut members = Vec::new();
                    for (position, variant) in variants.iter().enumerate() {
                        if *budget == 0 {
                            return Err("owned summary input value budget exceeded".into());
                        }
                        *budget -= 1;
                        self.trusted_owned_variant(
                            ty, variant, position, conditions, depth, budget,
                        )?;
                        let tag = def
                            .discriminant_for_variant(self.tcx, VariantIdx::from_usize(position))
                            .val;
                        members.push(self.terms.apply(
                            Op::Equal,
                            &[expression.clone(), self.terms.bit_vector(tag, bits)?],
                        )?);
                    }
                    let valid = self.terms.apply(Op::Or, &members)?;
                    if self
                        .feasible(&[conditions.to_vec(), vec![symbolic::not(&valid)]].concat())?
                    {
                        return Err("owned enum tag lacks proven exact membership".into());
                    }
                } else {
                    return Err(concat!(
                        "owned ADT needs exact modeled storage; ",
                        "opaque/lazy handles are unsupported"
                    )
                    .into());
                }
            }
            _ => {
                return Err(
                    "owned storage effect value contains unsupported aliases or handles".into(),
                );
            }
        }
        Ok(())
    }

    fn trusted_owned_variant(
        &mut self,
        ty: Ty<'tcx>,
        value: &Value,
        position: usize,
        conditions: &[Term],
        depth: usize,
        budget: &mut usize,
    ) -> Result<(), String> {
        let ty::Adt(def, args) = ty.kind() else {
            return Err("owned variant must have an ADT type".into());
        };
        let Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } = value
        else {
            return Err("owned variant requires exact modeled ADT storage".into());
        };
        if position >= def.variants().len()
            || *variant != position
            || *name != self.tcx.def_path_str(def.did())
            || *is_option != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
        {
            return Err("owned ADT identity or variant mismatch".into());
        }
        let index = VariantIdx::from_usize(position);
        let metadata = def.variant(index);
        let tag = if def.is_enum() {
            def.discriminant_for_variant(self.tcx, index).val
        } else {
            0
        };
        if *discriminant != tag || metadata.fields.len() != fields.len() {
            return Err("owned ADT discriminant or field inventory mismatch".into());
        }
        for (field, (name, value)) in metadata.fields.iter().zip(fields) {
            if name != field.name.as_str() {
                return Err("owned ADT field name mismatch".into());
            }
            let field_ty = self.trusted_owned_field(field.ty(self.tcx, args))?;
            self.trusted_owned_value(field_ty, value, conditions, depth + 1, budget)?;
        }
        Ok(())
    }

    fn trusted_owned_term(&self, term: &Term, sort: &Sort) -> Result<(), String> {
        if term.sort() != sort || !term.belongs_to(&self.terms) {
            return Err("owned storage effect scalar has wrong sort or context".into());
        }
        Ok(())
    }
}

fn trusted_owned_scalar_fields(representation: BackendRepr, fields: &[(u64, BackendRepr)]) -> bool {
    match representation {
        BackendRepr::Scalar(scalar) => matches!(fields,
                [(0, BackendRepr::Scalar(field))] if *field == scalar),
        BackendRepr::ScalarPair {
            a: first,
            b: second,
            b_offset,
        } => match fields {
            [
                (
                    0,
                    BackendRepr::ScalarPair {
                        a,
                        b,
                        b_offset: offset,
                    },
                ),
            ] => *a == first && *b == second && *offset == b_offset,
            [
                (0, BackendRepr::Scalar(a)),
                (offset, BackendRepr::Scalar(b)),
            ] => *a == first && *b == second && *offset == b_offset.bytes(),
            _ => false,
        },
        BackendRepr::SimdVector { .. } | BackendRepr::SimdScalableVector { .. } => false,
        BackendRepr::Memory { .. } => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::{Integer, Primitive, Scalar, Size, WrappingRange};
    fn scalar(start: u128, end: u128) -> BackendRepr {
        BackendRepr::Scalar(Scalar::Initialized {
            value: Primitive::Int(Integer::I32, false),
            valid_range: WrappingRange { start, end },
        })
    }
    #[test]
    fn scalar_wrapper_fields_cannot_lose_range_restrictions_or_offsets() {
        let full = scalar(0, u128::from(u32::MAX));
        let restricted = scalar(1, u128::from(u32::MAX));
        assert!(trusted_owned_scalar_fields(full, &[(0, full)]));
        assert!(!trusted_owned_scalar_fields(restricted, &[(0, full)]));
        assert!(!trusted_owned_scalar_fields(full, &[(4, full)]));
        let BackendRepr::Scalar(first) = full else {
            unreachable!()
        };
        let BackendRepr::Scalar(second) = restricted else {
            unreachable!()
        };
        let pair = BackendRepr::ScalarPair {
            a: first,
            b: first,
            b_offset: Size::from_bytes(4),
        };
        assert!(trusted_owned_scalar_fields(pair, &[(0, full), (4, full)]));
        assert!(!trusted_owned_scalar_fields(pair, &[(0, full), (8, full)]));
        let restricted_pair = BackendRepr::ScalarPair {
            a: first,
            b: second,
            b_offset: Size::from_bytes(4),
        };
        assert!(!trusted_owned_scalar_fields(
            restricted_pair,
            &[(0, full), (4, full)]
        ));
    }
}
