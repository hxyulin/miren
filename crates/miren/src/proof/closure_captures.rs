//! Compiler closure metadata only; payload validity and borrow rights stay with callers.
use super::*;

fn validate_capture_storage(
    expected_name: &str,
    count: usize,
    value: &Value,
) -> Result<(), String> {
    let Value::Adt {
        name,
        variant,
        discriminant,
        is_option,
        fields,
    } = value
    else {
        return Err("closure carrier lacks retained capture storage".into());
    };
    if name != expected_name
        || *variant != 0
        || *discriminant != 0
        || *is_option
        || fields.len() != count
        || fields
            .iter()
            .enumerate()
            .any(|(index, (name, _))| *name != index.to_string())
    {
        return Err("closure carrier differs from its exact compiler capture schema".into());
    }
    Ok(())
}

fn pure_slice_element_type(ty: Ty<'_>, depth: usize) -> bool {
    if depth >= 32 {
        return false;
    }
    match ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
        ty::Tuple(fields) => fields
            .iter()
            .all(|ty| pure_slice_element_type(ty, depth + 1)),
        ty::Array(element, _) => pure_slice_element_type(*element, depth + 1),
        _ => false,
    }
}

fn pure_retained_slice_storage(value: &Value, depth: usize) -> bool {
    if depth >= 32 {
        return false;
    }
    match value {
        Value::Bool(_) | Value::Int { .. } | Value::Float { .. } | Value::Unit => true,
        Value::Tuple(fields) => fields
            .iter()
            .all(|value| pure_retained_slice_storage(value, depth + 1)),
        Value::Elements(fields) => fields
            .iter()
            .all(|value| pure_retained_slice_storage(value, depth + 1)),
        Value::Bytes { length, .. }
        | Value::ScalarSlice { length, .. }
        | Value::CompositeSlice { length, .. } => pure_retained_slice_storage(length, depth + 1),
        Value::Uninitialized
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::RawPointer { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Input(_)
        | Value::Adt { .. }
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function => false,
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn closure_capture_types(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
    ) -> Result<Option<&'tcx ty::List<Ty<'tcx>>>, String> {
        let ty::Closure(id, args) = expected.kind() else {
            return Ok(None);
        };
        if self.tcx.def_kind(*id) != DefKind::Closure || self.tcx.coroutine_kind(*id).is_some() {
            return Err("closure carrier lacks its compiler definition identity".into());
        }
        let closure = args.as_closure();
        // The infallible compiler accessors assert on unresolved or malformed metadata.
        // These exact compiler encodings distinguish Fn, FnMut and FnOnce without
        // requiring a Fn closure to be invoked only through the Fn trait.
        match closure.kind_ty().kind() {
            ty::Int(ty::IntTy::I8 | ty::IntTy::I16 | ty::IntTy::I32) => {}
            _ => return Err("closure carrier requires a resolved compiler closure kind".into()),
        }
        let captures = closure.tupled_upvars_ty();
        let ty::Tuple(types) = captures.kind() else {
            return Err("closure carrier requires compiler tuple capture metadata".into());
        };
        validate_capture_storage(&self.tcx.def_path_str(*id), types.len(), value)?;
        Ok(Some(*types))
    }

    pub(super) fn validate_closure_escape(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
        state: &State,
        incoming: usize,
    ) -> Result<(), String> {
        self.closure_escape_depth(expected, value, state, incoming, 0)?;
        Ok(())
    }

    fn closure_escape_depth(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
        state: &State,
        incoming: usize,
        depth: usize,
    ) -> Result<bool, String> {
        if depth >= 32 {
            return Err("closure return carrier nesting limit reached".into());
        }
        if self.closure_capture_types(expected, value)?.is_some() {
            let Value::Adt { fields, .. } = value else {
                return Err("closure carrier lacks retained capture storage".into());
            };
            for (_, capture) in fields {
                Self::validate_reference_graph(capture, state, Some(incoming), &mut Vec::new())?;
            }
            // Shape checking above also validates closures without captures.
            return Ok(true);
        }
        let mut contains = false;
        match (expected.kind(), value) {
            (ty::Tuple(types), Value::Tuple(fields)) => {
                if types.len() != fields.len() {
                    return Err("closure return tuple carrier arity mismatch".into());
                }
                for (ty, value) in types.iter().zip(fields) {
                    contains |= self.closure_escape_depth(ty, value, state, incoming, depth + 1)?;
                }
            }
            (ty::Array(element, count), Value::Elements(fields)) => {
                if count.try_to_target_usize(self.tcx) != Some(fields.len() as u64) {
                    return Err("closure return array carrier count mismatch".into());
                }
                for value in fields {
                    contains |=
                        self.closure_escape_depth(*element, value, state, incoming, depth + 1)?;
                }
            }
            (
                ty::Adt(def, args),
                Value::Adt {
                    name,
                    variant,
                    discriminant,
                    is_option,
                    fields,
                },
            ) if !def.is_union() => {
                if *name != self.tcx.def_path_str(def.did()) {
                    return Err("closure return ADT carrier identity mismatch".into());
                }
                let layout = def
                    .variants()
                    .get(rustc_abi::VariantIdx::from_usize(*variant))
                    .ok_or("closure return carrier variant is invalid")?;
                let tag = if def.is_enum() {
                    def.discriminant_for_variant(
                        self.tcx,
                        rustc_abi::VariantIdx::from_usize(*variant),
                    )
                    .val
                } else {
                    0
                };
                if *discriminant != tag
                    || *is_option
                        != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                    || fields.len() != layout.fields.len()
                {
                    return Err("closure return ADT carrier schema mismatch".into());
                }
                for (field, (name, value)) in layout.fields.iter().zip(fields) {
                    if field.name.as_str() != name {
                        return Err("closure return ADT carrier field identity mismatch".into());
                    }
                    let ty = field.ty(self.tcx, args).skip_norm_wip();
                    contains |= self.closure_escape_depth(ty, value, state, incoming, depth + 1)?;
                }
            }
            (
                ty::Adt(def, _),
                Value::Enum {
                    discriminant,
                    variants,
                    is_option,
                },
            ) => {
                if !def.is_enum()
                    || variants.len() != def.variants().len()
                    || *is_option
                        != (self.tcx.lang_items().get(LangItem::Option) == Some(def.did()))
                {
                    return Err("closure return enum carrier inventory mismatch".into());
                }
                let (term, bits, signed) = discriminant.integer()?;
                if self.integer_type(expected.discriminant_ty(self.tcx)) != Some((bits, signed))
                    || term.sort() != &Sort::BitVec(bits)
                    || !term.belongs_to(&self.terms)
                {
                    return Err("closure return enum carrier tag metadata mismatch".into());
                }
                for (index, value) in variants.iter().enumerate() {
                    if !matches!(value, Value::Adt { variant, .. } if *variant == index) {
                        return Err("closure return enum carrier variant order mismatch".into());
                    }
                    contains |=
                        self.closure_escape_depth(expected, value, state, incoming, depth + 1)?;
                }
            }
            (ty::Ref(_, pointee, _), value @ Value::Reference { allocation, .. }) => {
                // Existing finite views may have symbolic lengths. Discover closure-bearing
                // returns without materializing a definitely pure retained slice allocation.
                // Both compiler type and raw storage must exclude captures; type alone cannot
                // certify a malformed reference pointing to closure storage.
                if let ty::Slice(element) = pointee.kind()
                    && pure_slice_element_type(*element, 0)
                    && state
                        .memory
                        .get(*allocation)
                        .and_then(Option::as_ref)
                        .is_some_and(|stored| pure_retained_slice_storage(stored, 0))
                {
                    return Ok(false);
                }
                let stored = self.reference_value(value, &state.memory, &state.conditions)?;
                contains =
                    self.closure_escape_depth(*pointee, &stored, state, incoming, depth + 1)?;
                if contains {
                    Self::validate_reference_graph(value, state, Some(incoming), &mut Vec::new())?;
                }
            }
            (
                _,
                Value::Adt { .. }
                | Value::Enum { .. }
                | Value::Tuple(_)
                | Value::Elements(_)
                | Value::Reference { .. },
            ) => {
                // An uncorrelated aggregate cannot hide a captured borrow from the pre-snapshot
                // check. Pure owned values remain safe under the existing return policy.
                Self::validate_reference_graph(value, state, Some(incoming), &mut Vec::new())?;
            }
            _ => {}
        }
        Ok(contains)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_retained_slice_storage_excludes_captured_and_nested_borrow_carriers() {
        let context = Context::default();
        let scalar = Value::Bool(context.boolean(true));
        let pure = Value::Elements(vec![Value::Tuple(vec![scalar.clone(), Value::Unit])].into());
        assert!(pure_retained_slice_storage(&pure, 0));
        let borrowed = Value::Reference {
            allocation: 0,
            projection: Vec::new(),
            mutable: false,
        };
        assert!(!pure_retained_slice_storage(&borrowed, 0));
        assert!(!pure_retained_slice_storage(
            &Value::Tuple(vec![borrowed.clone()]),
            0
        ));
        let closure = Value::Adt {
            name: "module::{closure#0}".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![("0".into(), borrowed)].into(),
        };
        assert!(!pure_retained_slice_storage(&closure, 0));
        assert!(!pure_retained_slice_storage(
            &Value::Elements(vec![closure].into()),
            0
        ));
    }

    #[test]
    fn capture_storage_rejects_foreign_identity_tags_options_arity_and_field_order() {
        let context = Context::default();
        let valid = Value::Adt {
            name: "module::{closure#0}".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![
                ("0".into(), Value::Bool(context.boolean(true))),
                ("1".into(), Value::Unit),
            ]
            .into(),
        };
        assert!(validate_capture_storage("module::{closure#0}", 2, &valid).is_ok());
        assert!(validate_capture_storage("other::{closure#0}", 2, &valid).is_err());
        assert!(validate_capture_storage("module::{closure#0}", 1, &valid).is_err());
        assert!(validate_capture_storage("module::{closure#0}", 2, &Value::Unit).is_err());
        for change in 0..5 {
            let mut malformed = valid.clone();
            let Value::Adt {
                variant,
                discriminant,
                is_option,
                fields,
                ..
            } = &mut malformed
            else {
                unreachable!();
            };
            match change {
                0 => *variant = 1,
                1 => *discriminant = 1,
                2 => *is_option = true,
                3 => fields[0].0 = "1".into(),
                4 => fields.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(validate_capture_storage("module::{closure#0}", 2, &malformed).is_err());
        }
    }
}
