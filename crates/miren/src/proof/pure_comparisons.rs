use super::*;
use crate::symbolic::ScalarSliceElement;
use rustc_middle::mir::Local;
use rustc_span::Symbol;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum CursorArithmetic {
    AddBelowEnd,
    SubAfterNonzero,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn certify_pure_comparison(
        &self,
        original: Ty<'tcx>,
        outer: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        use super::pure_comparison_templates as templates;
        let core = self
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("pure comparison core identity is unavailable")?
            .krate;
        let eq = self
            .tcx
            .get_diagnostic_item(Symbol::intern("cmp_partialeq_eq"))
            .filter(|id| id.krate == core)
            .ok_or("pure comparison PartialEq identity is unavailable")?;
        let ne = self
            .tcx
            .associated_items(self.tcx.parent(eq))
            .in_definition_order()
            .find(|item| item.opt_name() == Some(Symbol::intern("ne")))
            .map(|item| item.def_id)
            .ok_or("pure comparison PartialEq::ne identity is unavailable")?;
        let mut types = vec![original];
        let mut pending_types = vec![original];
        let mut pending = vec![(outer, None)];
        while let Some(original) = pending_types.pop() {
            if types.len() > 512 {
                return Err("pure comparison type traversal exceeds its node budget".into());
            }
            let args = self.tcx.mk_args(&[original.into(), original.into()]);
            pending.push((self.resolve_function_item(eq, args)?, None));
            pending.push((self.resolve_function_item(ne, args)?, None));
            let children: Vec<_> = match original.kind() {
                ty::Tuple(fields) => fields.iter().collect(),
                ty::Array(child, _) => vec![*child],
                ty::Adt(_, _) => self
                    .nominal_comparison_fields(original)?
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(_, original)| original)
                    .collect(),
                _ => Vec::new(),
            };
            for child in children {
                if !types.contains(&child) {
                    types.push(child);
                    pending_types.push(child);
                }
            }
        }
        let mut seen = std::collections::HashSet::new();
        while let Some((instance, arithmetic)) = pending.pop() {
            if !seen.insert((instance, arithmetic)) {
                continue;
            }
            if seen.len() > 512 {
                return Err("pure comparison body traversal exceeds its node budget".into());
            }
            if arithmetic.is_none() {
                let mut nominal = false;
                for original in &types {
                    if self.nominal_comparison_fields(*original)?.is_some() {
                        let args = self.tcx.mk_args(&[(*original).into(), (*original).into()]);
                        if instance == self.resolve_function_item(eq, args)?
                            || instance == self.resolve_function_item(ne, args)?
                        {
                            self.certify_nominal_comparison(*original, instance)?;
                            nominal = true;
                            break;
                        }
                    }
                }
                if nominal {
                    continue;
                }
            }
            if instance.def_id().krate != core {
                return Err("pure comparison has a non-core selected definition".into());
            }
            if !matches!(instance.def, ty::InstanceKind::Item(_)) {
                return Err("pure comparison has an unsupported selected adapter".into());
            }
            if !self.tcx.is_mir_available(instance.def_id()) {
                return Err(self.missing_body_reason(instance.def_id()));
            }
            let generic = self.tcx.instance_mir(instance.def);
            let encoded = templates::encode_template(self.tcx, generic, core)?;
            let definition = templates::definition_key(instance.def_id());
            let family = templates::reference_family(&definition, &encoded).ok_or_else(|| {
                format!("pure comparison body has no exact reference: {definition}")
            })?;
            let body = self.instantiated_body(instance)?;
            self.certify_comparison_layout_constants(&body, &types)?;
            match (family, arithmetic) {
                (
                    templates::PureTemplateFamily::AddPrecondition,
                    Some(CursorArithmetic::AddBelowEnd),
                )
                | (
                    templates::PureTemplateFamily::SubPrecondition,
                    Some(CursorArithmetic::SubAfterNonzero),
                ) => {}
                (
                    templates::PureTemplateFamily::AddPrecondition
                    | templates::PureTemplateFamily::SubPrecondition,
                    _,
                ) => {
                    return Err("cursor arithmetic lacks its exact matched caller premise".into());
                }
                (_, Some(_)) => {
                    return Err("cursor arithmetic premise reached a different helper".into());
                }
                (_, None) => {}
            }
            let element =
                self.validate_pure_comparison_instance(instance, family, &body, &types)?;
            if family == templates::PureTemplateFamily::ContainsBytes {
                let element = element.ok_or("bytewise membership has no original element type")?;
                if self.static_layout(element)?.size.bytes() == 1 {
                    return Err(self.categorized_error(
                        UnknownCategory::Semantics,
                        "one-byte composite membership transport is unsupported".into(),
                    ));
                }
            }
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    if let StatementKind::Assign(assignment) = &statement.kind
                        && let Rvalue::Aggregate(kind, _) = &assignment.1
                        && let AggregateKind::Closure(id, args) = kind.as_ref()
                    {
                        pending.push((ty::Instance::new_raw(*id, args), None));
                    }
                }
                let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                    continue;
                };
                let ty::FnDef(id, args) = func.ty(&body.local_decls, self.tcx).kind() else {
                    return Err("pure comparison transport contains a non-function call".into());
                };
                if id.krate != core {
                    return Err("pure comparison transport has a non-core callee".into());
                }
                if self.pure_comparison_intrinsic(*id, args.skip_binder(), family, &types)? {
                    continue;
                }
                let selected = self.resolve_function_item(*id, args.skip_binder())?;
                let selected_definition = templates::definition_key(selected.def_id());
                if matches!(
                    family,
                    templates::PureTemplateFamily::AddPrecondition
                        | templates::PureTemplateFamily::SubPrecondition
                ) && selected_definition == "DefId(core::panicking::panic_nounwind_fmt)"
                {
                    // The full reference pins the overflow test and panic operands. Valid
                    // source extents and cursor bounds make this branch unreachable.
                    // The matched caller supplied the checked unsigned cursor lemma.
                    // This exact precondition template branches to panic only on overflow.
                    continue;
                }
                if family == templates::PureTemplateFamily::ContainsBytes
                    && matches!(
                        selected_definition.as_str(),
                        "DefId(core::mem::transmute_copy::precondition_check)"
                            | "DefId(core::slice::raw::from_raw_parts::precondition_check)"
                            | "DefId(core::slice::memchr::memchr)"
                    )
                {
                    // The complete reference puts these calls solely in SIZE == 1.
                    // This family was refused above for that concrete compiler size.
                    continue;
                }
                let arithmetic = match (family, selected_definition.as_str()) {
                    (
                        templates::PureTemplateFamily::IterAny,
                        "DefId(core::num::{impl#11}::unchecked_sub::precondition_check)",
                    ) => Some(CursorArithmetic::SubAfterNonzero),
                    (
                        templates::PureTemplateFamily::SliceEqualityDefault,
                        "DefId(core::num::{impl#11}::unchecked_add::precondition_check)",
                    ) => Some(CursorArithmetic::AddBelowEnd),
                    _ => None,
                };
                if let Some(premise) = arithmetic {
                    self.certify_cursor_arithmetic(premise)?;
                }
                pending.push((selected, arithmetic));
            }
        }
        Ok(())
    }

    fn certify_comparison_layout_constants(
        &self,
        body: &Body<'tcx>,
        types: &[Ty<'tcx>],
    ) -> Result<(), String> {
        use rustc_middle::mir::visit::Visitor;
        let mut constants = ComparisonLayoutConstants::default();
        constants.visit_body(body);
        if constants.overflow {
            return Err("comparison layout constant traversal exceeds its node budget".into());
        }
        for operand in constants.values {
            let rustc_middle::mir::Const::Unevaluated(value, _) = operand.const_ else {
                continue;
            };
            let definition = super::pure_comparison_templates::definition_key(value.def);
            let property = match definition.as_str() {
                "DefId(core::mem::SizedTypeProperties::SIZE)" => 0,
                "DefId(core::mem::SizedTypeProperties::IS_ZST)" => 1,
                "DefId(core::mem::SizedTypeProperties::ALIGN)" => 2,
                _ => continue,
            };
            let zst = property == 1;
            let original = value.args.type_at(0);
            if (!types.contains(&original) && original != self.tcx.types.u8)
                || value.promoted.is_some()
                || operand.const_.ty()
                    != if zst {
                        self.tcx.types.bool
                    } else {
                        self.tcx.types.usize
                    }
            {
                return Err(format!(
                    "comparison layout constant lacks its original compiler type: {original:?}, {:?}, {definition}",
                    operand.const_.ty()
                ));
            }
            let evaluated = operand
                .const_
                .eval(self.tcx, ty::TypingEnv::fully_monomorphized(), operand.span)
                .map_err(|error| format!("comparison layout constant is unavailable: {error:?}"))?;
            let rustc_middle::mir::ConstValue::Scalar(scalar) = evaluated else {
                return Err("comparison layout constant is not a compiler scalar".into());
            };
            let layout = self.static_layout(original)?;
            let bytes = if property == 2 {
                layout.align.abi.bytes()
            } else {
                layout.size.bytes()
            };
            let exact = if zst {
                scalar
                    .to_bool()
                    .discard_err()
                    .is_some_and(|value| value == (bytes == 0))
            } else {
                scalar
                    .to_bits(self.tcx.data_layout.pointer_size())
                    .discard_err()
                    .is_some_and(|value| value == u128::from(bytes))
            };
            if !exact {
                return Err(
                    "comparison layout constant differs from actual compiler layout".into(),
                );
            }
        }
        Ok(())
    }

    fn certify_cursor_arithmetic(&self, premise: CursorArithmetic) -> Result<(), String> {
        let width = u32::from(self.tcx.sess.target.pointer_width);
        if !matches!(width, 32 | 64) {
            return Err(
                "pure comparison cursor arithmetic requires a certified target width".into(),
            );
        }
        let cursor = self.fresh(Sort::BitVec(width));
        let end = self.fresh(Sort::BitVec(width));
        let invalid = cursor_arithmetic_counterexample(&self.terms, premise, &cursor, &end)?;
        if self.feasible(&[invalid])? {
            return Err("pure comparison cursor arithmetic invariant was not proved".into());
        }
        Ok(())
    }

    fn validate_pure_comparison_instance(
        &self,
        instance: ty::Instance<'tcx>,
        family: super::pure_comparison_templates::PureTemplateFamily,
        body: &Body<'tcx>,
        types: &[Ty<'tcx>],
    ) -> Result<Option<Ty<'tcx>>, String> {
        use super::pure_comparison_templates::PureTemplateFamily as Family;
        let input = |position: usize| {
            body.local_decls
                .get(Local::from_usize(position))
                .map(|d| d.ty)
        };
        let output = body.return_ty();
        if matches!(family, Family::ClosureDefault | Family::ClosureBytes) {
            let (Some(receiver), Some(argument)) = (input(1), input(2)) else {
                return Err("pure comparison closure lacks its original arguments".into());
            };
            let ty::Ref(_, closure, mutable) = receiver.kind() else {
                return Err("pure comparison closure receiver is not a reference".into());
            };
            let ty::Closure(id, args) = closure.kind() else {
                return Err("pure comparison callback lacks a concrete closure identity".into());
            };
            if *id != instance.def_id()
                || !mutable.is_mut()
                || self.tcx.coroutine_kind(*id).is_some()
                || body.arg_count != 2
                || !output.is_bool()
            {
                return Err(
                    "pure comparison callback differs from its synchronous signature".into(),
                );
            }
            let element = shared_pointee(argument)
                .filter(|element| types.contains(element))
                .ok_or("pure comparison callback item differs from the original element")?;
            self.validate_pure_comparison_capture(*id, args, element)?;
            return Ok(Some(element));
        }
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust || signature.c_variadic() {
            return Err("pure comparison requires the exact Rust ABI".into());
        }
        let unsafe_family = matches!(
            family,
            Family::SliceEqualityDefault | Family::SliceEqualityBytes
        );
        if signature.safety()
            != if unsafe_family {
                rustc_hir::Safety::Unsafe
            } else {
                rustc_hir::Safety::Safe
            }
        {
            return Err("pure comparison has an incompatible compiler safety signature".into());
        }
        if matches!(family, Family::AddPrecondition | Family::SubPrecondition) {
            if signature.inputs() != [self.tcx.types.usize, self.tcx.types.usize]
                || !signature.output().is_unit()
                || body.arg_count != 2
            {
                return Err("pure comparison cursor arithmetic signature differs".into());
            }
            return Ok(None);
        }
        if !signature.output().is_bool() || !output.is_bool() {
            return Err("pure comparison output is not the exact compiler Bool".into());
        }
        match family {
            Family::Primitive
            | Family::Tuple
            | Family::Array
            | Family::SpecArrayDefault
            | Family::SpecArrayBytes
            | Family::SliceEquality => {
                let [left, right] = signature.inputs() else {
                    return Err("pure comparison requires two original receivers".into());
                };
                let element = shared_pointee(*left)
                    .filter(|left| shared_pointee(*right) == Some(*left))
                    .ok_or("pure comparison receivers have different original types")?;
                let admitted = types.contains(&element)
                    || matches!(element.kind(), ty::Slice(child) if types.contains(child));
                if !admitted || body.arg_count != 2 {
                    return Err(
                        "pure comparison receiver is outside the original pure type tree".into(),
                    );
                }
                Ok(Some(element))
            }
            Family::SliceEqualityDefault | Family::SliceEqualityBytes => {
                let [left, right, length] = signature.inputs() else {
                    return Err(
                        "pure slice comparator lacks its exact pointer/length signature".into(),
                    );
                };
                let (ty::RawPtr(left, left_mut), ty::RawPtr(right, right_mut)) =
                    (left.kind(), right.kind())
                else {
                    return Err(
                        "pure slice comparator lacks its selected raw receiver types".into(),
                    );
                };
                if left != right
                    || left_mut.is_mut()
                    || right_mut.is_mut()
                    || *length != self.tcx.types.usize
                    || !types.contains(left)
                    || (family == Family::SliceEqualityBytes && !bitwise_comparison_type(*left, 0))
                    || body.arg_count != 3
                {
                    return Err(
                        "pure slice comparator receivers differ from its original element".into(),
                    );
                }
                Ok(Some(*left))
            }
            Family::Contains | Family::ContainsDefault | Family::ContainsBytes => {
                let [first, second] = signature.inputs() else {
                    return Err("pure membership transport requires two receivers".into());
                };
                let (slice, needle) = if family == Family::Contains {
                    (shared_pointee(*first), shared_pointee(*second))
                } else {
                    (shared_pointee(*second), shared_pointee(*first))
                };
                let (Some(slice), Some(needle)) = (slice, needle) else {
                    return Err("pure membership transport lacks original shared references".into());
                };
                if !matches!(slice.kind(), ty::Slice(child) if *child == needle)
                    || !types.contains(&needle)
                    || body.arg_count != 2
                {
                    return Err("pure membership transport changed its slice or needle type".into());
                }
                Ok(Some(needle))
            }
            Family::IterAny => {
                let [receiver, closure] = signature.inputs() else {
                    return Err(
                        "pure membership any adapter requires its iterator and callback".into(),
                    );
                };
                let ty::Ref(_, iterator, mutable) = receiver.kind() else {
                    return Err("pure membership any receiver is not a cursor reference".into());
                };
                let ty::Adt(def, args) = iterator.kind() else {
                    return Err(
                        "pure membership any receiver lacks its compiler Iter identity".into(),
                    );
                };
                let Some(id) = self.tcx.get_diagnostic_item(Symbol::intern("SliceIter")) else {
                    return Err("pure membership Iter identity is unavailable".into());
                };
                let Some(element) = args.types().next() else {
                    return Err("pure membership Iter element metadata is missing".into());
                };
                let ty::Closure(closure_id, closure_args) = closure.kind() else {
                    return Err("pure membership callback is not a synchronous closure".into());
                };
                if def.did() != id
                    || !mutable.is_mut()
                    || !types.contains(&element)
                    || body.arg_count != 2
                {
                    return Err("pure membership any cursor differs from its original type".into());
                }
                self.validate_pure_comparison_capture(*closure_id, closure_args, element)?;
                Ok(Some(element))
            }
            Family::ClosureDefault
            | Family::ClosureBytes
            | Family::AddPrecondition
            | Family::SubPrecondition => unreachable!(),
        }
    }

    fn validate_pure_comparison_capture(
        &self,
        id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        element: Ty<'tcx>,
    ) -> Result<(), String> {
        if self.tcx.coroutine_kind(id).is_some()
            || !matches!(args.as_closure().kind_ty().kind(), ty::Int(ty::IntTy::I16))
        {
            return Err("pure membership capture is not a resolved synchronous FnMut".into());
        }
        let closure = Ty::new_closure(self.tcx, id, args);
        if closure.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) {
            return Err("pure membership callback has destructor effects".into());
        }
        let captures = args.as_closure().tupled_upvars_ty();
        let ty::Tuple(fields) = captures.kind() else {
            return Err("pure membership capture schema is not a compiler tuple".into());
        };
        if fields.len() != 1 || shared_pointee(fields[0]) != Some(element) {
            return Err(
                "pure membership closure does not capture exactly the original needle".into(),
            );
        }
        Ok(())
    }

    fn pure_comparison_intrinsic(
        &self,
        id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        family: super::pure_comparison_templates::PureTemplateFamily,
        types: &[Ty<'tcx>],
    ) -> Result<bool, String> {
        use super::pure_comparison_templates::PureTemplateFamily as Family;
        if family == Family::SpecArrayBytes && self.tcx.is_intrinsic(id, Symbol::intern("raw_eq")) {
            let original = args.type_at(0);
            if !types.contains(&original) || !bitwise_comparison_type(original, 0) {
                return Err("raw array comparison lacks its original bitwise equality type".into());
            }
            let signature = self.call_signature(ty::Instance::new_raw(id, args))?;
            if signature.inputs().len() != 2
                || signature
                    .inputs()
                    .iter()
                    .any(|input| shared_pointee(*input) != Some(original))
                || !signature.output().is_bool()
                || signature.c_variadic()
                || signature.safety() != rustc_hir::Safety::Unsafe
            {
                return Err("raw array comparison differs from its compiler signature".into());
            }
            return Ok(true);
        }
        if family != Family::SliceEqualityBytes
            || !self.tcx.is_intrinsic(id, Symbol::intern("compare_bytes"))
        {
            return Ok(false);
        }
        let signature = self.call_signature(ty::Instance::new_raw(id, args))?;
        let [left, right, count] = signature.inputs() else {
            return Err("byte comparison intrinsic lacks its exact compiler arguments".into());
        };
        if !matches!(left.kind(), ty::RawPtr(child, mutable)
            if *child == self.tcx.types.u8 && !mutable.is_mut())
            || left != right
            || *count != self.tcx.types.usize
            || signature.output() != self.tcx.types.i32
            || signature.c_variadic()
            || signature.safety() != rustc_hir::Safety::Unsafe
        {
            return Err("byte comparison intrinsic differs from its compiler signature".into());
        }
        Ok(true)
    }
}

fn shared_pointee(original: Ty<'_>) -> Option<Ty<'_>> {
    match original.kind() {
        ty::Ref(_, element, mutable) if !mutable.is_mut() => Some(*element),
        _ => None,
    }
}

fn bitwise_comparison_type(original: Ty<'_>, depth: usize) -> bool {
    if depth >= 16 {
        return false;
    }
    match original.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) => true,
        ty::Array(child, _) => bitwise_comparison_type(*child, depth + 1),
        _ => false,
    }
}

#[derive(Clone, Debug)]
pub(super) enum PureComparison<'tcx> {
    Primitive(Ty<'tcx>),
    Tuple(Vec<PureComparison<'tcx>>),
    Array {
        original: Ty<'tcx>,
        count: usize,
        child: Box<PureComparison<'tcx>>,
    },
    Struct {
        original: Ty<'tcx>,
        fields: Vec<(String, PureComparison<'tcx>)>,
    },
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn pure_comparison_shape(
        &self,
        original: Ty<'tcx>,
    ) -> Result<Option<PureComparison<'tcx>>, String> {
        let mut nodes = 0;
        self.pure_comparison_depth(original, 0, &mut nodes)
    }

    fn pure_comparison_depth(
        &self,
        original: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<PureComparison<'tcx>>, String> {
        if depth >= 16 || *nodes >= 512 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "pure comparison exceeds its expanded type budget".into(),
            ));
        }
        *nodes += 1;
        if self.scalar_slice_element(original)?.is_some() {
            return Ok(Some(PureComparison::Primitive(original)));
        }
        match original.kind() {
            ty::Tuple(types) => {
                let mut fields = Vec::new();
                for original in types.iter() {
                    let Some(field) = self.pure_comparison_depth(original, depth + 1, nodes)?
                    else {
                        return Ok(None);
                    };
                    fields.push(field);
                }
                Ok(Some(PureComparison::Tuple(fields)))
            }
            ty::Array(element, count) => {
                let count = count
                    .try_to_target_usize(self.tcx)
                    .ok_or("pure comparison needs a concrete array length")?;
                if count > 128 {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "pure comparison array exceeds its type budget".into(),
                    ));
                }
                let before = *nodes;
                // Even a vacant array certifies its original child type before admission.
                let Some(child) = self.pure_comparison_depth(*element, depth + 1, nodes)? else {
                    return Ok(None);
                };
                let cost = *nodes - before;
                *nodes = before
                    .checked_add(
                        cost.checked_mul(count.max(1) as usize)
                            .ok_or("pure comparison type cost overflow")?,
                    )
                    .ok_or("pure comparison type cost overflow")?;
                if *nodes > 512 {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "pure comparison exceeds its expanded type budget".into(),
                    ));
                }
                Ok(Some(PureComparison::Array {
                    original,
                    count: count as usize,
                    child: Box::new(child),
                }))
            }
            ty::Adt(_, _) => {
                let Some(original_fields) = self.nominal_comparison_fields(original)? else {
                    return Ok(None);
                };
                let mut fields = Vec::new();
                for (name, original) in original_fields {
                    let Some(field) = self.pure_comparison_depth(original, depth + 1, nodes)?
                    else {
                        return Ok(None);
                    };
                    fields.push((name, field));
                }
                Ok(Some(PureComparison::Struct { original, fields }))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn pure_comparison_equal(
        &self,
        plan: &PureComparison<'tcx>,
        left: &Value,
        right: &Value,
    ) -> Result<Term, String> {
        match plan {
            PureComparison::Primitive(original) => {
                let _ = original;
                symbolic::binary(&self.terms, "eq", left.clone(), right.clone())?.boolean()
            }
            PureComparison::Tuple(fields) if fields.is_empty() => {
                if !matches!((left, right), (Value::Unit, Value::Unit)) {
                    return Err("pure comparison unit carrier differs from its type".into());
                }
                Ok(self.terms.boolean(true))
            }
            PureComparison::Tuple(fields) => {
                let (Value::Tuple(left), Value::Tuple(right)) = (left, right) else {
                    return Err("pure comparison tuple carrier differs from its type".into());
                };
                if left.len() != fields.len() || right.len() != fields.len() {
                    return Err("pure comparison tuple field count differs".into());
                }
                let mut result = self.terms.boolean(true);
                for ((field, left), right) in fields.iter().zip(left).zip(right) {
                    let equal = self.pure_comparison_equal(field, left, right)?;
                    result = self.terms.apply(Op::And, &[result, equal])?;
                }
                Ok(result)
            }
            PureComparison::Array {
                original,
                count,
                child,
            } => {
                let left = self.pure_comparison_array(*original, *count, left)?;
                let right = self.pure_comparison_array(*original, *count, right)?;
                let mut result = self.terms.boolean(true);
                for (left, right) in left.iter().zip(&right) {
                    let equal = self.pure_comparison_equal(child, left, right)?;
                    result = self.terms.apply(Op::And, &[result, equal])?;
                }
                Ok(result)
            }
            PureComparison::Struct { original, fields } => {
                self.validate_nominal_comparison_observation(plan, left)?;
                self.validate_nominal_comparison_observation(plan, right)?;
                let left = self.pure_comparison_struct(*original, fields, left)?;
                let right = self.pure_comparison_struct(*original, fields, right)?;
                let mut result = self.terms.boolean(true);
                for (((_, plan), (_, left)), (_, right)) in fields.iter().zip(left).zip(right) {
                    let equal = self.pure_comparison_equal(plan, left, right)?;
                    result = self.terms.apply(Op::And, &[result, equal])?;
                }
                Ok(result)
            }
        }
    }

    fn validate_nominal_comparison_observation(
        &self,
        plan: &PureComparison<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        match plan {
            PureComparison::Primitive(original) => {
                let kind = self
                    .scalar_slice_element(*original)?
                    .ok_or("nominal comparison leaf has no exact primitive type")?;
                let valid = match (kind, value) {
                    (ScalarSliceElement::Bool, Value::Bool(term)) => {
                        term.sort() == &Sort::Bool && term.belongs_to(&self.terms)
                    }
                    (
                        ScalarSliceElement::Integer { bits, signed },
                        Value::Int {
                            expression,
                            bits: actual,
                            signed: sign,
                        },
                    ) => {
                        bits == *actual
                            && signed == *sign
                            && expression.sort() == &Sort::BitVec(bits)
                            && expression.belongs_to(&self.terms)
                    }
                    (
                        ScalarSliceElement::Char,
                        Value::Int {
                            expression,
                            bits: 32,
                            signed: false,
                        },
                    ) => {
                        expression.sort() == &Sort::BitVec(32) && expression.belongs_to(&self.terms)
                    }
                    (
                        ScalarSliceElement::Float { bits },
                        Value::Float {
                            expression,
                            bits: actual,
                            ..
                        },
                    ) => {
                        let (exponent, significand) = if bits == 32 { (8, 24) } else { (11, 53) };
                        bits == *actual
                            && expression.sort()
                                == &Sort::Float {
                                    exponent,
                                    significand,
                                }
                            && expression.belongs_to(&self.terms)
                    }
                    _ => false,
                };
                // Incoming/needle certificates already establish Unicode validity using their
                // actual free conditions. This is metadata validation, never a new char premise.
                if !valid {
                    return Err("nominal comparison primitive carrier differs from its type".into());
                }
            }
            PureComparison::Tuple(plans) if plans.is_empty() => {
                if !matches!(value, Value::Unit) {
                    return Err("nominal comparison unit has a different carrier".into());
                }
            }
            PureComparison::Tuple(plans) => {
                let Value::Tuple(values) = value else {
                    return Err("nominal comparison tuple has a different carrier".into());
                };
                if plans.len() != values.len() {
                    return Err("nominal comparison tuple has a different field count".into());
                }
                for (plan, value) in plans.iter().zip(values) {
                    self.validate_nominal_comparison_observation(plan, value)?;
                }
            }
            PureComparison::Array {
                original,
                count,
                child,
            } => {
                for value in self.pure_comparison_array(*original, *count, value)? {
                    self.validate_nominal_comparison_observation(child, &value)?;
                }
            }
            PureComparison::Struct { original, fields } => {
                let values = self.pure_comparison_struct(*original, fields, value)?;
                for ((_, plan), (_, value)) in fields.iter().zip(values) {
                    self.validate_nominal_comparison_observation(plan, value)?;
                }
            }
        }
        Ok(())
    }

    fn pure_comparison_struct<'a>(
        &self,
        original: Ty<'tcx>,
        expected: &[(String, PureComparison<'tcx>)],
        value: &'a Value,
    ) -> Result<&'a [(String, Value)], String> {
        let ty::Adt(definition, _) = original.kind() else {
            return Err("nominal comparison plan lacks its original struct type".into());
        };
        let Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } = value
        else {
            return Err("nominal comparison has a different struct carrier".into());
        };
        if *name != self.tcx.def_path_str(definition.did())
            || *variant != 0
            || *is_option
            || *discriminant != 0
            || fields.len() != expected.len()
            || fields
                .iter()
                .zip(expected)
                .any(|((actual, _), (expected, _))| actual != expected)
        {
            return Err("nominal comparison struct identity or fields differ".into());
        }
        Ok(fields)
    }

    fn pure_comparison_array(
        &self,
        original: Ty<'tcx>,
        count: usize,
        value: &Value,
    ) -> Result<Vec<Value>, String> {
        match value {
            Value::Elements(values) if values.len() == count => Ok(values.to_vec()),
            Value::Bytes { length, data }
                if matches!(original.kind(), ty::Array(element, _) if *element == self.tcx.types.u8)
                    && aggregate_validity::byte_array_payload_matches(
                        &self.terms,
                        u32::from(self.tcx.sess.target.pointer_width),
                        count as u64,
                        length,
                        data,
                    )? =>
            {
                (0..count)
                    .map(|index| {
                        let index = self.terms.bit_vector(
                            index as u128,
                            u32::from(self.tcx.sess.target.pointer_width),
                        )?;
                        Ok(Value::Int {
                            expression: self.terms.apply(Op::Select, &[data.clone(), index])?,
                            bits: 8,
                            signed: false,
                        })
                    })
                    .collect()
            }
            _ => Err("pure comparison array carrier differs from its exact type".into()),
        }
    }
}

fn cursor_arithmetic_counterexample(
    context: &Context,
    premise: CursorArithmetic,
    cursor: &Term,
    end: &Term,
) -> Result<Term, String> {
    let Sort::BitVec(width) = cursor.sort() else {
        return Err("cursor arithmetic requires unsigned bit vectors".into());
    };
    if !matches!(width, 32 | 64)
        || cursor.sort() != end.sort()
        || !cursor.belongs_to(context)
        || !end.belongs_to(context)
    {
        return Err("cursor arithmetic has incompatible target terms".into());
    }
    let one = context.bit_vector(1, *width)?;
    let zero = context.bit_vector(0, *width)?;
    let (guard, violates) = match premise {
        CursorArithmetic::SubAfterNonzero => {
            let result = context.apply(Op::BvSub, &[cursor.clone(), one])?;
            (
                context.apply(Op::BvUnsignedGt, &[cursor.clone(), zero])?,
                context.apply(Op::BvUnsignedGe, &[result, cursor.clone()])?,
            )
        }
        CursorArithmetic::AddBelowEnd => {
            let result = context.apply(Op::BvAdd, &[cursor.clone(), one])?;
            (
                context.apply(Op::BvUnsignedLt, &[cursor.clone(), end.clone()])?,
                context.apply(
                    Op::Or,
                    &[
                        context.apply(Op::BvUnsignedLe, &[result.clone(), cursor.clone()])?,
                        context.apply(Op::BvUnsignedGt, &[result, end.clone()])?,
                    ],
                )?,
            )
        }
    };
    context.apply(Op::And, &[guard, violates])
}

#[derive(Default)]
struct ComparisonLayoutConstants<'tcx> {
    values: Vec<rustc_middle::mir::ConstOperand<'tcx>>,
    overflow: bool,
}

impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for ComparisonLayoutConstants<'tcx> {
    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _: rustc_middle::mir::Location,
    ) {
        if self.values.len() >= 512 {
            self.overflow = true;
        } else {
            self.values.push(*constant);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsigned_cursor_guards_exclude_overflow_at_full_target_extent() {
        for width in [32, 64] {
            let context = Context::default();
            let cursor = context.symbol(0, Sort::BitVec(width)).unwrap();
            let end = context.symbol(1, Sort::BitVec(width)).unwrap();
            for premise in [
                CursorArithmetic::AddBelowEnd,
                CursorArithmetic::SubAfterNonzero,
            ] {
                let invalid =
                    cursor_arithmetic_counterexample(&context, premise, &cursor, &end).unwrap();
                let query =
                    Query::new(&context.declarations(), &[], &invalid.smt(200_000).unwrap());
                assert!(matches!(
                    Solver::default().check_query(&query),
                    Answer::Unsat
                ));
            }
            let max = (1u128 << width) - 1;
            for (premise, cursor, end) in [
                (CursorArithmetic::AddBelowEnd, max - 1, max),
                (CursorArithmetic::SubAfterNonzero, max, max),
                (CursorArithmetic::SubAfterNonzero, 1, max),
            ] {
                let invalid = cursor_arithmetic_counterexample(
                    &context,
                    premise,
                    &context.bit_vector(cursor, width).unwrap(),
                    &context.bit_vector(end, width).unwrap(),
                )
                .unwrap();
                assert_eq!(invalid.constant(), Some(miren::smt::Constant::Bool(false)));
            }
            // Removing the caller guard exposes exactly the wrap/borrow excluded above.
            assert_eq!(
                context
                    .apply(
                        Op::BvAdd,
                        &[
                            context.bit_vector(max, width).unwrap(),
                            context.bit_vector(1, width).unwrap(),
                        ]
                    )
                    .unwrap()
                    .constant(),
                Some(miren::smt::Constant::BitVec(0))
            );
            assert_eq!(
                context
                    .apply(
                        Op::BvSub,
                        &[
                            context.bit_vector(0, width).unwrap(),
                            context.bit_vector(1, width).unwrap(),
                        ]
                    )
                    .unwrap()
                    .constant(),
                Some(miren::smt::Constant::BitVec(max))
            );
        }
        let context = Context::default();
        let foreign = Context::default();
        assert!(
            cursor_arithmetic_counterexample(
                &context,
                CursorArithmetic::AddBelowEnd,
                &context.bit_vector(0, 32).unwrap(),
                &foreign.bit_vector(1, 32).unwrap(),
            )
            .is_err()
        );
    }
}
