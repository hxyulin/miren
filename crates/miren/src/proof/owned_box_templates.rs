//! Complete selected library bodies for the private zero-sized Box protocol.
//! Matching is a prerequisite; it neither issues a region nor grants pointer access.
use super::*;
use rustc_span::Symbol;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BoxTemplateFamily {
    MemDrop,
    UnitBoxDropGlue,
    UnitDropGlue,
    BoxDrop,
    LayoutPrecondition,
    AlignmentPrecondition,
    GlobalDeallocate,
    BoxNew,
    BoxNewUninit,
    GlobalAllocate,
    NonNullPrecondition,
}

fn reference_family(definition: &str, encoded: &str) -> Option<BoxTemplateFamily> {
    super::owned_box_references::REFERENCES
        .iter()
        .find_map(|(expected, family, body)| {
            (*expected == definition && body.strip_suffix('\n') == Some(encoded)).then_some(*family)
        })
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ProtocolInput {
    UnitPayload,
    OwnedUnit,
    OwnedUnitReference,
    UnitReference,
    ZeroLayout,
    NonNullUnitAlignment,
    UnitAlignment,
    ZeroSizeUnitAlignment,
}

fn reached_blocks(
    family: BoxTemplateFamily,
    input: ProtocolInput,
    bits: u32,
) -> Result<&'static [usize], String> {
    if !matches!(bits, 32 | 64) {
        return Err("Box protocol requires a certified target word width".into());
    }
    match (family, input) {
        // BoxNew forwards the actual compiler Layout(0,1), writes the Unit payload,
        // then returns the very pointer received from that allocation. Its cleanup
        // edge is excluded only after the zero allocation and no-drop Unit are certified.
        (BoxTemplateFamily::BoxNew, ProtocolInput::UnitPayload) => Ok(&[0, 1]),
        // Global's matched return is Ok(NonNull(slice(alignment, 0))). Therefore the
        // exact discriminant test at bb4 chooses Ok bb3, not OOM bb2 or impossible bb1.
        (BoxTemplateFamily::BoxNewUninit, ProtocolInput::ZeroLayout) => Ok(&[0, 4, 3]),
        // _3 = layout.size = 0, so bb0 selects bb2. _15 = layout.align = 1.
        // Both UbChecks branches converge on the same zero-length Ok allocation.
        // No allocator, failure Result, or nonzero-only Assume block is reachable.
        (BoxTemplateFamily::GlobalAllocate, ProtocolInput::ZeroLayout) => {
            Ok(&[0, 2, 8, 9, 10, 6, 7])
        }
        (BoxTemplateFamily::MemDrop, ProtocolInput::OwnedUnit) => Ok(&[0, 1]),
        (BoxTemplateFamily::UnitBoxDropGlue, ProtocolInput::OwnedUnitReference) => Ok(&[0, 2, 1]),
        (BoxTemplateFamily::UnitDropGlue, ProtocolInput::UnitReference) => Ok(&[0]),
        // size_of_val::<()> = 0 and align_of_val::<()> = 1. Both UbChecks settings
        // are covered. The exact final size switch chooses bb3, excluding deallocate.
        (BoxTemplateFamily::BoxDrop, ProtocolInput::OwnedUnitReference) => {
            Ok(&[0, 4, 5, 6, 7, 8, 9, 3])
        }
        // ctpop(1) = 1, so the matched equality chooses successful return bb1.
        (BoxTemplateFamily::AlignmentPrecondition, ProtocolInput::UnitAlignment)
            if 1_u128.count_ones() == 1 =>
        {
            Ok(&[0, 3, 1])
        }
        // The concrete target-width predicate is 0 <= (1 << (bits-1)) - 1.
        // It selects the successful return; no missing panic body is required.
        (BoxTemplateFamily::LayoutPrecondition, ProtocolInput::ZeroSizeUnitAlignment)
            if layout_predicate(0, 1, bits)? =>
        {
            Ok(&[0, 1])
        }
        // The matched pointer is the compiler alignment sentinel 1, never null.
        // This is template-only arithmetic, not a runtime numeric access grant.
        (BoxTemplateFamily::NonNullPrecondition, ProtocolInput::NonNullUnitAlignment)
            if 1_u128 != 0 =>
        {
            Ok(&[0, 2])
        }
        _ => Err("Box selected family lacks its exact caller input relation".into()),
    }
}

fn layout_predicate(size: u128, alignment: u128, bits: u32) -> Result<bool, String> {
    let ceiling = (1_u128 << (bits - 1))
        .checked_sub(alignment)
        .ok_or("Box layout rounded extent underflows")?;
    Ok(size <= ceiling)
}

fn local_argument(
    args: &[rustc_span::Spanned<Operand<'_>>],
    index: usize,
    local: usize,
) -> Result<(), String> {
    if matches!(args.get(index).map(|arg| &arg.node),
        Some(Operand::Copy(place) | Operand::Move(place))
        if place.local.as_usize() == local && place.projection.is_empty())
    {
        Ok(())
    } else {
        Err("Box delegate operand differs from its certified forwarding local".into())
    }
}

pub(super) fn compiler_unit_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
) -> Result<(), String> {
    use rustc_const_eval::const_eval::mk_eval_cx_for_const_val;
    let Operand::Constant(operand) = operand else {
        return Err("BoxNew did not pass its compiler Layout constant".into());
    };
    let env = ty::TypingEnv::fully_monomorphized();
    let value = operand
        .const_
        .eval(tcx, env, operand.span)
        .map_err(|_| "Box compiler Layout constant is unavailable")?;
    let (ecx, value) =
        mk_eval_cx_for_const_val(tcx.at(operand.span), env, value, operand.const_.ty())
            .ok_or("Box compiler Layout lacks concrete storage")?;
    if value.layout.fields.count() != 2 {
        return Err("Box compiler Layout differs from its certified two fields".into());
    }
    for (index, expected) in [(0, 0_u128), (1, 1_u128)] {
        let field = ecx
            .project_field(&value, rustc_abi::FieldIdx::from_usize(index))
            .discard_err()
            .ok_or("Box compiler Layout field is unavailable")?;
        let scalar = ecx
            .read_scalar(&field)
            .discard_err()
            .ok_or("Box Layout field is not a scalar")?;
        let actual = scalar
            .to_bits(field.layout.size)
            .discard_err()
            .ok_or("Box Layout field lacks concrete integer bits")?;
        if actual != expected {
            return Err("Box passed Layout differs from original Unit size/alignment".into());
        }
    }
    Ok(())
}

pub(super) fn certify_unit_protocol<'tcx>(
    tcx: TyCtxt<'tcx>,
    outer: ty::Instance<'tcx>,
) -> Result<(), String> {
    let owned = tcx
        .lang_items()
        .owned_box()
        .ok_or("Box lang identity is unavailable")?;
    let core = tcx
        .lang_items()
        .sized_trait()
        .ok_or("core identity is unavailable")?
        .krate;
    let constructor = tcx
        .get_diagnostic_item(Symbol::intern("box_new"))
        .filter(|id| id.krate == owned.krate)
        .ok_or("Box constructor identity is unavailable")?;
    let original = tcx.types.unit;
    let constructor_args = tcx.mk_args(&[original.into()]);
    let constructor_signature = tcx
        .fn_sig(constructor)
        .instantiate(tcx, constructor_args)
        .skip_binder();
    let box_type = constructor_signature.output();
    let ty::Adt(definition, box_args) = box_type.kind() else {
        return Err("Box constructor does not return the actual owned type".into());
    };
    if definition.did() != owned || box_args.type_at(0) != original {
        return Err("Box constructor original payload identity differs".into());
    }
    let global = box_args.type_at(1);
    let ty::Adt(global_def, global_args) = global.kind() else {
        return Err("Box constructor allocator is not an original concrete ADT".into());
    };
    if global_def.did().krate != owned.krate || !global_args.is_empty() {
        return Err("Box constructor allocator is not the exact default Global".into());
    }
    let outer_key = pure_comparison_templates::owned_definition_key(outer.def_id());
    let is_owner_glue = match outer.def {
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(t))) => t == box_type,
        _ => false,
    };
    if outer.def_id() != constructor && outer_key != "DefId(core::mem::drop)" && !is_owner_glue {
        return Err(
            "Box protocol must begin at its constructor or exact owned drop boundary".into(),
        );
    }
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
        .map_err(|error| format!("Box payload layout is unavailable: {error:?}"))?;
    let bits = u32::from(tcx.sess.target.pointer_width);
    let align = u128::from(layout.align.abi.bytes());
    if layout.size.bytes() != 0 || align != 1 || align > (u128::MAX >> (128 - bits)) {
        return Err("Box zero branch lacks a concrete nonzero target alignment".into());
    }
    if core == owned.krate {
        return Err("Box alloc identity is not distinct from core".into());
    }
    let root_input = if outer.def_id() == constructor {
        ProtocolInput::UnitPayload
    } else if matches!(outer.def, ty::InstanceKind::Shim(_)) {
        ProtocolInput::OwnedUnitReference
    } else {
        ProtocolInput::OwnedUnit
    };
    let mut pending = vec![(outer, root_input, None)];
    let mut seen = std::collections::HashSet::new();
    while let Some((instance, input, expected_family)) = pending.pop() {
        if !seen.insert((instance, input)) {
            continue;
        }
        if seen.len() > 512 {
            return Err("Box body certificate exceeds its node budget".into());
        }
        if instance.def_id().krate != core && instance.def_id().krate != owned.krate {
            return Err(
                "Box protocol selected a definition outside authenticated core/alloc".into(),
            );
        }
        match instance.def {
            ty::InstanceKind::Item(id) if tcx.is_mir_available(id) => {}
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, _)) => {}
            _ => {
                return Err("Box protocol requires an available concrete selected MIR body".into());
            }
        }
        let generic = tcx.instance_mir(instance.def);
        let encoded = pure_comparison_templates::encode_template_with_alloc(
            tcx,
            generic,
            core,
            Some(owned.krate),
        )?;
        let definition = pure_comparison_templates::owned_definition_key(instance.def_id());
        let family = reference_family(&definition, &encoded).ok_or_else(|| {
            format!("Box protocol body differs from its complete reference: {definition}")
        })?;
        if family == BoxTemplateFamily::BoxNew && instance.def_id() != constructor {
            return Err("Box constructor does not have the actual diagnostic identity".into());
        }
        let exact_arguments = match family {
            BoxTemplateFamily::BoxNew => instance.args.type_at(0) == original,
            BoxTemplateFamily::MemDrop | BoxTemplateFamily::UnitBoxDropGlue => {
                instance.args.type_at(0) == box_type
            }
            BoxTemplateFamily::UnitDropGlue => instance.args.type_at(0) == original,
            BoxTemplateFamily::BoxDrop => {
                instance.args.type_at(0) == original && instance.args.type_at(1) == global
            }
            BoxTemplateFamily::LayoutPrecondition
            | BoxTemplateFamily::AlignmentPrecondition
            | BoxTemplateFamily::GlobalDeallocate
            | BoxTemplateFamily::BoxNewUninit
            | BoxTemplateFamily::GlobalAllocate
            | BoxTemplateFamily::NonNullPrecondition => instance.args.is_empty(),
        };
        if !exact_arguments {
            return Err(
                "Box protocol selected different original payload or allocator arguments".into(),
            );
        }
        let body = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(tcx, generic.clone()),
            )
            .map_err(|_| "Box selected body could not be instantiated")?;
        if expected_family.is_some_and(|expected| expected != family) {
            return Err("Box selected delegate differs from the certified child family".into());
        }
        for index in reached_blocks(family, input, bits)? {
            let block = body
                .basic_blocks
                .get(rustc_middle::mir::BasicBlock::from_usize(*index))
                .ok_or("Box derivation references a missing matched block")?;
            for statement in &block.statements {
                if matches!(statement.kind, StatementKind::Intrinsic(_)) {
                    return Err("Box reachable Assume lacks an independently true predicate".into());
                }
            }
            match &block.terminator().kind {
                TerminatorKind::Call { func, args, .. } => {
                    let ty::FnDef(id, generic_args) = func.ty(&body.local_decls, tcx).kind() else {
                        return Err("Box protocol has an indirect selected call".into());
                    };
                    let intrinsic = match (family, *index) {
                        (BoxTemplateFamily::BoxDrop, 0) => Some("size_of_val"),
                        (BoxTemplateFamily::BoxDrop, 4) => Some("align_of_val"),
                        (BoxTemplateFamily::AlignmentPrecondition, 0) => Some("ctpop"),
                        _ => None,
                    };
                    if let Some(name) = intrinsic {
                        if id.krate != core || !tcx.is_intrinsic(*id, Symbol::intern(name)) {
                            return Err(
                                "Box arithmetic delegate is not the exact compiler intrinsic"
                                    .into(),
                            );
                        }
                        let expected = if name == "ctpop" {
                            tcx.types.usize
                        } else {
                            original
                        };
                        if generic_args.skip_binder().type_at(0) != expected {
                            return Err("Box intrinsic uses a different original type".into());
                        }
                        local_argument(args, 0, if name == "ctpop" { 1 } else { 3 })?;
                        continue;
                    }
                    let (child_family, child_input) = match (family, *index) {
                        (BoxTemplateFamily::BoxNew, 0) => {
                            compiler_unit_layout(tcx, &args[0].node)?;
                            (BoxTemplateFamily::BoxNewUninit, ProtocolInput::ZeroLayout)
                        }
                        (BoxTemplateFamily::BoxNewUninit, 0) => {
                            local_argument(args, 0, 1)?;
                            (BoxTemplateFamily::GlobalAllocate, ProtocolInput::ZeroLayout)
                        }
                        (BoxTemplateFamily::GlobalAllocate, 8) => {
                            local_argument(args, 0, 19)?;
                            (
                                BoxTemplateFamily::NonNullPrecondition,
                                ProtocolInput::NonNullUnitAlignment,
                            )
                        }
                        (BoxTemplateFamily::UnitBoxDropGlue, 2) => {
                            local_argument(args, 0, 2)?;
                            (
                                BoxTemplateFamily::BoxDrop,
                                ProtocolInput::OwnedUnitReference,
                            )
                        }
                        (BoxTemplateFamily::BoxDrop, 6) => {
                            local_argument(args, 0, 10)?;
                            (
                                BoxTemplateFamily::AlignmentPrecondition,
                                ProtocolInput::UnitAlignment,
                            )
                        }
                        (BoxTemplateFamily::BoxDrop, 8) => {
                            local_argument(args, 0, 8)?;
                            local_argument(args, 1, 9)?;
                            (
                                BoxTemplateFamily::LayoutPrecondition,
                                ProtocolInput::ZeroSizeUnitAlignment,
                            )
                        }
                        _ => {
                            return Err(
                                "Box reached a call outside its complete edge derivation".into()
                            );
                        }
                    };
                    let child = ty::Instance::try_resolve(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        *id,
                        generic_args.skip_binder(),
                    )
                    .map_err(|_| "Box delegate could not be resolved")?
                    .ok_or("Box delegate is unresolved")?;
                    pending.push((child, child_input, Some(child_family)));
                }
                TerminatorKind::Drop { place, .. } => {
                    let (child_family, child_input, expected) = match family {
                        BoxTemplateFamily::MemDrop => (
                            BoxTemplateFamily::UnitBoxDropGlue,
                            ProtocolInput::OwnedUnitReference,
                            box_type,
                        ),
                        BoxTemplateFamily::UnitBoxDropGlue => (
                            BoxTemplateFamily::UnitDropGlue,
                            ProtocolInput::UnitReference,
                            original,
                        ),
                        _ => return Err("Box reached an uncertified drop edge".into()),
                    };
                    if place.ty(&body.local_decls, tcx).ty != expected {
                        return Err("Box drop edge has a different original pointee type".into());
                    }
                    pending.push((
                        ty::Instance::resolve_drop_glue(tcx, expected),
                        child_input,
                        Some(child_family),
                    ));
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Return => {}
                _ => return Err("Box reached an unsupported effect or failure edge".into()),
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_box_templates_reject_changed_effect_and_return_bytes() {
        for (definition, family, body) in super::super::owned_box_references::REFERENCES {
            assert_eq!(
                reference_family(definition, body.strip_suffix('\n').unwrap()),
                Some(*family)
            );
            assert!(reference_family(definition, &(body.to_string() + "extra-effect\n")).is_none());
            assert!(reference_family("DefId(local::Box::new)", body).is_none());
            let changed = body.replacen("return", "unreachable", 1);
            if changed != *body {
                assert!(reference_family(definition, &changed).is_none());
            }
        }
    }
}
