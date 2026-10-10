//! Complete typed synthesized drop glue; no local type is erased in the core encoder.
use super::*;
use owned_box_templates::BoxTemplateFamily;
use rustc_middle::mir::{BasicBlock, BorrowKind, Local, MutBorrowKind, UnwindAction};

pub(super) fn nominal_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    certificate: &owned_box_payloads::Certificate<'tcx>,
    owner: Ty<'tcx>,
) -> Result<BoxTemplateFamily, String> {
    let payload = certificate.original();
    if body.coroutine.is_some()
        || body.tainted_by_errors.is_some()
        || body.spread_arg.is_some()
        || body.basic_blocks.iter().any(|block| block.is_cleanup)
    {
        return Err("nominal Box glue contains coroutine or cleanup metadata".into());
    }
    let ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, selected)) = instance.def else {
        return Err("nominal Box glue requires its exact selected DropGlue shim".into());
    };
    if body.arg_count != 1 || body.return_ty() != tcx.types.unit {
        return Err("nominal Box glue has a different original argument/result schema".into());
    }
    if instance.args.type_at(0) != selected.unwrap_or(payload) {
        return Err("nominal Box glue selected generic identity differs".into());
    }
    if selected.is_none() && !payload.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
        if body.local_decls.len() != 2
            || !mutable_reference(body.local_decls[Local::from_usize(1)].ty, payload)
            || body.basic_blocks.len() != 1
            || !body.basic_blocks[BasicBlock::from_usize(0)]
                .statements
                .is_empty()
            || !matches!(
                body.basic_blocks[BasicBlock::from_usize(0)]
                    .terminator()
                    .kind,
                TerminatorKind::Return
            )
        {
            return Err(
                "nominal payload no-drop glue differs from its complete Return body".into(),
            );
        }
        return Ok(BoxTemplateFamily::UnitDropGlue);
    }
    if selected != Some(owner) || body.local_decls.len() != 7 || body.basic_blocks.len() != 3 {
        return Err("nominal owned drop glue differs from its complete local/block schema".into());
    }
    let ty::Adt(def, args) = owner.kind() else {
        return Err("nominal Box glue owner is not its original ADT".into());
    };
    if tcx.lang_items().owned_box() != Some(def.did()) || args.type_at(0) != payload {
        return Err("nominal Box glue owner/payload identity differs".into());
    }
    let unique = def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)]
        .ty(tcx, args)
        .skip_norm_wip();
    let ty::Adt(unique_def, unique_args) = unique.kind() else {
        return Err("nominal Box glue Unique field type is unavailable".into());
    };
    let nonnull = unique_def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)]
        .ty(tcx, unique_args)
        .skip_norm_wip();
    for index in [1, 2, 4] {
        if !mutable_reference(body.local_decls[Local::from_usize(index)].ty, owner) {
            return Err("nominal Box glue mutable receiver declaration differs".into());
        }
    }
    for index in [0, 3, 5] {
        if body.local_decls[Local::from_usize(index)].ty != tcx.types.unit {
            return Err("nominal Box glue Unit declaration differs".into());
        }
    }
    let pointer = body.local_decls[Local::from_usize(6)].ty;
    if !matches!(pointer.kind(), ty::RawPtr(inner, mutable)
        if *inner == payload && !mutable.is_mut())
    {
        return Err("nominal Box glue payload pointer has a different original type".into());
    }
    let first = &body.basic_blocks[BasicBlock::from_usize(0)];
    let [statement] = first.statements.as_slice() else {
        return Err("nominal Box glue pointer block has a different complete effect count".into());
    };
    let StatementKind::Assign(assignment) = &statement.kind else {
        return Err("nominal Box glue lost its original pointer assignment".into());
    };
    let Rvalue::Cast(CastKind::Transmute, Operand::Copy(source), target) = &assignment.1 else {
        return Err("nominal Box glue pointer transport differs".into());
    };
    if !whole_local(assignment.0, 6)
        || *target != pointer
        || source.local.as_usize() != 1
        || !matches!(source.projection.as_ref(), [
            ProjectionElem::Deref,
            ProjectionElem::Field(first, first_ty),
            ProjectionElem::Field(second, second_ty),
        ] if first.as_usize() == 0 && *first_ty == unique
            && second.as_usize() == 0 && *second_ty == nonnull)
    {
        return Err("nominal Box glue pointer origin/type differs from its original owner".into());
    }
    if !matches!(&first.terminator().kind,
        TerminatorKind::Drop {
            place, target, unwind: UnwindAction::Unreachable, replace: false, drop: None,
        }
        if place.local.as_usize() == 6
            && matches!(place.projection.as_ref(), [ProjectionElem::Deref])
            && target.as_usize() == 2)
    {
        return Err("nominal Box glue payload Drop edge differs".into());
    }
    let last = &body.basic_blocks[BasicBlock::from_usize(1)];
    if !last.statements.is_empty() || !matches!(last.terminator().kind, TerminatorKind::Return) {
        return Err("nominal Box glue return block has an unsupported effect".into());
    }
    let delegate = &body.basic_blocks[BasicBlock::from_usize(2)];
    let [statement] = delegate.statements.as_slice() else {
        return Err("nominal Box glue delegate block has a different complete effect count".into());
    };
    let StatementKind::Assign(assignment) = &statement.kind else {
        return Err("nominal Box glue lost its same-owner reborrow".into());
    };
    if !whole_local(assignment.0, 2)
        || !matches!(&assignment.1,
            Rvalue::Ref(_, BorrowKind::Mut { kind: MutBorrowKind::Default }, place)
            if place.local.as_usize() == 1
                && matches!(place.projection.as_ref(), [ProjectionElem::Deref]))
    {
        return Err("nominal Box glue delegate receiver differs from its original owner".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target: Some(target),
        unwind: UnwindAction::Unreachable,
        ..
    } = &delegate.terminator().kind
    else {
        return Err("nominal Box glue delegate lacks its complete normal Call edge".into());
    };
    let Operand::Constant(constant) = func else {
        return Err("nominal Box glue delegate requires its exact constant FnDef operand".into());
    };
    if !matches!(
        constant
            .const_
            .eval(tcx, ty::TypingEnv::fully_monomorphized(), constant.span),
        Ok(rustc_middle::mir::ConstValue::ZeroSized)
    ) {
        return Err("nominal Box glue delegate constant has no exact function value".into());
    }
    let ty::FnDef(id, generic) = constant.const_.ty().kind() else {
        return Err("nominal Box glue selected delegate is not a direct function".into());
    };
    let drop_trait = tcx
        .lang_items()
        .drop_trait()
        .ok_or("Drop trait identity unavailable")?;
    if tcx.parent(*id) != drop_trait
        || tcx.item_name(*id).as_str() != "drop"
        || generic.skip_binder().len() != 1
        || generic.skip_binder().type_at(0) != owner
        || args.len() != 1
        || !matches!(&args[0].node, Operand::Move(place) if whole_local(*place, 2))
        || !whole_local(*destination, 3)
        || target.as_usize() != 1
    {
        return Err("nominal Box glue selected delegate arguments/result identity differs".into());
    }
    // Its actual selected full body is independently certified by the protocol worklist.
    Ok(BoxTemplateFamily::UnitBoxDropGlue)
}

fn whole_local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}

fn mutable_reference<'tcx>(original: Ty<'tcx>, inner: Ty<'tcx>) -> bool {
    matches!(original.kind(), ty::Ref(_, target, mutable) if *target == inner && mutable.is_mut())
}
