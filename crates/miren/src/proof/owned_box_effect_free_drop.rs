//! Exact fieldless local payload and complete effect-free Drop schemas, never receiver rights.
use super::*;
use owned_box_templates::BoxTemplateFamily;
use rustc_middle::mir::{BasicBlock, BorrowKind, Local, MutBorrowKind, UnwindAction};

pub(super) struct Certificate<'tcx> {
    pub(super) original: Ty<'tcx>,
    pub(super) destructor: ty::Instance<'tcx>,
    pub(super) layout: owned_box_payloads::ZeroLayout,
}

pub(super) fn certify_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
) -> Result<Certificate<'tcx>, String> {
    let ty::Adt(def, _) = original.kind() else {
        return Err("effect-free Box Drop requires its original local fieldless struct".into());
    };
    if !def.is_struct()
        || !def.did().is_local()
        || def.repr().packed()
        || !def.non_enum_variant().fields.is_empty()
        || !original.is_freeze(tcx, ty::TypingEnv::fully_monomorphized())
    {
        return Err("effect-free Box Drop requires local fieldless unpacked Freeze storage".into());
    }
    let layout = owned_box_payloads::ZeroLayout::for_type(tcx, original)?;
    let destructor = def
        .destructor(tcx)
        .ok_or("effect-free Box Drop requires an actual selected custom destructor")?;
    let drop_trait = tcx
        .lang_items()
        .drop_trait()
        .ok_or("Drop trait unavailable")?;
    let method = tcx
        .associated_items(drop_trait)
        .in_definition_order()
        .find(|item| item.name() == rustc_span::Symbol::intern("drop"))
        .ok_or("original Drop trait method unavailable")?;
    let selected = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        method.def_id,
        tcx.mk_args(&[original.into()]),
    )
    .map_err(|_| "effect-free Box Drop selected implementation cannot be resolved")?
    .ok_or("effect-free Box Drop selected implementation is unresolved")?;
    if selected.def != ty::InstanceKind::Item(destructor.did) || !selected.def_id().is_local() {
        return Err("effect-free Box Drop trait/self/full selected Instance differs".into());
    }
    let signature = tcx
        .fn_sig(selected.def_id())
        .instantiate(tcx, selected.args)
        .skip_binder();
    if signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || signature.inputs().len() != 1
        || !mutable_reference(signature.inputs()[0], original)
        || signature.output() != tcx.types.unit
    {
        return Err("effect-free Box Drop original destructor signature differs".into());
    }
    Ok(Certificate {
        original,
        destructor: selected,
        layout,
    })
}

pub(super) fn validate_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    certificate: &Certificate<'tcx>,
    value: &Value,
) -> Result<Value, String> {
    let ty::Adt(def, _) = certificate.original.kind() else {
        unreachable!()
    };
    if !matches!(value, Value::Adt {name,variant:0,is_option:false,discriminant:0,fields}
        if *name == tcx.def_path_str(def.did()) && fields.is_empty())
    {
        return Err(
            "effect-free Box Drop payload differs from its original fieldless value".into(),
        );
    }
    Ok(value.clone())
}

fn mutable_reference<'tcx>(original: Ty<'tcx>, target: Ty<'tcx>) -> bool {
    matches!(original.kind(), ty::Ref(_, inner, mutable) if *inner==target && mutable.is_mut())
}
fn local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}
fn metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
) -> Result<(), String> {
    if body.source.instance != instance.def
        || body.source.promoted.is_some()
        || body.arg_count != 1
        || body.return_ty() != tcx.types.unit
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.tainted_by_errors.is_some()
        || body.basic_blocks.iter().any(|b| b.is_cleanup)
    {
        return Err("effect-free Box Drop original/current body metadata differs".into());
    }
    Ok(())
}

pub(super) fn destructor_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    certificate: &Certificate<'tcx>,
) -> Result<BoxTemplateFamily, String> {
    metadata(tcx, instance, body)?;
    if instance != certificate.destructor
        || body.local_decls.len() != 2
        || !mutable_reference(
            body.local_decls[Local::from_usize(1)].ty,
            certificate.original,
        )
        || body.basic_blocks.len() != 1
    {
        return Err(
            "effect-free Box Drop original/current destructor identity or locals differ".into(),
        );
    }
    let block = &body.basic_blocks[BasicBlock::from_usize(0)];
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return Err("effect-free Box Drop destructor is not a complete normal Return".into());
    }
    match block.statements.as_slice() {
        [] => {}
        [statement] => {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return Err(
                    "effect-free Box Drop destructor contains an unsupported effect".into(),
                );
            };
            let Rvalue::Use(
                Operand::Constant(constant),
                rustc_middle::mir::WithRetag::No | rustc_middle::mir::WithRetag::Yes,
            ) = &assignment.1
            else {
                return Err(
                    "effect-free Box Drop destructor contains an unsupported effect".into(),
                );
            };
            if !local(assignment.0, 0)
                || constant.const_.ty() != tcx.types.unit
                || !matches!(
                    constant
                        .const_
                        .eval(tcx, ty::TypingEnv::fully_monomorphized(), constant.span),
                    Ok(rustc_middle::mir::ConstValue::ZeroSized)
                )
            {
                return Err("effect-free Box Drop destructor return value differs".into());
            }
        }
        _ => return Err("effect-free Box Drop destructor contains an unsupported effect".into()),
    }
    Ok(BoxTemplateFamily::EffectFreeDestructor)
}

pub(super) fn payload_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    certificate: &Certificate<'tcx>,
) -> Result<BoxTemplateFamily, String> {
    metadata(tcx, instance, body)?;
    if instance != ty::Instance::resolve_drop_glue(tcx, certificate.original)
        || !matches!(instance.def,ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_,Some(t)))
            if t==certificate.original)
        || body.local_decls.len() != 4
        || body.local_decls[Local::from_usize(3)].ty != tcx.types.unit
        || body.basic_blocks.len() != 2
        || !mutable_reference(
            body.local_decls[Local::from_usize(1)].ty,
            certificate.original,
        )
        || !mutable_reference(
            body.local_decls[Local::from_usize(2)].ty,
            certificate.original,
        )
    {
        return Err("effect-free Box Drop payload shim identity or original locals differ".into());
    }
    let first = &body.basic_blocks[BasicBlock::from_usize(0)];
    let [statement] = first.statements.as_slice() else {
        return Err("effect-free Box Drop payload shim effect count differs".into());
    };
    let StatementKind::Assign(assignment) = &statement.kind else {
        return Err("effect-free Box Drop payload shim lacks its exact receiver".into());
    };
    if !local(assignment.0, 2)
        || !matches!(&assignment.1,Rvalue::Ref(_,BorrowKind::Mut{kind:MutBorrowKind::Default},place)
            if place.local.as_usize()==1
                && matches!(place.projection.as_ref(),[ProjectionElem::Deref]))
    {
        return Err("effect-free Box Drop payload shim receiver differs".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target: Some(target),
        unwind: UnwindAction::Unreachable,
        ..
    } = &first.terminator().kind
    else {
        return Err("effect-free Box Drop payload shim lacks its exact normal Call".into());
    };
    let Operand::Constant(constant) = func else {
        return Err("effect-free Box Drop payload shim requires original constant FnDef".into());
    };
    let ty::FnDef(id, generic) = constant.const_.ty().kind() else {
        return Err("effect-free Box Drop payload shim target is not original FnDef".into());
    };
    let drop_trait = tcx
        .lang_items()
        .drop_trait()
        .ok_or("Drop trait unavailable")?;
    if tcx.parent(*id) != drop_trait
        || tcx.item_name(*id).as_str() != "drop"
        || generic.skip_binder().len() != 1
        || generic.skip_binder().type_at(0) != certificate.original
    {
        return Err("effect-free Box Drop payload shim original trait/Self differs".into());
    }
    let selected = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        *id,
        generic.skip_binder(),
    )
    .map_err(|_| "effect-free Box Drop shim target unavailable")?
    .ok_or("effect-free Box Drop shim target unresolved")?;
    if selected != certificate.destructor
        || args.len() != 1
        || !matches!(&args[0].node,Operand::Move(place) if local(*place,2))
        || !local(*destination, 3)
        || target.as_usize() != 1
        || !matches!(
            constant
                .const_
                .eval(tcx, ty::TypingEnv::fully_monomorphized(), constant.span),
            Ok(rustc_middle::mir::ConstValue::ZeroSized)
        )
    {
        return Err("effect-free Box Drop payload shim exact selected target/edge differs".into());
    }
    let last = &body.basic_blocks[BasicBlock::from_usize(1)];
    if !last.statements.is_empty() || !matches!(last.terminator().kind, TerminatorKind::Return) {
        return Err("effect-free Box Drop payload shim final Return differs".into());
    }
    Ok(BoxTemplateFamily::EffectFreePayloadGlue)
}

impl Engine<'_> {
    pub(super) fn effect_free_drop_error(&self, reason: String) -> String {
        if self.unknown_causes.borrow().contains_key(&reason) {
            return reason;
        }
        let category = if reason.contains("budget") || reason.contains("supported body domain") {
            UnknownCategory::ResourceLimit
        } else {
            UnknownCategory::Semantics
        };
        self.categorized_error(category, reason)
    }
}

#[cfg(test)]
#[path = "owned_box_effect_free_drop_probe.rs"]
mod probe;
