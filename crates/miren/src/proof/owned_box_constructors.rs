//! Exact current MIR transport for an inlined Unit-only Box constructor.
//! Scope identity is necessary, and the entire issue/store/seal sequence is also checked.
use super::*;
use rustc_middle::mir::{BasicBlock, Local, Location, SourceScope};

#[derive(Debug)]
pub(super) struct Constructor<'tcx> {
    pub(super) body: std::rc::Weak<Body<'tcx>>,
    pub(super) raw: Local,
    pub(super) typed: Option<Local>,
    pub(super) owner: Local,
    pub(super) seal: Location,
    pub(super) pointer_cast: Option<Location>,
    pub(super) store: Option<Location>,
    pub(super) elided_unit_store: bool,
}

fn constructor_scope<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    mut scope: SourceScope,
) -> Result<(SourceScope, ty::Instance<'tcx>), String> {
    let constructor = tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
        .ok_or("Box constructor identity is unavailable")?;
    for _ in 0..16 {
        let data = &body.source_scopes[scope];
        if let Some((instance, _)) = data.inlined {
            if instance.def_id() != constructor || instance.args.type_at(0) != tcx.types.unit {
                return Err("inlined Box transport has a different selected constructor".into());
            }
            return Ok((scope, instance));
        }
        scope = data
            .parent_scope
            .ok_or("raw Box allocation is outside its actual inlined constructor")?;
    }
    Err("inlined Box constructor scope exceeds its depth budget".into())
}

fn same_scope(body: &Body<'_>, mut scope: SourceScope, expected: SourceScope) -> bool {
    for _ in 0..16 {
        if scope == expected {
            return true;
        }
        let Some(parent) = body.source_scopes[scope].parent_scope else {
            return false;
        };
        if body.source_scopes[scope].inlined.is_some() {
            return false;
        }
        scope = parent;
    }
    false
}

pub(super) fn certify_inlined<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &std::rc::Rc<Body<'tcx>>,
    block: BasicBlock,
    original_box: Ty<'tcx>,
) -> Result<Constructor<'tcx>, String> {
    let term = body.basic_blocks[block].terminator();
    let (scope, instance) = constructor_scope(tcx, body, term.source_info.scope)?;
    owned_box_templates::certify_unit_protocol(tcx, instance)?;
    let output = tcx
        .fn_sig(instance.def_id())
        .instantiate(tcx, instance.args)
        .skip_binder()
        .output();
    if original_box != output {
        return Err(
            "inlined constructor seal does not have the exact original Box<Unit,Global> type"
                .into(),
        );
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target: Some(target),
        ..
    } = &term.kind
    else {
        return Err("inlined Box issue lacks an actual normal call edge".into());
    };
    let generic = tcx.instance_mir(instance.def);
    let TerminatorKind::Call { func: expected, .. } = &generic.basic_blocks
        [BasicBlock::from_usize(0)]
    .terminator()
    .kind
    else {
        return Err("Box constructor lost its allocation delegate".into());
    };
    let ty::FnDef(expected, _) = expected.ty(&generic.local_decls, tcx).kind() else {
        return Err("Box constructor allocation identity is unavailable".into());
    };
    if !matches!(func.ty(&body.local_decls, tcx).kind(), ty::FnDef(actual, _)
        if *actual == *expected)
        || args.len() != 1
        || !destination.projection.is_empty()
        || !matches!(destination.ty(&body.local_decls, tcx).ty.kind(),
            ty::RawPtr(element, mutability) if *element == tcx.types.u8 && mutability.is_mut())
    {
        return Err("inlined Box issue differs from the selected allocation signature".into());
    }
    owned_box_templates::compiler_unit_layout(tcx, &args[0].node)?;
    let continuation_block = *target;
    let raw = destination.local;
    let mut typed = None;
    let mut stored = false;
    let mut pointer_cast = None;
    let mut store = None;
    let continuation = &body.basic_blocks[*target];
    if continuation.statements.len() > 512 {
        return Err("inlined Box constructor exceeds the existing operation budget".into());
    }
    for (statement_index, statement) in continuation.statements.iter().enumerate() {
        if !same_scope(body, statement.source_info.scope, scope) {
            return Err(
                "inlined Box construction contains a mixed source scope before sealing".into(),
            );
        }
        match &statement.kind {
            StatementKind::StorageLive(_) => {}
            StatementKind::StorageDead(local) if *local != raw => {}
            StatementKind::StorageDead(_) => {
                return Err("inlined Box source storage ends before its owner seal".into());
            }
            StatementKind::Assign(assignment) => {
                let (place, value) = &**assignment;
                if place.projection.is_empty() {
                    match value {
                        Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(source), target)
                            if source.local == raw
                                && source.projection.is_empty()
                                && matches!(target.kind(), ty::RawPtr(element, mutability)
                                    if *element == tcx.types.unit && mutability.is_mut())
                                && body.local_decls[place.local].ty == *target
                                && typed.is_none()
                                && !stored =>
                        {
                            typed = Some(place.local);
                            pointer_cast = Some(Location {
                                block: continuation_block,
                                statement_index,
                            });
                        }
                        Rvalue::Cast(CastKind::Transmute, Operand::Copy(source), target)
                            if source.local == raw
                                && source.projection.is_empty()
                                && *target == original_box
                                && body.local_decls[place.local].ty == original_box =>
                        {
                            if typed.is_some() && !stored {
                                return Err(
                                    "inlined Box pointer was returned before its payload store"
                                        .into(),
                                );
                            }
                            return Ok(Constructor {
                                body: std::rc::Rc::downgrade(body),
                                raw,
                                typed,
                                owner: place.local,
                                seal: Location {
                                    block: continuation_block,
                                    statement_index,
                                },
                                pointer_cast,
                                store,
                                elided_unit_store: !stored,
                            });
                        }
                        _ => {
                            return Err(
                                "inlined Box construction has an extra or changed effect".into()
                            );
                        }
                    }
                } else if Some(place.local) == typed
                    && matches!(place.projection.as_ref(), [ProjectionElem::Deref])
                    && !stored
                    && matches!(value, Rvalue::Use(operand, _)
                        if operand.ty(&body.local_decls, tcx) == tcx.types.unit)
                {
                    stored = true;
                    store = Some(Location {
                        block: continuation_block,
                        statement_index,
                    });
                } else {
                    return Err(
                        "inlined Box payload store has a different target or original type".into(),
                    );
                }
            }
            _ => {
                return Err(
                    "inlined Box construction has an unsupported intermediate effect".into(),
                );
            }
        }
    }
    Err("inlined Box constructor has no exact seal in its normal continuation".into())
}
