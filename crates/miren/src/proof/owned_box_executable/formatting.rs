//! Closed literal-only Arguments::from_str primitive; no reference or pointer is returned.
use super::*;
use rustc_middle::mir::interpret::{GlobalAlloc, alloc_range};
use rustc_middle::mir::{AggregateKind, Local, RawPtrKind};

fn local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}
fn copied(operand: &Operand<'_>, index: usize) -> bool {
    matches!(operand, Operand::Copy(place) if local(*place, index))
}
fn moved(operand: &Operand<'_>, index: usize) -> bool {
    matches!(operand, Operand::Move(place) if local(*place, index))
}
fn constant_one<'tcx>(engine: &Engine<'tcx>, operand: &Operand<'tcx>, original: Ty<'tcx>) -> bool {
    matches!(operand, Operand::Constant(value) if value.const_.ty() == original
        && value.const_.try_eval_scalar_int(engine.tcx, ty::TypingEnv::fully_monomorphized())
            .is_some_and(|value| value.to_bits(value.size()) == 1))
}

fn nonnull<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    byte: bool,
) -> Result<bool, String> {
    pay(engine, 48)?; // Original lang-item/type-argument and scalar layout service.
    let ty::Adt(def, args) = original.kind() else {
        return Ok(false);
    };
    if engine.tcx.lang_items().get(LangItem::NonNull) != Some(def.did()) || args.len() != 1 {
        return Ok(false);
    }
    let pointee = args.type_at(0);
    if if byte {
        pointee != engine.tcx.types.u8
    } else {
        !matches!(pointee.kind(), ty::Adt(def, args)
            if engine.tcx.lang_items().get(LangItem::FormatArgument) == Some(def.did())
                && args.len() == 1 && matches!(args[0].kind(), ty::GenericArgKind::Lifetime(_)))
    } {
        return Ok(false);
    }
    let layout = engine.static_layout(original)?;
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    Ok(
        matches!(layout.backend_repr, rustc_abi::BackendRepr::Scalar(
        rustc_abi::Scalar::Initialized { value: rustc_abi::Primitive::Pointer(_), valid_range })
        if layout.size.bits() == u64::from(bits) && valid_range.start == 1
            && valid_range.end == (1u128 << bits) - 1),
    )
}

pub(super) fn schema<'tcx>(engine: &mut Engine<'tcx>, body: &Body<'tcx>) -> Result<(), String> {
    pay(engine, 160)?; // Distinct bounded schema visits, scalar constant and nominal reads.
    if body.arg_count != 1 || body.local_decls.len() != 10 || body.basic_blocks.len() != 1 {
        return Err("Box literal formatting exact Body shape differs".into());
    }
    let block = &body.basic_blocks[BasicBlock::from_usize(0)];
    if block.statements.len() != 25
        || block.is_cleanup
        || !matches!(block.terminator().kind, TerminatorKind::Return)
        || !block.after_last_stmt_debuginfos.is_empty()
    {
        return Err("Box literal formatting exact normal block differs".into());
    }
    for (index, local_index, live) in [
        (0, 2, true),
        (1, 3, true),
        (2, 8, true),
        (5, 8, false),
        (7, 3, false),
        (8, 4, true),
        (9, 5, true),
        (10, 6, true),
        (11, 7, true),
        (12, 9, true),
        (15, 9, false),
        (17, 7, false),
        (19, 6, false),
        (21, 5, false),
        (23, 4, false),
        (24, 2, false),
    ] {
        if !matches!(&block.statements[index].kind,
            StatementKind::StorageLive(local) if live && local.as_usize() == local_index)
            && !matches!(&block.statements[index].kind,
                StatementKind::StorageDead(local) if !live && local.as_usize() == local_index)
        {
            return Err("Box literal formatting storage lifetime schema differs".into());
        }
    }
    for statement in &block.statements {
        if !statement.debuginfos.is_empty() {
            return Err("Box literal formatting additional debug operations unsupported".into());
        }
    }
    for (index, destination) in [
        (3, 8),
        (4, 3),
        (6, 2),
        (13, 9),
        (14, 7),
        (16, 6),
        (18, 5),
        (20, 4),
        (22, 0),
    ] {
        let StatementKind::Assign(pair) = &block.statements[index].kind else {
            return Err("Box literal formatting assignment schema differs".into());
        };
        if !local(pair.0, destination) {
            return Err("Box literal formatting destination schema differs".into());
        }
        let valid = match (index, &pair.1) {
            (3, Rvalue::RawPtr(RawPtrKind::Const, place)) => {
                place.local.as_usize() == 1
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
            }
            (4, Rvalue::Cast(CastKind::PtrToPtr, operand, original)) => {
                copied(operand, 8) && *original == body.local_decls[pair.0.local].ty
            }
            (6, Rvalue::Cast(CastKind::Transmute, operand, original)) => {
                copied(operand, 3) && *original == body.local_decls[pair.0.local].ty
            }
            (13, Rvalue::Cast(CastKind::Transmute, operand, original)) => {
                copied(operand, 1) && *original == body.local_decls[pair.0.local].ty
            }
            (14, Rvalue::UnaryOp(UnOp::PtrMetadata, operand)) => copied(operand, 9),
            (16, Rvalue::BinaryOp(BinOp::Shl, operands)) => {
                moved(&operands.0, 7) && constant_one(engine, &operands.1, engine.tcx.types.i32)
            }
            (18, Rvalue::BinaryOp(BinOp::BitOr, operands)) => {
                moved(&operands.0, 6) && constant_one(engine, &operands.1, engine.tcx.types.usize)
            }
            (20, Rvalue::Cast(CastKind::Transmute, operand, original)) => {
                moved(operand, 5) && *original == body.local_decls[pair.0.local].ty
            }
            (22, Rvalue::Aggregate(kind, operands)) => {
                matches!(kind.as_ref(),
                AggregateKind::Adt(def, variant, _, None, None)
                    if engine.tcx.lang_items().get(LangItem::FormatArguments) == Some(*def)
                        && variant.as_usize() == 0)
                    && operands.len() == 2
                    && operands
                        .iter()
                        .enumerate()
                        .all(|(index, operand)| moved(operand, if index == 0 { 2 } else { 4 }))
            }
            _ => false,
        };
        if !valid {
            return Err("Box literal formatting original operation schema differs".into());
        }
    }
    let types = &body.local_decls;
    let ty::Ref(_, text, rustc_hir::Mutability::Not) = types[Local::from_usize(1)].ty.kind() else {
        return Err("Box literal formatting original str receiver differs".into());
    };
    if !text.is_str()
        || !matches!(types[Local::from_usize(0)].ty.kind(), ty::Adt(def, _)
            if engine.tcx.lang_items().get(LangItem::FormatArguments) == Some(def.did()))
        || ![5, 6, 7]
            .into_iter()
            .all(|local| types[Local::from_usize(local)].ty == engine.tcx.types.usize)
        || !matches!(types[Local::from_usize(3)].ty.kind(),
            ty::RawPtr(child, rustc_hir::Mutability::Not) if *child == engine.tcx.types.u8)
        || !matches!(types[Local::from_usize(8)].ty.kind(),
            ty::RawPtr(child, rustc_hir::Mutability::Not) if child.is_str())
        || !matches!(types[Local::from_usize(9)].ty.kind(),
            ty::Ref(_, child, rustc_hir::Mutability::Not)
                if matches!(child.kind(), ty::Slice(byte) if *byte == engine.tcx.types.u8))
    {
        return Err("Box literal formatting original scalar/reference types differ".into());
    }
    if !nonnull(engine, types[Local::from_usize(2)].ty, true)?
        || !nonnull(engine, types[Local::from_usize(4)].ty, false)?
    {
        return Err("Box literal formatting original NonNull/tag validity differs".into());
    }
    Ok(())
}

pub(super) fn literal<'tcx>(
    engine: &mut Engine<'tcx>,
    invocation: &Invocation<'tcx>,
    body: &Rc<Body<'tcx>>,
    block: BasicBlock,
    callee: ty::Instance<'tcx>,
    state: &State,
) -> Result<Option<Value>, String> {
    invocation.check(engine, state)?;
    pay(engine, invocation.source.bodies.len() + 16)?;
    let Some(source) = invocation
        .source
        .bodies
        .iter()
        .find(|source| source.instance == callee && source.kind == Kind::Format)
    else {
        return Ok(None);
    };
    if !Rc::ptr_eq(body, &invocation.body)
        || direct_callee(engine, body, block.as_usize())? != callee
    {
        return Err("Box literal formatting caller/current occurrence differs".into());
    }
    if engine.specification(callee)?.is_some()
        || engine
            .configured_contracts(callee)?
            .iter()
            .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
    {
        return Err("Box literal formatting contract observations remain unsupported".into());
    }
    let TerminatorKind::Call {
        args,
        target: Some(_),
        ..
    } = &body.basic_blocks[block].terminator().kind
    else {
        return Err("Box literal formatting lacks actual normal Call".into());
    };
    let [argument] = args.as_ref() else {
        return Err("Box literal formatting requires one original argument".into());
    };
    let Operand::Constant(argument) = &argument.node else {
        return Err("Box literal formatting nonconstant transport remains unsupported".into());
    };
    if !matches!(argument.const_.ty().kind(), ty::Ref(_, child, rustc_hir::Mutability::Not)
        if child.is_str())
    {
        return Err("Box literal formatting original str argument differs".into());
    }
    // Independently authenticated immutable Body schema has no callbacks, branches or calls.
    // Recheck the bounded schema at this actual occurrence before any primitive result is issued.
    schema(engine, &source.current)?;
    pay(engine, 32)?;
    let constant = argument
        .const_
        .eval(
            engine.tcx,
            ty::TypingEnv::fully_monomorphized(),
            argument.span,
        )
        .map_err(|_| "Box literal formatting original constant is unavailable")?;
    let rustc_middle::mir::ConstValue::Slice {
        alloc_id,
        meta: length,
    } = constant
    else {
        return Err("Box literal formatting constant backing shape unsupported".into());
    };
    if length > 512 {
        return Err("Box literal formatting exceeds the fixed 512-byte domain".into());
    }
    pay(
        engine,
        usize::try_from(length).map_err(|_| "Box literal length exceeds host usize")? + 32,
    )?;
    let Some(GlobalAlloc::Memory(allocation)) = engine.tcx.try_get_global_alloc(alloc_id) else {
        return Err("Box literal formatting immutable compiler backing unavailable".into());
    };
    let allocation = allocation.inner();
    let range = alloc_range(rustc_abi::Size::ZERO, rustc_abi::Size::from_bytes(length));
    if allocation.mutability.is_mut()
        || length > allocation.len() as u64
        || !allocation.provenance().range_empty(range, &engine.tcx)
    {
        return Err(
            "Box literal formatting compiler backing is mutable/indirect/out of bounds".into(),
        );
    }
    let bytes = allocation
        .get_bytes_strip_provenance(&engine.tcx, range)
        .map_err(|_| "Box literal formatting initialized bytes unavailable")?;
    std::str::from_utf8(bytes)
        .map_err(|_| "Box literal formatting original bytes are not UTF-8")?;
    // length <=512 establishes the exact shift/tag arithmetic on both admitted target widths.
    // The result has no public fields, reference, address, guest storage or callback authority.
    pay(engine, 12)?;
    engine.record_model(
        callee.def_id(),
        "authenticated literal Arguments::from_str primitive; opaque panic payload",
    );
    Ok(Some(Value::FormatArguments))
}
