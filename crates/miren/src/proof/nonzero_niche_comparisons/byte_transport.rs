//! Complete typed source transport metadata; no Rust storage or search result is issued here.
use super::*;
use rustc_middle::mir::{BasicBlock, BinOp, BorrowKind, CallSource, Local, Place, UnwindAction};
use rustc_middle::mir::{MutBorrowKind, ProjectionElem};
use rustc_span::Symbol;

#[derive(Clone, Copy)]
pub(super) enum SourcePhase {
    Raw,
    Current,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SharedTransfer {
    Copy,
    Move,
}

#[derive(Clone, Copy)]
pub(super) struct HelperCall<'tcx> {
    pub(super) definition: DefId,
    pub(super) parameters: ty::GenericArgsRef<'tcx>,
}

pub(super) enum TransportShape<'tcx> {
    Forwarder {
        transfers: [SharedTransfer; 2],
        helper: HelperCall<'tcx>,
    },
    Dispatcher {
        transfers: [SharedTransfer; 2],
        helpers: [HelperCall<'tcx>; 9],
    },
}

fn direct(place: Place<'_>, expected: usize) -> bool {
    place.local == Local::from_usize(expected) && place.projection.is_empty()
}

fn transfer(operand: &Operand<'_>, expected: usize) -> Option<SharedTransfer> {
    match operand {
        Operand::Copy(place) if direct(*place, expected) => Some(SharedTransfer::Copy),
        Operand::Move(place) if direct(*place, expected) => Some(SharedTransfer::Move),
        Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_) | Operand::RuntimeChecks(_) => {
            None
        }
    }
}

fn copy(operand: &Operand<'_>, expected: usize) -> bool {
    transfer(operand, expected) == Some(SharedTransfer::Copy)
}

fn moved(operand: &Operand<'_>, expected: usize) -> bool {
    transfer(operand, expected) == Some(SharedTransfer::Move)
}

fn pointee(ty: Ty<'_>, mutable: rustc_hir::Mutability) -> Option<Ty<'_>> {
    match ty.kind() {
        ty::Ref(_, item, actual) if *actual == mutable => Some(*item),
        _ => None,
    }
}

fn slice<'tcx>(ty: Ty<'tcx>, item: Ty<'tcx>) -> bool {
    matches!(pointee(ty, rustc_hir::Mutability::Not).map(Ty::kind),
        Some(ty::Slice(actual)) if *actual == item)
}

fn header<'tcx>(
    body: &Body<'tcx>,
    locals: usize,
    statements: &[usize],
    budget: &mut GraphBudget<'tcx>,
) -> Result<(), String> {
    budget.charge(32 + 8 * locals + 8 * statements.len())?;
    if body.arg_count != 2
        || body.local_decls.len() != locals
        || body.basic_blocks.len() != statements.len()
        || body.spread_arg.is_some()
        || body.coroutine.is_some()
        || body.source.promoted.is_some()
        || body.tainted_by_errors.is_some()
        || body.injection_phase.is_some()
        || !body.user_type_annotations.is_empty()
    {
        return Err("typed byte transport complete Body header differs".into());
    }
    for declaration in &body.local_decls {
        if declaration.user_ty.is_some() {
            return Err("typed byte transport has an unsupported local annotation".into());
        }
    }
    for (block, expected) in body.basic_blocks.iter().zip(statements) {
        if block.is_cleanup
            || block.statements.len() != *expected
            || !block.terminator().attributes.is_empty()
        {
            return Err("typed byte transport complete block/attribute inventory differs".into());
        }
    }
    Ok(())
}

fn assignment<'a, 'tcx>(
    body: &'a Body<'tcx>,
    block: usize,
    position: usize,
    destination: usize,
) -> Result<&'a Rvalue<'tcx>, String> {
    let StatementKind::Assign(value) =
        &body.basic_blocks[BasicBlock::from_usize(block)].statements[position].kind
    else {
        return Err("typed byte transport has a non-assignment statement".into());
    };
    if !direct(value.0, destination) {
        return Err("typed byte transport assignment destination differs".into());
    }
    Ok(&value.1)
}

fn function<'a, 'tcx>(
    engine: &Engine<'tcx>,
    caller: ty::Instance<'tcx>,
    body: &'a Body<'tcx>,
    block: usize,
    edge: (usize, usize),
    key: &str,
    budget: &mut GraphBudget<'tcx>,
) -> Result<
    (
        DefId,
        ty::GenericArgsRef<'tcx>,
        &'a [rustc_span::Spanned<Operand<'tcx>>],
    ),
    String,
> {
    budget.charge(24)?;
    if body.source.instance != caller.def {
        return Err("typed byte raw helper belongs to another caller Body".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        destination: place,
        target: actual_target,
        unwind,
        call_source,
        ..
    } = &body.basic_blocks[BasicBlock::from_usize(block)]
        .terminator()
        .kind
    else {
        return Err("typed byte transport helper terminator is not Call".into());
    };
    if !direct(*place, edge.0)
        || *actual_target != Some(BasicBlock::from_usize(edge.1))
        || *unwind != UnwindAction::Unreachable
        || *call_source != CallSource::Normal
    {
        return Err("typed byte transport helper destination/normal/unwind edge differs".into());
    }
    let Operand::Constant(constant) = func else {
        return Err("typed byte transport helper lacks its original FnDef constant".into());
    };
    if !matches!(
        constant.const_,
        rustc_middle::mir::Const::Val(rustc_middle::mir::ConstValue::ZeroSized, _)
    ) {
        return Err("typed byte transport helper constant is not ZeroSized".into());
    }
    let ty::FnDef(id, parameters) = constant.const_.ty().kind() else {
        return Err("typed byte transport helper constant type is not FnDef".into());
    };
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("typed byte transport lacks original core identity")?
        .krate;
    if id.krate != core
        || !matches!(engine.tcx.def_kind(*id), DefKind::Fn | DefKind::AssocFn)
        || !parameters.bound_vars().is_empty()
        || budget.key(*id)? != key
    {
        return Err("typed byte transport original helper identity differs".into());
    }
    let parameters = parameters.skip_binder();
    budget.arguments_in_caller(engine.tcx, parameters, caller)?;
    Ok((*id, parameters, args))
}

fn arguments<'tcx>(args: ty::GenericArgsRef<'tcx>, expected: &[Ty<'tcx>], region: bool) -> bool {
    if args.len() != expected.len() + usize::from(region) {
        return false;
    }
    let mut types = 0;
    let mut regions = 0;
    for arg in args {
        match arg.kind() {
            ty::GenericArgKind::Type(actual) => {
                if expected.get(types) != Some(&actual) {
                    return false;
                }
                types += 1;
            }
            ty::GenericArgKind::Lifetime(actual) => {
                if !region || regions != 0 || !actual.is_erased() {
                    return false;
                }
                regions += 1;
            }
            ty::GenericArgKind::Const(_) => return false,
        }
    }
    types == expected.len() && regions == usize::from(region)
}

fn outer<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    budget: &mut GraphBudget<'tcx>,
) -> Result<TransportShape<'tcx>, String> {
    header(body, 3, &[0, 0], budget)?;
    let item = pointee(
        body.local_decls[Local::from_usize(2)].ty,
        rustc_hir::Mutability::Not,
    )
    .ok_or("typed byte outer lacks original immutable needle type")?;
    if body.return_ty() != engine.tcx.types.bool
        || !slice(body.local_decls[Local::from_usize(1)].ty, item)
        || !matches!(
            body.basic_blocks[BasicBlock::from_usize(1)]
                .terminator()
                .kind,
            TerminatorKind::Return
        )
    {
        return Err("typed byte outer complete signature/Return differs".into());
    }
    let (definition, parameters, args) = function(
        engine,
        instance,
        body,
        0,
        (0, 1),
        "DefId(core::slice::cmp::SliceContains::slice_contains)",
        budget,
    )?;
    if !arguments(parameters, &[item], false) || args.len() != 2 {
        return Err("typed byte outer original helper arguments differ".into());
    }
    budget.charge(8)?; // Actual transfer/helper receipt and shape construction.
    Ok(TransportShape::Forwarder {
        transfers: [
            transfer(&args[0].node, 2).ok_or("typed byte outer needle operand differs")?,
            transfer(&args[1].node, 1).ok_or("typed byte outer slice operand differs")?,
        ],
        helper: HelperCall {
            definition,
            parameters,
        },
    })
}

fn option_usize<'tcx>(engine: &Engine<'tcx>, candidate: Ty<'tcx>) -> bool {
    matches!(candidate.kind(), ty::Adt(def, args)
        if engine.tcx.lang_items().get(LangItem::Option) == Some(def.did())
            && args.len() == 1 && args.type_at(0) == engine.tcx.types.usize)
}

fn const_pointer<'tcx>(candidate: Ty<'tcx>, item: Ty<'tcx>) -> bool {
    matches!(candidate.kind(), ty::RawPtr(actual, rustc_hir::Mutability::Not) if *actual == item)
}

fn closure<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    ty: Ty<'tcx>,
    item: Ty<'tcx>,
) -> bool {
    let ty::Closure(id, args) = ty.kind() else {
        return false;
    };
    if engine.tcx.def_kind(*id) != DefKind::Closure
        || engine.tcx.parent(*id) != instance.def_id()
        || args.len() != 4
        || args[0].as_type() != Some(item)
        || args[1].as_type() != Some(engine.tcx.types.i16)
    {
        return false;
    }
    let (Some(callable), Some(captures)) = (args[2].as_type(), args[3].as_type()) else {
        return false;
    };
    let ty::FnPtr(types, header) = callable.kind() else {
        return false;
    };
    if !types.bound_vars().is_empty() {
        return false;
    }
    let signature = types.with(*header).skip_binder();
    let [argument] = signature.inputs() else {
        return false;
    };
    let ty::Tuple(argument) = argument.kind() else {
        return false;
    };
    let ty::Tuple(captures) = captures.kind() else {
        return false;
    };
    signature.safety() == rustc_hir::Safety::Safe
        && signature.abi() == rustc_abi::ExternAbi::RustCall
        && !signature.c_variadic()
        && signature.output() == engine.tcx.types.bool
        && argument.len() == 1
        && captures.len() == 1
        && pointee(argument[0], rustc_hir::Mutability::Not) == Some(item)
        && pointee(captures[0], rustc_hir::Mutability::Not) == Some(item)
}

fn dispatcher_types<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
) -> Result<Ty<'tcx>, String> {
    let tcx = engine.tcx;
    let local = |index| body.local_decls[Local::from_usize(index)].ty;
    let item = pointee(local(1), rustc_hir::Mutability::Not)
        .ok_or("typed byte dispatcher has no original shared needle")?;
    let mut valid = slice(local(2), item);
    for index in [0, 3] {
        valid &= local(index) == tcx.types.bool;
    }
    for index in [4, 12] {
        valid &= local(index) == tcx.types.usize;
    }
    for index in [5, 8] {
        valid &= local(index) == tcx.types.u8;
    }
    for index in [6, 9] {
        valid &= slice(local(index), tcx.types.u8);
    }
    valid &= matches!(local(7).kind(), ty::Tuple(items)
        if items.len() == 2 && items[0] == local(5) && items[1] == local(6));
    valid &= const_pointer(local(10), tcx.types.u8) && const_pointer(local(11), item);
    valid &= option_usize(engine, local(14));
    valid &= pointee(local(13), rustc_hir::Mutability::Not) == Some(local(14));
    let iterator = local(16);
    valid &= matches!(iterator.kind(), ty::Adt(def, args)
        if Some(def.did()) == tcx.get_diagnostic_item(Symbol::intern("SliceIter"))
            && arguments(args, &[item], true));
    valid &= pointee(local(15), rustc_hir::Mutability::Mut) == Some(iterator);
    valid &= closure(engine, instance, local(17), item);
    if !valid {
        return Err("typed byte dispatcher original local type inventory differs".into());
    }
    let immutable = [1, 2, 5, 6, 14];
    for (index, declaration) in body.local_decls.iter().enumerate() {
        let expected = if immutable.contains(&index) {
            rustc_hir::Mutability::Not
        } else {
            rustc_hir::Mutability::Mut
        };
        if declaration.mutability != expected {
            return Err("typed byte dispatcher local binding mutability differs".into());
        }
    }
    Ok(item)
}

// This authenticates wrapper source only. It does not evaluate SIZE or exclude a branch.
pub(super) fn size_body<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    item: Ty<'tcx>,
    budget: &mut GraphBudget<'tcx>,
) -> Result<(), String> {
    budget.charge(64)?; // Closed locals, block, statement, constant identity and generic binding.
    if body.source.instance != instance.def
        || body.arg_count != 0
        || body.local_decls.len() != 1
        || body.local_decls[Local::from_usize(0)].ty != engine.tcx.types.usize
        || body.local_decls[Local::from_usize(0)].mutability != rustc_hir::Mutability::Mut
        || body.local_decls[Local::from_usize(0)].user_ty.is_some()
        || !body.user_type_annotations.is_empty()
        || body.basic_blocks.len() != 1
        || body.basic_blocks[rustc_middle::mir::START_BLOCK].is_cleanup
        || body.basic_blocks[rustc_middle::mir::START_BLOCK]
            .statements
            .len()
            != 1
        || !body.basic_blocks[rustc_middle::mir::START_BLOCK]
            .terminator()
            .attributes
            .is_empty()
        || !matches!(
            body.basic_blocks[rustc_middle::mir::START_BLOCK]
                .terminator()
                .kind,
            TerminatorKind::Return
        )
    {
        return Err("typed byte sizeof wrapper complete body differs".into());
    }
    let Rvalue::Use(Operand::Constant(constant), _) = assignment(body, 0, 0, 0)? else {
        return Err("typed byte sizeof wrapper has no original constant assignment".into());
    };
    let rustc_middle::mir::Const::Unevaluated(value, ty) = constant.const_ else {
        return Err("typed byte sizeof wrapper lost original associated constant".into());
    };
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("typed byte sizeof original core unavailable")?
        .krate;
    if value.def.krate != core
        || engine.tcx.def_kind(value.def) != DefKind::AssocConst
        || value.promoted.is_some()
        || ty != engine.tcx.types.usize
        || !arguments(value.args, &[item], false)
        || budget.key(value.def)? != "DefId(core::mem::SizedTypeProperties::SIZE)"
    {
        return Err("typed byte sizeof associated constant original identity/type differs".into());
    }
    size_trait(engine, engine.tcx.parent(value.def), budget)
}

pub(super) fn size_trait(
    engine: &Engine<'_>,
    parent: rustc_hir::def_id::DefId,
    budget: &mut GraphBudget<'_>,
) -> Result<(), String> {
    budget.charge(2)?; // New concrete trait-gate dispatch; prior wrapper allowance retained.
    if engine.tcx.def_kind(parent) != DefKind::Trait
        || budget.key(parent)? != "DefId(core::mem::SizedTypeProperties)"
    {
        return Err("typed byte sizeof associated constant original trait differs".into());
    }
    Ok(())
}

fn size_source<'tcx>(
    engine: &Engine<'tcx>,
    caller: ty::Instance<'tcx>,
    definition: rustc_hir::def_id::DefId,
    budget: &mut GraphBudget<'tcx>,
) -> Result<(), String> {
    budget.charge(16)?; // Checked concrete environment, resolution, original declaration queries.
    let Some(item) = caller.args.first().and_then(|argument| argument.as_type()) else {
        return Err("typed byte sizeof caller has no original concrete item".into());
    };
    if caller.args.len() != 1 || item.has_param() {
        return Err("typed byte sizeof caller is not fully instantiated".into());
    }
    let selected = engine.resolve_function_item(definition, caller.args)?;
    if !matches!(selected.def, ty::InstanceKind::Item(_))
        || engine.tcx.def_kind(definition) != DefKind::Fn
        || engine.tcx.intrinsic(definition).is_some()
        || !engine.tcx.is_mir_available(definition)
    {
        return Err(engine.missing_body_reason(definition));
    }
    let captured =
        engine.capture_niche_comparison_body(selected, budget, false, GraphGoal::ByteRoute)?;
    budget.record(selected)?;
    budget.charge(8)?; // Original complete signature and current/raw wrapper dispatch.
    let signature = engine.call_poly_signature(selected)?;
    let callable = signature.skip_binder();
    if !signature.bound_vars().is_empty()
        || !callable.inputs().is_empty()
        || callable.output() != engine.tcx.types.usize
        || callable.safety() != rustc_hir::Safety::Safe
        || callable.abi() != rustc_abi::ExternAbi::Rust
        || callable.c_variadic()
    {
        return Err("typed byte sizeof wrapper original full signature differs".into());
    }
    let raw = engine.tcx.instance_mir(selected.def);
    let formal = Ty::new_param(engine.tcx, 0, rustc_span::Symbol::intern("T"));
    size_body(engine, selected, raw, formal, budget)?;
    size_body(engine, selected, &captured.body, item, budget)?;
    Ok(())
}

pub(super) fn dispatcher<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    budget: &mut GraphBudget<'tcx>,
) -> Result<TransportShape<'tcx>, String> {
    header(body, 18, &[0, 1, 0, 0, 0, 1, 3, 1, 0, 2, 0], budget)?;
    budget.charge(768)?; // Complete bounded typed statements/calls/projections/branch inventory.
    let item = dispatcher_types(engine, instance, body)?;
    let tcx = engine.tcx;
    let size = function(
        engine,
        instance,
        body,
        0,
        (4, 1),
        "DefId(core::mem::size_of)",
        budget,
    )?;
    if !arguments(size.1, &[item], false) || !size.2.is_empty() {
        return Err("typed byte dispatcher sizeof original arguments differ".into());
    }
    size_source(engine, instance, size.0, budget)?;
    let Rvalue::BinaryOp(BinOp::Eq, compared) = assignment(body, 1, 0, 3)? else {
        return Err("typed byte dispatcher actual size comparison differs".into());
    };
    let Operand::Constant(one) = &compared.1 else {
        return Err("typed byte dispatcher has no actual size-one constant".into());
    };
    if !moved(&compared.0, 4)
        || one.const_.ty() != tcx.types.usize
        || one
            .const_
            .try_eval_bits(tcx, ty::TypingEnv::fully_monomorphized())
            != Some(1)
        || !matches!(&body.basic_blocks[BasicBlock::from_usize(1)].terminator().kind,
            TerminatorKind::SwitchInt { discr, targets }
                if moved(discr, 3)
                    && targets.iter().next() == Some((0, BasicBlock::from_usize(8)))
                    && targets.iter().nth(1).is_none()
                    && targets.otherwise() == BasicBlock::from_usize(2))
    {
        return Err(
            "typed byte dispatcher size predicate or complete branch targets differ".into(),
        );
    }
    let transmute = function(
        engine,
        instance,
        body,
        2,
        (8, 3),
        "DefId(core::mem::transmute_copy)",
        budget,
    )?;
    if !arguments(transmute.1, &[item, tcx.types.u8], false) || transmute.2.len() != 1 {
        return Err("typed byte dispatcher needle transmute signature differs".into());
    }
    let needle = transfer(&transmute.2[0].node, 1)
        .ok_or("typed byte dispatcher original needle operand differs")?;
    let pointer = function(
        engine,
        instance,
        body,
        3,
        (11, 4),
        "DefId(core::slice::{impl#0}::as_ptr)",
        budget,
    )?;
    if !arguments(pointer.1, &[item], false) || pointer.2.len() != 1 {
        return Err("typed byte dispatcher original slice pointer signature differs".into());
    }
    let slice_transfer = transfer(&pointer.2[0].node, 2)
        .ok_or("typed byte dispatcher original slice operand differs")?;
    let cast = function(
        engine,
        instance,
        body,
        4,
        (10, 5),
        "DefId(core::ptr::const_ptr::{impl#0}::cast)",
        budget,
    )?;
    if !arguments(cast.1, &[item, tcx.types.u8], false)
        || cast.2.len() != 1
        || !moved(&cast.2[0].node, 11)
        || !matches!(assignment(body, 5, 0, 12)?,
            Rvalue::UnaryOp(rustc_middle::mir::UnOp::PtrMetadata, source) if copy(source, 2))
    {
        return Err("typed byte dispatcher pointer cast or actual length transport differs".into());
    }
    // The slice is read again at bb5: a Move at bb3 would consume its carrier. This shape requires
    // actual Copy there, rather than silently reinitializing or treating Move as Copy.
    if slice_transfer != SharedTransfer::Copy {
        return Err("typed byte dispatcher moved slice has no metadata carrier".into());
    }
    let raw = function(
        engine,
        instance,
        body,
        5,
        (9, 6),
        "DefId(core::slice::raw::from_raw_parts)",
        budget,
    )?;
    if !arguments(raw.1, &[tcx.types.u8], true)
        || raw.2.len() != 2
        || !moved(&raw.2[0].node, 10)
        || !moved(&raw.2[1].node, 12)
    {
        return Err("typed byte dispatcher raw-parts actual argument mapping differs".into());
    }
    let Rvalue::Aggregate(kind, fields) = assignment(body, 6, 0, 7)? else {
        return Err("typed byte dispatcher lacks actual argument tuple".into());
    };
    if !matches!(kind.as_ref(), AggregateKind::Tuple)
        || fields.len() != 2
        || !moved(&fields[rustc_abi::FieldIdx::from_usize(0)], 8)
        || !moved(&fields[rustc_abi::FieldIdx::from_usize(1)], 9)
    {
        return Err("typed byte dispatcher argument tuple mapping differs".into());
    }
    for (position, destination, field) in [(1, 5, 0), (2, 6, 1)] {
        let expected = body.local_decls[Local::from_usize(destination)].ty;
        if !matches!(assignment(body, 6, position, destination)?,
            Rvalue::Use(Operand::Copy(place), rustc_middle::mir::WithRetag::Yes)
                if place.local == Local::from_usize(7)
                    && matches!(place.projection.as_ref(), [ProjectionElem::Field(index, ty)]
                        if index.as_usize() == field && *ty == expected))
        {
            return Err("typed byte dispatcher exact tuple field transport differs".into());
        }
    }
    let search = function(
        engine,
        instance,
        body,
        6,
        (14, 7),
        "DefId(core::slice::memchr::memchr)",
        budget,
    )?;
    if !search.1.is_empty()
        || search.2.len() != 2
        || !copy(&search.2[0].node, 5)
        || !copy(&search.2[1].node, 6)
        || !matches!(assignment(body, 7, 0, 13)?,
            Rvalue::Ref(_, BorrowKind::Shared, value) if direct(*value, 14))
    {
        return Err("typed byte dispatcher exact search operand/result reference differs".into());
    }
    let some = function(
        engine,
        instance,
        body,
        7,
        (0, 10),
        "DefId(core::option::{impl#0}::is_some)",
        budget,
    )?;
    if !arguments(some.1, &[tcx.types.usize], false)
        || some.2.len() != 1
        || !moved(&some.2[0].node, 13)
    {
        return Err("typed byte dispatcher original search-result observation differs".into());
    }
    let iter = function(
        engine,
        instance,
        body,
        8,
        (16, 9),
        "DefId(core::slice::{impl#0}::iter)",
        budget,
    )?;
    if !arguments(iter.1, &[item], false)
        || iter.2.len() != 1
        || !copy(&iter.2[0].node, 2)
        || !matches!(assignment(body, 9, 0, 15)?,
            Rvalue::Ref(_, BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow },
                value) if direct(*value, 16))
    {
        return Err("typed byte dispatcher complete false iterator branch differs".into());
    }
    let Rvalue::Aggregate(kind, fields) = assignment(body, 9, 1, 17)? else {
        return Err("typed byte dispatcher false closure construction differs".into());
    };
    if !matches!(kind.as_ref(), AggregateKind::Closure(id, args)
        if matches!(body.local_decls[Local::from_usize(17)].ty.kind(),
            ty::Closure(actual, parameters) if actual == id && parameters == args))
        || fields.len() != 1
        || !copy(&fields[rustc_abi::FieldIdx::from_usize(0)], 1)
    {
        return Err("typed byte dispatcher exact false closure capture differs".into());
    }
    let any = function(
        engine,
        instance,
        body,
        9,
        (0, 10),
        "DefId(core::iter::traits::iterator::Iterator::any)",
        budget,
    )?;
    if !arguments(
        any.1,
        &[
            body.local_decls[Local::from_usize(16)].ty,
            body.local_decls[Local::from_usize(17)].ty,
        ],
        false,
    ) || any.2.len() != 2
        || !moved(&any.2[0].node, 15)
        || !moved(&any.2[1].node, 17)
        || !matches!(
            body.basic_blocks[BasicBlock::from_usize(10)]
                .terminator()
                .kind,
            TerminatorKind::Return
        )
    {
        return Err("typed byte dispatcher complete false Call/Return inventory differs".into());
    }
    budget.charge(32)?; // Actual nine helper receipt copies and typed shape construction.
    Ok(TransportShape::Dispatcher {
        transfers: [needle, slice_transfer],
        helpers: [size, transmute, pointer, cast, raw, search, some, iter, any].map(
            |(definition, parameters, _)| HelperCall {
                definition,
                parameters,
            },
        ),
    })
}

pub(super) fn source<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    phase: SourcePhase,
    budget: &mut GraphBudget<'tcx>,
) -> Result<Option<TransportShape<'tcx>>, String> {
    budget.charge(12)?; // Old4 selector plus actual new caller/phase/type binding8.
    let key = budget.key(instance.def_id())?;
    let needle = match key.as_str() {
        "DefId(core::slice::{impl#0}::contains)" => 2,
        "DefId(core::slice::cmp::{impl#18}::slice_contains)" => 1,
        _ => return Ok(None),
    };
    if body.source.instance != instance.def || instance.args.len() != 1 {
        return Err("typed byte source has a foreign complete caller environment".into());
    }
    let Some(caller_item) = instance
        .args
        .first()
        .and_then(|argument| argument.as_type())
    else {
        return Err("typed byte source caller argument is not an original Rust type".into());
    };
    let item = body
        .local_decls
        .get(Local::from_usize(needle))
        .and_then(|decl| pointee(decl.ty, rustc_hir::Mutability::Not))
        .ok_or("typed byte source has no original caller item type")?;
    match phase {
        SourcePhase::Raw => {
            if !matches!(item.kind(), ty::Param(param) if param.index == 0) {
                return Err("typed byte raw source lacks exact caller Param0".into());
            }
        }
        SourcePhase::Current => {
            if item != caller_item || item.has_param() {
                return Err("typed byte current source differs from actual caller argument".into());
            }
        }
    }
    match key.as_str() {
        "DefId(core::slice::{impl#0}::contains)" => outer(engine, instance, body, budget).map(Some),
        "DefId(core::slice::cmp::{impl#18}::slice_contains)" => {
            dispatcher(engine, instance, body, budget).map(Some)
        }
        _ => unreachable!(), // The exact closed key selection above already refused other kinds.
    }
}

impl TransportShape<'_> {
    pub(super) fn family(
        &self,
    ) -> super::super::super::pure_comparison_templates::PureTemplateFamily {
        use super::super::super::pure_comparison_templates::PureTemplateFamily;
        match self {
            Self::Forwarder { .. } => PureTemplateFamily::Contains,
            Self::Dispatcher { .. } => PureTemplateFamily::ContainsBytes,
        }
    }
}

pub(super) struct HelperReceipt<'tcx> {
    pub(super) instance: ty::Instance<'tcx>,
    pub(super) signature: ty::PolyFnSig<'tcx>,
}

pub(super) struct TypedRoute<'tcx> {
    outer: ty::Instance<'tcx>,
    dispatcher: ty::Instance<'tcx>,
    pub(super) outer_transfers: [SharedTransfer; 2],
    pub(super) dispatcher_transfers: [SharedTransfer; 2],
    pub(super) helpers: Vec<HelperReceipt<'tcx>>,
}

pub(super) fn bind_current<'tcx>(
    engine: &Engine<'tcx>,
    original: Ty<'tcx>,
    outer_instance: ty::Instance<'tcx>,
    dispatcher_instance: ty::Instance<'tcx>,
    bodies: &[(ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>)],
    budget: &mut GraphBudget<'tcx>,
) -> Result<Option<Box<TypedRoute<'tcx>>>, String> {
    budget.charge(8 + 4 * bodies.len())?;
    let dispatcher_body = bodies
        .iter()
        .find(|(instance, _)| *instance == dispatcher_instance)
        .map(|(_, body)| body)
        .ok_or("typed byte route lacks actual dispatcher record")?;
    if dispatcher_body.local_decls.len() != 18 || dispatcher_body.basic_blocks.len() != 11 {
        // Existing canonical inlined inventory stays metadata, without claiming this typed map.
        return Ok(None);
    }
    let outer_body = bodies
        .iter()
        .find(|(instance, _)| *instance == outer_instance)
        .map(|(_, body)| body)
        .ok_or("typed byte route lacks actual outer record")?;
    let TransportShape::Forwarder { transfers, helper } = source(
        engine,
        outer_instance,
        outer_body,
        SourcePhase::Current,
        budget,
    )?
    .ok_or("typed byte route outer source kind differs")?
    else {
        return Err("typed byte route outer selected wrong source shape".into());
    };
    budget.arguments(engine.tcx, helper.parameters)?;
    budget.charge(4)?;
    if engine.resolve_function_item(helper.definition, helper.parameters)? != dispatcher_instance {
        return Err("typed byte route outer actual Call selects another dispatcher".into());
    }
    let TransportShape::Dispatcher {
        transfers: dispatcher_transfers,
        helpers,
    } = source(
        engine,
        dispatcher_instance,
        dispatcher_body,
        SourcePhase::Current,
        budget,
    )?
    .ok_or("typed byte route dispatcher source kind differs")?
    else {
        return Err("typed byte route dispatcher selected wrong source shape".into());
    };
    budget.charge(8)?;
    if pointee(
        outer_body.local_decls[Local::from_usize(2)].ty,
        rustc_hir::Mutability::Not,
    ) != Some(original)
        || pointee(
            dispatcher_body.local_decls[Local::from_usize(1)].ty,
            rustc_hir::Mutability::Not,
        ) != Some(original)
    {
        return Err("typed byte route original outer/dispatcher elements differ".into());
    }
    budget.charge(3 + 3 * helpers.len())?;
    let mut receipts = Vec::new();
    receipts
        .try_reserve_exact(helpers.len())
        .map_err(|_| "typed byte helper receipt allocation failed")?;
    for helper in helpers {
        budget.arguments(engine.tcx, helper.parameters)?;
        budget.charge(8)?;
        let selected = engine.resolve_function_item(helper.definition, helper.parameters)?;
        budget.record(selected)?;
        // Fixed closed transport signatures: all formal types are the checked locals above.
        // These are new payments; the ordinary graph's existing signature fees remain literal.
        budget.phase(GraphPhase::SignatureInstantiate, 256)?;
        budget.phase(GraphPhase::SignatureNormalize, 256)?;
        budget.phase(GraphPhase::SignatureValidate, 256)?;
        let expected = engine
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                engine
                    .tcx
                    .fn_sig(selected.def_id())
                    .instantiate(engine.tcx, selected.args),
            )
            .map_err(|_| "typed byte helper full original signature normalization failed")?;
        budget.record(selected)?;
        budget.charge(4)?;
        let signature = engine.call_poly_signature(selected)?;
        if signature != expected {
            return Err("typed byte helper cached full signature differs from original".into());
        }
        receipts.push(HelperReceipt {
            instance: selected,
            signature,
        });
    }
    budget.charge(17)?; // Shape fields12 plus actual new boxed allocation/move/release5.
    Ok(Some(Box::new(TypedRoute {
        outer: outer_instance,
        dispatcher: dispatcher_instance,
        outer_transfers: transfers,
        dispatcher_transfers,
        helpers: receipts,
    })))
}

pub(super) fn mirrored_metadata<'tcx>(
    expected: &Body<'tcx>,
    current: &Body<'tcx>,
    budget: &mut GraphBudget<'tcx>,
) -> Result<(), String> {
    budget.charge(
        8 + 8 * expected.local_decls.len()
            + 8 * expected.basic_blocks.len()
            + 8 * expected.source_scopes.len(),
    )?;
    if expected.source != current.source
        || expected.source_scopes.len() != current.source_scopes.len()
        || expected.arg_count != current.arg_count
        || expected.local_decls.len() != current.local_decls.len()
        || expected.basic_blocks.len() != current.basic_blocks.len()
        || !expected.user_type_annotations.is_empty()
        || !current.user_type_annotations.is_empty()
    {
        return Err("typed byte current source metadata differs from original".into());
    }
    for (expected, current) in expected.source_scopes.iter().zip(&current.source_scopes) {
        let local = match (&expected.local_data, &current.local_data) {
            (
                rustc_middle::mir::ClearCrossCrate::Clear,
                rustc_middle::mir::ClearCrossCrate::Clear,
            ) => true,
            (
                rustc_middle::mir::ClearCrossCrate::Set(expected),
                rustc_middle::mir::ClearCrossCrate::Set(current),
            ) => expected.lint_root == current.lint_root,
            (
                rustc_middle::mir::ClearCrossCrate::Clear,
                rustc_middle::mir::ClearCrossCrate::Set(_),
            )
            | (
                rustc_middle::mir::ClearCrossCrate::Set(_),
                rustc_middle::mir::ClearCrossCrate::Clear,
            ) => false,
        };
        if expected.span != current.span
            || expected.parent_scope != current.parent_scope
            || expected.inlined != current.inlined
            || expected.inlined_parent_scope != current.inlined_parent_scope
            || !local
        {
            return Err("typed byte current scope inventory differs from original".into());
        }
    }
    for (expected, current) in expected.local_decls.iter().zip(&current.local_decls) {
        if expected.source_info != current.source_info
            || expected.user_ty.is_some()
            || current.user_ty.is_some()
        {
            return Err("typed byte current local source metadata differs from original".into());
        }
    }
    for (expected, current) in expected
        .basic_blocks
        .iter()
        .zip(current.basic_blocks.iter())
    {
        if expected.statements.len() != current.statements.len()
            || expected.terminator().source_info != current.terminator().source_info
            || !expected.terminator().attributes.is_empty()
            || !current.terminator().attributes.is_empty()
        {
            return Err("typed byte current block/source attributes differ from original".into());
        }
        // The complete encoded terminator equality below still checks all kinds/operands.
        if let (
            TerminatorKind::Call {
                args: expected_args,
                fn_span: expected_span,
                ..
            },
            TerminatorKind::Call {
                args: current_args,
                fn_span: current_span,
                ..
            },
        ) = (&expected.terminator().kind, &current.terminator().kind)
        {
            budget.charge(4 + 2 * expected_args.len())?;
            if expected_span != current_span
                || expected_args.len() != current_args.len()
                || expected_args
                    .iter()
                    .zip(current_args.iter())
                    .any(|(expected, current)| expected.span != current.span)
            {
                return Err("typed byte current Call occurrence spans differ from original".into());
            }
        }
        for (expected, current) in expected.statements.iter().zip(&current.statements) {
            if expected.source_info != current.source_info {
                return Err(
                    "typed byte current statement source metadata differs from original".into(),
                );
            }
        }
    }
    Ok(())
}

impl<'tcx> TypedRoute<'tcx> {
    pub(super) fn check_held_modes(
        &self,
        bodies: &std::collections::HashMap<ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>>,
    ) -> Result<(), String> {
        let outer = bodies
            .get(&self.outer)
            .ok_or("typed byte route lost its held outer Body")?;
        let dispatcher = bodies
            .get(&self.dispatcher)
            .ok_or("typed byte route lost its held dispatcher Body")?;
        let outer_args = held_arguments(outer, 0).ok_or("typed byte held outer Call differs")?;
        let needle_args =
            held_arguments(dispatcher, 2).ok_or("typed byte held needle Call differs")?;
        let slice_args =
            held_arguments(dispatcher, 3).ok_or("typed byte held slice Call differs")?;
        if outer_args.len() != 2
            || needle_args.len() != 1
            || slice_args.len() != 1
            || transfer(&outer_args[0].node, 2) != Some(self.outer_transfers[0])
            || transfer(&outer_args[1].node, 1) != Some(self.outer_transfers[1])
            || transfer(&needle_args[0].node, 1) != Some(self.dispatcher_transfers[0])
            || transfer(&slice_args[0].node, 2) != Some(self.dispatcher_transfers[1])
        {
            return Err("typed byte held actual Copy/Move transport differs".into());
        }
        Ok(())
    }
}

fn held_arguments<'a, 'tcx>(
    body: &'a Body<'tcx>,
    block: usize,
) -> Option<&'a [rustc_span::Spanned<Operand<'tcx>>]> {
    body.basic_blocks
        .get(BasicBlock::from_usize(block))
        .and_then(|block| match &block.terminator().kind {
            TerminatorKind::Call { args, .. } => Some(args.as_ref()),
            _ => None,
        })
}
