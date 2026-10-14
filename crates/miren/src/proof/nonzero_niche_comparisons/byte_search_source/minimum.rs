//! Source-specific target-usize minimum association. No search or reference authority escapes.
use super::*;
use rustc_span::Symbol;

#[cfg(test)]
#[path = "minimum_probe.rs"]
pub(super) mod probe;

// Non-Clone, operation-local evidence. Held Rc records cannot be mutated in place, and the
// consumer must additionally hold and check both actual registries before using the association.
pub(super) struct MinimumRecord<'tcx> {
    instance: ty::Instance<'tcx>,
    current: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    primitive: ty::Instance<'tcx>,
    primitive_signature: ty::PolyFnSig<'tcx>,
    bits: u32,
}

fn identity<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(32 + instance.args.len())?;
    let tcx = engine.tcx;
    let core = tcx
        .lang_items()
        .sized_trait()
        .ok_or("minimum core unavailable")?
        .krate;
    let parent = tcx.parent(instance.def_id());
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || instance.def_id().krate != core
        || tcx.def_kind(instance.def_id()) != DefKind::AssocFn
        || tcx.item_name(instance.def_id()) != Symbol::intern("min")
        || !matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true })
        || !instance.args.is_empty()
        || tcx.generics_of(instance.def_id()).count() != 0
        || tcx.intrinsic(instance.def_id()).is_some()
    {
        return Err("minimum requires its original non-generic core Ord implementation".into());
    }
    let trait_ref = tcx
        .impl_trait_ref(parent)
        .instantiate(tcx, instance.args)
        .skip_norm_wip();
    if trait_ref.self_ty() != tcx.types.usize
        || trait_ref.def_id.krate != core
        || range::key(work, trait_ref.def_id)? != "DefId(core::cmp::Ord)"
    {
        return Err("minimum original Ord/target-usize implementation differs".into());
    }
    Ok(())
}

fn signature<'tcx>(
    engine: &Engine<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(20 + signature.bound_vars().len())?;
    let concrete = bind_signature(engine, signature, work)?;
    if !signature.bound_vars().is_empty()
        || concrete.inputs() != [engine.tcx.types.usize, engine.tcx.types.usize]
        || concrete.output() != engine.tcx.types.usize
        || concrete.safety() != rustc_hir::Safety::Safe
        || concrete.abi() != rustc_abi::ExternAbi::Rust
        || concrete.c_variadic()
    {
        return Err("minimum full original safe Rust usize signature differs".into());
    }
    Ok(())
}

fn direct(place: Place<'_>, local: usize) -> bool {
    place.local.as_usize() == local && place.projection.is_empty()
}

fn primitive<'tcx>(
    engine: &Engine<'tcx>,
    body: &Body<'tcx>,
    work: &mut Work,
) -> Result<ty::Instance<'tcx>, Failure> {
    work.charge(48)?;
    if body.arg_count != 2
        || body.local_decls.len() != 3
        || body.basic_blocks.len() != 2
        || body
            .local_decls
            .iter()
            .any(|local| local.ty != engine.tcx.types.usize)
        || body
            .basic_blocks
            .iter()
            .any(|block| block.is_cleanup || !block.statements.is_empty())
    {
        return Err("minimum complete local/block/statement schema differs".into());
    }
    let first = &body.basic_blocks[rustc_middle::mir::START_BLOCK];
    let last = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(1)];
    if !matches!(last.terminator().kind, TerminatorKind::Return) {
        return Err("minimum complete return continuation differs".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        call_source,
        ..
    } = &first.terminator().kind
    else {
        return Err("minimum must execute its original intrinsic Call".into());
    };
    if args.len() != 2
        || !matches!(&args[0].node, Operand::Copy(place) if direct(*place, 1))
        || !matches!(&args[1].node, Operand::Copy(place) if direct(*place, 2))
        || !direct(*destination, 0)
        || *target != Some(rustc_middle::mir::BasicBlock::from_usize(1))
        || *unwind != rustc_middle::mir::UnwindAction::Unreachable
        || *call_source != rustc_middle::mir::CallSource::Normal
    {
        return Err("minimum exact original operand/result/continuation differs".into());
    }
    work.charge(24)?;
    let ty::FnDef(id, arguments) = func.ty(&body.local_decls, engine.tcx).kind() else {
        return Err("minimum intrinsic lacks an original function item".into());
    };
    let arguments = arguments.skip_binder();
    work.charge(12 + arguments.len())?;
    let selected = engine.resolve_function_item(*id, arguments)?;
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("minimum core unavailable")?
        .krate;
    if !matches!(selected.def, ty::InstanceKind::Intrinsic(_))
        || selected.def_id() != *id
        || selected.def_id().krate != core
        || arguments != selected.args
        || arguments.len() != 1
        || arguments[0].as_type() != Some(engine.tcx.types.usize)
        || !engine.tcx.is_intrinsic(*id, Symbol::intern("integer_min"))
    {
        return Err("minimum requires exact genuine integer_min::<usize> identity".into());
    }
    Ok(selected)
}

pub(super) fn prepare<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    work: &mut Work,
) -> Result<MinimumRecord<'tcx>, Failure> {
    work.depth(3)?;
    identity(engine, instance, work)?;
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    work.charge(16)?;
    if !matches!(bits, 32 | 64) {
        return Err("minimum association requires a 32/64-bit target usize".into());
    }
    work.charge(260)?;
    let layout = engine
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(engine.tcx.types.usize))
        .map_err(|_| "minimum original usize layout is unavailable")?;
    if layout.size.bits() != u64::from(bits) {
        return Err("minimum target width differs from original usize layout".into());
    }
    let wrapper_signature = checked_signature(engine, instance, work)?;
    signature(engine, wrapper_signature, work)?;
    if !engine.tcx.is_mir_available(instance.def_id()) {
        return Err(Failure {
            category: UnknownCategory::MissingCompilerEvidence,
            reason: engine.missing_body_reason(instance.def_id()),
        });
    }
    work.charge(8)?;
    let raw = engine.tcx.instance_mir(instance.def);
    if raw.source.instance != instance.def || raw.source.promoted.is_some() {
        return Err("minimum original Body identity differs".into());
    }
    let raw_work = inventory(engine, instance, raw, SourcePhase::Raw, work)?;
    let raw_primitive = primitive(engine, raw, work)?;
    work.charge(3 * raw_work + 4)?;
    let expected = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            engine.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(engine.tcx, raw.clone()),
        )
        .map_err(|_| "minimum original MIR normalization failed")?;
    let expected_work = inventory(engine, instance, &expected, SourcePhase::Normalized, work)?;
    // Check the complete original-normalized schema independently before current publication.
    let original_primitive = primitive(engine, &expected, work)?;
    work.charge(4)?;
    if original_primitive != raw_primitive {
        return Err("minimum raw/normalized intrinsic association differs".into());
    }
    let primitive_signature = checked_signature(engine, original_primitive, work)?;
    signature(engine, primitive_signature, work)?;
    work.charge(8)?;
    let prior = engine
        .bodies
        .try_borrow()
        .map_err(|_| "minimum Body registry is borrowed")?
        .get(&instance)
        .cloned();
    let current = if let Some(current) = prior {
        current
    } else {
        let mut bodies = engine
            .bodies
            .try_borrow_mut()
            .map_err(|_| "minimum Body registry cannot publish")?;
        if bodies.len() >= 128 {
            return Err("minimum source miss would clear unrelated bodies".into());
        }
        work.charge(expected_work + 10 + 3 * bodies.len())?;
        bodies
            .try_reserve(1)
            .map_err(|_| "minimum Body allocation failed")?;
        let current = Rc::new(expected.clone());
        bodies.insert(instance, current.clone());
        current
    };
    // Shared authentication independently inventories raw/original/current Bodies and mirrors
    // exact typed dataflow. Its signature and both registry guards stay live through schema checks.
    let source = caller_source(engine, instance, &current, work)?;
    let current_primitive = primitive(engine, &current, work)?;
    let TerminatorKind::Call {
        args, destination, ..
    } = &current.basic_blocks[rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        return Err("minimum checked Call disappeared".into());
    };
    check_occurrence(
        engine,
        &current,
        args,
        Some(*destination),
        primitive_signature,
        work,
    )?;
    work.charge(8)?;
    if current_primitive != original_primitive
        || source.signatures.get(&original_primitive) != Some(&primitive_signature)
    {
        return Err("minimum original/current intrinsic association changed".into());
    }
    drop(source);
    work.charge(12)?; // Actual non-Clone record fields and current Rc ownership transition.
    Ok(MinimumRecord {
        instance,
        current,
        signature: wrapper_signature,
        primitive: original_primitive,
        primitive_signature,
        bits,
    })
}

pub(super) fn check<'tcx>(
    engine: &Engine<'tcx>,
    record: &MinimumRecord<'tcx>,
    bodies: &HashMap<ty::Instance<'tcx>, Rc<Body<'tcx>>>,
    signatures: &HashMap<ty::Instance<'tcx>, ty::PolyFnSig<'tcx>>,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(20)?;
    if record.bits != u32::from(engine.tcx.sess.target.pointer_width)
        || !bodies
            .get(&record.instance)
            .is_some_and(|body| Rc::ptr_eq(body, &record.current))
        || signatures.get(&record.instance) != Some(&record.signature)
        || signatures.get(&record.primitive) != Some(&record.primitive_signature)
    {
        return Err(
            "minimum held original/current Body/signature/target association changed".into(),
        );
    }
    // The genuine primitive uses the existing integer-intrinsic unsigned-Lt/Ite semantics.
    // This record associates that operation with exact wrapper dataflow; no result, predicate,
    // Memory rights or solver outcome is issued by this source-only consumer.
    Ok(())
}
