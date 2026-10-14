//! Actual original/current minimum schema controls, separate from arithmetic proof evidence.
use super::*;

pub(in super::super) fn instance<'tcx>(record: &MinimumRecord<'tcx>) -> ty::Instance<'tcx> {
    record.instance
}

fn first<'a, 'tcx>(body: &'a mut Body<'tcx>) -> &'a mut TerminatorKind<'tcx> {
    &mut body.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
        .terminator_mut()
        .kind
}

fn mutate<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &mut Body<'tcx>,
    index: usize,
    work: &mut Work,
) {
    work.charge(40).unwrap();
    match index {
        0 | 1 | 2 | 3 | 4 | 5 | 10 | 11 | 12 => {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                ..
            } = first(body)
            else {
                panic!("actual minimum Call disappeared")
            };
            match index {
                0 => args[0].node = Operand::Copy(Place::from(Local::from_usize(2))),
                1 => args[0].node = Operand::Move(Place::from(Local::from_usize(1))),
                2 => *destination = Place::from(Local::from_usize(1)),
                3 => *target = None,
                4 => *unwind = rustc_middle::mir::UnwindAction::Continue,
                5 => *call_source = rustc_middle::mir::CallSource::Misc,
                10 | 11 => {
                    work.charge(24).unwrap();
                    let Operand::Constant(constant) = func else {
                        panic!("actual minimum function constant")
                    };
                    let ty::FnDef(id, _) = constant.const_.ty().kind() else {
                        panic!("actual minimum primitive item")
                    };
                    let (id, arguments) = if index == 10 {
                        (*id, engine.tcx.mk_args(&[engine.tcx.types.u32.into()]))
                    } else {
                        (instance.def_id(), instance.args)
                    };
                    constant.const_ = rustc_middle::mir::Const::Val(
                        rustc_middle::mir::ConstValue::ZeroSized,
                        Ty::new_fn_def(engine.tcx, id, ty::Binder::dummy(arguments)),
                    );
                }
                12 => {
                    work.charge(8).unwrap();
                    *args = args[..1].to_vec().into_boxed_slice();
                }
                _ => unreachable!("outer Call mutation dispatch"),
            }
        }
        6 => {
            body.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(1)]
                .terminator_mut()
                .kind = TerminatorKind::Unreachable;
        }
        7 => {
            let block = &mut body.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK];
            work.charge(12 + 2 * block.statements.len()).unwrap();
            block.statements.reserve_exact(1);
            block.statements.push(rustc_middle::mir::Statement::new(
                block.terminator().source_info,
                StatementKind::Nop,
            ));
        }
        8 => {
            body.local_decls[Local::from_usize(1)].ty = match engine.tcx.sess.target.pointer_width {
                32 => engine.tcx.types.u32,
                64 => engine.tcx.types.u64,
                _ => panic!("unsupported compiler target"),
            };
        }
        9 => body.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK].is_cleanup = true,
        13 => {
            work.charge(12 + 2 * body.local_decls.len()).unwrap();
            let extra = body.local_decls[Local::from_usize(1)].clone();
            body.local_decls.raw.reserve(1);
            body.local_decls.push(extra);
        }
        14 => body.arg_count = 1,
        15 => {
            *first(body) = TerminatorKind::Goto {
                target: rustc_middle::mir::START_BLOCK,
            }
        }
        _ => panic!("unknown minimum mutation"),
    }
}

fn held_check<'tcx>(
    engine: &Engine<'tcx>,
    record: &MinimumRecord<'tcx>,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(8)?;
    let bodies = engine
        .bodies
        .try_borrow()
        .map_err(|_| "minimum control Body registry borrowed")?;
    let signatures = engine
        .call_signatures
        .try_borrow()
        .map_err(|_| "minimum control signature registry borrowed")?;
    check(engine, record, &bodies, &signatures, work)
}

pub(in super::super) fn compiler_controls<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    prior: usize,
) {
    let mut work = Work::new(prior).unwrap();
    let mut record = prepare(engine, instance, &mut work).unwrap();
    held_check(engine, &record, &mut work).unwrap();
    assert!(matches!(record.bits, 32 | 64));
    let mut schema_work = Work::new(work.used).unwrap();
    assert_eq!(
        primitive(engine, &record.current, &mut schema_work).unwrap(),
        record.primitive
    );
    for (phase, original) in [
        (SourcePhase::Raw, engine.tcx.instance_mir(instance.def)),
        (SourcePhase::Normalized, record.current.as_ref()),
    ] {
        for index in 0..16 {
            let mut paid = Work::new(work.used).unwrap();
            let clone = inventory(engine, instance, original, phase, &mut paid).unwrap();
            paid.charge(clone + 16).unwrap();
            let mut changed = original.clone();
            mutate(engine, instance, &mut changed, index, &mut paid);
            let error = primitive(engine, &changed, &mut paid).unwrap_err();
            assert_eq!(error.category, UnknownCategory::Semantics);
            let phase_name = match phase {
                SourcePhase::Raw => "Raw",
                SourcePhase::Normalized => "Current",
            };
            eprintln!("BYTE MINIMUM {phase_name} mutant={index} semantic refusal");
        }
    }
    work.charge(12 + 3 * engine.call_signatures.borrow().len())
        .unwrap();
    let foreign = engine
        .call_signatures
        .borrow()
        .values()
        .copied()
        .find(|signature| *signature != record.signature)
        .expect("actual distinct core signature");
    for selected in [record.instance, record.primitive] {
        let mut paid = Work::new(work.used).unwrap();
        paid.charge(16).unwrap();
        let original = engine
            .call_signatures
            .borrow_mut()
            .insert(selected, foreign)
            .unwrap();
        let error = held_check(engine, &record, &mut paid).unwrap_err();
        assert_eq!(error.category, UnknownCategory::Semantics);
        assert_eq!(
            error.reason,
            "minimum held original/current Body/signature/target association changed"
        );
        engine
            .call_signatures
            .borrow_mut()
            .insert(selected, original);
        eprintln!("BYTE MINIMUM actual full signature replacement semantic refusal");
    }
    let mut paid = Work::new(work.used).unwrap();
    let clone = inventory(
        engine,
        instance,
        &record.current,
        SourcePhase::Normalized,
        &mut paid,
    )
    .unwrap();
    paid.charge(clone + 20).unwrap();
    let replacement = Rc::new(record.current.as_ref().clone());
    let current = engine
        .bodies
        .borrow_mut()
        .insert(instance, replacement)
        .unwrap();
    let error = held_check(engine, &record, &mut paid).unwrap_err();
    assert_eq!(error.category, UnknownCategory::Semantics);
    engine.bodies.borrow_mut().insert(instance, current);
    eprintln!("BYTE MINIMUM actual current Rc replacement semantic refusal");
    for signature_registry in [false, true] {
        let mut paid = Work::new(work.used).unwrap();
        let error = if signature_registry {
            let held = engine.call_signatures.borrow_mut();
            let error = prepare(engine, instance, &mut paid).err().unwrap();
            drop(held);
            error
        } else {
            let held = engine.bodies.borrow_mut();
            let error = prepare(engine, instance, &mut paid).err().unwrap();
            drop(held);
            error
        };
        assert_eq!(error.category, UnknownCategory::Semantics);
        assert!(error.reason.contains("registry is borrowed"));
        eprintln!("BYTE MINIMUM actual registry conflict signature={signature_registry}");
    }
    let mut paid = Work::new(work.used).unwrap();
    assert_eq!(
        identity(engine, record.primitive, &mut paid)
            .unwrap_err()
            .category,
        UnknownCategory::Semantics
    );
    assert_eq!(
        signature(engine, foreign, &mut paid).unwrap_err().category,
        UnknownCategory::Semantics
    );
    paid.charge(12).unwrap();
    let original_bits = record.bits;
    record.bits = if original_bits == 32 { 64 } else { 32 };
    assert_eq!(
        held_check(engine, &record, &mut paid).unwrap_err().category,
        UnknownCategory::Semantics
    );
    record.bits = original_bits;
    eprintln!("BYTE MINIMUM wrapper identity/full signature and target mismatch semantic refusal");
    let mut exhausted = Work::new(0).unwrap();
    let first = exhausted.charge(NICHE_GRAPH_WORK).unwrap_err();
    assert_eq!(first.category, UnknownCategory::ResourceLimit);
    let used = exhausted.used;
    let second = prepare(engine, instance, &mut exhausted).err().unwrap();
    assert_eq!(second.category, UnknownCategory::ResourceLimit);
    assert_eq!(second.reason, first.reason);
    assert_eq!(exhausted.used, used);
    let mut fresh = Work::new(work.used).unwrap();
    held_check(engine, &record, &mut fresh).unwrap();
    eprintln!(
        "BYTE MINIMUM target bits={} sticky resource refusal; no search authority",
        record.bits
    );
}
