use super::*;
fn options(steps: usize) -> VerificationOptions {
    let limits = miren::AnalysisLimits {
        max_steps: steps,
        ..Default::default()
    };
    VerificationOptions {
        all_failures: false,
        induction: false,
        startup: false,
        isolated_startup: false,
        async_entry: false,
        limits,
    }
}
fn root<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> ty::Instance<'tcx> {
    ty::Instance::mono(
        tcx,
        tcx.mir_keys(())
            .iter()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == name
            })
            .unwrap()
            .to_def_id(),
    )
}
fn lease_controls<'tcx>(engine: &mut Engine<'tcx>, owner_value: &Value) {
    let source = engine
        .array_iterator_step_evidence
        .iter()
        .find(|evidence| {
            engine.tcx.item_name(evidence.instance.def_id()).as_str() == "next"
                && evidence.current.basic_blocks.len() == 10
        })
        .unwrap();
    let parent = BodyEvidence {
        instance: source.instance,
        current: source.current.clone(),
    };
    let TerminatorKind::Call {
        func: Operand::Constant(function),
        ..
    } = &parent.current.basic_blocks[BasicBlock::from_usize(6)]
        .terminator()
        .kind
    else {
        panic!("real pending bounds Call")
    };
    let ty::FnDef(id, args) = function.const_.ty().kind() else {
        panic!("helper FnDef")
    };
    let callee = engine
        .resolve_function_item(*id, args.skip_binder())
        .unwrap();
    let evidence = load_evidence(engine, callee).unwrap();
    let entry = Rc::new(());
    let mut value = owner_value.clone();
    let Value::OwnedArrayIterator {
        identity,
        payload: Some(payload),
    } = &mut value
    else {
        panic!("retained real owner")
    };
    let identity = identity.clone();
    payload.front = 2;
    payload.pending = Some(Pending {
        index: 1,
        entry: entry.clone(),
    });
    payload.validate(2, true).unwrap();
    let state = State {
        locals: Vec::new(),
        addresses: Vec::new(),
        missing_places: initialized_places::MissingPlaces::default(),
        constant_receipts: constant_reference_receipts::Slots::default(),
        conditions: Vec::new(),
        memory: Memory::from(vec![Some(value)]),
        flow: activation_flow::Flow::Unarmed,
    };
    let words = observe_payload(engine, &state, 0).unwrap();
    let lease = Lease {
        owner: 0,
        parent,
        callee,
        block: BasicBlock::from_usize(6),
        entry: entry.clone(),
        front: 2,
        back: 2,
        pending: 1,
        words,
    };
    let mut invocation = Invocation {
        owner: 0,
        identity,
        entry,
        evidence,
        direction: Direction::Front,
        kind: FrameKind::BoundsHelper,
        lease: Some(lease),
    };
    invocation
        .lease
        .as_ref()
        .unwrap()
        .check(engine, &invocation, &state)
        .unwrap();
    invocation.owner = 1;
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &state)
            .is_err()
    );
    invocation.owner = 0;
    invocation.kind = FrameKind::Inner;
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &state)
            .is_err()
    );
    invocation.kind = FrameKind::BoundsHelper;
    let entry = invocation.entry.clone();
    invocation.entry = Rc::new(());
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &state)
            .is_err()
    );
    invocation.entry = entry;
    invocation.lease.as_mut().unwrap().block = BasicBlock::from_usize(5);
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &state)
            .is_err()
    );
    invocation.lease.as_mut().unwrap().block = BasicBlock::from_usize(6);
    let original = invocation.evidence.instance;
    invocation.evidence.instance = root(engine.tcx, "front_drop");
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &state)
            .is_err()
    );
    invocation.evidence.instance = original;
    for mutation in 0..4 {
        let mut branch = state.clone();
        let Value::OwnedArrayIterator {
            payload: Some(payload),
            ..
        } = branch.memory[0].as_mut().unwrap()
        else {
            unreachable!()
        };
        match mutation {
            0 => payload.front = 1,
            1 => payload.pending.as_mut().unwrap().index = 0,
            2 => payload.pending.as_mut().unwrap().entry = Rc::new(()),
            3 => Rc::make_mut(&mut payload.slots)[1] = None,
            _ => unreachable!(),
        }
        assert!(
            invocation
                .lease
                .as_ref()
                .unwrap()
                .check(engine, &invocation, &branch)
                .is_err()
        );
    }
    let mut absent = state.clone();
    absent.memory[0] = None;
    assert!(
        invocation
            .lease
            .as_ref()
            .unwrap()
            .check(engine, &invocation, &absent)
            .is_err()
    );
    invocation
        .lease
        .as_ref()
        .unwrap()
        .check(engine, &invocation, &state)
        .unwrap();
}
fn controls<'tcx>(tcx: TyCtxt<'tcx>) {
    let config = miren::ContractConfig::default();
    let mut default = Engine::new(tcx, &config, options(8192));
    let refusal = default
        .execute(
            root(tcx, "front_drop"),
            Vec::new(),
            Vec::new(),
            Memory::default(),
            &[],
        )
        .err()
        .unwrap();
    assert!(refusal.contains("step limit"), "default refusal: {refusal}");
    for entry in ["mixed", "empty", "zero_sized", "helper_transport"] {
        let mut diagnostic = Engine::new(tcx, &config, options(30000));
        let returns = diagnostic
            .execute(
                root(tcx, entry),
                Vec::new(),
                Vec::new(),
                Memory::default(),
                &[],
            )
            .unwrap();
        assert_eq!(returns.len(), 1, "actual {entry}");
        let owner = match &returns[0].value {
            Value::OwnedArrayIterator { .. } => &returns[0].value,
            Value::Tuple(parts) => parts
                .iter()
                .find(|part| matches!(part, Value::OwnedArrayIterator { .. }))
                .unwrap(),
            _ => panic!("actual iterator or tuple ownership return"),
        };
        diagnostic.array_iterator_return(owner).unwrap();
    }
    let mut engine = Engine::new(tcx, &config, options(30000));
    let mut returned = engine
        .execute(
            root(tcx, "front_drop"),
            Vec::new(),
            Vec::new(),
            Memory::default(),
            &[],
        )
        .unwrap();
    assert_eq!(returned.len(), 1);
    let mut result = returned.pop().unwrap();
    engine.array_iterator_return(&result.value).unwrap();
    let Value::OwnedArrayIterator {
        identity,
        payload: Some(payload),
    } = &result.value
    else {
        panic!("owner return")
    };
    assert_eq!((payload.front, payload.back), (1, 2));
    assert!(payload.slots[0].is_none() && payload.slots[1].is_some() && payload.pending.is_none());
    let mut branch = result.value.clone();
    let Value::OwnedArrayIterator {
        payload: Some(branch),
        ..
    } = &mut branch
    else {
        unreachable!()
    };
    Rc::make_mut(&mut branch.slots)[1] = None;
    assert!(payload.slots[1].is_some());
    assert!(branch.validate(2, false).is_err());
    let mut corrupt = identity.clone();
    corrupt.view = Some(PrivateView::Step(View {
        owner: 0,
        entry: Rc::new(()),
        role: Role::Data,
    }));
    assert!(
        engine
            .array_iterator_return(&Value::OwnedArrayIterator {
                identity: corrupt,
                payload: Some(payload.clone())
            })
            .is_err()
    );
    let mut retired = payload.clone();
    retired.retired = true;
    assert!(retired.validate(2, false).is_err());
    let mut replay = payload.clone();
    Rc::make_mut(&mut replay.slots)[0] = replay.slots[1].clone();
    assert!(replay.validate(2, false).is_err());
    let mut context = Engine::new(tcx, &config, options(30000));
    context.array_iterator_types.clear();
    assert!(context.array_iterator_return(&result.value).is_err());
    let mut unsupported = engine.steps;
    let wrong = Value::Int {
        expression: engine.terms.boolean(true),
        bits: 16,
        signed: false,
    };
    let original = tcx.types.u16;
    assert!(validate_element(&mut engine, original, &wrong, &[], 0, &mut 0).is_err());
    assert!(engine.steps > unsupported);
    unsupported = engine.steps;
    let foreign = symbolic::Context::default();
    let wrong = symbolic::integer(&foreign, 22, 16, false);
    assert!(validate_element(&mut engine, original, &wrong, &[], 0, &mut 0).is_err());
    assert!(engine.steps > unsupported);
    for (raw, valid) in [
        (0, true),
        (0xd7ff, true),
        (0xe000, true),
        (0x10ffff, true),
        (0xd800, false),
        (0xdfff, false),
        (0x110000, false),
    ] {
        let value = symbolic::integer(&engine.terms, raw, 32, false);
        assert_eq!(
            validate_element(&mut engine, tcx.types.char, &value, &[], 0, &mut 0).is_ok(),
            valid,
            "Char scalar {raw:x}"
        );
    }
    let raw = engine
        .terms
        .symbol(700, miren::smt::Sort::BitVec(32))
        .unwrap();
    let value = Value::Int {
        expression: raw.clone(),
        bits: 32,
        signed: false,
    };
    assert!(validate_element(&mut engine, tcx.types.char, &value, &[], 0, &mut 0).is_err());
    let valid = characters::unicode_scalar(&engine.terms, &raw).unwrap();
    validate_element(&mut engine, tcx.types.char, &value, &[valid], 0, &mut 0).unwrap();
    let bad_bool = Value::Bool(engine.terms.bit_vector(1, 1).unwrap());
    assert!(validate_element(&mut engine, tcx.types.bool, &bad_bool, &[], 0, &mut 0).is_err());
    let bad_float = Value::Float {
        expression: engine.terms.boolean(true),
        bits: 32,
        raw_bits: None,
    };
    assert!(validate_element(&mut engine, tcx.types.f32, &bad_float, &[], 0, &mut 0).is_err());
    let foreign_bool = Value::Bool(foreign.boolean(true));
    assert!(validate_element(&mut engine, tcx.types.bool, &foreign_bool, &[], 0, &mut 0).is_err());
    let foreign_float = symbolic::float(&foreign, 0, 32);
    assert!(validate_element(&mut engine, tcx.types.f32, &foreign_float, &[], 0, &mut 0).is_err());
    for value in [&wrong, &bad_bool, &bad_float, &foreign_bool, &foreign_float] {
        assert!(observe_word(&mut engine, value, 0, &mut Vec::new()).is_err());
    }
    lease_controls(&mut engine, &result.value);
    // The actual ordinary helper receives the owning returned value and executes next_back.
    let next = engine
        .execute(
            root(tcx, "resume"),
            vec![std::mem::replace(&mut result.value, Value::Unit)],
            result.conditions,
            result.memory,
            &[],
        )
        .unwrap();
    let Value::Tuple(parts) = &next[0].value else {
        panic!("ordinary helper tuple return")
    };
    let Value::Adt {
        variant, fields, ..
    } = &parts[0]
    else {
        panic!("real Option Some")
    };
    assert_eq!(*variant, 1);
    let Value::Adt { fields, .. } = &fields[0].1 else {
        panic!("real owning Stamp")
    };
    assert_eq!(
        fields[0].1.integer().unwrap().0.constant(),
        Some(miren::smt::Constant::BitVec(22))
    );
    let Value::OwnedArrayIterator {
        payload: Some(payload),
        ..
    } = &parts[1]
    else {
        panic!("remaining owner")
    };
    assert_eq!((payload.front, payload.back), (1, 1));
    assert!(payload.slots.iter().all(Option::is_none));
    let source = engine
        .array_iterator_step_evidence
        .iter()
        .find(|evidence| {
            tcx.item_name(evidence.instance.def_id()).as_str() == "next_back"
                && evidence.current.basic_blocks.len() == 10
        })
        .unwrap();
    let instance = source.instance;
    let mut changed = source.current.as_ref().clone();
    changed.basic_blocks.as_mut()[BasicBlock::from_usize(9)].statements[2].kind =
        StatementKind::Nop;
    engine
        .bodies
        .borrow_mut()
        .insert(instance, Rc::new(changed));
    assert!(
        load_evidence(&mut engine, instance)
            .err()
            .unwrap()
            .contains("cache was replaced")
    );
    println!(
        "Actual transfer/typed slot/COW/helper/cache controls; default U, diagnostic30000 complete"
    );
}
#[test]
fn actual_iterator_transfer_protocol_and_hostile_controls() {
    struct Capture(bool);
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            controls(tcx);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!(
        "miren-iterator-transfer-controls-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("guest.rs");
    std::fs::write(
        &source,
        include_str!("../../../../../../tests/fixtures/array_iterator_transfers.rs"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
            ];
            let mut args = args;
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut capture = Capture(false);
            rustc_driver::run_compiler(&args, &mut capture);
            assert!(capture.0);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
