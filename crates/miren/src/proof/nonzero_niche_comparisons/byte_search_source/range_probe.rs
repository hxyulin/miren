//! Actual compiler source binding controls. They grant no search or Rust memory authority.
use super::*;

#[derive(Clone, Copy)]
enum Role {
    Root,
    Forwarder,
    Naive,
    Runtime,
}

fn specification(role: Role) -> (&'static str, &'static [LocalType], &'static [Block]) {
    match role {
        Role::Root => (ROOT_KEY, ROOT_LOCALS, ROOT),
        Role::Forwarder => (ALIGNED_KEY, FORWARDER_LOCALS, FORWARDER),
        Role::Naive => (NAIVE_KEY, NAIVE_LOCALS, NAIVE),
        Role::Runtime => (RUNTIME_KEY, RUNTIME_LOCALS, RUNTIME),
    }
}

fn assignment_mut<'a, 'tcx>(
    body: &'a mut Body<'tcx>,
    block: usize,
    index: usize,
) -> &'a mut Rvalue<'tcx> {
    let StatementKind::Assign(value) = &mut body.basic_blocks.as_mut()
        [rustc_middle::mir::BasicBlock::from_usize(block)]
    .statements[index]
        .kind
    else {
        panic!("actual range assignment disappeared")
    };
    &mut value.1
}

fn change_binary(body: &mut Body<'_>, block: usize, statement: usize, replacement: BinOp) {
    let Rvalue::BinaryOp(operation, _) = assignment_mut(body, block, statement) else {
        panic!("actual range binary operation disappeared")
    };
    *operation = replacement;
}

fn normal_edge(body: &mut Body<'_>, block: usize, next: usize) {
    match &mut body.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(block)]
        .terminator_mut()
        .kind
    {
        TerminatorKind::Goto { target } => {
            *target = rustc_middle::mir::BasicBlock::from_usize(next)
        }
        TerminatorKind::Call { target, .. } => {
            *target = Some(rustc_middle::mir::BasicBlock::from_usize(next))
        }
        _ => panic!("actual range normal edge disappeared"),
    }
}

fn unwind_edge(body: &mut Body<'_>, block: usize, next: usize) {
    match &mut body.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(block)]
        .terminator_mut()
        .kind
    {
        TerminatorKind::Assert { unwind, .. } | TerminatorKind::Call { unwind, .. } => {
            *unwind = UnwindAction::Cleanup(rustc_middle::mir::BasicBlock::from_usize(next));
        }
        _ => panic!("actual range unwind edge disappeared"),
    }
}

fn wrong_word_type<'tcx>(engine: &Engine<'tcx>, body: &mut Body<'tcx>, block: usize, index: usize) {
    let Rvalue::BinaryOp(_, operands) = assignment_mut(body, block, index) else {
        panic!("actual word arithmetic disappeared")
    };
    let Operand::Constant(constant) = &mut operands.1 else {
        panic!("actual USIZE_BYTES constant disappeared")
    };
    let rustc_middle::mir::Const::Unevaluated(original, _) = constant.const_ else {
        panic!("actual compiler word constant is not unevaluated")
    };
    let foreign = match engine.tcx.data_layout.pointer_size().bits() {
        32 => engine.tcx.types.u32,
        64 => engine.tcx.types.u64,
        _ => panic!("unexpected compiler target width"),
    };
    constant.const_ = rustc_middle::mir::Const::Unevaluated(original, foreign);
}

fn mutate<'tcx>(
    engine: &Engine<'tcx>,
    role: Role,
    index: usize,
    body: &mut Body<'tcx>,
    work: &mut Work,
) {
    // Actual bounded mutation, owned primitive operands and source-info copy.
    work.charge(24).unwrap();
    if index == 3 {
        let block = &mut body.basic_blocks.as_mut()[START_BLOCK];
        work.charge(8 + 2 * block.statements.len()).unwrap();
        let mut extra = block
            .statements
            .first()
            .expect("actual first assignment")
            .clone();
        extra.kind = StatementKind::Nop;
        block.statements.reserve_exact(1);
        block.statements.push(extra);
        return;
    }
    match (role, index) {
        (Role::Root, 0) => change_binary(body, 1, 1, BinOp::Le),
        (Role::Root, 1) => change_binary(body, 0, 1, BinOp::AddWithOverflow),
        (Role::Root, 2) => {
            let Rvalue::BinaryOp(_, operands) = assignment_mut(body, 5, 2) else {
                panic!("actual result range")
            };
            operands.0 = Operand::Copy(Place::from(Local::from_usize(12)));
        }
        (Role::Root, 4) => normal_edge(body, 2, 3),
        (Role::Root, 5) => unwind_edge(body, 2, 7),
        (Role::Root, 6) => wrong_word_type(engine, body, 0, 1),
        (Role::Root, 7) => {
            let TerminatorKind::Call { args, .. } = &mut body.basic_blocks.as_mut()
                [rustc_middle::mir::BasicBlock::from_usize(2)]
            .terminator_mut()
            .kind
            else {
                panic!("actual naive Call")
            };
            args[1].node = Operand::Move(Place::from(Local::from_usize(2)));
        }
        (Role::Forwarder, 0) => {
            let Rvalue::Aggregate(_, operands) = assignment_mut(body, 0, 0) else {
                panic!("actual argument tuple")
            };
            operands[rustc_abi::FieldIdx::from_usize(0)] =
                Operand::Move(Place::from(Local::from_usize(1)));
        }
        (Role::Forwarder, 1) => {
            let TerminatorKind::Call { args, .. } = &mut body.basic_blocks.as_mut()[START_BLOCK]
                .terminator_mut()
                .kind
            else {
                panic!("actual runtime Call")
            };
            let Operand::Move(place) = args[0].node else {
                panic!("actual moved tuple field")
            };
            args[0].node = Operand::Copy(place);
        }
        (Role::Forwarder, 2) => {
            let TerminatorKind::Call { destination, .. } = &mut body.basic_blocks.as_mut()
                [START_BLOCK]
                .terminator_mut()
                .kind
            else {
                panic!("actual runtime destination")
            };
            *destination = Place::from(Local::from_usize(3));
        }
        (Role::Forwarder, 4) => normal_edge(body, 0, 0),
        (Role::Forwarder, 5) => unwind_edge(body, 0, 1),
        (Role::Forwarder, 6) => body.local_decls[Local::from_usize(1)].ty = engine.tcx.types.u16,
        (Role::Forwarder, 7) => {
            body.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(1)]
                .terminator_mut()
                .kind = TerminatorKind::Unreachable
        }
        (Role::Naive, 0) => change_binary(body, 1, 2, BinOp::Le),
        (Role::Naive, 1) => change_binary(body, 5, 0, BinOp::SubWithOverflow),
        (Role::Naive, 2) => {
            let Rvalue::Aggregate(_, operands) = assignment_mut(body, 4, 1) else {
                panic!("actual Some index")
            };
            operands[rustc_abi::FieldIdx::from_usize(0)] =
                Operand::Copy(Place::from(Local::from_usize(10)));
        }
        (Role::Naive, 4) => normal_edge(body, 6, 8),
        (Role::Naive, 5) => unwind_edge(body, 2, 8),
        (Role::Naive, 6) => body.local_decls[Local::from_usize(8)].ty = engine.tcx.types.u16,
        (Role::Naive, 7) => {
            let Rvalue::UnaryOp(UnOp::PtrMetadata, value) = assignment_mut(body, 1, 1) else {
                panic!("actual naive length")
            };
            *value = Operand::Copy(Place::from(Local::from_usize(0)));
        }
        (Role::Runtime, 0) => change_binary(body, 11, 1, BinOp::Lt),
        (Role::Runtime, 1) => change_binary(body, 19, 0, BinOp::AddWithOverflow),
        (Role::Runtime, 2) => change_binary(body, 28, 2, BinOp::SubWithOverflow),
        (Role::Runtime, 4) => normal_edge(body, 21, 31),
        (Role::Runtime, 5) => unwind_edge(body, 20, 31),
        (Role::Runtime, 6) => wrong_word_type(engine, body, 9, 1),
        (Role::Runtime, 7) => {
            let TerminatorKind::Call { args, .. } = &mut body.basic_blocks.as_mut()
                [rustc_middle::mir::BasicBlock::from_usize(3)]
            .terminator_mut()
            .kind
            else {
                panic!("actual min Call")
            };
            args.swap(0, 1);
        }
        (_, 3) => unreachable!("extra statement handled before exact role controls"),
        (Role::Root | Role::Forwarder | Role::Naive | Role::Runtime, _) => {
            panic!("invalid range mutation control")
        }
    }
}

fn actual_search<'tcx>(
    engine: &Engine<'tcx>,
    root: ty::Instance<'tcx>,
) -> (ty::Instance<'tcx>, usize) {
    let root_body = engine.instantiated_body(root).unwrap();
    let outer = root_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return None;
            };
            let ty::FnDef(id, args) = func.ty(&root_body.local_decls, engine.tcx).kind() else {
                return None;
            };
            Some(
                engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap(),
            )
        })
        .expect("actual original byte outer Call");
    let mut budget = GraphBudget::new(0).unwrap();
    let outer_body = engine
        .capture_niche_comparison_body(outer, &mut budget, true, GraphGoal::ByteRoute)
        .unwrap()
        .body;
    let TerminatorKind::Call { func, .. } = &outer_body.basic_blocks[START_BLOCK].terminator().kind
    else {
        panic!("actual dispatcher")
    };
    let ty::FnDef(id, args) = func.ty(&outer_body.local_decls, engine.tcx).kind() else {
        panic!("actual dispatcher item")
    };
    let dispatcher = engine
        .resolve_function_item(*id, args.skip_binder())
        .unwrap();
    let dispatcher_body = engine
        .capture_niche_comparison_body(dispatcher, &mut budget, true, GraphGoal::ByteRoute)
        .unwrap()
        .body;
    let original = outer
        .args
        .first()
        .and_then(|argument| argument.as_type())
        .expect("actual outer item");
    budget.charge(8).unwrap();
    let records = [
        (outer, outer_body.clone()),
        (dispatcher, dispatcher_body.clone()),
    ];
    let mapping = super::super::super::byte_transport::bind_current(
        engine,
        original,
        outer,
        dispatcher,
        &records,
        &mut budget,
    )
    .unwrap()
    .unwrap();
    (mapping.helpers[5].instance, budget.work)
}

pub(in super::super) fn compiler_controls<'tcx>(engine: &Engine<'tcx>, root: ty::Instance<'tcx>) {
    let (search, prior) = actual_search(engine, root);
    let metadata = conditional(engine, search, prior).unwrap();
    assert_eq!(metadata.records.len(), 4);
    assert!(metadata.work.used > prior);
    assert!(engine.bodies.try_borrow_mut().is_err());
    assert!(engine.call_signatures.try_borrow_mut().is_err());
    for (record, role) in
        metadata
            .records
            .iter()
            .zip([Role::Root, Role::Forwarder, Role::Naive, Role::Runtime])
    {
        let source = GuardedRangeSource {
            engine,
            instance: record.instance,
            helpers: &record.helpers,
            signatures: &metadata.signatures,
        };
        let (name, locals, blocks) = specification(role);
        for phase in [SourcePhase::Raw, SourcePhase::Normalized] {
            let original = match phase {
                SourcePhase::Raw => engine.tcx.instance_mir(record.instance.def),
                SourcePhase::Normalized => record.current.as_ref(),
            };
            for index in 0..8 {
                // Each hostile shape is an independent diagnostic invocation. No failed object
                // resumes and no diagnostic starting work is fed into a production certificate.
                let mut paid = Work::new(metadata.work.used).unwrap();
                let clone = inventory(engine, record.instance, original, phase, &mut paid).unwrap();
                paid.charge(clone + 16).unwrap();
                let mut changed = original.clone();
                mutate(engine, role, index, &mut changed, &mut paid);
                let error = shape(&source, &mut paid, &changed, name, locals, blocks).unwrap_err();
                assert_eq!(error.category, UnknownCategory::Semantics);
                assert!(matches!(
                    error.reason.as_str(),
                    "range source exact original local type differs"
                        | "range source complete block/statement inventory differs"
                        | "range source typed assignment/dataflow differs"
                        | "range source complete terminator/dataflow differs"
                ));
                let phase_name = match phase {
                    SourcePhase::Raw => "Raw",
                    SourcePhase::Normalized => "Normalized",
                };
                eprintln!("BYTE RANGE actual {name} {phase_name} mutant={index} semantic refusal");
            }
        }
        if !matches!(role, Role::Forwarder) {
            let mut paid = Work::new(metadata.work.used).unwrap();
            let clone = inventory(
                engine,
                record.instance,
                &record.current,
                SourcePhase::Normalized,
                &mut paid,
            )
            .unwrap();
            paid.charge(clone + 24).unwrap();
            let mut changed = record.current.as_ref().clone();
            let (block, index) = match role {
                Role::Root => (1, 0),
                Role::Naive => (0, 0),
                Role::Runtime => (2, 0),
                Role::Forwarder => unreachable!("forwarder has no Use assignment"),
            };
            let Rvalue::Use(_, retag) = assignment_mut(&mut changed, block, index) else {
                panic!("actual Use with retag")
            };
            assert_eq!(*retag, rustc_middle::mir::WithRetag::Yes);
            *retag = rustc_middle::mir::WithRetag::No;
            let error = shape(&source, &mut paid, &changed, name, locals, blocks).unwrap_err();
            assert_eq!(error.category, UnknownCategory::Semantics);
            assert_eq!(
                error.reason,
                "range source typed assignment/dataflow differs"
            );
            eprintln!("BYTE RANGE actual {name} original RetagYes/nonmatching RetagNo; auth only");
        }
    }
    // Original compiler W is evaluated independently from its source identity and usize layout.
    let StatementKind::Assign(value) =
        &metadata.records[0].current.basic_blocks[START_BLOCK].statements[1].kind
    else {
        panic!("actual compiler W assignment")
    };
    let Rvalue::BinaryOp(_, operands) = &value.1 else {
        panic!("actual compiler W")
    };
    let mut paid = Work::new(metadata.work.used).unwrap();
    assert!(constant(engine, &mut paid, &operands.1, Input::Word).unwrap());
    assert!(!constant(engine, &mut paid, &operands.0, Input::Word).unwrap());
    let word = u128::from(engine.tcx.data_layout.pointer_size().bytes());
    assert!(constant(engine, &mut paid, &operands.1, Input::Number(word)).unwrap());
    assert!(!constant(engine, &mut paid, &operands.1, Input::Number(word + 1)).unwrap());
    let used = metadata.work.used;
    eprintln!(
        "BYTE RANGE complete 9/33 source CFG plus 8/2 routing; \
         W={word} used={used}; conditional only"
    );
    let ConditionalRangeMetadata {
        records,
        minimum,
        bodies,
        signatures,
        work,
    } = metadata;
    drop(bodies);
    drop(signatures);
    // Actual final binding rejects a replaced cache object even when its typed shape is unchanged.
    let mut paid = Work::new(work.used).unwrap();
    paid.charge(4).unwrap();
    let current = records[0].current.clone();
    let clone = inventory(engine, search, &current, SourcePhase::Normalized, &mut paid).unwrap();
    paid.charge(clone + 20).unwrap();
    engine
        .bodies
        .borrow_mut()
        .insert(search, Rc::new(current.as_ref().clone()));
    let error = match bind_records(engine, records, minimum, paid) {
        Ok(_) => panic!("replaced current source admitted conditional metadata"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "range prepared original/current source identity changed"
    );
    engine.bodies.borrow_mut().insert(search, current);
    let fresh = conditional(engine, search, prior).unwrap();
    let ConditionalRangeMetadata {
        records,
        minimum,
        bodies,
        signatures,
        mut work,
    } = fresh;
    work.charge(12).unwrap(); // Actual original/foreign full-signature copies and cache insertion.
    let original = records[0].signature;
    let foreign = records[0]
        .helpers
        .last()
        .expect("actual assertion helper")
        .signature;
    assert_ne!(original, foreign);
    drop(bodies);
    drop(signatures);
    engine.call_signatures.borrow_mut().insert(search, foreign);
    let error = match bind_records(engine, records, minimum, work) {
        Ok(_) => panic!("foreign current full signature issued conditional metadata"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "range prepared original/current source identity changed"
    );
    engine.call_signatures.borrow_mut().insert(search, original);
    let held = engine.bodies.borrow_mut();
    let error = match conditional(engine, search, prior) {
        Ok(_) => panic!("borrowed registry issued range metadata"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(error.reason, "byte source Body registry is borrowed");
    drop(held);
    let error = match conditional(engine, search, usize::MAX) {
        Ok(_) => panic!("overflowing prior issued range metadata"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::ResourceLimit);
    assert!(conditional(engine, search, prior).is_ok());
    eprintln!("BYTE RANGE registry replacement/conflict and resource refusal; no search authority");
    let metadata = conditional(engine, search, prior).unwrap();
    let minimum = minimum::probe::instance(&metadata.minimum);
    let used = metadata.work.used;
    drop(metadata);
    minimum::probe::compiler_controls(engine, minimum, used);
}
