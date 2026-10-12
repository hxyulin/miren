//! Real compiler producer and hostile receipt controls, not guest semantic proof claims.
use super::*;
use std::path::PathBuf;

fn producer<'a, 'tcx>(body: &'a Body<'tcx>) -> (Location, &'a ConstOperand<'tcx>, Place<'tcx>) {
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .find_map(|(statement_index, statement)| {
                    let StatementKind::Assign(assignment) = &statement.kind else {
                        return None;
                    };
                    let Rvalue::Use(Operand::Constant(constant), _) = &assignment.1 else {
                        return None;
                    };
                    if matches!(constant.const_, rustc_middle::mir::Const::Unevaluated(value, _)
                if value.promoted.is_some())
                    {
                        Some((
                            Location {
                                block,
                                statement_index,
                            },
                            constant.as_ref(),
                            assignment.0,
                        ))
                    } else {
                        None
                    }
                })
        })
        .expect("actual retained promoted producer")
}

fn controls<'tcx>(tcx: TyCtxt<'tcx>, root: DefId, other: DefId) {
    let mut engine = nonzero_niches::test_engine(tcx);
    let caller = ty::Instance::mono(tcx, root);
    let body = engine.instantiated_body(caller).unwrap();
    let (location, constant, place) = producer(&body);
    let raw_caller = tcx.instance_mir(caller.def);
    let raw_producer =
        &raw_caller.basic_blocks[location.block].statements[location.statement_index];
    let current_producer = &body.basic_blocks[location.block].statements[location.statement_index];
    assert_eq!(
        matching_constant_producer(raw_producer, current_producer)
            .unwrap()
            .1,
        rustc_middle::mir::WithRetag::Yes
    );
    let mut wrong_retag = current_producer.clone();
    let StatementKind::Assign(assignment) = &mut wrong_retag.kind else {
        panic!("actual constant assignment");
    };
    let Rvalue::Use(_, retag) = &mut assignment.1 else {
        panic!("actual constant use");
    };
    *retag = rustc_middle::mir::WithRetag::No;
    assert!(matching_constant_producer(raw_producer, &wrong_retag).is_none());
    assert!(matching_constant_producer(&wrong_retag, current_producer).is_none());
    assert_eq!(
        matching_constant_producer(&wrong_retag, &wrong_retag)
            .unwrap()
            .1,
        rustc_middle::mir::WithRetag::No
    ); // Matching metadata alone issues no receipt.

    let mut registry = Registry::new(&engine, caller, &body);
    let ordinary = engine
        .constant(root, constant.const_, constant.span)
        .unwrap();
    let (decoded, key) = registry
        .paired_constant(&engine, &body, location, constant)
        .unwrap();
    assert!(matches!((&ordinary, &decoded),
        (Value::Adt { variant: 0, fields: a, .. }, Value::Adt { variant: 0, fields: b, .. })
            if a.is_empty() && b.is_empty()));
    let key = key.expect("genuine immutable promoted None receipt");
    registry
        .validate_argument(&engine, &body, &key, constant.const_.ty())
        .unwrap();
    assert_eq!(
        registry.receipts[key.index].producer_retag,
        rustc_middle::mir::WithRetag::Yes
    );
    registry.receipts[key.index].producer_retag = rustc_middle::mir::WithRetag::No;
    assert!(
        registry
            .validate_argument(&engine, &body, &key, constant.const_.ty())
            .unwrap_err()
            .contains("retained producer metadata")
    );
    registry.receipts[key.index].producer_retag = rustc_middle::mir::WithRetag::Yes;
    let receipt = &registry.receipts[key.index];
    let raw = tcx
        .promoted_mir(receipt.owner.def_id())
        .get(receipt.promoted)
        .unwrap();
    // Genuine actual Body mutations must fail the independent closed semantic schema.
    let mut changed = raw.clone();
    changed.basic_blocks.as_mut()[START_BLOCK].statements[0].kind = StatementKind::Nop;
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let mut changed = raw.clone();
    let StatementKind::Assign(assignment) =
        &mut changed.basic_blocks.as_mut()[START_BLOCK].statements[1].kind
    else {
        panic!("actual shared borrow")
    };
    let Rvalue::Ref(_, borrow, _) = &mut assignment.1 else {
        panic!("actual shared borrow")
    };
    *borrow = BorrowKind::Fake(rustc_middle::mir::FakeBorrowKind::Shallow);
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let mut changed = raw.clone();
    changed.basic_blocks.as_mut()[START_BLOCK]
        .terminator_mut()
        .kind = TerminatorKind::Unreachable;
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let mut changed = raw.clone();
    changed.local_decls[Local::from_usize(1)].ty = tcx.types.u8;
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let mut changed = raw.clone();
    changed.required_consts = None;
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let mut changed = raw.clone();
    changed.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)].span =
        rustc_span::DUMMY_SP;
    assert!(same_closed_body(raw, &changed).is_err());
    let mut changed = raw.clone();
    changed.source.promoted = None;
    assert!(
        closed_none_body(
            &engine,
            &changed,
            receipt.owner,
            receipt.promoted,
            receipt.original
        )
        .is_err()
    );
    let foreign_registry = Registry::new(&engine, caller, &body);
    assert!(
        foreign_registry
            .validate_argument(&engine, &body, &key, constant.const_.ty())
            .unwrap_err()
            .contains("namespace")
    );
    let replaced = Rc::new(body.as_ref().clone());
    assert!(
        registry
            .validate_argument(&engine, &replaced, &key, constant.const_.ty())
            .unwrap_err()
            .contains("Body")
    );
    let foreign_engine = nonzero_niches::test_engine(tcx);
    // Hold the exact same actual cached Body so this control reaches Context freshness.
    foreign_engine
        .bodies
        .borrow_mut()
        .insert(caller, body.clone());
    assert!(
        registry
            .validate_argument(&foreign_engine, &body, &key, constant.const_.ty())
            .is_err()
    );
    let original = constant.const_.ty();
    assert!(
        registry
            .validate_argument(&engine, &body, &key, tcx.types.u8)
            .is_err()
    );
    let invalid = Key {
        namespace: key.namespace.clone(),
        index: usize::MAX,
    };
    assert!(
        registry
            .validate_argument(&engine, &body, &invalid, original)
            .is_err()
    );
    let other_body = engine
        .instantiated_body(ty::Instance::mono(tcx, other))
        .unwrap();
    let (other_location, other_constant, _) = producer(&other_body);
    let mut other_registry = Registry::new(&engine, ty::Instance::mono(tcx, other), &other_body);
    let (_, absent) = other_registry
        .paired_constant(&engine, &other_body, other_location, other_constant)
        .unwrap();
    assert!(
        absent.is_none(),
        "Some producer is outside the closed None schema"
    );
    assert!(compiler_backing(&engine, original, ConstValue::ZeroSized).is_err());
    let evaluated = constant
        .const_
        .eval(tcx, ty::TypingEnv::fully_monomorphized(), constant.span)
        .unwrap();
    let ConstValue::Scalar(Scalar::Ptr(pointer, width)) = evaluated else {
        panic!("actual shared immutable promoted pointer");
    };
    let without_flags = pointer.map_provenance(|provenance| {
        rustc_middle::mir::interpret::CtfeProvenance::from(provenance.alloc_id())
    });
    assert!(
        compiler_backing(
            &engine,
            original,
            ConstValue::Scalar(Scalar::Ptr(without_flags, width))
        )
        .is_err()
    );
    let shared_only = pointer.map_provenance(|provenance| {
        rustc_middle::mir::interpret::CtfeProvenance::from(provenance.alloc_id()).as_shared_ref()
    });
    assert!(
        compiler_backing(
            &engine,
            original,
            ConstValue::Scalar(Scalar::Ptr(shared_only, width))
        )
        .is_err()
    );
    assert!(
        compiler_backing(
            &engine,
            original,
            ConstValue::Scalar(Scalar::Ptr(
                pointer.wrapping_offset(Size::from_bytes(1), &tcx),
                width
            ))
        )
        .is_err()
    );
    let actual_promoted = registry.receipts[key.index].promoted;
    registry.receipts[key.index].promoted = Promoted::from_usize(
        tcx.promoted_mir(registry.receipts[key.index].owner.def_id())
            .len(),
    );
    assert!(
        registry
            .validate_argument(&engine, &body, &key, original)
            .unwrap_err()
            .contains("unavailable")
    );
    registry.receipts[key.index].promoted = actual_promoted;
    let static_id = tcx
        .mir_keys(())
        .iter()
        .copied()
        .find(|id| tcx.item_name(id.to_def_id()).as_str() == "OTHER")
        .unwrap()
        .to_def_id();
    assert!(
        checked_allocation(&engine, tcx.reserve_and_set_static_alloc(static_id))
            .unwrap_err()
            .contains("static identity")
    );

    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: Slots::default(),
        missing_places: Default::default(),
        conditions: Vec::new(),
        memory: Memory::from(Vec::new()),
    };
    state.constant_receipts.publish(place, Some(key.clone()));
    state.locals[place.local.as_usize()] = Some(decoded.clone());
    let copy = Operand::Copy(place);
    let copied = state.constant_receipts.operand(&copy).unwrap();
    engine
        .evaluate_operand(root, &body, &mut state, &copy)
        .unwrap();
    assert!(state.constant_receipts.operand(&copy).is_some());
    let moved = state
        .constant_receipts
        .operand(&Operand::Move(place))
        .unwrap();
    engine
        .evaluate_operand(root, &body, &mut state, &Operand::Move(place))
        .unwrap();
    assert!(state.constant_receipts.operand(&copy).is_none());
    registry
        .validate_argument(&engine, &body, &moved, original)
        .unwrap();
    registry
        .validate_argument(&engine, &body, &copied, original)
        .unwrap();
    engine.write(&mut state, place, decoded.clone()).unwrap();
    state.constant_receipts.publish(place, Some(key.clone()));
    let continuation = state.continuation(Vec::new(), Memory::from(Vec::new()));
    assert!(continuation.constant_receipts.operand(&copy).is_some());
    engine.write(&mut state, place, decoded.clone()).unwrap();
    assert!(
        state.constant_receipts.operand(&copy).is_none(),
        "overwrite invalidates"
    );
    state.constant_receipts.publish(place, Some(key.clone()));
    engine
        .store_call_result(&body, &mut state, place, None, decoded)
        .unwrap();
    assert!(
        state.constant_receipts.operand(&copy).is_none(),
        "call result invalidates"
    );
    state.constant_receipts.publish(place, Some(key));
    engine
        .statement(
            caller,
            &body,
            &mut state,
            &StatementKind::StorageDead(place.local),
        )
        .unwrap();
    assert!(
        state.constant_receipts.operand(&copy).is_none(),
        "StorageDead invalidates"
    );
    // An actual typed local-use mutation reaches the normal evaluator/store with Retag Yes.
    // The current value remains initialized; the existing receipt key must not transfer.
    engine.write(&mut state, place, ordinary.clone()).unwrap();
    state.constant_receipts.publish(place, Some(moved.clone()));
    let mut local_use = body.as_ref().clone();
    let StatementKind::Assign(assignment) = &mut local_use.basic_blocks.as_mut()[location.block]
        .statements[location.statement_index]
        .kind
    else {
        panic!("actual assignment");
    };
    assignment.1 = Rvalue::Use(Operand::Copy(place), rustc_middle::mir::WithRetag::Yes);
    let local_use = Rc::new(local_use);
    let mut local_registry = Registry::new(&engine, caller, &local_use);
    engine
        .receipt_statement(
            caller,
            &local_use,
            &mut state,
            &mut local_registry,
            location,
        )
        .unwrap();
    assert!(
        state.constant_receipts.operand(&copy).is_none(),
        "Yes local use has no receipt transport"
    );
    assert!(local_registry.receipts.is_empty());
    // The independent namespace/key cannot be minted by publishing a decoded None value.
    assert_eq!(Slots::default().len(), 0);
    let original_len = registry.receipts.len();
    let (_, rollback) = registry
        .paired_constant(&engine, &body, location, constant)
        .unwrap();
    assert!(rollback.is_some());
    registry.discard(rollback);
    assert_eq!(registry.receipts.len(), original_len);
    eprintln!(
        "compiler constant receipts: actual None, Some refusal, Copy/Move and hostile controls"
    );
}

#[test]
fn actual_promoted_none_receipts_and_hostile_transport() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let locate = |name: &str| {
                tcx.mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(*id) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap()
                    .to_def_id()
            };
            controls(tcx, locate("receipt"), locate("some_receipt"));
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = PathBuf::from(format!(
        "/tmp/miren-constant-receipts-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("guest.rs");
    std::fs::write(
        &source,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        pub static OTHER:Option<core::num::NonZeroU8>=None;\n\
        #[inline(never)] pub fn receipt(v:&[Option<core::num::NonZeroU8>])->bool\n\
        {v.contains(&None)}\n\
        #[inline(never)] pub fn some_receipt(v:&[Option<core::num::NonZeroU8>])->bool\n\
        {v.contains(&Some(core::num::NonZeroU8::MIN))}\n",
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
    let args = vec![
        "rustc".into(),
        source.to_str().unwrap().into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "-Cpanic=abort".into(),
        "-Copt-level=0".into(),
        "--sysroot".into(),
        sysroot.trim().into(),
        "--out-dir".into(),
        directory.to_str().unwrap().into(),
    ];
    let mut check = Check(false);
    rustc_driver::run_compiler(&args, &mut check);
    assert!(check.0);
}
