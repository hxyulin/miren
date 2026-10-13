//! Compiler-owned receiver, region, storage and body admission controls.
use super::super::initialized_places::Step;
use super::*;
use rustc_middle::mir::Local;
use std::path::Path;

#[test]
fn actual_shared_drop_calls_authenticate_receivers_and_execute_bodies() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let config = miren::ContractConfig::default();
            let options = || VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            };
            let find = |name: &str| {
                ty::Instance::mono(
                    tcx,
                    tcx.mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(*id) == DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap()
                        .to_def_id(),
                )
            };
            let mut engine = Engine::new(tcx, &config, options());
            let caller = find("claim");
            let helper = find("observe");
            let body = engine.instantiated_body(caller).unwrap();
            let place = body
                .basic_blocks
                .iter()
                .flat_map(|b| &b.statements)
                .find_map(|s| {
                    let StatementKind::Assign(pair) = &s.kind else {
                        return None;
                    };
                    let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place) = &pair.1
                    else {
                        return None;
                    };
                    matches!(place.projection.first(), Some(ProjectionElem::Index(_)))
                        .then_some(*place)
                })
                .unwrap();
            let ProjectionElem::Index(index) = place.projection[0] else {
                unreachable!()
            };
            let (block, actual) = body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(bb, data)| {
                    let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, _) = func.ty(&body.local_decls, tcx).kind() else {
                        return None;
                    };
                    (*id == helper.def_id())
                        .then_some((bb, args[0].node.ty(&body.local_decls, tcx)))
                })
                .unwrap();
            let legacy = engine.call_signature(helper).unwrap().inputs()[0];
            let canonical = engine
                .shared_drop_signature(helper)
                .unwrap()
                .unwrap()
                .inputs()[0];
            println!("original legacy receiver: {legacy:?}; actual MIR: {actual:?}");
            println!("erased compiler receiver: {canonical:?}");
            assert_ne!(legacy, actual);
            // The skipped binder still contains a bound region. Ordinary region erasure
            // cannot instantiate it; the existing compiler binder service is required.
            assert_eq!(tcx.erase_and_anonymize_regions(legacy), legacy);
            assert_eq!(canonical, actual);
            let ty::Ref(_, legacy_target, _) = legacy.kind() else {
                unreachable!()
            };
            let ty::Ref(_, actual_target, _) = actual.kind() else {
                unreachable!()
            };
            assert_eq!(legacy_target, actual_target);
            let original = body.local_decls[place.local].ty;
            let mut conditions = Vec::new();
            let owner = engine
                .argument(caller.def_id(), original, &mut conditions)
                .unwrap();
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                conditions,
                memory: Memory::default(),
                missing_places: initialized_places::MissingPlaces::default(),
            };
            state.locals[place.local.as_usize()] = Some(owner);
            state.locals[index.as_usize()] = Some(engine.iterator_index(0));
            let receiver = engine
                .borrow_drop_shared_place(&body, &mut state, place)
                .unwrap()
                .unwrap();
            let Value::Reference { allocation, .. } = &receiver else {
                unreachable!()
            };
            let allocation = *allocation;
            let values = [receiver.clone()];
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &state.memory,
                        &state.conditions
                    )
                    .unwrap()
            );
            assert!(
                engine
                    .shared_drop_receiver_call(
                        (caller, &body, block),
                        helper,
                        &values,
                        &mut state.clone(),
                        &[]
                    )
                    .unwrap()
                    .is_some()
            );
            assert!(
                engine
                    .proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function.contains("observe"))
            );
            assert!(
                engine
                    .reference_value(&receiver, &state.memory, &state.conditions)
                    .is_err()
            );
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        find("other_observe"),
                        &values,
                        &state.memory,
                        &state.conditions
                    )
                    .unwrap_err()
                    .contains("pointee type differs")
            );
            let cloned = Rc::new(body.as_ref().clone());
            assert!(
                engine
                    .shared_drop_receiver_call(
                        (caller, &cloned, block),
                        helper,
                        &values,
                        &mut state.clone(),
                        &[]
                    )
                    .is_err()
            );
            let mut consumed = state.clone();
            consumed
                .memory
                .missing_places
                .consume(allocation, vec![Step::Element(0)])
                .unwrap();
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &consumed.memory,
                        &consumed.conditions
                    )
                    .is_err()
            );
            let mut sibling = state.clone();
            sibling
                .memory
                .missing_places
                .consume(allocation, vec![Step::Element(1)])
                .unwrap();
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &sibling.memory,
                        &sibling.conditions
                    )
                    .unwrap()
            );
            let mut retired = state.clone();
            retired.memory.retire_initialized_owner(allocation);
            retired.memory[allocation] = None;
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &retired.memory,
                        &retired.conditions
                    )
                    .is_err()
            );
            let mut foreign = Engine::new(tcx, &config, options());
            foreign.owned_projection_certificates = engine.owned_projection_certificates.clone();
            foreign.bodies.borrow_mut().insert(caller, body.clone());
            assert!(
                foreign
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &state.memory,
                        &state.conditions
                    )
                    .is_err()
            );
            let mut mutable = receiver.clone();
            let Value::Reference { mutable: flag, .. } = &mut mutable else {
                unreachable!()
            };
            *flag = true;
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &[mutable],
                        &state.memory,
                        &state.conditions
                    )
                    .is_err()
            );
            let mut infeasible = state.clone();
            infeasible.conditions.push(engine.terms.boolean(false));
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &infeasible.memory,
                        &infeasible.conditions
                    )
                    .is_err()
            );
            let callee = engine.instantiated_body(helper).unwrap();
            let mut wrong = callee.as_ref().clone();
            wrong.local_decls[Local::from_usize(1)].ty = tcx.types.bool;
            engine.bodies.borrow_mut().insert(helper, Rc::new(wrong));
            assert!(
                engine
                    .shared_drop_receiver_call(
                        (caller, &body, block),
                        helper,
                        &values,
                        &mut state.clone(),
                        &[]
                    )
                    .err()
                    .unwrap()
                    .contains("Body or signature")
            );
            engine.bodies.borrow_mut().insert(helper, callee);
            let mut wrong = body.as_ref().clone();
            wrong.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
            engine.bodies.borrow_mut().insert(caller, Rc::new(wrong));
            assert!(
                engine
                    .shared_drop_receiver_arguments(
                        helper,
                        &values,
                        &state.memory,
                        &state.conditions
                    )
                    .is_err()
            );
            engine.bodies.borrow_mut().insert(caller, body.clone());
            assert!(
                engine
                    .shared_drop_receiver_call(
                        (caller, &body, block),
                        helper,
                        &values,
                        &mut state,
                        &[]
                    )
                    .unwrap()
                    .is_some()
            );
            println!(
                "exact nominal/Context/masks/live owner/current caller/callee controls passed"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory =
        std::env::temp_dir().join(format!("miren-shared-drop-call-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/shared_drop_calls.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut check = Check(false);
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
