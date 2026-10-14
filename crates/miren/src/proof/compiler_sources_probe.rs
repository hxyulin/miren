//! Original compiler clone inventories; these rows are not proofs or source-admission receipts.
use super::*;

#[test]
fn actual_root_compiler_source_clone_inventory() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut count = 0;
            for id in tcx.hir_body_owners() {
                let id = id.to_def_id();
                if tcx.def_kind(id) != DefKind::Fn {
                    continue;
                }
                let path = tcx.def_path_str(id);
                if !["option_u8::", "empty_u8::", "payload_u8::"]
                    .iter()
                    .any(|family| path.contains(family))
                    || ![
                        "copy_fields",
                        "whole_product",
                        "replace",
                        "outer_preservation",
                        "via_helper",
                        "wrong_sibling",
                        "partial_payload",
                        "bare_owner",
                    ]
                    .contains(&tcx.item_name(id).as_str())
                {
                    continue;
                }
                let instance = ty::Instance::mono(tcx, id);
                let raw = tcx.instance_mir(instance.def);
                let mut old = super::super::nonzero_niches::test_engine(tcx);
                old.limits.max_steps = 2_000_000;
                let (legacy, legacy_nodes) =
                    array_iterator_constructors::compiler_clone_inventory(&mut old, raw, false);
                let mut general = super::super::nonzero_niches::test_engine(tcx);
                general.limits.max_steps = 2_000_000;
                let (actual, actual_nodes) =
                    array_iterator_constructors::compiler_clone_inventory(&mut general, raw, true);
                let owned = actual.expect("bounded actual original compiler graph inventory");
                if actual_nodes > 512 {
                    assert_eq!(legacy_nodes, 513);
                    assert!(legacy.unwrap_err().contains("512-node limit"));
                } else {
                    assert_eq!(legacy.unwrap(), owned);
                }
                eprintln!(
                    concat!(
                        "RUST_SOURCE_INVENTORY path={} target={} opt={:?} ",
                        "raw_nodes={} legacy_nodes={} owned={} blocks={} locals={} statements={}"
                    ),
                    path,
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                    actual_nodes,
                    legacy_nodes,
                    owned,
                    raw.basic_blocks.len(),
                    raw.local_decls.len(),
                    raw.basic_blocks
                        .iter()
                        .map(|block| block.statements.len())
                        .sum::<usize>()
                );
                count += 1;
            }
            assert_eq!(count, 24);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_niche_owners.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-general-source-inventory".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}

#[test]
fn actual_authenticated_general_source_guards() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let id = tcx
                .hir_body_owners()
                .map(|id| id.to_def_id())
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.def_path_str(*id).ends_with("option_u8::copy_fields")
                })
                .unwrap();
            let instance = ty::Instance::mono(tcx, id);
            for mode in 0..8 {
                let mut engine = super::super::nonzero_niches::test_engine(tcx);
                engine.limits.max_steps = 2_000_000;
                if mode == 0 {
                    let current = authenticated_item(&mut engine, instance).unwrap();
                    assert_eq!(engine.compiler_sources.len(), 1);
                    assert!(Rc::ptr_eq(
                        &current,
                        &authenticated_item(&mut engine, instance).unwrap()
                    ));
                } else {
                    match mode {
                        1 | 2 => {
                            let current = engine.instantiated_body(instance).unwrap();
                            let mut altered = (*current).clone();
                            if mode == 1 {
                                altered.local_decls.raw.clear();
                            } else {
                                let mut found = false;
                                for block in altered.basic_blocks.as_mut() {
                                    for statement in &mut block.statements {
                                        if let StatementKind::Assign(assignment) =
                                            &mut statement.kind
                                            && let Rvalue::Use(_, retag) = &mut assignment.1
                                        {
                                            *retag = match retag {
                                                rustc_middle::mir::WithRetag::Yes => {
                                                    rustc_middle::mir::WithRetag::No
                                                }
                                                rustc_middle::mir::WithRetag::No => {
                                                    rustc_middle::mir::WithRetag::Yes
                                                }
                                            };
                                            found = true;
                                            break;
                                        }
                                    }
                                    if found {
                                        break;
                                    }
                                }
                                assert!(found);
                            }
                            engine
                                .bodies
                                .borrow_mut()
                                .insert(instance, Rc::new(altered));
                        }
                        3 => engine.limits.max_steps = 0,
                        4 => {
                            let mut catalogue = engine.call_signatures.borrow_mut();
                            for other in tcx.hir_body_owners().map(|id| id.to_def_id()) {
                                if other == id || tcx.def_kind(other) != DefKind::Fn {
                                    continue;
                                }
                                catalogue.insert(
                                    ty::Instance::mono(tcx, other),
                                    tcx.try_normalize_erasing_regions(
                                        ty::TypingEnv::fully_monomorphized(),
                                        tcx.fn_sig(other).instantiate_identity(),
                                    )
                                    .unwrap(),
                                );
                                if catalogue.len() == 256 {
                                    break;
                                }
                            }
                            assert_eq!(catalogue.len(), 256);
                            drop(catalogue);
                            authenticated_item(&mut engine, instance).unwrap();
                            assert_eq!(engine.call_signatures.borrow().len(), 256);
                            assert!(!engine.call_signatures.borrow().contains_key(&instance));
                            eprintln!(
                                "RUST_SOURCE_CONTROL mode={mode} target={} opt={:?}",
                                tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                            );
                            continue;
                        }
                        5 => {
                            engine
                                .call_signatures
                                .borrow_mut()
                                .insert(instance, ty::Binder::dummy(ty::FnSig::dummy()));
                        }
                        6 | 7 => {
                            authenticated_item(&mut engine, instance).unwrap();
                            if mode == 6 {
                                let current =
                                    engine.bodies.borrow().get(&instance).unwrap().clone();
                                engine
                                    .bodies
                                    .borrow_mut()
                                    .insert(instance, Rc::new((*current).clone()));
                            } else {
                                engine.compiler_sources[0].context =
                                    Context::default().boolean(true);
                            }
                        }
                        _ => unreachable!(),
                    }
                    let before_bodies = engine.bodies.borrow().clone();
                    let before_records = engine.compiler_sources.len();
                    assert!(
                        authenticated_item(&mut engine, instance).is_err(),
                        "mode={mode}"
                    );
                    assert_eq!(before_records, engine.compiler_sources.len());
                    let after = engine.bodies.borrow();
                    assert_eq!(before_bodies.len(), after.len());
                    for (instance, body) in &before_bodies {
                        assert!(
                            after
                                .get(instance)
                                .is_some_and(|current| Rc::ptr_eq(body, current))
                        );
                    }
                }
                eprintln!(
                    "RUST_SOURCE_CONTROL mode={mode} target={} opt={:?}",
                    tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                );
            }
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_niche_owners.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-general-source-controls".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}

#[test]
fn actual_general_source_coroutine_local_refusal_before_publication() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut count = 0;
            for id in tcx.hir_body_owners().map(|id| id.to_def_id()).filter(|id| {
                tcx.def_kind(*id) == DefKind::Fn
                    && tcx
                        .item_name(*id)
                        .as_str()
                        .starts_with("ordinary_source_with_")
            }) {
                let mut engine = super::super::nonzero_niches::test_engine(tcx);
                engine.limits.max_steps = 2_000_000;
                let error =
                    authenticated_item(&mut engine, ty::Instance::mono(tcx, id)).unwrap_err();
                assert!(error.contains("coroutine-containing locals"));
                assert!(engine.bodies.borrow().is_empty());
                assert!(engine.compiler_sources.is_empty());
                assert!(engine.coroutine_places.borrow().is_empty());
                eprintln!(
                    "RUST_SOURCE_COROUTINE_LOCAL_REFUSAL name={} target={} opt={:?}",
                    tcx.item_name(id),
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize
                );
                count += 1;
            }
            assert_eq!(count, 2);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/compiler_source_future.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-source-coro-local".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}
