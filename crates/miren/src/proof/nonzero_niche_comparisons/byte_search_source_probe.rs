//! Compiler source authority controls, never proof of memchr semantics.
use super::*;
use std::path::Path;
use std::rc::Rc;

#[test]
fn actual_byte_source_original_current_and_conservative_boundaries() {
    struct Check;
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = super::super::super::nonzero_niches::test_engine(tcx);
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "word"
                })
                .unwrap();
            let root = engine
                .instantiated_body(ty::Instance::mono(tcx, id.to_def_id()))
                .unwrap();
            let selected = root
                .basic_blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, arguments) = func.ty(&root.local_decls, tcx).kind() else {
                        return None;
                    };
                    Some(
                        engine
                            .resolve_function_item(*id, arguments.skip_binder())
                            .unwrap(),
                    )
                })
                .unwrap();
            let observation =
                byte_search_source::observe(&engine, selected, 0, 0).unwrap_or_else(|error| {
                    panic!("actual available core source observation failed: {error}")
                });
            assert_eq!(
                observation.reject_unverified_search().unwrap_err(),
                "niche byte-sized transport needs a separate available-body certificate"
            );
            eprintln!("SOURCE available-original-current-but-unverified");
            let original = engine.instantiated_body(selected).unwrap();
            let mut wrong = original.as_ref().clone();
            wrong.local_decls[Local::from_usize(0)].ty = tcx.types.bool;
            engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
            assert_eq!(
                byte_search_source::observe(&engine, selected, 0, 0)
                    .err()
                    .unwrap(),
                "byte source current local differs from original compiler local"
            );
            engine
                .bodies
                .borrow_mut()
                .insert(selected, original.clone());
            eprintln!("SOURCE altered-current-type-refused");
            let mut wrong = original.as_ref().clone();
            let statement = wrong.basic_blocks[START_BLOCK]
                .statements
                .iter()
                .position(|statement| matches!(statement.kind, StatementKind::Assign(_)))
                .unwrap();
            wrong.basic_blocks.as_mut()[START_BLOCK].statements[statement].kind =
                StatementKind::Nop;
            engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
            assert_eq!(
                byte_search_source::observe(&engine, selected, 0, 0)
                    .err()
                    .unwrap(),
                "byte source current statement differs from original compiler statement"
            );
            engine.bodies.borrow_mut().insert(selected, original);
            eprintln!("SOURCE altered-current-statement-refused");
            let original = engine.instantiated_body(selected).unwrap();
            let mut wrong = original.as_ref().clone();
            wrong.basic_blocks.as_mut()[START_BLOCK]
                .terminator_mut()
                .attributes
                .push(rustc_hir::attrs::AttributeKind::Cold);
            engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
            assert_eq!(
                byte_search_source::observe(&engine, selected, 0, 0)
                    .err()
                    .unwrap(),
                "byte source terminator attributes require separate clone planning"
            );
            engine.bodies.borrow_mut().insert(selected, original);
            eprintln!("SOURCE altered-current-terminator-attribute-refused");
            assert_eq!(
                byte_search_source::observe(&engine, selected, 16, 0)
                    .err()
                    .unwrap(),
                "byte source helper edge exceeds depth16"
            );
            eprintln!("SOURCE repeated-instance-depth-refused");
            let borrowed = engine.bodies.borrow_mut();
            assert_eq!(
                byte_search_source::observe(&engine, selected, 0, 0)
                    .err()
                    .unwrap(),
                "byte source Body registry is borrowed"
            );
            drop(borrowed);
            eprintln!("SOURCE competing-body-borrow-refused");
            byte_search_source::observe(&engine, selected, 0, 0)
                .unwrap_or_else(|error| panic!("restored actual source failed: {error}"))
                .reject_unverified_search()
                .unwrap_err();
            eprintln!("SOURCE restored-current-source-unverified");
            let local = ty::Instance::mono(tcx, id.to_def_id());
            assert_eq!(
                byte_search_source::observe(&engine, local, 0, 0)
                    .err()
                    .unwrap(),
                "byte source original core/full Instance identity differs"
            );
            eprintln!("SOURCE non-core-available-source-conservative");
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "source_unknown"
                })
                .unwrap();
            let root = ty::Instance::mono(tcx, id.to_def_id());
            let mut pending = vec![root];
            let mut seen = Vec::new();
            let mut missing = None;
            while let Some(instance) = pending.pop() {
                if seen.contains(&instance) {
                    continue;
                }
                assert!(seen.len() < 16);
                seen.push(instance);
                let body = engine.instantiated_body(instance).unwrap();
                for block in body.basic_blocks.iter() {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        continue;
                    };
                    let ty::FnDef(id, arguments) = func.ty(&body.local_decls, tcx).kind() else {
                        continue;
                    };
                    let next = engine
                        .resolve_function_item(*id, arguments.skip_binder())
                        .unwrap();
                    let name = tcx.def_path_str(next.def_id());
                    // Names locate actual selected MIR edges here; they grant no semantic rule.
                    if name.ends_with("::memchr_aligned") {
                        assert!(!tcx.is_mir_available(next.def_id()));
                        missing = Some(next);
                    } else if name.ends_with("::contains")
                        || name.ends_with("::slice_contains")
                        || name.ends_with("::memchr")
                    {
                        pending.push(next);
                    }
                }
            }
            let missing = missing.expect("actual default-core aligned search edge was not located");
            let error = byte_search_source::observe(&engine, missing, 0, 0)
                .err()
                .unwrap();
            assert!(error.starts_with("MIR body unavailable for "));
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::MissingCompilerEvidence)
            );
            eprintln!("SOURCE actual-missing-default-core-body-unknown");
            let duplicate = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "duplicate_words"
                })
                .unwrap();
            let duplicate = engine
                .instantiated_body(ty::Instance::mono(tcx, duplicate.to_def_id()))
                .unwrap();
            byte_search_source::duplicate_occurrence_control(&engine, &duplicate);
            rustc_driver::Compilation::Stop
        }
    }
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/byte_search_source.rs");
    let directory = std::env::temp_dir().join(format!("miren-byte-source-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                source.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
                "--out-dir".into(),
                directory.display().to_string(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            eprintln!("SOURCE PROFILE {target:?} O{level}");
            rustc_driver::run_compiler(&args, &mut Check);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
