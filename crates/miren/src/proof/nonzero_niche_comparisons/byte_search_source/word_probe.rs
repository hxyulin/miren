//! Explicit retained-core compiler evidence. No application search result is promoted.
use super::*;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

#[test]
fn actual_retained_word_body_equivalence_and_conservative_search() {
    compiler_controls(ProbePhase::Word);
}

#[test]
fn actual_core_projection_inventory_and_conservative_runtime_frontier() {
    compiler_controls(ProbePhase::Runtime);
}

#[test]
fn actual_retained_population_wrapper_semantics_and_conservative_search() {
    compiler_controls(ProbePhase::Population);
}

#[test]
fn actual_retained_allocation_size_source_and_size_one_fact() {
    compiler_controls(ProbePhase::AllocationSize);
}

#[test]
fn actual_cold_membership_production_frontier() {
    compiler_controls(ProbePhase::ColdPipeline);
}

#[test]
fn actual_retained_shared_copy_route_source_controls() {
    compiler_controls(ProbePhase::RouteCopy);
}

#[test]
fn actual_retained_typed_byte_transport_source_and_hostile_dataflow() {
    compiler_controls(ProbePhase::TypedRoute);
}

#[test]
fn actual_byte_compiler_layout_and_consumed_missing_source_controls() {
    compiler_controls(ProbePhase::Preconditions);
}

#[test]
fn actual_typed_naive_aligned_range_sources_and_hostile_dataflow() {
    compiler_controls(ProbePhase::Range);
}

#[derive(Clone, Copy)]
enum ProbePhase {
    Word,
    Runtime,
    Population,
    AllocationSize,
    ColdPipeline,
    RouteCopy,
    TypedRoute,
    Preconditions,
    Range,
}

fn compiler_controls(phase: ProbePhase) {
    struct Check {
        retained: bool,
        phase: ProbePhase,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = super::super::super::super::super::nonzero_niches::test_engine(tcx);
            if matches!(self.phase, ProbePhase::Population) {
                let actual_core_call = |name: &str| {
                    let id = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(*id) == DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap();
                    let body = engine
                        .instantiated_body(ty::Instance::mono(tcx, id.to_def_id()))
                        .unwrap();
                    body.basic_blocks
                        .iter()
                        .find_map(|block| {
                            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                                return None;
                            };
                            let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                                return None;
                            };
                            Some(
                                engine
                                    .resolve_function_item(*id, args.skip_binder())
                                    .unwrap(),
                            )
                        })
                        .expect("actual word helper Call disappeared")
                };
                population::compiler_controls(
                    &engine,
                    actual_core_call("population_word"),
                    actual_core_call("trailing_word"),
                    self.retained,
                );
                eprintln!("POPULATION CALLBACK COMPLETE");
                return rustc_driver::Compilation::Stop;
            }
            let root = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "source_unknown"
                })
                .unwrap();
            let root = ty::Instance::mono(tcx, root.to_def_id());
            if matches!(self.phase, ProbePhase::Range) {
                if self.retained {
                    super::super::range::probe::compiler_controls(&engine, root);
                    eprintln!("BYTE RANGE CALLBACK COMPLETE");
                } else {
                    eprintln!("BYTE RANGE default-core remains unavailable; no retained credit");
                }
                return rustc_driver::Compilation::Stop;
            }
            if matches!(self.phase, ProbePhase::Preconditions) {
                if self.retained {
                    super::super::super::byte_transport_probe::compiler_precondition_controls(
                        &engine, root,
                    );
                    eprintln!("BYTE PRECONDITIONS CALLBACK COMPLETE");
                } else {
                    eprintln!(
                        "BYTE PRECONDITIONS default-core remains unavailable; no retained credit"
                    );
                }
                return rustc_driver::Compilation::Stop;
            }
            if matches!(self.phase, ProbePhase::TypedRoute) {
                if self.retained {
                    super::super::super::byte_transport_probe::compiler_controls(&engine, root);
                    eprintln!("TYPED BYTE CALLBACK COMPLETE");
                } else {
                    eprintln!("TYPED BYTE default-core controls provide no retained source credit");
                }
                return rustc_driver::Compilation::Stop;
            }
            if matches!(self.phase, ProbePhase::RouteCopy) {
                if self.retained {
                    super::super::super::byte_route_probe::compiler_controls(&engine, root);
                    eprintln!("BYTE COPY CALLBACK COMPLETE");
                } else {
                    eprintln!("BYTE COPY default-core controls are not retained-source evidence");
                }
                return rustc_driver::Compilation::Stop;
            }
            if matches!(self.phase, ProbePhase::ColdPipeline) {
                // verify issues inputs/references and executes actual Rust statements itself.
                // Its fresh Engine/cache/work is independent of the locating diagnostic Engine.
                let proof = crate::proof::verify(
                    tcx,
                    root.def_id(),
                    &miren::ContractConfig::default(),
                    crate::proof::VerificationOptions {
                        all_failures: false,
                        induction: false,
                        startup: false,
                        isolated_startup: false,
                        async_entry: false,
                        limits: miren::AnalysisLimits::default(),
                    },
                );
                eprintln!(
                    "COLD PRODUCTION PROOF START\n{}\nPROOF END",
                    serde_json::to_string_pretty(&proof).unwrap()
                );
                eprintln!("COLD PRODUCTION CALLBACK COMPLETE");
                return rustc_driver::Compilation::Stop;
            }
            let mut pending = vec![root];
            let mut seen = Vec::new();
            let mut selected = None;
            let mut missing = None;
            while let Some(instance) = pending.pop() {
                if seen.contains(&instance) {
                    continue;
                }
                assert!(seen.len() < 16);
                seen.push(instance);
                if !tcx.is_mir_available(instance.def_id()) {
                    missing = Some(instance);
                    continue;
                }
                let body = engine.instantiated_body(instance).unwrap();
                for block in body.basic_blocks.iter() {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        continue;
                    };
                    let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                        continue;
                    };
                    let next = engine
                        .resolve_function_item(*id, args.skip_binder())
                        .unwrap();
                    let path = tcx.def_path_str(next.def_id());
                    if path.ends_with("::contains_zero_byte") {
                        selected = Some(next);
                    } else if path.ends_with("::contains")
                        || path.ends_with("::slice_contains")
                        || path.ends_with("::memchr")
                        || path.ends_with("::memchr_aligned")
                        || path.ends_with("::memchr_aligned::runtime")
                    {
                        pending.push(next);
                    }
                }
            }
            if matches!(self.phase, ProbePhase::AllocationSize) && self.retained {
                let runtime = seen
                    .iter()
                    .copied()
                    .find(|instance| {
                        tcx.def_path_str(instance.def_id())
                            .ends_with("::memchr_aligned::runtime")
                    })
                    .expect("actual retained memchr runtime missing");
                let actual_call = |instance, name: &str| {
                    let body = engine.instantiated_body(instance).unwrap();
                    body.basic_blocks
                        .iter()
                        .find_map(|block| {
                            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                                return None;
                            };
                            let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                                return None;
                            };
                            (tcx.item_name(*id).as_str() == name).then(|| {
                                engine
                                    .resolve_function_item(*id, args.skip_binder())
                                    .unwrap()
                            })
                        })
                        .unwrap_or_else(|| panic!("actual retained {name} call missing"))
                };
                let raw_parts = actual_call(runtime, "from_raw_parts");
                let precondition = actual_call(raw_parts, "precondition_check");
                let size = actual_call(precondition, "is_valid_allocation_size");
                let fresh = super::super::super::super::super::nonzero_niches::test_engine(tcx);
                allocation_size::compiler_controls(&fresh, size);
                eprintln!("ALLOCATION SIZE CALLBACK COMPLETE");
                return rustc_driver::Compilation::Stop;
            }
            if matches!(self.phase, ProbePhase::Runtime) && self.retained {
                for instance in seen.iter().copied().filter(|instance| {
                    tcx.def_path_str(instance.def_id())
                        .ends_with("::memchr_aligned::runtime")
                }) {
                    let fresh = super::super::super::super::super::nonzero_niches::test_engine(tcx);
                    eprintln!(
                        "SEARCH RAW RUNTIME {instance:?}\n{:#?}",
                        tcx.instance_mir(instance.def)
                    );
                    let current = engine.instantiated_body(instance).unwrap();
                    let index = current
                        .basic_blocks
                        .iter()
                        .find_map(|block| {
                            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                                return None;
                            };
                            let ty::FnDef(id, args) = func.ty(&current.local_decls, tcx).kind()
                            else {
                                return None;
                            };
                            if tcx.item_name(*id).as_str() != "index" {
                                return None;
                            }
                            Some(
                                engine
                                    .resolve_function_item(*id, args.skip_binder())
                                    .unwrap(),
                            )
                        })
                        .expect("actual runtime Index Call missing");
                    raw_projection_control(&engine, index);
                    match observe_inner(&fresh, instance, 0, 0) {
                        Ok(source) => {
                            eprintln!(
                                "SEARCH CURRENT RUNTIME\n{:#?}",
                                source.bodies.get(&instance).unwrap()
                            );
                            eprintln!("SEARCH OBSERVATION AVAILABLE used={}", source.work.used);
                            let selected_hint = source
                                .helpers
                                .iter()
                                .find(|helper| {
                                    tcx.def_path_str(helper.selected.def_id())
                                        .ends_with("::from_raw_parts")
                                })
                                .expect("actual raw slice helper was not selected")
                                .selected;
                            constant_hint_control(&engine, selected_hint);
                            metadata_projection_control(&engine, selected_hint);
                            for helper in &source.helpers {
                                eprintln!(
                                    "SEARCH HELPER {:?} available={}",
                                    helper.selected,
                                    helper.body_available()
                                );
                            }
                        }
                        Err(failure) => eprintln!(
                            "SEARCH OBSERVATION REFUSED {:?}: {}",
                            failure.category, failure.reason
                        ),
                    }
                }
                eprintln!("SEARCH PROJECTION CALLBACK COMPLETE");
                return rustc_driver::Compilation::Stop;
            }
            if !self.retained {
                assert!(selected.is_none());
                let error = observe(&engine, missing.unwrap(), 0, 0).err().unwrap();
                assert_eq!(
                    engine.unknown_causes.borrow().get(&error),
                    Some(&UnknownCategory::MissingCompilerEvidence)
                );
                eprintln!("WORD default-core-missing-source-unknown");
                return rustc_driver::Compilation::Stop;
            }
            let selected = selected.expect("actual retained search had no word helper Call");
            let observation = observe_inner(&engine, selected, 0, 0).unwrap();
            let certificate = certify(observation).unwrap_or_else(|failure| {
                panic!(
                    "actual word certificate failed: {:?}: {}",
                    failure.category, failure.reason
                )
            });
            eprintln!(
                "WORD ACTUAL ROOT {selected:?}\n{:#?}",
                certificate.source.bodies.get(&selected).unwrap()
            );
            eprintln!("WORD ACTUAL ARITHMETIC\n{:#?}", certificate.arithmetic);
            eprintln!("WORD ACTUAL QUERY\n{}", certificate.query.text());
            assert!(engine.bodies.try_borrow_mut().is_err());
            assert!(engine.call_signatures.try_borrow_mut().is_err());
            eprintln!("WORD authenticated-equivalence-unsat-with-live-source-guards");
            let helper = certificate.source.helpers[0].selected;
            drop(certificate);
            let original = engine.instantiated_body(helper).unwrap();
            let mut wrong = original.as_ref().clone();
            let StatementKind::Assign(value) =
                &mut wrong.basic_blocks.as_mut()[START_BLOCK].statements[0].kind
            else {
                panic!("actual helper assignment disappeared")
            };
            let Rvalue::BinaryOp(operation, _) = &mut value.1 else {
                panic!("actual helper binary operation disappeared")
            };
            *operation = rustc_middle::mir::BinOp::Add;
            engine.bodies.borrow_mut().insert(helper, Rc::new(wrong));
            let error = certify(observe_inner(&engine, selected, 0, 0).unwrap())
                .err()
                .unwrap();
            assert_eq!(
                error.reason,
                "byte source current statement differs from original compiler statement"
            );
            assert_eq!(error.category, UnknownCategory::Semantics);
            engine.bodies.borrow_mut().insert(helper, original);
            eprintln!("WORD actual-arithmetic-add-mutation-refused");
            let original = engine.instantiated_body(selected).unwrap();
            let mut wrong = original.as_ref().clone();
            wrong.local_decls[Local::from_usize(1)].ty =
                if tcx.data_layout.pointer_size().bits() == 64 {
                    tcx.types.u64
                } else {
                    tcx.types.u32
                };
            engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
            let error = observe(&engine, selected, 0, 0).err().unwrap();
            assert_eq!(
                error,
                "byte source current local differs from original compiler local"
            );
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::Semantics)
            );
            engine
                .bodies
                .borrow_mut()
                .insert(selected, original.clone());
            eprintln!("WORD same-width-fixed-integer-current-source-refused");
            let mut wrong = original.as_ref().clone();
            let tail =
                &mut wrong.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(1)];
            let StatementKind::Assign(last) = &tail.statements[3].kind else {
                panic!("actual result assignment disappeared")
            };
            let Rvalue::BinaryOp(_, values) = &last.1 else {
                panic!("actual result operation disappeared")
            };
            let zero = values.1.clone();
            let StatementKind::Assign(mask) = &mut tail.statements[2].kind else {
                panic!("actual mask assignment disappeared")
            };
            let Rvalue::BinaryOp(_, values) = &mut mask.1 else {
                panic!("actual mask operation disappeared")
            };
            values.1 = zero;
            engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
            let error = observe(&engine, selected, 0, 0).err().unwrap();
            assert_eq!(
                error,
                "byte source current statement differs from original compiler statement"
            );
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::Semantics)
            );
            engine.bodies.borrow_mut().insert(selected, original);
            eprintln!("WORD actual-high-mask-zero-mutation-refused");
            let error = observe(&engine, selected, 0, 0)
                .unwrap()
                .reject_unverified_search()
                .unwrap_err();
            assert_eq!(
                error,
                "authenticated word fact does not establish complete byte search"
            );
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::Semantics)
            );
            eprintln!("WORD restored-word-fact-full-search-still-unknown");
            rustc_driver::Compilation::Stop
        }
    }
    // Optional explicit retained configuration; ordinary full-suite runs preserve missing-body U.
    let packet = std::env::var_os("MIREN_BYTE_WORD_CORE_ARTIFACTS").map(|path| {
        serde_json::from_slice::<serde_json::Value>(&std::fs::read(path).unwrap()).unwrap()
    });
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/byte_search_source.rs");
    let directory = std::env::temp_dir().join(format!(
        "miren-word-source-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&directory).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut arguments = vec![
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
                arguments.extend(["--target".into(), target.into()]);
            }
            if let Some(packet) = &packet {
                let target_name = target.unwrap_or("aarch64-apple-darwin");
                for (name, prefix) in [
                    ("core", "libcore-"),
                    ("compiler_builtins", "libcompiler_builtins-"),
                ] {
                    let file = packet
                        .as_object()
                        .unwrap()
                        .keys()
                        .find(|path| {
                            path.contains(&format!("/{target_name}/"))
                                && Path::new(path)
                                    .file_name()
                                    .unwrap()
                                    .to_str()
                                    .unwrap()
                                    .starts_with(prefix)
                                && path.ends_with(".rmeta")
                        })
                        .unwrap();
                    arguments.extend([
                        "--extern".into(),
                        format!("noprelude,nounused:{name}={file}"),
                        "-L".into(),
                        format!("dependency={}", Path::new(file).parent().unwrap().display()),
                    ]);
                }
                arguments.push("-Zunstable-options".into());
            }
            eprintln!(
                "WORD PROFILE {target:?} O{level} RETAINED {} ARGS {arguments:?}",
                packet.is_some()
            );
            rustc_driver::run_compiler(
                &arguments,
                &mut Check {
                    retained: packet.is_some(),
                    phase,
                },
            );
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
