//! Actual compiler constructor certificate controls; no executable owner or receiver is issued.
use super::*;

#[test]
fn actual_fieldless_box_constructor_source_and_hostile_controls() {
    struct Check;
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
                limits: miren::AnalysisLimits {
                    max_steps: 2_000_000,
                    ..Default::default()
                },
            };
            for name in ["Marker", "Panicking", "Effectful", "HelperMarker"] {
                let id=tcx.mir_keys(()).iter().copied().find(|id|
                    tcx.def_kind(id.to_def_id())==DefKind::AssocFn
                    && tcx.item_name(id.to_def_id()).as_str()=="drop"
                    && matches!(tcx.fn_sig(id.to_def_id()).instantiate_identity().skip_binder()
                        .inputs()[0].kind(),ty::Ref(_,child,_) if matches!(child.kind(),
                            ty::Adt(def,_) if tcx.item_name(def.did()).as_str()==name))).unwrap();
                let receiver = tcx
                    .fn_sig(id.to_def_id())
                    .instantiate_identity()
                    .skip_binder()
                    .inputs()[0];
                let ty::Ref(_, payload, _) = receiver.kind() else {
                    unreachable!()
                };
                let mut engine = Engine::new(tcx, &config, options());
                let constructor = engine
                    .resolve_function_item(
                        tcx.get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
                            .unwrap(),
                        tcx.mk_args(&[(*payload).into()]),
                    )
                    .unwrap();
                let certificate = prepare(&mut engine, constructor).unwrap();
                println!(
                    "BOX_PREP name={name} target={} opt={:?} work={} parts={}",
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                    engine.steps.used(),
                    certificate.parts.len()
                );
                certificate.validate(&mut engine).unwrap();
                assert!(engine.proof.body_entries.is_empty());
                assert!(engine.proof.assumptions.is_empty());
                assert!(engine.owned_box_types.is_empty());
                assert_eq!(engine.next_owned_region, 0);
                let mut foreign = Engine::new(tcx, &config, options());
                assert!(
                    certificate
                        .validate(&mut foreign)
                        .unwrap_err()
                        .contains("Context")
                );
                for part in &certificate.parts {
                    let instance = part.raw.instance;
                    let original = part.current.clone();
                    let mut changed = original.as_ref().clone();
                    let mut added = changed
                        .basic_blocks
                        .iter()
                        .find_map(|block| block.statements.first())
                        .unwrap()
                        .clone();
                    added.kind = StatementKind::Nop;
                    changed.basic_blocks.as_mut()[START_BLOCK]
                        .statements
                        .push(added);
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(instance, Rc::new(changed));
                    assert!(certificate.validate(&mut engine).is_err());
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(instance, original.clone());
                    certificate.validate(&mut engine).unwrap();
                    assert!(
                        part.raw.check_instance(constructor).is_err() || instance == constructor
                    );
                }
                if name != "Marker" {
                    let root_name = match name {
                        "Panicking" => "panicking",
                        "Effectful" => "effectful",
                        "HelperMarker" => "helper_box",
                        _ => unreachable!(),
                    };
                    let root = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == root_name
                        })
                        .unwrap();
                    for maximum in [8192, 2_000_000] {
                        let mut application_options = options();
                        application_options.limits.max_steps = maximum;
                        let mut application = Engine::new(tcx, &config, application_options);
                        let caller = ty::Instance::mono(tcx, root.to_def_id());
                        let body = application.instantiated_body(caller).unwrap();
                        let block = body
                            .basic_blocks
                            .iter_enumerated()
                            .find_map(|(block, data)| {
                                let TerminatorKind::Call { func, .. } = &data.terminator().kind
                                else {
                                    return None;
                                };
                                let ty::FnDef(id, _) = func.ty(&body.local_decls, tcx).kind()
                                else {
                                    return None;
                                };
                                (Some(*id)
                                    == tcx
                                        .get_diagnostic_item(rustc_span::Symbol::intern("box_new")))
                                .then_some(block)
                            })
                            .expect("actual Runtime MIR Box::new call");
                        let ty::Adt(definition, _) = payload.kind() else {
                            unreachable!()
                        };
                        let value = Value::Adt {
                            name: tcx.def_path_str(definition.did()),
                            variant: 0,
                            is_option: false,
                            discriminant: 0,
                            fields: Vec::new().into(),
                        };
                        let mut state = State {
                            flow: activation_flow::Flow::Unarmed,
                            locals: vec![None; body.local_decls.len()],
                            addresses: vec![None; body.local_decls.len()],
                            constant_receipts: constant_reference_receipts::Slots::default(),
                            conditions: Vec::new(),
                            memory: Memory::from(vec![Some(Value::Unit)]),
                            missing_places: initialized_places::MissingPlaces::default(),
                        };
                        let memory_before = state.memory.clone();
                        let generation_before = application.next_owned_region;
                        let types_before = application.owned_box_types.len();
                        let error = application
                            .owned_box_call(&body, block, constructor, &[value], &mut state)
                            .unwrap_err();
                        println!(
                            "BOX_APPLICATION_REFUSAL name={name} budget={maximum} \
                            registered={} reason={error}",
                            application.owned_box_types.len()
                        );
                        let expected = if maximum == 8192 {
                            UnknownCategory::ResourceLimit
                        } else {
                            UnknownCategory::Semantics
                        };
                        assert_eq!(
                            application.unknown_causes.borrow().get(&error),
                            Some(&expected)
                        );
                        assert_eq!(application.owned_box_types.len(), types_before);
                        assert_eq!(application.next_owned_region, generation_before);
                        assert_eq!(state.memory.as_ptr(), memory_before.as_ptr());
                        assert_eq!(state.memory.len(), memory_before.len());
                        assert!(matches!(state.memory[0], Some(Value::Unit)));
                        assert!(Rc::ptr_eq(
                            &state.memory.owned_regions,
                            &memory_before.owned_regions
                        ));
                        assert!(Rc::ptr_eq(
                            &state.memory.mutable_u16,
                            &memory_before.mutable_u16
                        ));
                        assert!(Rc::ptr_eq(
                            &state.memory.initialized_owners,
                            &memory_before.initialized_owners
                        ));
                        assert!(state.memory.incoming_byte_roots.is_empty());
                        assert!(!state.memory.byte_copy_opaque);
                        assert_eq!(
                            state.memory.mutable_hierarchy,
                            memory_before.mutable_hierarchy
                        );
                        assert!(state.memory.missing_places.is_empty());
                        assert!(state.memory.startup_values.is_empty());
                        assert!(!state.memory.startup_invalidated);
                        assert!(state.memory.isolated_static_types.is_empty());
                        assert!(state.memory.startup_overwritten.is_empty());
                        assert!(state.memory.static_uninitialized.is_empty());
                        assert!(application.proof.body_entries.is_empty());
                        assert!(application.proof.assumptions.is_empty());
                        let work_before_invalid = application.steps.used();
                        assert_eq!(
                            application
                                .owned_box_call(&body, block, constructor, &[], &mut state,)
                                .unwrap_err(),
                            "nominal Box constructor requires its exact single payload"
                        );
                        assert_eq!(
                            application
                                .owned_box_call(
                                    &body,
                                    block,
                                    constructor,
                                    &[Value::Unit],
                                    &mut state,
                                )
                                .unwrap_err(),
                            "effect-free Box Drop payload differs from its original fieldless value"
                        );
                        assert_eq!(application.steps.used(), work_before_invalid);
                        assert_eq!(application.owned_box_types.len(), types_before);
                        assert_eq!(application.next_owned_region, generation_before);
                        assert_eq!(state.memory.as_ptr(), memory_before.as_ptr());
                        assert!(Rc::ptr_eq(
                            &state.memory.owned_regions,
                            &memory_before.owned_regions
                        ));
                    }
                }
                let original = engine.call_poly_signature(constructor).unwrap();
                for mutation in 0..5 {
                    let poisoned = match mutation {
                        0 => original.map_bound(|s| s.set_safety(rustc_hir::Safety::Unsafe)),
                        1 => original.map_bound(|s| ty::FnSig {
                            fn_sig_kind: s
                                .fn_sig_kind
                                .set_abi(rustc_abi::ExternAbi::C { unwind: false }),
                            ..s
                        }),
                        2 => ty::Binder::bind_with_vars(
                            original.skip_binder(),
                            tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Ty(
                                ty::BoundTyKind::Anon,
                            )]),
                        ),
                        3 | 4 => original.map_bound(|s| {
                            let mut types = s.inputs_and_output.to_vec();
                            let index = if mutation == 3 { 0 } else { types.len() - 1 };
                            types[index] = tcx.types.u8;
                            ty::FnSig {
                                inputs_and_output: tcx.mk_type_list(&types),
                                ..s
                            }
                        }),
                        _ => unreachable!(),
                    };
                    engine
                        .call_signatures
                        .borrow_mut()
                        .insert(constructor, poisoned);
                    assert!(
                        certificate
                            .validate(&mut engine)
                            .unwrap_err()
                            .contains("cached/original full signature differs")
                    );
                    engine
                        .call_signatures
                        .borrow_mut()
                        .insert(constructor, original);
                }
                let global = certificate
                    .parts
                    .iter()
                    .find(|part| part.raw.family == BoxTemplateFamily::GlobalAllocate)
                    .unwrap();
                // The dedicated Box cache cannot authorize the older flat-plan domain.
                let before = engine.steps.used();
                let before_entries = engine.array_iterator_step_evidence.len();
                let before_box_entries = engine.box_constructor_source_evidence.len();
                assert_eq!(before_entries, 0);
                assert_eq!(before_box_entries, certificate.parts.len());
                let error = array_iterator_constructors::original_iterator_item_source(
                    &mut engine,
                    global.raw.instance,
                )
                .unwrap_err();
                assert!(error.contains("512-node"), "{error}");
                assert_eq!(engine.array_iterator_step_evidence.len(), before_entries);
                assert_eq!(
                    engine.box_constructor_source_evidence.len(),
                    before_box_entries
                );
                let old_work = engine.steps.used() - before;
                let mut fresh_iterator = Engine::new(tcx, &config, options());
                let fresh_error = array_iterator_constructors::original_iterator_item_source(
                    &mut fresh_iterator,
                    global.raw.instance,
                )
                .unwrap_err();
                assert_eq!(fresh_error, error);
                assert_eq!(old_work, fresh_iterator.steps.used());
                println!(
                    "BOX_THEN_ITERATOR_REFUSAL paid={} reason={error}",
                    engine.steps.used() - before
                );
                certificate.validate(&mut engine).unwrap();
                // Conversely, a small original Iterator admission cannot skip Box admission.
                let mut reciprocal = Engine::new(tcx, &config, options());
                array_iterator_constructors::original_iterator_item_source(
                    &mut reciprocal,
                    constructor,
                )
                .unwrap();
                let before_entries = reciprocal.array_iterator_step_evidence.len();
                let before_box_entries = reciprocal.box_constructor_source_evidence.len();
                let constructor_part = certificate
                    .parts
                    .iter()
                    .find(|part| part.raw.instance == constructor)
                    .unwrap();
                array_iterator_constructors::authenticated_box_constructor_source(
                    &mut reciprocal,
                    constructor,
                    &constructor_part.raw,
                )
                .unwrap();
                assert_eq!(
                    reciprocal.array_iterator_step_evidence.len(),
                    before_entries
                );
                assert_eq!(
                    reciprocal.box_constructor_source_evidence.len(),
                    before_box_entries + 1
                );
                // Cached Box admission still authenticates full Instance and original Body.
                let before_refusal = reciprocal.steps.used();
                assert!(
                    array_iterator_constructors::authenticated_box_constructor_source(
                        &mut reciprocal,
                        global.raw.instance,
                        &constructor_part.raw,
                    )
                    .unwrap_err()
                    .contains("full Instance differs")
                );
                assert_eq!(reciprocal.steps.used() - before_refusal, 2);
                let wrong_raw = RawWitness {
                    instance: constructor,
                    raw: global.raw.raw,
                    family: constructor_part.raw.family,
                };
                assert!(
                    array_iterator_constructors::authenticated_box_constructor_source(
                        &mut reciprocal,
                        constructor,
                        &wrong_raw,
                    )
                    .unwrap_err()
                    .contains("original Body differs")
                );
                let before_entries = reciprocal.array_iterator_step_evidence.len();
                let before_box_entries = reciprocal.box_constructor_source_evidence.len();
                array_iterator_constructors::authenticated_box_constructor_source(
                    &mut reciprocal,
                    constructor,
                    &constructor_part.raw,
                )
                .unwrap();
                assert_eq!(
                    reciprocal.array_iterator_step_evidence.len(),
                    before_entries
                );
                assert_eq!(
                    reciprocal.box_constructor_source_evidence.len(),
                    before_box_entries
                );
                let mut clone_exhausted = Engine::new(
                    tcx,
                    &config,
                    VerificationOptions {
                        all_failures: false,
                        induction: false,
                        startup: false,
                        isolated_startup: false,
                        async_entry: false,
                        limits: miren::AnalysisLimits {
                            max_steps: 10,
                            ..Default::default()
                        },
                    },
                );
                assert!(
                    array_iterator_constructors::authenticated_box_constructor_source(
                        &mut clone_exhausted,
                        global.raw.instance,
                        &global.raw,
                    )
                    .err()
                    .unwrap()
                    .contains("shared execution step limit reached")
                );
                assert!(clone_exhausted.bodies.borrow().is_empty());
                assert!(clone_exhausted.steps.used() > clone_exhausted.limits.max_steps);
                let missing = tcx.lang_items().get(LangItem::PanicFmt).unwrap();
                assert!(!tcx.is_mir_available(missing));
                let mut unavailable = Engine::new(tcx, &config, options());
                let error = raw_witness(&mut unavailable, ty::Instance::mono(tcx, missing))
                    .err()
                    .unwrap();
                assert!(error.contains("MIR body unavailable"));
                assert!(unavailable.bodies.borrow().is_empty());
                let mut exhausted = Engine::new(
                    tcx,
                    &config,
                    VerificationOptions {
                        all_failures: false,
                        induction: false,
                        startup: false,
                        isolated_startup: false,
                        async_entry: false,
                        limits: miren::AnalysisLimits::default(),
                    },
                );
                let error = prepare(&mut exhausted, constructor).err().unwrap();
                assert!(
                    error.contains("Box constructor source shared execution step limit reached")
                );
                assert!(exhausted.bodies.borrow().is_empty());
                assert!(exhausted.owned_box_types.is_empty());
                assert_eq!(exhausted.next_owned_region, 0);
                assert!(exhausted.steps.used() > exhausted.limits.max_steps);
            }
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effect_free_zst_box_drop.rs");
    let directory = std::env::temp_dir().join(format!(
        "miren-box-constructor-source-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in ["0", "2"] {
            let mut args = vec![
                "rustc".into(),
                fixture.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={opt}"),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout.clone())
                    .unwrap()
                    .trim()
                    .into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Check);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
