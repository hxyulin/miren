use super::*;

#[test]
fn compiler_shared_trait_choices_preserve_sources_and_actual_return_memory() {
    struct Capture {
        output: std::path::PathBuf,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check_actual_roots(tcx, &self.output);
            check_constructor_behavior(tcx, &self.output);
            check_source_receipts(tcx);
            check_actual_return_faults(tcx);
            rustc_driver::Compilation::Stop
        }
    }
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "miren-shared-trait-choice-{}-{stamp}",
        std::process::id(),
    ));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("fixture.rs");
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/trait_object_choices.rs");
    std::fs::copy(fixture, &source).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut capture = Capture {
                output: output.clone(),
            };
            rustc_driver::run_compiler(&args, &mut capture);
            std::fs::write(
                output.join("controls.txt"),
                "actual roots; live-source swap; mask context; extent; dead backing; escape; \
                 mutable reborrow; original target/Body ReturnTy; work refusal\n",
            )
            .unwrap();
        }
    }
    eprintln!("Shared trait choice compiler assets: {}", root.display());
}

fn find<'tcx>(tcx: TyCtxt<'tcx>, name: &str, kind: DefKind) -> DefId {
    tcx.mir_keys(())
        .iter()
        .copied()
        .find(|id| {
            tcx.def_kind(id.to_def_id()) == kind && tcx.item_name(id.to_def_id()).as_str() == name
        })
        .unwrap()
        .to_def_id()
}

fn check_constructor_behavior(tcx: TyCtxt<'_>, output: &std::path::Path) {
    let config = miren::ContractConfig::default();
    let id = find(tcx, "constant", DefKind::Fn);
    let low_limit = super::super::verify(
        tcx,
        id,
        &config,
        VerificationOptions {
            all_failures: false,
            induction: false,
            startup: false,
            isolated_startup: false,
            async_entry: false,
            limits: miren::AnalysisLimits {
                max_steps: 1,
                ..miren::AnalysisLimits::default()
            },
        },
    );
    std::fs::write(
        output.join("constructor-low-step-limit-proof.json"),
        serde_json::to_vec_pretty(&low_limit).unwrap(),
    )
    .unwrap();
    assert_eq!(low_limit.status, ProofStatus::Unknown);
    assert!(low_limit.obligations.iter().any(|obligation| {
        obligation.status == ProofStatus::Unknown
            && obligation.unknown_category == Some(UnknownCategory::ResourceLimit)
    }));
    let invalid_mode = super::super::verify(
        tcx,
        id,
        &config,
        VerificationOptions {
            all_failures: false,
            induction: false,
            startup: true,
            isolated_startup: true,
            async_entry: true,
            limits: miren::AnalysisLimits::default(),
        },
    );
    std::fs::write(
        output.join("constructor-invalid-startup-async-proof.json"),
        serde_json::to_vec_pretty(&invalid_mode).unwrap(),
    )
    .unwrap();
    assert_eq!(invalid_mode.status, ProofStatus::Unknown);
    assert!(invalid_mode.entry_assumptions.is_empty());
    assert!(invalid_mode.obligations.iter().any(|obligation| {
        obligation.status == ProofStatus::Unknown
            && obligation.detail.starts_with(
                "async entries cannot inherit executor startup history or use induction",
            )
    }));
    let first = test_engine(tcx);
    let second = test_engine(tcx);
    let first_term = first.fresh(Sort::BitVec(8));
    let second_term = second.fresh(Sort::BitVec(8));
    assert!(
        second
            .terms
            .apply(Op::Equal, &[first_term, second_term])
            .is_err()
    );
    std::fs::write(
        output.join("constructor-behavior-controls.txt"),
        "actual max_steps1 refusal; invalid startup+async refusal without premises; \
         separate Engine contexts reject foreign terms
",
    )
    .unwrap();
}

fn check_actual_roots(tcx: TyCtxt<'_>, output: &std::path::Path) {
    for (name, expected) in [
        ("constant", ProofStatus::Proved),
        ("symbolic", ProofStatus::Proved),
        ("wrong", ProofStatus::Refuted),
        ("slice_helper", ProofStatus::Proved),
        ("inherited", ProofStatus::Proved),
        ("upcast", ProofStatus::Proved),
        ("caller_backed_return", ProofStatus::Proved),
        ("captured_index", ProofStatus::Proved),
        ("repeated", ProofStatus::Proved),
        ("returned_memory", ProofStatus::Proved),
        ("opaque", ProofStatus::Unknown),
    ] {
        let id = find(tcx, name, DefKind::Fn);
        let proof = super::super::verify(
            tcx,
            id,
            &miren::ContractConfig::default(),
            VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            },
        );
        // Preserve the entire emitted Proof, including UNKNOWN partials, before assertions.
        std::fs::write(
            output.join(format!("{name}-proof.json")),
            serde_json::to_vec_pretty(&proof).unwrap(),
        )
        .unwrap();
        assert_eq!(proof.status, expected, "{name}: {:?}", proof.obligations);
        assert!(
            proof.assumptions.is_empty()
                && proof.entry_assumptions.is_empty()
                && proof.trusted_calls.is_empty()
        );
        if name == "symbolic" {
            for method in ["<Masked as Parent>::read", "<Different as Parent>::read"] {
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == method)
                );
            }
        }
        if expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
}

fn sample(tcx: TyCtxt<'_>) -> (Engine<'_>, State, Vec<Value>, Ty<'_>) {
    let mut engine = test_engine(tcx);
    let root = find(tcx, "constant", DefKind::Fn);
    let object = tcx
        .optimized_mir(root)
        .local_decls
        .iter()
        .find_map(|local| {
            if let ty::Ref(_, object, mutability) = local.ty.kind()
                && !mutability.is_mut()
                && matches!(object.kind(), ty::Dynamic(..))
            {
                Some(tcx.erase_and_anonymize_regions(*object))
            } else {
                None
            }
        })
        .unwrap();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: Vec::new(),
        addresses: Vec::new(),
        conditions: Vec::new(),
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: initialized_places::MissingPlaces::default(),
        memory: Memory::default(),
    };
    let mut values = Vec::new();
    for (allocation, name) in ["Masked", "Different"].into_iter().enumerate() {
        let selected_body = tcx.optimized_mir(find(tcx, "symbolic", DefKind::Fn));
        let id = selected_body
            .local_decls
            .iter()
            .find_map(|local| {
                if let ty::Adt(definition, _) = local.ty.kind()
                    && tcx.item_name(definition.did()).as_str() == name
                {
                    Some(definition.did())
                } else {
                    None
                }
            })
            .unwrap();
        let concrete = tcx.type_of(id).instantiate_identity().skip_norm_wip();
        state.memory.push(Some(Value::Adt {
            name: tcx.def_path_str(id),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![("0".into(), symbolic::integer(&engine.terms, 7, 8, false))].into(),
        }));
        let reference = Value::Reference {
            allocation,
            projection: Vec::new(),
            mutable: false,
        };
        let source = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, concrete);
        let target = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, object);
        values.push(
            engine
                .trait_object_coercion(PointerCoercion::Unsize, source, target, reference, &state)
                .unwrap()
                .unwrap(),
        );
    }
    (engine, state, values, object)
}

fn check_source_receipts(tcx: TyCtxt<'_>) {
    let (mut engine, state, values, object) = sample(tcx);
    let masks = vec![engine.terms.boolean(true), engine.terms.boolean(false)];
    let selected = engine
        .publish_shared_trait_choice(object, values, masks, &state)
        .unwrap();
    let Value::TraitObject { source, id, .. } = &selected else {
        panic!("choice missing");
    };
    engine.trait_object_choice_work.set(0);
    engine.validate_tracked_value(&selected, &state).unwrap();
    assert!(
        engine
            .return_value(selected.clone(), &state, state.memory.len())
            .is_ok()
    );
    engine.trait_object_choice_work.set(0);
    assert!(engine.return_value(selected.clone(), &state, 0).is_err());
    engine.trait_object_choice_work.set(0);
    assert!(
        engine
            .borrow_trait_object(source, *id, true, &state)
            .is_err()
    );
    let Value::Elements(children) = source.as_ref() else {
        panic!("bundle missing");
    };
    let mut swapped = children.to_vec();
    let Value::TraitObject { source, .. } = &mut swapped[0] else {
        panic!("leaf missing");
    };
    let Value::Reference { allocation, .. } = source.as_mut() else {
        panic!("source missing");
    };
    *allocation = 1;
    engine.trait_object_choice_work.set(0);
    assert!(
        engine
            .validate_shared_trait_bundle(&Value::Elements(swapped.into()), *id)
            .is_err()
    );
    let mut dead = state.clone();
    dead.memory[0] = None;
    engine.trait_object_choice_work.set(0);
    assert!(engine.validate_tracked_value(&selected, &dead).is_err());
    let mut registry = engine.trait_objects.borrow_mut();
    let Witness::SharedChoice(choice) = &mut registry[*id] else {
        panic!("receipt missing");
    };
    let original_mask = choice.leaves[0].mask.clone();
    choice.leaves[0].mask = Context::default().boolean(true);
    drop(registry);
    engine.trait_object_choice_work.set(0);
    assert!(
        engine
            .validate_shared_trait_graph(&selected, &state)
            .is_err()
    );
    let mut registry = engine.trait_objects.borrow_mut();
    let Witness::SharedChoice(choice) = &mut registry[*id] else {
        panic!("receipt missing");
    };
    choice.leaves[0].mask = original_mask;
    drop(registry);
    let before = engine.trait_objects.borrow().len();
    let budget_values = children.to_vec();
    let budget_masks = vec![engine.terms.boolean(true), engine.terms.boolean(false)];
    // Exact named-policy boundaries; fee refusal must not advance the cumulative counter.
    engine
        .trait_object_choice_work
        .set(MAX_SHARED_TRAIT_CHOICE_WORK - 1);
    engine.shared_trait_fee(1).unwrap();
    assert_eq!(
        engine.trait_object_choice_work.get(),
        MAX_SHARED_TRAIT_CHOICE_WORK
    );
    assert!(engine.shared_trait_fee(1).is_err());
    assert_eq!(
        engine.trait_object_choice_work.get(),
        MAX_SHARED_TRAIT_CHOICE_WORK
    );
    engine
        .trait_object_choice_work
        .set(MAX_SHARED_TRAIT_CHOICE_WORK + 1);
    assert!(engine.shared_trait_fee(0).is_err());
    assert_eq!(
        engine.trait_object_choice_work.get(),
        MAX_SHARED_TRAIT_CHOICE_WORK + 1
    );
    engine
        .trait_object_choice_work
        .set(MAX_SHARED_TRAIT_CHOICE_WORK);
    let error = engine
        .publish_shared_trait_choice(object, budget_values, budget_masks, &state)
        .err()
        .unwrap();
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    assert_eq!(engine.trait_objects.borrow().len(), before);
    engine.trait_object_choice_work.set(0);
    let choice = engine.shared_trait_descriptor(*id).unwrap().unwrap();
    let first = engine
        .concrete_trait_object(choice.leaves[0].witness)
        .unwrap();
    let ty::Dynamic(predicates, _) = object.kind() else {
        panic!("object missing");
    };
    let trait_ref = predicates
        .principal()
        .unwrap()
        .skip_binder()
        .with_self_ty(tcx, first.concrete);
    let target = tcx
        .vtable_entries(trait_ref)
        .iter()
        .find_map(|entry| match entry {
            ty::VtblEntry::Method(target) => Some(*target),
            _ => None,
        })
        .unwrap();
    let original = engine.instantiated_body(target).unwrap();
    let mut bad = (*original).clone();
    bad.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.u16;
    engine
        .bodies
        .borrow_mut()
        .insert(target, std::rc::Rc::new(bad));
    let method = tcx
        .associated_items(predicates.principal().unwrap().skip_binder().def_id)
        .in_definition_order()
        .find(|item| tcx.item_name(item.def_id).as_str() == "read")
        .unwrap()
        .def_id;
    let virtual_call = engine
        .resolve_function_item(method, tcx.mk_args(&[object.into()]))
        .unwrap();
    engine.trait_object_choice_work.set(0);
    let old_locals = format!("{:?}", state.locals);
    let old_memory = format!("{:?}", &state.memory[..]);
    assert!(
        engine
            .shared_trait_object_call(
                virtual_call,
                &[selected],
                &state,
                &[],
                (root_id(tcx), tcx.def_span(root_id(tcx)))
            )
            .is_err()
    );
    assert_eq!(format!("{:?}", state.locals), old_locals);
    assert_eq!(format!("{:?}", &state.memory[..]), old_memory);
    engine.bodies.borrow_mut().insert(target, original);
}

fn root_id(tcx: TyCtxt<'_>) -> DefId {
    find(tcx, "constant", DefKind::Fn)
}

fn test_engine(tcx: TyCtxt<'_>) -> Engine<'_> {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    Engine::new(
        tcx,
        &config,
        VerificationOptions {
            all_failures,
            induction,
            startup,
            isolated_startup,
            async_entry,
            limits,
        },
    )
}

struct ReturnFaultScope(SharedReturnFault);
impl ReturnFaultScope {
    fn new(fault: SharedReturnFault) -> Self {
        Self(SHARED_RETURN_FAULT.with(|current| current.replace(fault)))
    }
}
impl Drop for ReturnFaultScope {
    fn drop(&mut self) {
        SHARED_RETURN_FAULT.with(|current| current.set(self.0));
    }
}

#[test]
fn return_fault_scope_restores_nested_and_panicking_threads() {
    assert!(SHARED_RETURN_FAULT.with(|fault| fault.get() == SharedReturnFault::None));
    {
        let _outer = ReturnFaultScope::new(SharedReturnFault::MissingBundle);
        {
            let _inner = ReturnFaultScope::new(SharedReturnFault::SwappedBacking);
            assert!(
                SHARED_RETURN_FAULT.with(|fault| fault.get() == SharedReturnFault::SwappedBacking)
            );
        }
        assert!(SHARED_RETURN_FAULT.with(|fault| fault.get() == SharedReturnFault::MissingBundle));
    }
    let result = std::panic::catch_unwind(|| {
        let _scope = ReturnFaultScope::new(SharedReturnFault::MissingBundle);
        panic!("restore actual Return fault scope");
    });
    assert!(result.is_err());
    assert!(SHARED_RETURN_FAULT.with(|fault| fault.get() == SharedReturnFault::None));
}

fn check_actual_return_faults(tcx: TyCtxt<'_>) {
    for fault in [
        SharedReturnFault::MissingBundle,
        SharedReturnFault::SwappedBacking,
    ] {
        let _scope = ReturnFaultScope::new(fault);
        SHARED_RETURN_OBSERVATIONS.with(|count| count.set(0));
        let id = find(tcx, "caller_backed_return", DefKind::Fn);
        let proof = super::super::verify(
            tcx,
            id,
            &miren::ContractConfig::default(),
            VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            },
        );
        assert_eq!(proof.status, ProofStatus::Unknown);
        assert!(SHARED_RETURN_OBSERVATIONS.with(|count| count.get() > 0));
        assert!(
            proof
                .body_entries
                .iter()
                .any(|entry| entry.function == "returned")
        );
        assert!(
            !proof
                .body_entries
                .iter()
                .any(|entry| entry.function == "invoke")
        );
    }
}
