use super::*;
#[test]
fn compiler_checked_interval_family_capture() {
    struct Capture {
        output: std::path::PathBuf,
        name: &'static str,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let core = tcx.lang_items().sized_trait().unwrap().krate;
            let root = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == self.name
                })
                .unwrap();
            let original = match self.name {
                "selected" => tcx.types.u16,
                "selected_i32" => tcx.types.i32,
                "selected_usize" => tcx.types.usize,
                _ => panic!("selected type"),
            };
            check_active_lifecycle(tcx, root.to_def_id(), original);
            assert!(
                templates::integer_wrapper_element(
                    tcx,
                    ty::Instance::new_raw(root.to_def_id(), tcx.mk_args(&[])),
                )
                .is_none()
            );
            let closure_root = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "closure_root"
                })
                .unwrap();
            let closure_body = tcx.optimized_mir(closure_root.to_def_id());
            let closure = closure_body
                .local_decls
                .iter()
                .find_map(|declaration| {
                    if let ty::Closure(id, args) = declaration.ty.kind() {
                        Some(ty::Instance::new_raw(*id, args))
                    } else {
                        None
                    }
                })
                .unwrap();
            assert_eq!(tcx.def_kind(closure.def_id()), DefKind::Closure);
            assert!(templates::integer_wrapper_element(tcx, closure).is_none());
            let body = tcx.optimized_mir(root.to_def_id());
            std::fs::write(self.output.join("caller.txt"), format!("{body:#?}")).unwrap();
            let mut pending = Vec::new();
            for data in body.basic_blocks.iter() {
                if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                    && let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind()
                    && id.krate == core
                    && tcx.def_kind(*id) == DefKind::AssocFn
                    && tcx.item_name(*id).as_str() == "index_mut"
                {
                    pending.push(
                        ty::Instance::try_resolve(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            *id,
                            args.skip_binder(),
                        )
                        .unwrap()
                        .unwrap(),
                    );
                }
            }
            let mut seen = std::collections::HashSet::new();
            let mut inventory = Vec::new();
            while let Some(instance) = pending.pop() {
                if !seen.insert(instance) {
                    continue;
                }
                assert!(seen.len() <= 512);
                let key = pure_comparison_templates::definition_key(instance.def_id());
                let available = tcx.is_mir_available(instance.def_id());
                inventory.push(format!("{key} {instance:?} available={available}"));
                if !available {
                    let error = templates::available_integer_body(tcx, instance).unwrap_err();
                    assert_eq!(error.category, UnknownCategory::MissingCompilerEvidence);
                    assert_eq!(
                        error.reason,
                        "interval integer selected compiler body is unavailable",
                    );
                    continue;
                }
                if key == "DefId(core::slice::index::{impl#1}::index_mut)"
                    && self.name == "selected"
                {
                    templates::certify_u16_guarded_family(tcx, instance).unwrap();
                } else if key == "DefId(core::slice::index::{impl#1}::index_mut)" {
                    const { assert!(INTEGER_ISSUANCE_ENABLED) };
                    let element = templates::integer_wrapper_element(tcx, instance).unwrap();
                    templates::certify_integer_guarded_family(tcx, instance, element).unwrap();
                    let mut wrong = element;
                    wrong.original = tcx.types.u32;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                    let mut wrong = element;
                    wrong.bytes += 1;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                    let mut wrong = element;
                    wrong.alignment *= 2;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                    let mut wrong = element;
                    wrong.bits += 1;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                    let mut wrong = element;
                    wrong.original = tcx.types.u64;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                    let mut wrong = element;
                    wrong.signed = !element.signed;
                    assert!(
                        templates::certify_integer_guarded_family(tcx, instance, wrong).is_err()
                    );
                }
                let generic = tcx.instance_mir(instance.def);
                let mono = instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(tcx, generic.clone()),
                    )
                    .unwrap();
                let template_body = if key == "DefId(core::slice::index::{impl#1}::index_mut)" {
                    &mono
                } else {
                    generic
                };
                std::fs::write(
                    self.output.join("pending-generic.txt"),
                    format!("{key}\n{generic:#?}"),
                )
                .unwrap();
                let encoded =
                    pure_comparison_templates::encode_byte_copy_template(tcx, template_body, core)
                        .unwrap();
                let index = seen.len();
                let instantiated =
                    pure_comparison_templates::encode_byte_copy_template(tcx, &mono, core).unwrap();
                std::fs::write(
                    self.output.join(format!("{index}-instantiated.mir")),
                    instantiated,
                )
                .unwrap();
                std::fs::write(self.output.join(format!("{index}-key.txt")), &key).unwrap();
                std::fs::write(self.output.join(format!("{index}-generic.mir")), encoded).unwrap();
                std::fs::write(
                    self.output.join(format!("{index}-mono.txt")),
                    format!("{mono:#?}"),
                )
                .unwrap();
                for data in mono.basic_blocks.iter() {
                    if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                        && let ty::FnDef(id, args) = func.ty(&mono.local_decls, tcx).kind()
                    {
                        pending.push(
                            ty::Instance::try_resolve(
                                tcx,
                                ty::TypingEnv::fully_monomorphized(),
                                *id,
                                args.skip_binder(),
                            )
                            .unwrap()
                            .unwrap(),
                        );
                    }
                }
            }
            std::fs::write(self.output.join("inventory.txt"), inventory.join("\n")).unwrap();
            rustc_driver::Compilation::Stop
        }
    }
    let root = std::path::PathBuf::from("/tmp/miren-stage205-parent203/compiler-lifecycle");
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "pub fn closure_root(value:u32)->u32 { let f=|word:u32| word; f(value) }\n",
            "pub fn selected(v:&mut[u16],a:usize,b:usize) {\n",
            "if a<b && b<=v.len() { update(&mut v[a..b]); }\n}\n",
            "#[inline(never)] fn update(v:&mut[u16]) { if v.len()>0 { v[0]=19; } }\n",
            "pub fn selected_i32(v:&mut[i32],a:usize,b:usize) {\n",
            "if a<b && b<=v.len() { update_i32(&mut v[a..b]); } }\n",
            "#[inline(never)] fn update_i32(v:&mut[i32]) { if v.len()>0 { v[0]=19; } }\n",
            "pub fn selected_usize(v:&mut[usize],a:usize,b:usize) {\n",
            "if a<b && b<=v.len() { update_usize(&mut v[a..b]); } }\n",
            "#[inline(never)] fn update_usize(v:&mut[usize]) { if v.len()>0 { v[0]=19; } }\n",
        ),
    )
    .unwrap();
    for (target, tag) in [(None, "host"), (Some("thumbv7em-none-eabihf"), "arm")] {
        for opt in [0, 2] {
            for name in ["selected", "selected_i32", "selected_usize"] {
                let output = root.join(format!("{tag}-o{opt}-{name}"));
                std::fs::create_dir_all(&output).unwrap();
                let mut args = vec![
                    "rustc".into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    source.display().to_string(),
                    "--out-dir".into(),
                    output.display().to_string(),
                    "-Zmir-opt-level=0".into(),
                    "-Cpanic=abort".into(),
                    format!("-Copt-level={opt}"),
                ];
                if let Some(target) = target {
                    args.extend(["--target".into(), target.into()]);
                }
                std::fs::write(output.join("command.txt"), args.join("\n")).unwrap();
                rustc_driver::run_compiler(&args, &mut Capture { output, name });
            }
        }
    }
}

fn check_active_lifecycle<'tcx>(tcx: TyCtxt<'tcx>, root: DefId, original_type: Ty<'tcx>) {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    let mut engine = Engine {
        tcx,
        terms: Context::default(),
        next_symbol: std::cell::Cell::new(0),
        float_encodings: BTreeMap::new(),
        float_pairs: float_pairs::Registry::default(),
        abstraction_symbols: std::cell::RefCell::new(BTreeMap::new()),
        static_views: std::cell::RefCell::new(Vec::new()),
        static_origins: Default::default(),
        static_epoch: None,
        static_roots: None,
        function_pointers: std::cell::RefCell::new(Vec::new()),
        static_addresses: std::collections::HashMap::new(),
        tracked_addresses: Vec::new(),
        maybe_uninit_types: Vec::new(),
        scalar_slice_types: Vec::new(),
        composite_slice_types: Vec::new(),
        steps: 0,
        call_chain: Vec::new(),
        failed_call_chain: None,
        trait_objects: std::cell::RefCell::new(Vec::new()),
        trait_object_choice_work: std::cell::Cell::new(0),
        trait_object_choices_issued: std::cell::Cell::new(false),
        input_depth: 0,
        input_values: 0,
        input_reservations: Vec::new(),
        owned_projection_certificates: Vec::new(),
        input_shapes: std::collections::HashMap::new(),
        zero_sized_inputs: std::collections::HashMap::new(),
        zero_sized_input_nodes: 0,
        prefer_lazy_inputs: false,
        building_mutable_input: false,
        unknown_causes: std::cell::RefCell::new(BTreeMap::new()),
        started: std::time::Instant::now(),
        config: config.clone(),
        all_failures,
        induction,
        startup,
        isolated_startup,
        limits,
        resolved_contracts: BTreeMap::new(),
        solver: std::cell::RefCell::new(Solver::with_limits(limits)),
        mutable_u16_frames: Default::default(),
        mutable_integer_types: Vec::new(),
        mutable_u16_staging: Default::default(),
        activation: Default::default(),
        coroutine_places: Default::default(),
        owned_box_types: Vec::new(),
        next_owned_region: 0,
        owned_box_constructors: Vec::new(),
        bodies: std::cell::RefCell::new(std::collections::HashMap::new()),
        call_signatures: std::cell::RefCell::new(std::collections::HashMap::new()),
        proof: Proof {
            status: ProofStatus::Proved,
            async_entry,
            assumptions: Vec::new(),
            entry_assumptions: Vec::new(),
            inputs: BTreeMap::new(),
            models: Vec::new(),
            invariants: Vec::new(),
            analyzed_bodies: Vec::new(),
            body_entries: Vec::new(),
            body_entries_truncated: false,
            obligations: Vec::new(),
            trusted_calls: Vec::new(),
            matched_contracts: Vec::new(),
            stopped_after_counterexample: false,
            replay_inputs: None,
        },
    };

    let instance = engine
        .resolve_function_item(root, tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(instance).unwrap();
    let range_local = body
        .local_decls
        .iter_enumerated()
        .find_map(|(local, declaration)| {
            matches!(declaration.ty.kind(), ty::Adt(def, arguments)
            if tcx.lang_items().get(LangItem::Range) == Some(def.did())
                && arguments.type_at(0) == tcx.types.usize)
            .then_some(local)
        })
        .unwrap();
    let field = |recorded| Place {
        local: range_local,
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(0),
            recorded,
        )]),
    };
    assert!(
        engine
            .owned_field_footprint(&body, field(tcx.types.usize))
            .is_ok()
    );
    assert!(
        engine
            .owned_field_footprint(&body, field(tcx.types.u32))
            .is_err()
    );
    let (block, args, destination, target, selected) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &data.terminator().kind
            else {
                return None;
            };
            let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
                return None;
            };
            if tcx.def_kind(*id) != DefKind::AssocFn {
                return None;
            }
            let selected = engine
                .resolve_function_item(*id, generic.skip_binder())
                .unwrap();
            (pure_comparison_templates::definition_key(selected.def_id())
                == "DefId(core::slice::index::{impl#1}::index_mut)")
                .then_some((block, args.as_ref(), *destination, *target, selected))
        })
        .unwrap();
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let root_value = engine
        .mutable_u16_input(original_type, &mut memory, &mut conditions)
        .unwrap();
    let bits = u32::from(tcx.sess.target.pointer_width);
    let end = symbolic::integer(&engine.terms, 3, bits, false);
    conditions.push(
        symbolic::binary(
            &engine.terms,
            "le",
            end.clone(),
            memory.mutable_u16[0].length.clone(),
        )
        .unwrap()
        .boolean()
        .unwrap(),
    );
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        conditions,
        memory,
    };
    state.locals[1] = Some(root_value);
    state.locals[2] = Some(symbolic::integer(&engine.terms, 1, bits, false));
    state.locals[3] = Some(end);
    for statement in &body.basic_blocks[block].statements {
        if let StatementKind::Assign(assignment) = &statement.kind {
            if engine
                .mutable_u16_stage(
                    &body,
                    &mut state,
                    assignment.0,
                    &assignment.1,
                    &statement.kind,
                )
                .unwrap()
            {
                continue;
            }
            let value = engine
                .rvalue(root, &body, &mut state, &assignment.1)
                .unwrap();
            engine.write(&mut state, assignment.0, value).unwrap();
        }
    }
    let call = || ChildCall {
        body: &body,
        block,
        instance: selected,
        args,
        destination,
        target,
        stack: &[],
        site: (root, body.span),
    };
    assert!(
        engine
            .mutable_interval_call(&state, call())
            .unwrap()
            .is_some()
    );
    let original = state.clone();
    let (_, issued) = engine
        .mutable_interval_issuer(&state, call())
        .unwrap()
        .unwrap();
    assert!(original.memory.mutable_u16[0].interval.is_none());
    assert_eq!(
        original.memory.mutable_u16[0].data,
        issued.memory.mutable_u16[0].data
    );
    assert_eq!(
        issued.memory.storage_slots(),
        original.memory.storage_slots() + 7
    );
    engine
        .validate_mutable_interval(0, &issued.memory.mutable_u16[0])
        .unwrap();
    if original_type != tcx.types.u16 {
        let wrong = if original_type == tcx.types.i32 {
            tcx.types.u32
        } else {
            match u32::from(tcx.sess.target.pointer_width) {
                32 => tcx.types.u32,
                64 => tcx.types.u64,
                _ => panic!("pointer width"),
            }
        };
        let mut wrong_memory = Memory::default();
        engine
            .mutable_u16_input(wrong, &mut wrong_memory, &mut Vec::new())
            .unwrap();
        let wrong_certificate = wrong_memory.mutable_u16[0].certificate;
        let mut wrong_state = state.clone();
        std::rc::Rc::make_mut(&mut wrong_state.memory.mutable_u16)[0].certificate =
            wrong_certificate;
        assert!(
            engine
                .mutable_interval_issuer(&wrong_state, call())
                .is_err()
        );
        let mut wrong_view = issued.clone();
        let backing = &mut std::rc::Rc::make_mut(&mut wrong_view.memory.mutable_u16)[0];
        backing.certificate = wrong_certificate;
        std::rc::Rc::make_mut(&mut backing.interval.as_mut().unwrap().issue).certificate =
            wrong_certificate;
        assert!(engine.validate_mutable_interval(0, backing).is_err());
    }
    let foreign_data_context = Context::default();
    let mut malformed_data = Vec::new();
    for context in [&engine.terms, &foreign_data_context] {
        let element_sort = if std::ptr::eq(context, &engine.terms) {
            Sort::Bool
        } else {
            match issued.memory.mutable_u16[0].data.sort() {
                Sort::Array(_, element) => element.as_ref().clone(),
                _ => panic!("array backing"),
            }
        };
        malformed_data.push(
            context
                .symbol(
                    777,
                    Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(element_sort)),
                )
                .unwrap(),
        );
    }
    for data in malformed_data {
        let mut malformed = state.clone();
        std::rc::Rc::make_mut(&mut malformed.memory.mutable_u16)[0].data = data;
        assert!(engine.mutable_interval_issuer(&malformed, call()).is_err());
    }
    let mut masked_memory = state.clone();
    let allocation = masked_memory.memory.mutable_u16[0].allocation;
    masked_memory
        .memory
        .missing_places
        .consume(allocation, Vec::new())
        .unwrap();
    assert!(
        engine
            .mutable_interval_issuer(&masked_memory, call())
            .is_err()
    );
    let mut missing_backing = state.clone();
    missing_backing.memory[allocation] = None;
    assert!(
        engine
            .mutable_interval_issuer(&missing_backing, call())
            .is_err()
    );
    let mut changed = issued.clone();
    let current = &mut std::rc::Rc::make_mut(&mut changed.memory.mutable_u16)[0];
    current.interval.as_mut().unwrap().offset = symbolic::integer(&engine.terms, 2, bits, false);
    assert!(engine.validate_mutable_interval(0, current).is_err());
    let mut changed = issued.clone();
    let current = &mut std::rc::Rc::make_mut(&mut changed.memory.mutable_u16)[0];
    current.generation += 1;
    assert!(engine.validate_mutable_interval(0, current).is_err());
    let mut changed = issued.clone();
    let current = &mut std::rc::Rc::make_mut(&mut changed.memory.mutable_u16)[0];
    current.phase = Phase::Idle;
    assert!(engine.validate_mutable_interval(0, current).is_err());
    assert!(
        engine
            .mutable_interval_index(
                0,
                &issued.memory.mutable_u16[0],
                symbolic::integer(&engine.terms, 0, bits, false),
                &issued.conditions
            )
            .is_err()
    );
    let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
        panic!("source");
    };
    assert!(
        engine
            .mutable_u16_staging_tip(
                &body,
                &issued,
                source.local.as_usize(),
                0,
                issued.memory.mutable_u16[0].generation
            )
            .is_err()
    );
    let mut consumed = state.clone();
    consumed
        .missing_places
        .consume(source.local.as_usize(), Vec::new())
        .unwrap();
    assert!(engine.mutable_interval_issuer(&consumed, call()).is_err());
    let copied_args = args.to_vec();
    assert!(
        engine
            .mutable_interval_issuer(
                &state,
                ChildCall {
                    args: &copied_args,
                    ..call()
                }
            )
            .is_err()
    );
    let mut full = state.clone();
    full.memory.resize(MAX_INPUT_VALUES, Some(Value::Unit));
    assert!(engine.mutable_interval_issuer(&full, call()).is_err());
    let mut other_context = issued.clone();
    let foreign = Context::default();
    std::rc::Rc::make_mut(&mut other_context.memory.mutable_u16)[0]
        .interval
        .as_mut()
        .unwrap()
        .offset = symbolic::integer(&foreign, 1, bits, false);
    assert!(
        engine
            .validate_mutable_interval(0, &other_context.memory.mutable_u16[0])
            .is_err()
    );
    let mut changed = issued.clone();
    let current = &mut std::rc::Rc::make_mut(&mut changed.memory.mutable_u16)[0];
    current.phase = Phase::Active { frames: vec![0] };
    let child_role = Value::MutableU16 {
        id: 0,
        role: MutableU16Role::Child {
            generation: current.generation,
        },
    };
    let ghost = engine
        .mutable_u16_snapshot(&child_role, &changed.memory)
        .unwrap();
    assert!(same_integer(
        &engine.mutable_u16_length(&ghost, &changed.memory).unwrap(),
        &symbolic::integer(&engine.terms, 2, bits, false)
    ));
    let mut metadata_state = changed.clone();
    metadata_state.locals[1] = Some(child_role);
    let observed = engine
        .mutable_u16_direct_metadata(
            &body,
            &metadata_state,
            &Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1))),
        )
        .unwrap()
        .unwrap();
    assert!(same_integer(
        &observed,
        &symbolic::integer(&engine.terms, 2, bits, false)
    ));
    let current = &changed.memory.mutable_u16[0];
    let translated = engine
        .mutable_interval_index(
            0,
            current,
            symbolic::integer(&engine.terms, 1, bits, false),
            &issued.conditions,
        )
        .unwrap();
    assert_eq!(
        translated.integer().unwrap().0,
        symbolic::integer(&engine.terms, 2, bits, false)
            .integer()
            .unwrap()
            .0
    );
    assert!(
        engine
            .mutable_interval_index(
                0,
                current,
                symbolic::integer(&engine.terms, 2, bits, false),
                &issued.conditions
            )
            .is_err()
    );
    let mut next = issued.clone();
    let continuation = target.unwrap();
    for statement in &body.basic_blocks[continuation].statements {
        if let StatementKind::Assign(assignment) = &statement.kind {
            if engine
                .mutable_u16_stage(
                    &body,
                    &mut next,
                    assignment.0,
                    &assignment.1,
                    &statement.kind,
                )
                .unwrap()
            {
                continue;
            }
            let value = engine
                .rvalue(root, &body, &mut next, &assignment.1)
                .unwrap();
            engine.write(&mut next, assignment.0, value).unwrap();
        }
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &body.basic_blocks[continuation].terminator().kind
    else {
        panic!("child Call");
    };
    let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
        panic!("child FnDef");
    };
    let child = engine
        .resolve_function_item(*id, generic.skip_binder())
        .unwrap();
    let returned = engine
        .mutable_u16_child_call(
            &mut next,
            ChildCall {
                body: &body,
                block: continuation,
                instance: child,
                args,
                destination: *destination,
                target: *target,
                stack: &[],
                site: (root, body.span),
            },
        )
        .unwrap()
        .unwrap();
    assert!(!returned.is_empty());
    for result in returned {
        assert_eq!(result.memory.mutable_u16[0].phase, Phase::Idle);
        assert!(result.memory.mutable_u16[0].interval.is_none());
        assert_ne!(
            result.memory.mutable_u16[0].data,
            original.memory.mutable_u16[0].data
        );
        assert_eq!(
            result.memory.mutable_u16[0].generation,
            issued.memory.mutable_u16[0].generation
        );
        assert!(result.memory.storage_slots() <= MAX_INPUT_VALUES);
    }
}
