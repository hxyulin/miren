use super::*;

#[test]
fn compiler_known_function_table_prepared_calls() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check_prepared_calls(tcx);
            rustc_driver::Compilation::Stop
        }
    }
    let root =
        std::env::temp_dir().join(format!("miren-function-table-unit-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    let dependency = root.join("dependency.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#[inline(never)] pub fn unavailable(value: u16) -> u16 { value }\n",
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"#![no_std]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
extern crate alloc;
#[inline(never)] pub fn first(value: u16) -> u16 { value }
#[inline(never)] pub fn second(value: u16) -> u16 { value ^ 1 }
#[inline(never)] pub fn wide(value: u32) -> u32 { value }
pub fn omitted_wrapper(value: u16) -> u16 { fn_table_external::unavailable(value) }
#[inline(never)] pub fn allocated(value: u16) -> u16 {
    let owned = alloc::boxed::Box::new(());
    core::mem::drop(owned);
    value
}
pub fn selected(index: usize, value: u16) -> u16 {
    let table: [fn(u16)->u16;2] = [first, second];
    if index < 2 { table[index](value) } else { value }
}
pub fn field_source(index: usize, record: ([fn(u16)->u16;2], bool), value: u16) -> u16 {
    if index < 2 { record.0[index](value) } else { value }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved(callback: fn(u16)->u16, word: u16) -> u16 {
    mir! {
        { Call(RET = Move(callback)(Move(word)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn copied(callback: fn(u16)->u16, record: (u16, bool)) -> u16 {
    mir! {
        { Call(RET = Move(callback)(record.0), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir_all(&output).unwrap();
            let archive = output.join("libfn_table_external.rlib");
            let compiler = std::path::Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
            let mut dependency_command = std::process::Command::new(compiler);
            dependency_command
                .args([
                    "--crate-type=rlib",
                    "--crate-name=fn_table_external",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Zalways-encode-mir=no",
                    "-Copt-level=0",
                ])
                .arg(&dependency)
                .arg("-o")
                .arg(&archive);
            if let Some(target) = target {
                dependency_command.args(["--target", target]);
            }
            let compiled = dependency_command.output().unwrap();
            assert!(
                compiled.status.success(),
                "{}",
                String::from_utf8_lossy(&compiled.stderr)
            );
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "--extern".into(),
                format!("fn_table_external={}", archive.display()),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture);
        }
    }
    std::fs::remove_dir_all(root).unwrap();
}

fn check_prepared_calls<'tcx>(tcx: TyCtxt<'tcx>) {
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
        trait_objects: Vec::new(),
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

    let find = |name: &str| {
        tcx.mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == name
            })
            .unwrap()
            .to_def_id()
    };
    let moved = find("moved");
    let instance = engine
        .resolve_function_item(moved, tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(instance).unwrap();
    let (block, func, args, destination, target, span) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let terminator = data.terminator();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &terminator.kind
            else {
                return None;
            };
            Some((
                block,
                func,
                args.as_ref(),
                *destination,
                *target,
                terminator.source_info.span,
            ))
        })
        .unwrap();
    let signature = func.ty(&body.local_decls, tcx);
    let selected = engine
        .resolve_function_item(find("selected"), tcx.mk_args(&[]))
        .unwrap();
    let selected_body = engine.instantiated_body(selected).unwrap();
    let original = selected_body
        .local_decls
        .iter()
        .map(|local| local.ty)
        .find(|ty| {
            matches!(ty.kind(),ty::Array(element,count)
            if *element == signature && count.try_to_target_usize(tcx) == Some(2))
        })
        .unwrap();
    let mut pointers = Vec::new();
    for name in ["first", "second"] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let id = engine
            .register_function_pointer(Target::Known {
                instance,
                signature,
            })
            .unwrap();
        pointers.push(Value::FunctionPointer { id });
    }
    let bits = u32::from(tcx.sess.target.pointer_width);
    let raw = engine.fresh(Sort::BitVec(bits));
    let index = Value::Int {
        expression: raw.clone(),
        bits,
        signed: false,
    };
    let bound = engine
        .terms
        .apply(
            Op::BvUnsignedLt,
            &[raw.clone(), engine.terms.bit_vector(2, bits).unwrap()],
        )
        .unwrap();
    let conditions = vec![bound];
    let table_local = selected_body
        .local_decls
        .iter_enumerated()
        .find_map(|(local, decl)| (decl.ty == original).then_some(local))
        .unwrap();
    let source_index = selected_body
        .args_iter()
        .find(|local| selected_body.local_decls[*local].ty == tcx.types.usize)
        .unwrap();
    let mut source_state = State {
        locals: vec![None; selected_body.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; selected_body.local_decls.len()],
        memory: Default::default(),
    };
    source_state.locals[table_local.as_usize()] = Some(Value::Elements(pointers.clone().into()));
    source_state.locals[source_index.as_usize()] = Some(index.clone());
    let source = TableSource {
        body: &selected_body,
        prefix: Place::from(table_local),
        state: &source_state,
        index: source_index,
    };
    let pointer = engine
        .function_table_choice(original, &pointers, &index, &conditions, Some(source))
        .unwrap()
        .unwrap();
    let Value::FunctionPointer { id: choice_id } = pointer else {
        panic!("missing Choice");
    };
    assert_eq!(
        engine
            .function_pointers
            .borrow()
            .iter()
            .map(registry_cost)
            .sum::<usize>(),
        5
    );
    assert!(
        engine
            .function_table_choice(original, &pointers, &index, &conditions, None)
            .unwrap()
            .is_none()
    );
    let reversed = [pointers[1].clone(), pointers[0].clone()];
    assert!(
        engine
            .function_table_choice(original, &reversed, &index, &conditions, Some(source))
            .is_err()
    );
    let mismatched_source = TableSource {
        prefix: Place::from(source_index),
        ..source
    };
    assert!(
        engine
            .function_table_choice(
                original,
                &pointers,
                &index,
                &conditions,
                Some(mismatched_source)
            )
            .is_err()
    );
    let changed_index = Value::Int {
        expression: engine.terms.bit_vector(0, bits).unwrap(),
        bits,
        signed: false,
    };
    assert!(
        engine
            .function_table_choice(
                original,
                &pointers,
                &changed_index,
                &conditions,
                Some(source)
            )
            .is_err()
    );
    let mut masked_source = source_state.clone();
    masked_source
        .missing_places
        .consume(table_local.as_usize(), Vec::new())
        .unwrap();
    let masked_source = TableSource {
        state: &masked_source,
        ..source
    };
    assert!(
        engine
            .function_table_choice(
                original,
                &pointers,
                &index,
                &conditions,
                Some(masked_source)
            )
            .is_err()
    );
    let field_instance = engine
        .resolve_function_item(find("field_source"), tcx.mk_args(&[]))
        .unwrap();
    let field_body = engine.instantiated_body(field_instance).unwrap();
    let record = field_body
        .local_decls
        .iter_enumerated()
        .find_map(|(local, decl)| {
            matches!(decl.ty.kind(),ty::Tuple(types) if types.len()==2 && types[0]==original)
                .then_some(local)
        })
        .unwrap();
    let field_index = field_body
        .args_iter()
        .find(|local| field_body.local_decls[*local].ty == tcx.types.usize)
        .unwrap();
    let prefix = Place {
        local: record,
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(0),
            original,
        )]),
    };
    let mut field_state = State {
        locals: vec![None; field_body.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; field_body.local_decls.len()],
        memory: Default::default(),
    };
    field_state.locals[record.as_usize()] = Some(Value::Tuple(vec![
        Value::Elements(pointers.clone().into()),
        Value::Bool(engine.terms.boolean(true)),
    ]));
    field_state.locals[field_index.as_usize()] = Some(index.clone());
    let field_source = TableSource {
        body: &field_body,
        prefix,
        state: &field_state,
        index: field_index,
    };
    assert!(
        engine
            .function_table_choice(original, &pointers, &index, &conditions, Some(field_source))
            .unwrap()
            .is_some()
    );
    let wide = engine
        .resolve_function_item(find("wide"), tcx.mk_args(&[]))
        .unwrap();
    let wide_signature = Ty::new_fn_ptr(tcx, engine.call_poly_signature(wide).unwrap());
    let mut forged_source = field_body.as_ref().clone();
    forged_source.local_decls[record].ty = Ty::new_tup(
        tcx,
        &[Ty::new_array(tcx, wide_signature, 2), tcx.types.bool],
    );
    let forged_source = TableSource {
        body: &forged_source,
        ..field_source
    };
    assert!(
        engine
            .function_table_choice(
                original,
                &pointers,
                &index,
                &conditions,
                Some(forged_source)
            )
            .is_err()
    );
    assert!(
        engine
            .capture_function_table(original, &pointers, &index, &[])
            .is_err()
    );
    let foreign = Context::default();
    let foreign_index = Value::Int {
        expression: foreign.bit_vector(0, bits).unwrap(),
        bits,
        signed: false,
    };
    assert!(
        engine
            .capture_function_table(original, &pointers, &foreign_index, &conditions)
            .is_err()
    );
    let signed = Value::Int {
        expression: raw.clone(),
        bits,
        signed: true,
    };
    assert!(
        engine
            .capture_function_table(original, &pointers, &signed, &conditions)
            .is_err()
    );
    assert!(
        engine
            .capture_function_table(original, &[pointers[0].clone()], &index, &conditions)
            .is_err()
    );
    let bad = [
        Value::FunctionPointer { id: usize::MAX },
        pointers[1].clone(),
    ];
    assert!(
        engine
            .capture_function_table(original, &bad, &index, &conditions)
            .is_err()
    );
    let nested = [
        Value::FunctionPointer { id: choice_id },
        pointers[1].clone(),
    ];
    assert!(
        engine
            .capture_function_table(original, &nested, &index, &conditions)
            .is_err()
    );
    let opaque_id = engine.opaque_function_pointer_id(signature).unwrap();
    let opaque = [
        Value::FunctionPointer { id: opaque_id },
        pointers[1].clone(),
    ];
    assert!(
        engine
            .capture_function_table(original, &opaque, &index, &conditions)
            .is_err()
    );
    let Operand::Move(callable_place) = func else {
        panic!("actual callable Move absent");
    };
    let Operand::Move(word_place) = &args[0].node else {
        panic!("actual argument Move absent");
    };
    let mut state = State {
        locals: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; body.local_decls.len()],
        memory: Default::default(),
    };
    state.locals[callable_place.local.as_usize()] = Some(Value::FunctionPointer { id: choice_id });
    state.locals[word_place.local.as_usize()] =
        Some(symbolic::integer(&engine.terms, 129, 16, false));
    let stack = [moved];
    let make_call = || TableCall {
        body: &body,
        block,
        func,
        args,
        destination,
        target,
        stack: &stack,
        site: (moved, span),
    };
    let returns = engine
        .function_table_call(&state, make_call())
        .unwrap()
        .unwrap();
    assert_eq!(returns.len(), 2);
    for (position, (consumed, result)) in returns.iter().enumerate() {
        assert!(engine.operand(moved, &body, consumed, func).is_err());
        assert!(
            engine
                .operand(moved, &body, consumed, &args[0].node)
                .is_err()
        );
        let (term, bits, signed) = result.value.integer().unwrap();
        assert_eq!((bits, signed), (16, false));
        let wrong = engine
            .terms
            .apply(
                Op::Not,
                &[engine
                    .terms
                    .apply(
                        Op::Equal,
                        &[
                            term,
                            engine
                                .terms
                                .bit_vector(if position == 0 { 129 } else { 128 }, 16)
                                .unwrap(),
                        ],
                    )
                    .unwrap()],
            )
            .unwrap();
        let mut conditions = result.conditions.clone();
        conditions.push(wrong);
        assert!(!engine.feasible(&conditions).unwrap());
    }
    assert!(engine.operand(moved, &body, &state, func).is_ok());
    assert!(engine.operand(moved, &body, &state, &args[0].node).is_ok());
    assert!(!state.memory.byte_copy_opaque);
    assert!(returns.iter().all(
        |(consumed, result)| consumed.memory.byte_copy_opaque && result.memory.byte_copy_opaque
    ));
    for name in ["first", "second"] {
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function == name)
        );
    }
    let mut uncovered = state.clone();
    uncovered.conditions.clear();
    assert!(
        engine
            .prepared_function_table_call(&uncovered, make_call())
            .is_err()
    );
    let wrong_call = TableCall {
        site: (find("first"), span),
        ..make_call()
    };
    assert!(
        engine
            .prepared_function_table_call(&state, wrong_call)
            .is_err()
    );
    let mut masked = returns[0].0.clone();
    masked.conditions = state.conditions.clone();
    assert!(
        engine
            .prepared_function_table_call(&masked, make_call())
            .is_err()
    );
    let saved = engine.function_pointers.borrow()[choice_id].clone();
    let Target::Choice(valid) = &saved else {
        panic!("choice missing");
    };
    let mut forged = valid.clone();
    forged.original = Ty::new_array(tcx, signature, 3);
    engine.function_pointers.borrow_mut()[choice_id] = Target::Choice(forged);
    assert!(
        engine
            .prepared_function_table_call(&state, make_call())
            .is_err()
    );
    let mut forged = valid.clone();
    forged.index = foreign.bit_vector(0, bits).unwrap();
    engine.function_pointers.borrow_mut()[choice_id] = Target::Choice(forged);
    assert!(
        engine
            .prepared_function_table_call(&state, make_call())
            .is_err()
    );
    let mut forged = valid.clone();
    forged.targets[1] = usize::MAX;
    engine.function_pointers.borrow_mut()[choice_id] = Target::Choice(forged);
    assert!(
        engine
            .prepared_function_table_call(&state, make_call())
            .is_err()
    );
    let mut forged = valid.clone();
    forged.signature = tcx.types.u16;
    engine.function_pointers.borrow_mut()[choice_id] = Target::Choice(forged);
    assert!(
        engine
            .prepared_function_table_call(&state, make_call())
            .is_err()
    );
    engine.function_pointers.borrow_mut()[choice_id] = saved;
    let allocated = engine
        .resolve_function_item(find("allocated"), tcx.mk_args(&[]))
        .unwrap();
    let allocated_id = engine
        .register_function_pointer(Target::Known {
            instance: allocated,
            signature,
        })
        .unwrap();
    let allocation_choice = engine
        .capture_function_table(
            original,
            &[
                Value::FunctionPointer { id: allocated_id },
                pointers[1].clone(),
            ],
            &index,
            &conditions,
        )
        .unwrap()
        .unwrap();
    let mut allocation_state = state.clone();
    allocation_state.locals[callable_place.local.as_usize()] = Some(allocation_choice);
    let allocated_returns = engine
        .prepared_function_table_call(&allocation_state, make_call())
        .unwrap()
        .unwrap();
    assert_eq!(allocated_returns.len(), 2);
    assert!(!allocated_returns[0].1.memory.owned_regions.is_empty());
    assert!(
        allocated_returns[0]
            .1
            .memory
            .owned_regions
            .iter()
            .all(|region| !region.live)
    );
    assert!(allocated_returns[1].1.memory.owned_regions.is_empty());
    assert!(allocation_state.memory.owned_regions.is_empty());
    let copied = find("copied");
    let copied_instance = engine
        .resolve_function_item(copied, tcx.mk_args(&[]))
        .unwrap();
    let copied_body = engine.instantiated_body(copied_instance).unwrap();
    let copied_block = copied_body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            matches!(data.terminator().kind, TerminatorKind::Call { .. }).then_some(block)
        })
        .unwrap();
    let TerminatorKind::Call {
        func: copied_func,
        args: copied_args,
        destination: copied_destination,
        target: copied_target,
        ..
    } = &copied_body.basic_blocks[copied_block].terminator().kind
    else {
        panic!("Call missing");
    };
    let Operand::Move(copied_pointer) = copied_func else {
        panic!("callable Move missing");
    };
    let Operand::Copy(copied_record) = &copied_args[0].node else {
        panic!("field Copy missing");
    };
    let mut copied_state = State {
        locals: vec![None; copied_body.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; copied_body.local_decls.len()],
        memory: Default::default(),
    };
    copied_state.locals[copied_pointer.local.as_usize()] =
        Some(Value::FunctionPointer { id: choice_id });
    copied_state.locals[copied_record.local.as_usize()] = Some(Value::Tuple(vec![
        symbolic::integer(&engine.terms, 129, 16, false),
        Value::Bool(engine.terms.boolean(true)),
    ]));
    let copied_stack = [copied];
    let copied_call = TableCall {
        body: &copied_body,
        block: copied_block,
        func: copied_func,
        args: copied_args,
        destination: *copied_destination,
        target: *copied_target,
        stack: &copied_stack,
        site: (
            copied,
            copied_body.basic_blocks[copied_block]
                .terminator()
                .source_info
                .span,
        ),
    };
    assert_eq!(
        engine
            .prepared_function_table_call(&copied_state, copied_call)
            .unwrap()
            .unwrap()
            .len(),
        2
    );
    let mut forged_body = copied_body.as_ref().clone();
    forged_body.local_decls[copied_record.local].ty =
        Ty::new_tup(tcx, &[tcx.types.u32, tcx.types.bool]);
    let forged_terminator = forged_body.basic_blocks[copied_block].terminator();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &forged_terminator.kind
    else {
        panic!("Call missing");
    };
    let forged_call = TableCall {
        body: &forged_body,
        block: copied_block,
        func,
        args,
        destination: *destination,
        target: *target,
        stack: &copied_stack,
        site: (copied, forged_terminator.source_info.span),
    };
    assert!(
        engine
            .prepared_function_table_call(&copied_state, forged_call)
            .is_err()
    );
    let wrapper = engine
        .resolve_function_item(find("omitted_wrapper"), tcx.mk_args(&[]))
        .unwrap();
    let wrapper = engine.instantiated_body(wrapper).unwrap();
    let omitted = wrapper
        .basic_blocks
        .iter()
        .find_map(|data| {
            let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                return None;
            };
            let ty::FnDef(id, args) = func.ty(&wrapper.local_decls, tcx).kind() else {
                return None;
            };
            (!id.is_local()).then(|| {
                engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap()
            })
        })
        .unwrap();
    assert!(!tcx.is_mir_available(omitted.def_id()));
    let omitted_id = engine
        .register_function_pointer(Target::Known {
            instance: omitted,
            signature,
        })
        .unwrap();
    let omitted_choice = engine
        .capture_function_table(
            original,
            &[
                pointers[0].clone(),
                Value::FunctionPointer { id: omitted_id },
            ],
            &index,
            &conditions,
        )
        .unwrap()
        .unwrap();
    let mut omitted_state = state.clone();
    omitted_state.locals[callable_place.local.as_usize()] = Some(omitted_choice);
    let missing = engine
        .prepared_function_table_call(&omitted_state, make_call())
        .err()
        .unwrap();
    assert!(missing.contains("MIR body unavailable for"));
    assert!(
        engine
            .unknown_causes
            .borrow()
            .values()
            .any(|category| *category == UnknownCategory::MissingCompilerEvidence)
    );
    let mut infeasible_omitted = omitted_state.clone();
    infeasible_omitted.conditions.push(
        engine
            .terms
            .apply(
                Op::Equal,
                &[raw.clone(), engine.terms.bit_vector(0, bits).unwrap()],
            )
            .unwrap(),
    );
    assert_eq!(
        engine
            .prepared_function_table_call(&infeasible_omitted, make_call())
            .unwrap()
            .unwrap()
            .len(),
        1
    );
    engine.steps = engine.limits.max_steps - 1;
    assert!(
        engine
            .prepared_function_table_call(&state, make_call())
            .is_err()
    );
    let before = engine.function_pointers.borrow().len();
    engine
        .function_pointers
        .borrow_mut()
        .resize(510, Target::Opaque { signature });
    let fresh = engine.fresh(Sort::BitVec(bits));
    let fresh_index = Value::Int {
        expression: fresh.clone(),
        bits,
        signed: false,
    };
    let bound = engine
        .terms
        .apply(
            Op::BvUnsignedLt,
            &[fresh, engine.terms.bit_vector(2, bits).unwrap()],
        )
        .unwrap();
    assert!(
        engine
            .capture_function_table(original, &pointers, &fresh_index, &[bound])
            .is_err()
    );
    assert_eq!(engine.function_pointers.borrow().len(), 510);
    assert!(before < 510);
}
