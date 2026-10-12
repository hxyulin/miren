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
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "#[inline(never)] pub fn unavailable(value: u16) -> u16 { value }\n",
        ),
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
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
    let mut engine = test_engine(tcx);

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
        flow: activation_flow::Flow::Unarmed,
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
        flow: activation_flow::Flow::Unarmed,
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
        flow: activation_flow::Flow::Unarmed,
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
    let mut incompatible = returns[0].1.conditions.clone();
    incompatible.extend(returns[1].1.conditions.iter().cloned());
    assert!(!engine.feasible(&incompatible).unwrap());
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
        flow: activation_flow::Flow::Unarmed,
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

pub(super) fn test_engine(tcx: TyCtxt<'_>) -> Engine<'_> {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    Engine {
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
    }
}

struct TwoArgumentOverride(bool);
impl TwoArgumentOverride {
    fn new() -> Self {
        Self(TWO_ARGUMENT_TABLE_OVERRIDE.with(|flag| flag.replace(true)))
    }
}
impl Drop for TwoArgumentOverride {
    fn drop(&mut self) {
        TWO_ARGUMENT_TABLE_OVERRIDE.with(|flag| flag.set(self.0));
    }
}

#[test]
fn two_argument_override_restores_actual_cell() {
    assert!(!TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get));
    {
        let _outer = TwoArgumentOverride::new();
        assert!(TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get));
        {
            let _inner = TwoArgumentOverride::new();
            assert!(two_argument_tables_enabled());
        }
        assert!(TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get));
    }
    assert!(!TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get));
    let panic = std::panic::catch_unwind(|| {
        let _scope = TwoArgumentOverride::new();
        panic!("restore override");
    });
    assert!(panic.is_err());
    assert!(!TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get));
}

#[test]
fn compiler_two_argument_integer_prepared_calls() {
    struct Capture(std::path::PathBuf);
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check_two_argument_calls(tcx, &self.0);
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "miren-two-argument-tcx-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    eprintln!("two-argument compiler assets: {}", root.display());
    let source = root.join("fixture.rs");
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
extern crate alloc;
#[inline(never)] pub fn first(a: u16, b: i32) -> i64 { (a as i64) + (b as i64) }
#[inline(never)] pub fn second(a: u16, b: i32) -> i64 { (a as i64) - (b as i64) }
#[inline(never)] pub fn allocated(a: u16, b: i32) -> i64 {
    let owned = alloc::boxed::Box::new(());
    core::mem::drop(owned);
    (a as i64) + (b as i64)
}
#[inline(never)] pub fn wrong_a(a: i16, b: i32) -> i64 { (a as i64) + (b as i64) }
#[inline(never)] pub fn wrong_b(a: u16, b: u32) -> i64 { (a as i64) + (b as i64) }
#[inline(never)] pub fn wrong_r(a: u16, b: i32) -> u64 { (a as u64) + (b as u64) }
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved(callback: fn(u16, i32)->i64, a: u16, b: i32) -> i64 {
    mir! {
        { Call(RET = Move(callback)(Move(a), Move(b)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn copied(callback: fn(u16, i32)->i64, record: (u16, i32)) -> i64 {
    mir! {
        { Call(RET = Move(callback)(record.0, record.1), ReturnTo(done), UnwindUnreachable()) }
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
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture(output));
        }
    }
}

fn check_two_argument_calls<'tcx>(tcx: TyCtxt<'tcx>, output: &std::path::Path) {
    let mut engine = test_engine(tcx);
    let find = |name: &str| {
        tcx.mir_keys(())
            .iter()
            .map(|id| id.to_def_id())
            .find(|id| tcx.def_kind(*id) == DefKind::Fn && tcx.item_name(*id).as_str() == name)
            .unwrap()
    };
    for name in [
        "first",
        "second",
        "allocated",
        "wrong_a",
        "wrong_b",
        "wrong_r",
        "moved",
        "copied",
    ] {
        let body = tcx.optimized_mir(find(name).expect_local());
        std::fs::write(output.join(format!("{name}.mir.txt")), format!("{body:#?}")).unwrap();
    }
    for name in ["moved", "copied"] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        let (block, data) = body
            .basic_blocks
            .iter_enumerated()
            .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
            .unwrap();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &data.terminator().kind
        else {
            panic!("missing actual Call");
        };
        let signature = func.ty(&body.local_decls, tcx);
        let integer = engine.two_argument_integer_signature(signature).unwrap();
        assert_eq!(integer.first.original, tcx.types.u16);
        assert_eq!(integer.second.original, tcx.types.i32);
        assert_eq!(integer.result.original, tcx.types.i64);
        assert_eq!(
            engine.table_signature(signature),
            ENABLE_TWO_ARGUMENT_INTEGER_FUNCTION_TABLES
        );
        let _scope = TwoArgumentOverride::new();
        assert!(engine.table_signature(signature));
        let mut pointers = Vec::new();
        for helper in ["first", "second"] {
            let instance = engine
                .resolve_function_item(find(helper), tcx.mk_args(&[]))
                .unwrap();
            let id = engine
                .register_function_pointer(Target::Known {
                    instance,
                    signature,
                })
                .unwrap();
            pointers.push(Value::FunctionPointer { id });
        }
        for helper in ["wrong_a", "wrong_b", "wrong_r"] {
            let instance = engine
                .resolve_function_item(find(helper), tcx.mk_args(&[]))
                .unwrap();
            let id = engine
                .register_function_pointer(Target::Known {
                    instance,
                    signature,
                })
                .unwrap();
            assert!(engine.validate_table_target(id, signature).is_err());
        }
        let bits = u32::from(tcx.sess.target.pointer_width);
        let raw = engine.fresh(Sort::BitVec(bits));
        let index = Value::Int {
            expression: raw.clone(),
            bits,
            signed: false,
        };
        let condition = engine
            .terms
            .apply(
                Op::BvUnsignedLt,
                &[raw, engine.terms.bit_vector(2, bits).unwrap()],
            )
            .unwrap();
        let conditions = vec![condition];
        let original = Ty::new_array(tcx, signature, 2);
        let pointer = engine
            .capture_function_table(original, &pointers, &index, &conditions)
            .unwrap()
            .unwrap();
        let Operand::Move(function) = func else {
            panic!("Move func");
        };
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            addresses: vec![None; body.local_decls.len()],
            missing_places: Default::default(),
            memory: Default::default(),
            conditions,
        };
        state.locals[function.local.as_usize()] = Some(pointer);
        let first = symbolic::integer(&engine.terms, 129, 16, false);
        let second = symbolic::integer(&engine.terms, 7, 32, true);
        if name == "moved" {
            for (arg, value) in args.iter().zip([first, second]) {
                let Operand::Move(place) = arg.node else {
                    panic!("Move arg");
                };
                state.locals[place.local.as_usize()] = Some(value);
            }
        } else {
            let Operand::Copy(place) = args[0].node else {
                panic!("Copy field");
            };
            state.locals[place.local.as_usize()] = Some(Value::Tuple(vec![first, second]));
        }
        let make_call = || TableCall {
            body: &body,
            block,
            func,
            args,
            destination: *destination,
            target: *target,
            stack: &[],
            site: (body.source.def_id(), data.terminator().source_info.span),
        };
        let returns = engine
            .prepared_function_table_call(&state, make_call())
            .unwrap()
            .unwrap();
        assert_eq!(returns.len(), 2);
        let mut incompatible = returns[0].1.conditions.clone();
        incompatible.extend(returns[1].1.conditions.iter().cloned());
        assert!(!engine.feasible(&incompatible).unwrap());
        for (position, (consumed, result)) in returns.iter().enumerate() {
            assert!(
                engine
                    .operand(body.source.def_id(), &body, consumed, func)
                    .is_err()
            );
            let expected = symbolic::integer(
                &engine.terms,
                if position == 0 { 136 } else { 122 },
                64,
                true,
            );
            let wrong = symbolic::binary(&engine.terms, "ne", result.value.clone(), expected)
                .unwrap()
                .boolean()
                .unwrap();
            let mut conditions = result.conditions.clone();
            conditions.push(wrong);
            assert!(!engine.feasible(&conditions).unwrap());
            if name == "moved" {
                for arg in args.iter() {
                    let Operand::Move(place) = arg.node else {
                        panic!("Move arg");
                    };
                    assert!(
                        engine
                            .operand(body.source.def_id(), &body, consumed, &arg.node)
                            .is_err()
                    );
                    assert!(state.locals[place.local.as_usize()].is_some());
                }
            }
        }
        let allocated_instance = engine
            .resolve_function_item(find("allocated"), tcx.mk_args(&[]))
            .unwrap();
        let allocated_id = engine
            .register_function_pointer(Target::Known {
                instance: allocated_instance,
                signature,
            })
            .unwrap();
        let allocated_choice = engine
            .capture_function_table(
                original,
                &[
                    Value::FunctionPointer { id: allocated_id },
                    pointers[1].clone(),
                ],
                &index,
                &state.conditions,
            )
            .unwrap()
            .unwrap();
        let mut allocation_state = state.clone();
        allocation_state.locals[function.local.as_usize()] = Some(allocated_choice);
        let allocation_returns = engine
            .function_table_call(&allocation_state, make_call())
            .unwrap()
            .unwrap();
        assert!(!allocation_returns[0].1.memory.owned_regions.is_empty());
        assert!(
            allocation_returns[0]
                .1
                .memory
                .owned_regions
                .iter()
                .all(|region| !region.live)
        );
        assert!(allocation_returns[1].1.memory.owned_regions.is_empty());
        assert!(allocation_state.memory.owned_regions.is_empty());
        std::fs::write(
            output.join(format!("{name}-body-entries.txt")),
            format!("{:#?}", engine.proof.body_entries),
        )
        .unwrap();
        let foreign = Context::default();
        for bad in [
            symbolic::integer(&engine.terms, 1, 32, false),
            symbolic::integer(&engine.terms, 1, 16, true),
            Value::Int {
                expression: foreign.bit_vector(1, 16).unwrap(),
                bits: 16,
                signed: false,
            },
            Value::Unit,
        ] {
            let mut invalid = state.clone();
            let (Operand::Copy(place) | Operand::Move(place)) = args[0].node else {
                panic!("place argument");
            };
            if name == "moved" {
                invalid.locals[place.local.as_usize()] = Some(bad);
            } else {
                invalid.locals[place.local.as_usize()] = Some(Value::Tuple(vec![
                    bad,
                    symbolic::integer(&engine.terms, 7, 32, true),
                ]));
            }
            assert!(engine.function_table_call(&invalid, make_call()).is_err());
            assert!(
                engine
                    .operand(body.source.def_id(), &body, &state, func)
                    .is_ok()
            );
        }
        for bad in [
            symbolic::integer(&engine.terms, 1, 32, true),
            symbolic::integer(&engine.terms, 1, 64, false),
            Value::Int {
                expression: foreign.bit_vector(1, 64).unwrap(),
                bits: 64,
                signed: true,
            },
            Value::Unit,
        ] {
            assert!(engine.validate_table_result(&bad, integer.result).is_err());
        }
        let mut missing = state.clone();
        let (Operand::Copy(place) | Operand::Move(place)) = args[0].node else {
            panic!("place arg");
        };
        missing.locals[place.local.as_usize()] = None;
        assert!(
            engine
                .prepared_function_table_call(&missing, make_call())
                .is_err()
        );
        let mut forged = body.as_ref().clone();
        let local = match args[1].node {
            Operand::Copy(p) | Operand::Move(p) => p.local,
            _ => panic!("place arg"),
        };
        if name == "moved" {
            forged.local_decls[local].ty = tcx.types.u32;
        } else {
            forged.local_decls[local].ty = Ty::new_tup(tcx, &[tcx.types.u16, tcx.types.u32]);
        }
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &forged.basic_blocks[block].terminator().kind
        else {
            panic!("Call");
        };
        assert!(
            engine
                .prepared_function_table_call(
                    &state,
                    TableCall {
                        body: &forged,
                        block,
                        func,
                        args,
                        destination: *destination,
                        target: *target,
                        stack: &[],
                        site: (
                            forged.source.def_id(),
                            forged.basic_blocks[block].terminator().source_info.span
                        ),
                    }
                )
                .is_err()
        );
    }
}

#[test]
fn compiler_known_pointer_repeat_authenticates_cached_assignments() {
    struct Capture(std::path::PathBuf);
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check_known_repeats(tcx, &self.0);
            rustc_driver::Compilation::Stop
        }
    }
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("miren-known-repeat-{}-{stamp}", std::process::id(),));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("fixture.rs");
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn identity(value: u16) -> u16 { value }
#[inline(never)] pub fn boolean(value: bool) -> bool { value }
#[inline(never)] pub fn character(value: char) -> char { value }
#[inline(never)] pub fn floating32(value: f32) -> f32 { value }
#[inline(never)] pub fn floating64(value: f64) -> f64 { value }
pub fn float32_twice(value: fn(f32)->f32) -> [fn(f32)->f32;2] { [value;2] }
pub fn float64_twice(value: fn(f64)->f64) -> [fn(f64)->f64;2] { [value;2] }
pub fn mixed_float(value: f32) -> f64 { value as f64 }

pub fn bool_twice(value: fn(bool)->bool) -> [fn(bool)->bool;2] { [value;2] }
pub fn char_twice(value: fn(char)->char) -> [fn(char)->char;2] { [value;2] }
#[inline(never)] pub fn binary(a: u16, b: i32) -> i64 { (a as i64) - (b as i64) }
#[inline(never)] pub fn generic<T: Copy>(value: T) -> T { value }
pub fn result_bool(_: u16) -> bool { true }
pub fn result_char(_: u16) -> char { 'A' }
pub fn result_float(_: u16) -> f32 { 0.0 }
pub fn over_arity(_: u16, _: u16, _: u16) -> u16 { 0 }
pub extern "C" fn foreign(value: u16) -> u16 { value }
pub struct Holder<T> { pub callback: T }
pub fn record(value: Holder<fn(u16)->u16>) -> [fn(u16)->u16;2] { [value.callback;2] }
pub fn twice(value: fn(u16)->u16) -> [fn(u16)->u16;2] { [value;2] }
pub fn generic_repeat<T: Copy>(_: T, value: fn(u16)->u16) -> [fn(u16)->u16;2] { [value;2] }
pub fn once(value: fn(u16)->u16) -> [fn(u16)->u16;1] { [value;1] }
pub fn sixteen(value: fn(u16)->u16) -> [fn(u16)->u16;16] { [value;16] }
pub fn large(value: fn(u16)->u16) -> [fn(u16)->u16;128] { [value;128] }
pub fn too_large(value: fn(u16)->u16) -> [fn(u16)->u16;129] { [value;129] }
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture(output));
        }
    }
    // Retain source/MIR/control assets in this exclusive invocation directory for association.
    println!("known Repeat compiler assets: {}", root.display());
}

fn repeat_state(body: &Body<'_>) -> State {
    State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        conditions: Vec::new(),
        addresses: vec![None; body.local_decls.len()],
        memory: Default::default(),
    }
}

fn check_known_repeats<'tcx>(tcx: TyCtxt<'tcx>, output: &std::path::Path) {
    use super::super::aggregates::RepeatWork;
    let mut engine = test_engine(tcx);
    let find = |name: &str| {
        tcx.mir_keys(())
            .iter()
            .map(|id| id.to_def_id())
            .find(|id| tcx.def_kind(*id) == DefKind::Fn && tcx.item_name(*id).as_str() == name)
            .unwrap()
    };
    let mut observations = Vec::new();
    for name in [
        "once",
        "twice",
        "sixteen",
        "large",
        "too_large",
        "bool_twice",
        "char_twice",
        "float32_twice",
        "float64_twice",
    ] {
        let definition = find(name);
        let instance = engine
            .resolve_function_item(definition, tcx.mk_args(&[]))
            .unwrap();
        let original = engine.instantiated_body(instance).unwrap();
        std::fs::write(output.join(format!("{name}.mir")), format!("{original:#?}")).unwrap();
        let (block, position) = original
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                data.statements
                    .iter()
                    .position(|statement| {
                        matches!(&statement.kind,
                StatementKind::Assign(pair) if matches!(pair.1, Rvalue::Repeat(..)))
                    })
                    .map(|position| (block, position))
            })
            .expect("actual unoptimized compiler Repeat");
        let StatementKind::Assign(pair) = &original.basic_blocks[block].statements[position].kind
        else {
            panic!("actual Assign");
        };
        let Rvalue::Repeat(operand, _) = &pair.1 else {
            panic!("actual Repeat");
        };
        let (Operand::Copy(source) | Operand::Move(source)) = operand else {
            panic!("actual local Repeat operand");
        };
        let signature = original.local_decls[source.local].ty;
        let helper = match name {
            "bool_twice" => "boolean",
            "char_twice" => "character",
            "float32_twice" => "floating32",
            "float64_twice" => "floating64",
            _ => "identity",
        };
        let selected = engine
            .resolve_function_item(find(helper), tcx.mk_args(&[]))
            .unwrap();
        let token = engine
            .register_function_pointer(Target::Known {
                instance: selected,
                signature,
            })
            .unwrap();
        let mut state = repeat_state(&original);
        state.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: token });
        let registry = engine.function_pointers.borrow().len();
        let actual = engine.known_repeat_assignment(
            instance,
            &original,
            &mut state,
            pair.0,
            &pair.1,
            &original.basic_blocks[block].statements[position].kind,
        );
        if name == "too_large" {
            assert!(actual.is_err());
            assert!(state.missing_places.is_empty());
        } else {
            let Value::Elements(values) = actual.unwrap().unwrap() else {
                panic!("Elements");
            };
            let count = match name {
                "once" => 1,
                "twice" | "bool_twice" | "char_twice" | "float32_twice" | "float64_twice" => 2,
                "sixteen" => 16,
                "large" => 128,
                "too_large" => unreachable!(),
                _ => unreachable!(),
            };
            assert_eq!(values.len(), count);
            assert!(
                values.iter().all(|value| {
                    matches!(value, Value::FunctionPointer { id } if *id == token)
                })
            );
        }
        assert!(state.locals[pair.0.local.as_usize()].is_none());
        assert_eq!(registry, engine.function_pointers.borrow().len());
        let detached = original.as_ref().clone();
        let before = engine.call_signatures.borrow().len();
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &detached,
                    &mut state,
                    pair.0,
                    &pair.1,
                    &original.basic_blocks[block].statements[position].kind
                )
                .is_err()
        );
        let detached_statement = original.basic_blocks[block].statements[position]
            .kind
            .clone();
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &original,
                    &mut state,
                    pair.0,
                    &pair.1,
                    &detached_statement
                )
                .is_err()
        );
        assert_eq!(before, engine.call_signatures.borrow().len());
        observations.push(format!(
            "{name}: actual Repeat/cached identity/refusal controls"
        ));
        if !matches!(
            name,
            "twice" | "bool_twice" | "char_twice" | "float32_twice" | "float64_twice"
        ) {
            continue;
        }
        for count in [0, 1, 16, 128, 129] {
            // Deliberate cached-MIR Move mutation, separate from safe compiler lowering.
            let mut changed = original.as_ref().clone();
            let array = Ty::new_array(tcx, signature, count);
            changed.local_decls[pair.0.local].ty = array;
            let ty::Array(_, length) = array.kind() else {
                unreachable!()
            };
            let StatementKind::Assign(assignment) =
                &mut changed.basic_blocks_mut()[block].statements[position].kind
            else {
                unreachable!()
            };
            assignment.1 = Rvalue::Repeat(Operand::Move(*source), *length);
            let changed = std::rc::Rc::new(changed);
            engine.bodies.borrow_mut().insert(instance, changed.clone());
            let statement = &changed.basic_blocks[block].statements[position].kind;
            let StatementKind::Assign(assignment) = statement else {
                unreachable!()
            };
            let mut moved = repeat_state(&changed);
            moved.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: token });
            let result = engine.known_repeat_assignment(
                instance,
                &changed,
                &mut moved,
                assignment.0,
                &assignment.1,
                statement,
            );
            if count <= 128 {
                assert!(result.is_ok());
                assert!(!moved.missing_places.is_empty());
                // A second operand evaluation would fail this consumed Move.
                assert!(
                    engine
                        .known_repeat_assignment(
                            instance,
                            &changed,
                            &mut moved,
                            assignment.0,
                            &assignment.1,
                            statement
                        )
                        .is_err()
                );
            } else {
                assert!(result.is_err());
                assert!(moved.missing_places.is_empty());
            }
            if count == 0 {
                let opaque = engine
                    .register_function_pointer(Target::Opaque { signature })
                    .unwrap();
                let mut bad = repeat_state(&changed);
                bad.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: opaque });
                let cache = engine.call_signatures.borrow().len();
                assert!(
                    engine
                        .known_repeat_assignment(
                            instance,
                            &changed,
                            &mut bad,
                            assignment.0,
                            &assignment.1,
                            statement
                        )
                        .is_err()
                );
                assert!(!bad.missing_places.is_empty());
                assert!(bad.locals[assignment.0.local.as_usize()].is_none());
                assert_eq!(cache, engine.call_signatures.borrow().len());
                observations.push("post-evaluation target refusal preserves zero Move".into());
            }
            assert!(moved.locals[assignment.0.local.as_usize()].is_none());
            observations.push(format!(
                "cached Move count{count}: consumed once iff admitted"
            ));
        }
        engine
            .bodies
            .borrow_mut()
            .insert(instance, original.clone());
        let mut missing = repeat_state(&original);
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &original,
                    &mut missing,
                    pair.0,
                    &pair.1,
                    &original.basic_blocks[block].statements[position].kind
                )
                .is_err()
        );
        let mut stale = repeat_state(&original);
        stale.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: usize::MAX });
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &original,
                    &mut stale,
                    pair.0,
                    &pair.1,
                    &original.basic_blocks[block].statements[position].kind
                )
                .is_err()
        );
        let opaque = engine
            .register_function_pointer(Target::Opaque { signature })
            .unwrap();
        stale.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: opaque });
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &original,
                    &mut stale,
                    pair.0,
                    &pair.1,
                    &original.basic_blocks[block].statements[position].kind
                )
                .is_err()
        );
        let wrong = engine
            .resolve_function_item(
                find(if name == "float32_twice" {
                    "mixed_float"
                } else {
                    "binary"
                }),
                tcx.mk_args(&[]),
            )
            .unwrap();
        let wrong = engine
            .register_function_pointer(Target::Known {
                instance: wrong,
                signature,
            })
            .unwrap();
        stale.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: wrong });
        let signatures = engine.call_signatures.borrow().len();
        assert!(
            engine
                .known_repeat_assignment(
                    instance,
                    &original,
                    &mut stale,
                    pair.0,
                    &pair.1,
                    &original.basic_blocks[block].statements[position].kind
                )
                .is_err()
        );
        assert_eq!(signatures, engine.call_signatures.borrow().len());
        observations.push("missing/stale/opaque/wrong-signature refusal".into());
    }
    let record_instance = engine
        .resolve_function_item(find("record"), tcx.mk_args(&[]))
        .unwrap();
    let record = engine.instantiated_body(record_instance).unwrap();
    let holder = record
        .local_decls
        .iter_enumerated()
        .find_map(|(local, declaration)| {
            matches!(declaration.ty.kind(), ty::Adt(..)).then_some(local)
        })
        .unwrap();
    let ty::Adt(def, args) = record.local_decls[holder].ty.kind() else {
        unreachable!()
    };
    let signature = def
        .non_enum_variant()
        .fields
        .iter()
        .next()
        .unwrap()
        .ty(tcx, args)
        .skip_norm_wip();
    let field = Place {
        local: holder,
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(0usize.into(), signature)]),
    };
    assert_eq!(
        engine
            .repeat_place_type(&record, field, &mut RepeatWork::new())
            .unwrap(),
        signature,
    );
    let forged = Place {
        local: holder,
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(0usize.into(), tcx.types.u32)]),
    };
    assert!(
        engine
            .repeat_place_type(&record, forged, &mut RepeatWork::new())
            .is_err()
    );
    let mut disguised = record.as_ref().clone();
    disguised.local_decls[holder].ty = Ty::new_adt(tcx, *def, tcx.mk_args(&[tcx.types.u32.into()]));
    assert!(
        engine
            .repeat_place_type(&disguised, field, &mut RepeatWork::new())
            .is_err()
    );
    let mut deep = tcx.types.u16;
    for _ in 0..MAX_INPUT_DEPTH {
        deep = Ty::new_tup(tcx, &[deep]);
    }
    assert!(
        engine
            .repeat_type_work(deep, tcx.mk_args(&[]), 0, &mut RepeatWork::new())
            .is_err()
    );
    let wide = Ty::new_tup(tcx, &vec![tcx.types.u16; MAX_INPUT_VALUES + 1]);
    assert!(
        engine
            .repeat_type_work(wide, tcx.mk_args(&[]), 0, &mut RepeatWork::new())
            .is_err()
    );
    assert!(
        engine
            .repeat_charge(&mut RepeatWork::new(), MAX_INPUT_VALUES + 1)
            .is_err()
    );
    let generic = find("generic");
    for original in [tcx.types.u16, tcx.types.u32, deep, wide] {
        let instance = ty::Instance::new_raw(generic, tcx.mk_args(&[original.into()]));
        let token = engine
            .register_function_pointer(Target::Known {
                instance,
                signature,
            })
            .unwrap();
        let cache = engine.call_signatures.borrow().len();
        let result = engine.validate_repeat_target(
            &Value::FunctionPointer { id: token },
            signature,
            &mut RepeatWork::new(),
        );
        if original == tcx.types.u16 {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
            assert_eq!(cache, engine.call_signatures.borrow().len());
        }
    }
    for name in [
        "result_bool",
        "result_char",
        "result_float",
        "over_arity",
        "foreign",
    ] {
        let raw = tcx
            .fn_sig(find(name))
            .instantiate_identity()
            .skip_norm_wip();
        let original = Ty::new_fn_ptr(tcx, raw);
        assert!(
            engine
                .repeat_type_work(original, tcx.mk_args(&[]), 0, &mut RepeatWork::new())
                .is_err()
        );
    }
    let raw = tcx
        .fn_sig(find("identity"))
        .instantiate_identity()
        .skip_norm_wip();
    let unsafe_signature = Ty::new_fn_ptr(
        tcx,
        raw.map_bound(|signature| signature.set_safety(rustc_hir::Safety::Unsafe)),
    );
    assert!(
        engine
            .repeat_type_work(
                unsafe_signature,
                tcx.mk_args(&[]),
                0,
                &mut RepeatWork::new()
            )
            .is_err()
    );
    // Same cached body under a different full key is ambiguous, never a fresh authority.
    let alias = ty::Instance::new_raw(
        record_instance.def_id(),
        tcx.mk_args(&[tcx.types.u16.into()]),
    );
    engine.bodies.borrow_mut().insert(alias, record.clone());
    let twice = engine
        .resolve_function_item(find("twice"), tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(twice).unwrap();
    let statement = body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find(|statement| {
            matches!(&statement.kind, StatementKind::Assign(pair)
            if matches!(pair.1, Rvalue::Repeat(..)))
        })
        .unwrap();
    let StatementKind::Assign(pair) = &statement.kind else {
        unreachable!()
    };
    let alias = ty::Instance::new_raw(twice.def_id(), tcx.mk_args(&[tcx.types.u16.into()]));
    engine.bodies.borrow_mut().insert(alias, body.clone());
    let mut state = repeat_state(&body);
    assert!(
        engine
            .known_repeat_assignment(twice, &body, &mut state, pair.0, &pair.1, &statement.kind)
            .is_err()
    );
    engine.bodies.borrow_mut().remove(&alias);
    let Rvalue::Repeat(operand, _) = &pair.1 else {
        unreachable!()
    };
    let (Operand::Copy(source) | Operand::Move(source)) = operand else {
        unreachable!()
    };
    let selected = engine
        .resolve_function_item(find("identity"), tcx.mk_args(&[]))
        .unwrap();
    let token = engine
        .register_function_pointer(Target::Known {
            instance: selected,
            signature,
        })
        .unwrap();
    state.locals[source.local.as_usize()] = Some(Value::FunctionPointer { id: token });
    // Remove the authenticated key: a sole same-DefId substitute must still refuse.
    engine.bodies.borrow_mut().remove(&twice);
    engine.bodies.borrow_mut().insert(alias, body.clone());
    let before = engine.call_signatures.borrow().len();
    assert!(
        engine
            .known_repeat_assignment(twice, &body, &mut state, pair.0, &pair.1, &statement.kind)
            .is_err()
    );
    assert!(state.missing_places.is_empty());
    assert!(state.locals[pair.0.local.as_usize()].is_none());
    assert_eq!(before, engine.call_signatures.borrow().len());
    engine.bodies.borrow_mut().remove(&alias);
    engine.bodies.borrow_mut().insert(twice, body.clone());
    let generic_owner = engine
        .resolve_function_item(find("generic_repeat"), tcx.mk_args(&[tcx.types.u16.into()]))
        .unwrap();
    let selected = engine
        .resolve_function_item(find("identity"), tcx.mk_args(&[]))
        .unwrap();
    let token = engine
        .register_function_pointer(Target::Known {
            instance: selected,
            signature,
        })
        .unwrap();
    let returns = engine
        .execute_body(
            generic_owner,
            vec![
                symbolic::integer(&engine.terms, 0, 16, false),
                Value::FunctionPointer { id: token },
            ],
            Vec::new(),
            Memory::default(),
            &[],
            activation_flow::Flow::Unarmed,
        )
        .unwrap();
    assert_eq!(returns.len(), 1);
    assert!(matches!(&returns[0].value, Value::Elements(values) if values.len() == 2));
    observations.push("sole substituted-key refusal/full generic execute_body positive".into());
    observations.push("raw ADT Param/forged FieldTy/depth/work/pre-normalization/full-key".into());
    let selected = engine
        .resolve_function_item(find("identity"), tcx.mk_args(&[]))
        .unwrap();
    let known = Target::Known {
        instance: selected,
        signature,
    };
    let choice = Choice {
        original: Ty::new_array(tcx, signature, 2),
        signature,
        index: symbolic::integer(
            &engine.terms,
            0,
            tcx.sess.target.pointer_width.into(),
            false,
        )
        .integer()
        .unwrap()
        .0
        .clone(),
        targets: vec![0, 0],
    };
    let choice = engine
        .register_function_pointer(Target::Choice(choice))
        .unwrap();
    assert!(
        engine
            .validate_repeat_target(
                &Value::FunctionPointer { id: choice },
                signature,
                &mut RepeatWork::new()
            )
            .is_err()
    );
    // Direct cached-registry fault setup, not a claim that safe source naturally fills it.
    *engine.function_pointers.borrow_mut() = vec![known; 512];
    let binary = tcx
        .fn_sig(find("binary"))
        .instantiate_identity()
        .skip_norm_wip();
    assert!(
        engine
            .register_function_pointer(Target::Opaque {
                signature: Ty::new_fn_ptr(tcx, binary),
            })
            .is_err()
    );
    assert!(
        engine
            .validate_repeat_target(
                &Value::FunctionPointer { id: 0 },
                signature,
                &mut RepeatWork::new()
            )
            .is_ok()
    );
    assert_eq!(engine.function_pointers.borrow().len(), 512);
    assert_eq!(super::super::aggregates::known_repeat_cost(0), Some(2));
    assert_eq!(super::super::aggregates::known_repeat_cost(128), Some(129));
    assert_eq!(
        super::super::aggregates::known_repeat_cost(usize::MAX),
        None
    );
    observations.push("Choice/full registry/checked-cost fault; no natural cost exhaustion".into());
    std::fs::write(output.join("controls.txt"), observations.join("\n")).unwrap();
}

#[test]
fn compiler_primitive_table_borrowed_body_and_values() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = test_engine(tcx);
            for name in ["bool_first", "bool_second", "char_first", "char_second"] {
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap()
                    .to_def_id();
                let instance = engine.resolve_function_item(id, tcx.mk_args(&[])).unwrap();
                let mut work = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: 0,
                };
                let body = tcx.optimized_mir(id);
                let result = engine.primitive_table_body_work(instance, body, &mut work);
                assert!(result.is_ok(), "{name}: {result:?}");
                let mut forged_return = body.clone();
                forged_return.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.u32;
                let mut forged_work = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, &forged_return, &mut forged_work)
                        .is_err()
                );
                let other = Context::default();
                let foreign_bool = Value::Bool(other.boolean(true));
                assert!(
                    engine
                        .validate_primitive_table_value(
                            &foreign_bool,
                            PrimitiveSignature::Bool(tcx.types.bool),
                            &[]
                        )
                        .is_err()
                );
                let foreign_char = symbolic::integer(&other, 65, 32, false);
                assert!(
                    engine
                        .validate_primitive_table_value(
                            &foreign_char,
                            PrimitiveSignature::Char(tcx.types.char),
                            &[]
                        )
                        .is_err()
                );
                let mut wrong = body.clone();
                wrong.spread_arg = Some(rustc_middle::mir::Local::from_usize(1));
                let mut bounded = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, &wrong, &mut bounded)
                        .is_err()
                );
                let mut exhausted = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: MAX_INPUT_VALUES,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, body, &mut exhausted)
                        .is_err()
                );
                let before = engine.bodies.borrow().len();
                let mut unsupported = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: body.local_decls.len(),
                };
                unsupported.original_type(
                    Ty::new_ref(
                        tcx,
                        tcx.lifetimes.re_erased,
                        tcx.types.char,
                        rustc_hir::Mutability::Not,
                    ),
                    0,
                );
                assert!(unsupported.error.is_some());
                assert_eq!(engine.bodies.borrow().len(), before);
                let mut too_deep = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: 0,
                };
                too_deep.original_type(tcx.types.char, MAX_INPUT_DEPTH);
                assert!(too_deep.error.is_some());
                let bool_value = Value::Bool(engine.terms.boolean(true));
                assert!(
                    engine
                        .validate_primitive_table_value(
                            &bool_value,
                            PrimitiveSignature::Bool(tcx.types.bool),
                            &[]
                        )
                        .is_ok()
                );
                let wrong_bool = symbolic::integer(&engine.terms, 1, 1, false);
                assert!(
                    engine
                        .validate_primitive_table_value(
                            &wrong_bool,
                            PrimitiveSignature::Bool(tcx.types.bool),
                            &[]
                        )
                        .is_err()
                );
                for raw in [0, 0xd7ff, 0xe000, 0x10ffff] {
                    let value = symbolic::integer(&engine.terms, raw, 32, false);
                    assert!(
                        engine
                            .validate_primitive_table_value(
                                &value,
                                PrimitiveSignature::Char(tcx.types.char),
                                &[]
                            )
                            .is_ok()
                    );
                }
                for raw in [0xd800, 0xdfff, 0x110000] {
                    let value = symbolic::integer(&engine.terms, raw, 32, false);
                    assert!(
                        engine
                            .validate_primitive_table_value(
                                &value,
                                PrimitiveSignature::Char(tcx.types.char),
                                &[]
                            )
                            .is_err()
                    );
                }
            }
            check_primitive_move_call(
                tcx,
                "moved_bool",
                "bool_first",
                "bool_second",
                PrimitiveProbeValue::Bool,
            );
            check_primitive_move_call(
                tcx,
                "moved_char",
                "char_first",
                "char_second",
                PrimitiveProbeValue::Char,
            );
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "miren-primitive-table-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    std::fs::copy(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/primitive_function_tables.rs"),
        &source,
    )
    .unwrap();
    let original = std::fs::read_to_string(&source).unwrap();
    std::fs::write(
        &source,
        format!(
            "#![feature(custom_mir, core_intrinsics)]\n{original}\n{}",
            r#"
use core::intrinsics::mir::*;
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved_bool(callback: fn(bool)->bool, value: bool) -> bool {
    mir! {
        { Call(RET = Move(callback)(Move(value)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved_char(callback: fn(char)->char, value: char) -> char {
    mir! {
        { Call(RET = Move(callback)(Move(value)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
"#
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir_all(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture);
        }
    }
    eprintln!("primitive compiler assets: {}", root.display());
}

#[derive(Clone, Copy)]
enum PrimitiveProbeValue {
    Bool,
    Char,
    Float32,
    Float64,
}

// Separate generated custom-MIR boundary controls, not ordinary application lowering claims.
fn check_primitive_move_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: &str,
    first: &str,
    second: &str,
    kind: PrimitiveProbeValue,
) {
    let mut engine = test_engine(tcx);
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
    let caller_id = find(caller);
    let instance = engine
        .resolve_function_item(caller_id, tcx.mk_args(&[]))
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
    let mut elements = Vec::new();
    let mut signature = None;
    for name in [first, second] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let original = Ty::new_fn_ptr(tcx, engine.call_poly_signature(instance).unwrap());
        signature = Some(original);
        let token = engine
            .register_function_pointer(Target::Known {
                instance,
                signature: original,
            })
            .unwrap();
        elements.push(Value::FunctionPointer { id: token });
    }
    let signature = signature.unwrap();
    assert!(engine.primitive_table_signature(signature).is_some());
    let bits = u32::from(tcx.sess.target.pointer_width);
    let raw_index = engine.fresh(Sort::BitVec(bits));
    let index = Value::Int {
        expression: raw_index.clone(),
        bits,
        signed: false,
    };
    let bound = engine
        .terms
        .apply(
            Op::BvUnsignedLt,
            &[raw_index, engine.terms.bit_vector(2, bits).unwrap()],
        )
        .unwrap();
    let conditions = vec![bound];
    let pointer = engine
        .capture_function_table(
            Ty::new_array(tcx, signature, 2),
            &elements,
            &index,
            &conditions,
        )
        .unwrap()
        .unwrap();
    let Operand::Move(function) = func else {
        panic!("callable Move absent");
    };
    let Operand::Move(argument) = &args[0].node else {
        panic!("argument Move absent");
    };
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        addresses: vec![None; body.local_decls.len()],
        conditions,
        memory: Default::default(),
    };
    state.locals[function.local.as_usize()] = Some(pointer);
    state.locals[argument.local.as_usize()] = Some(match kind {
        PrimitiveProbeValue::Bool => Value::Bool(engine.terms.boolean(true)),
        PrimitiveProbeValue::Char => symbolic::integer(&engine.terms, 65, 32, false),
        PrimitiveProbeValue::Float32 => symbolic::float(&engine.terms, 0x7fc1_2345, 32),
        PrimitiveProbeValue::Float64 => symbolic::float(&engine.terms, 0x7ff8_1234_5678_9abc, 64),
    });
    let stack = [caller_id];
    let call = || TableCall {
        body: &body,
        block,
        func,
        args,
        destination,
        target,
        stack: &stack,
        site: (caller_id, span),
    };
    let captured = engine
        .capture_call_destination(&body, &state, destination)
        .unwrap();
    let Some(Value::FunctionPointer { id: choice_id }) = &state.locals[function.local.as_usize()]
    else {
        unreachable!();
    };
    let choice_id = *choice_id;
    let saved_choice = engine.function_pointers.borrow()[choice_id].clone();
    let Target::Choice(valid_choice) = &saved_choice else {
        unreachable!();
    };
    let mut wrong_signature = valid_choice.clone();
    // An original array mismatch must refuse before the Choice vector is cloned.
    wrong_signature.original = tcx.types.u32;
    engine.function_pointers.borrow_mut()[choice_id] = Target::Choice(wrong_signature);
    let steps_before = engine.steps;
    assert!(engine.function_table_call(&state, call()).is_err());
    assert_eq!(engine.steps, steps_before);
    engine.function_pointers.borrow_mut()[choice_id] = saved_choice;
    if matches!(
        kind,
        PrimitiveProbeValue::Float32 | PrimitiveProbeValue::Float64
    ) {
        struct Restore(FloatTableReturnFault);
        impl Drop for Restore {
            fn drop(&mut self) {
                FLOAT_TABLE_RETURN_FAULT.with(|fault| fault.set(self.0));
            }
        }
        let before = format!(
            "{:?}/{:?}/{:?}/{:?}/{:?}",
            state.locals,
            state.missing_places,
            state.conditions,
            state.addresses,
            state.memory.as_slice()
        );
        for fault in [
            FloatTableReturnFault::WrongWidth,
            FloatTableReturnFault::MissingRaw,
            FloatTableReturnFault::ForeignContext,
            FloatTableReturnFault::InconsistentRaw,
        ] {
            let prior = FLOAT_TABLE_RETURN_FAULT.with(|cell| cell.replace(fault));
            let restore = Restore(prior);
            let observed = FLOAT_TABLE_RETURN_OBSERVATIONS.with(std::cell::Cell::get);
            assert!(engine.function_table_call(&state, call()).is_err());
            assert!(FLOAT_TABLE_RETURN_OBSERVATIONS.with(std::cell::Cell::get) > observed);
            assert_eq!(
                format!(
                    "{:?}/{:?}/{:?}/{:?}/{:?}",
                    state.locals,
                    state.missing_places,
                    state.conditions,
                    state.addresses,
                    state.memory.as_slice()
                ),
                before
            );
            assert!(engine.read_place(&state, destination, Some(&body)).is_err());
            assert!(!state.memory.byte_copy_opaque);
            assert!(state.memory.incoming_byte_roots.is_empty());
            assert!(state.memory.mutable_u16.is_empty());
            assert!(state.memory.mutable_hierarchy.is_none());
            assert!(state.memory.owned_regions.is_empty());
            assert!(state.memory.startup_values.is_empty());
            assert!(!state.memory.startup_invalidated);
            assert!(state.memory.isolated_static_types.is_empty());
            assert!(state.memory.startup_overwritten.is_empty());
            assert!(state.memory.static_uninitialized.is_empty());

            // Valid entry/callee effects may already have happened. Refusal prevents caller
            // continuation/result publication; this does not claim whole-call rollback.
            drop(restore);
            assert!(
                FLOAT_TABLE_RETURN_FAULT.with(std::cell::Cell::get) == FloatTableReturnFault::None
            );
        }
        let caught = std::panic::catch_unwind(|| {
            let prior = FLOAT_TABLE_RETURN_FAULT
                .with(|cell| cell.replace(FloatTableReturnFault::WrongWidth));
            let _restore = Restore(prior);
            panic!("scoped Float Return fault restoration");
        });
        assert!(caught.is_err());
        assert!(FLOAT_TABLE_RETURN_FAULT.with(std::cell::Cell::get) == FloatTableReturnFault::None);
    }
    let returns = engine.function_table_call(&state, call()).unwrap().unwrap();
    assert_eq!(returns.len(), 2);
    let mut joined = returns[0].1.conditions.clone();
    joined.extend(returns[1].1.conditions.iter().cloned());
    assert!(!engine.feasible(&joined).unwrap());
    for (consumed, result) in &returns {
        assert!(engine.operand(caller_id, &body, consumed, func).is_err());
        assert!(
            engine
                .operand(caller_id, &body, consumed, &args[0].node)
                .is_err()
        );
        assert!(result.memory.byte_copy_opaque);
        let mut continuation =
            consumed.continuation(result.conditions.clone(), result.memory.clone());
        engine
            .store_call_result(
                &body,
                &mut continuation,
                destination,
                captured.as_ref(),
                result.value.clone(),
            )
            .unwrap();
        assert!(continuation.memory.byte_copy_opaque);
        assert!(
            engine
                .read_place(&continuation, destination, Some(&body))
                .is_ok()
        );
    }
    assert!(!state.memory.byte_copy_opaque);
    assert!(engine.operand(caller_id, &body, &state, func).is_ok());
    assert!(
        engine
            .operand(caller_id, &body, &state, &args[0].node)
            .is_ok()
    );
    let Value::FunctionPointer { id: first_token } = elements[0] else {
        unreachable!();
    };
    let first_instance = match &engine.function_pointers.borrow()[first_token] {
        Target::Known { instance, .. } => *instance,
        Target::Opaque { .. } | Target::Choice(_) => unreachable!(),
    };
    let saved_body = engine.bodies.borrow().get(&first_instance).unwrap().clone();
    let mut oversized = saved_body.as_ref().clone();
    let declaration = oversized.local_decls[rustc_middle::mir::RETURN_PLACE].clone();
    for _ in 0..MAX_INPUT_VALUES {
        oversized.local_decls.push(declaration.clone());
    }
    engine
        .bodies
        .borrow_mut()
        .insert(first_instance, std::rc::Rc::new(oversized));
    let steps = engine.steps;
    assert!(engine.function_table_call(&state, call()).is_err());
    assert_eq!(engine.steps, steps);
    assert!(engine.operand(caller_id, &body, &state, func).is_ok());
    engine
        .bodies
        .borrow_mut()
        .insert(first_instance, saved_body.clone());
    let mut wrong_return = saved_body.as_ref().clone();
    wrong_return.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.u32;
    engine
        .bodies
        .borrow_mut()
        .insert(first_instance, std::rc::Rc::new(wrong_return));
    assert!(engine.function_table_call(&state, call()).is_err());
    assert_eq!(engine.steps, steps);
    engine
        .bodies
        .borrow_mut()
        .insert(first_instance, saved_body);
    let before = engine.bodies.borrow().len();
    let mut masked = state.clone();
    masked
        .missing_places
        .consume(argument.local.as_usize(), Vec::new())
        .unwrap();
    assert!(engine.function_table_call(&masked, call()).is_err());
    assert_eq!(engine.bodies.borrow().len(), before);
    assert!(
        engine
            .operand(caller_id, &body, &state, &args[0].node)
            .is_ok()
    );
}

#[test]
fn compiler_float_table_original_body_and_representation() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut engine = test_engine(tcx);
            for (name, width, original, signature) in [
                (
                    "first32",
                    32,
                    tcx.types.f32,
                    PrimitiveSignature::Float32(tcx.types.f32),
                ),
                (
                    "second32",
                    32,
                    tcx.types.f32,
                    PrimitiveSignature::Float32(tcx.types.f32),
                ),
                (
                    "first64",
                    64,
                    tcx.types.f64,
                    PrimitiveSignature::Float64(tcx.types.f64),
                ),
                (
                    "second64",
                    64,
                    tcx.types.f64,
                    PrimitiveSignature::Float64(tcx.types.f64),
                ),
            ] {
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap()
                    .to_def_id();
                let instance = engine.resolve_function_item(id, tcx.mk_args(&[])).unwrap();
                let callable = Ty::new_fn_ptr(tcx, engine.call_poly_signature(instance).unwrap());
                assert!(engine.primitive_table_signature(callable) == Some(signature));
                let body = tcx.optimized_mir(id);
                let mut work = PrimitiveBodyWork {
                    engine: &engine,
                    domain: signature.body_domain(),
                    used: 0,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, body, &mut work)
                        .is_ok()
                );
                let mut old_domain = PrimitiveBodyWork {
                    engine: &engine,
                    domain: PrimitiveBodyDomain::BoolChar,
                    used: 0,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, body, &mut old_domain)
                        .is_err()
                );
                let mut forged = body.clone();
                forged.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.u32;
                let mut work = PrimitiveBodyWork {
                    engine: &engine,
                    domain: signature.body_domain(),
                    used: 0,
                    error: None,
                    locals: 0,
                };
                assert!(
                    engine
                        .primitive_table_body_work(instance, &forged, &mut work)
                        .is_err()
                );
                assert!(signature.original() == original);
                let valid = symbolic::float(&engine.terms, 0, width);
                assert!(
                    engine
                        .validate_primitive_table_value(&valid, signature, &[])
                        .is_ok()
                );
                let wrong = symbolic::float(&engine.terms, 0, if width == 32 { 64 } else { 32 });
                assert!(
                    engine
                        .validate_primitive_table_value(&wrong, signature, &[])
                        .is_err()
                );
                let other = Context::default();
                let foreign = symbolic::float(&other, 0, width);
                assert!(
                    engine
                        .validate_primitive_table_value(&foreign, signature, &[])
                        .is_err()
                );
                let Value::Float {
                    expression, bits, ..
                } = valid
                else {
                    unreachable!()
                };
                let absent = Value::Float {
                    expression: expression.clone(),
                    bits,
                    raw_bits: None,
                };
                assert!(
                    engine
                        .validate_primitive_table_value(&absent, signature, &[])
                        .is_err()
                );
                let wrong_raw = Value::Float {
                    expression: expression.clone(),
                    bits,
                    raw_bits: Some(engine.terms.bit_vector(1, width).unwrap()),
                };
                assert!(
                    engine
                        .validate_primitive_table_value(&wrong_raw, signature, &[])
                        .is_err()
                );
                let arithmetic = Value::Float {
                    expression,
                    bits,
                    raw_bits: None,
                };
                let tracked = engine.materialize_float(arithmetic);
                assert!(
                    engine
                        .validate_primitive_table_value(&tracked, signature, &[])
                        .is_ok()
                );
                let saved = engine.float_encodings.clone();
                engine.float_encodings.clear();
                assert!(
                    engine
                        .validate_primitive_table_value(&tracked, signature, &[])
                        .is_err()
                );
                engine.float_encodings = saved;
                // Copied NaNs are transported by actual Values. Decoding alone cannot certify
                // the payload provenance of an arbitrary numerically consistent NaN carrier.
                let nan = symbolic::float(
                    &engine.terms,
                    if width == 32 {
                        0x7fc1_2345
                    } else {
                        0x7ff8_1234_5678_9abc
                    },
                    width,
                );
                assert!(
                    engine
                        .validate_primitive_table_value(&nan, signature, &[])
                        .is_ok()
                );
            }
            check_primitive_move_call(
                tcx,
                "moved32",
                "first32",
                "second32",
                PrimitiveProbeValue::Float32,
            );
            check_primitive_move_call(
                tcx,
                "moved64",
                "first64",
                "second64",
                PrimitiveProbeValue::Float64,
            );
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("miren-float-table-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("fixture.rs");
    let original = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/float_function_tables.rs"),
    )
    .unwrap();
    std::fs::write(
        &source,
        format!(
            "#![feature(custom_mir, core_intrinsics)]\n{original}\n{}",
            r#"
use core::intrinsics::mir::*;
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved32(callback: fn(f32)->f32, value: f32) -> f32 {
    mir! {
        { Call(RET = Move(callback)(Move(value)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved64(callback: fn(f64)->f64, value: f64) -> f64 {
    mir! {
        { Call(RET = Move(callback)(Move(value)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
"#
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture);
        }
    }
    eprintln!("Float table compiler assets: {}", root.display());
}
