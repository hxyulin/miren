use super::*;

const INTEGERS: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

#[test]
fn compiler_integer_function_table_pairs_and_actual_returns() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            for argument in INTEGERS {
                for result in INTEGERS {
                    check_pair(tcx, &format!("{argument}_to_{result}"));
                }
            }
            check_result_refusals(tcx);
            rustc_driver::Compilation::Stop
        }
    }
    let root = std::env::temp_dir().join(format!(
        "miren-integer-function-table-pairs-unit-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    let mut guest = String::from(
        "#![no_std]\n#![feature(custom_mir, core_intrinsics)]\nuse core::intrinsics::mir::*;\n",
    );
    for argument in INTEGERS {
        for result in INTEGERS {
            let name = format!("{argument}_to_{result}");
            guest.push_str(&format!(
                r#"
#[inline(never)] pub fn first_{name}(word: {argument}) -> {result} {{word as {result}}}
#[inline(never)] pub fn second_{name}(word: {argument}) -> {result} {{(word ^ 1) as {result}}}
pub fn selected_{name}(index: usize, word: {argument}) -> {result} {{
    let table: [fn({argument})->{result};2] = [first_{name},second_{name}];
    if index < 2 {{table[index](word)}} else {{word as {result}}}
}}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved_{name}(callback: fn({argument})->{result}, word: {argument}) -> {result} {{
    mir! {{
        {{Call(RET = Move(callback)(Move(word)), ReturnTo(done), UnwindUnreachable())}}
        done = {{Return()}}
    }}
}}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn copied_{name}(callback: fn({argument})->{result}, record: ({argument}, bool))
    -> ({result}, bool) {{
    mir! {{
        let output: ({result}, bool);
        {{Call(output.0 = Move(callback)(record.0), ReturnTo(done), UnwindUnreachable())}}
        done = {{output.1 = true; RET = Move(output); Return()}}
    }}
}}
"#
            ));
        }
    }
    guest.push_str(
        "pub fn result_bool(word: u16) -> bool {word != 0}\n\
         pub fn result_char(_: u16) -> char {'a'}\n\
         pub fn result_float(word: u16) -> f32 {word as f32}\n\
         pub fn result_ref(_: u16) -> &'static u16 {&1}\n\
         pub fn result_nz(word: u16) -> core::num::NonZeroU16 {\n\
             core::num::NonZeroU16::new(word).unwrap()\n}\n",
    );
    std::fs::write(&source, guest).unwrap();
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
    std::fs::remove_dir_all(root).unwrap();
}

fn actual_call<'a, 'tcx>(body: &'a Body<'tcx>, stack: &'a [DefId]) -> TableCall<'a, 'tcx> {
    let (block, terminator) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            matches!(data.terminator().kind, TerminatorKind::Call { .. })
                .then_some((block, data.terminator()))
        })
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &terminator.kind
    else {
        unreachable!()
    };
    TableCall {
        body,
        block,
        func,
        args,
        destination: *destination,
        target: *target,
        stack,
        site: (body.source.def_id(), terminator.source_info.span),
    }
}

fn same_sort_peer<'tcx>(tcx: TyCtxt<'tcx>, signature: IntegerSignature<'tcx>) -> Option<Ty<'tcx>> {
    let peer = if signature.signed {
        match signature.bits {
            32 => tcx.types.i32,
            64 => tcx.types.i64,
            _ => return None,
        }
    } else {
        match signature.bits {
            32 => tcx.types.u32,
            64 => tcx.types.u64,
            _ => return None,
        }
    };
    let pointer = if signature.signed {
        tcx.types.isize
    } else {
        tcx.types.usize
    };
    if signature.original == pointer {
        Some(peer)
    } else if signature.original == peer
        && signature.bits == u32::from(tcx.sess.target.pointer_width)
    {
        Some(pointer)
    } else {
        None
    }
}

fn check_pair(tcx: TyCtxt<'_>, name: &str) {
    let find = |suffix: &str| {
        tcx.mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == format!("{suffix}_{name}")
            })
            .unwrap()
            .to_def_id()
    };
    let mut engine = super::tests::test_engine(tcx);
    let moved = find("moved");
    let instance = engine
        .resolve_function_item(moved, tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(instance).unwrap();
    let stack = [moved];
    let call = actual_call(&body, &stack);
    let callable = call.func.ty(&body.local_decls, tcx);
    let certificate = engine.integer_table_signature(callable).unwrap();
    assert_eq!(
        certificate.argument.original,
        call.args[0].node.ty(&body.local_decls, tcx)
    );
    assert_eq!(
        certificate.result.original,
        call.destination.ty(&body.local_decls, tcx).ty
    );
    let mut pointers = Vec::new();
    for helper in ["first", "second"] {
        let target = engine
            .resolve_function_item(find(helper), tcx.mk_args(&[]))
            .unwrap();
        let id = engine
            .register_function_pointer(Target::Known {
                instance: target,
                signature: callable,
            })
            .unwrap();
        pointers.push(Value::FunctionPointer { id });
    }
    let pointer_bits = u32::from(tcx.sess.target.pointer_width);
    let raw = engine.fresh(Sort::BitVec(pointer_bits));
    let index = Value::Int {
        expression: raw.clone(),
        bits: pointer_bits,
        signed: false,
    };
    let conditions = vec![
        engine
            .terms
            .apply(
                Op::BvUnsignedLt,
                &[raw, engine.terms.bit_vector(2, pointer_bits).unwrap()],
            )
            .unwrap(),
    ];
    let original = Ty::new_array(tcx, callable, 2);
    let selected = engine
        .resolve_function_item(find("selected"), tcx.mk_args(&[]))
        .unwrap();
    let source = engine.instantiated_body(selected).unwrap();
    let table = source
        .local_decls
        .iter_enumerated()
        .find_map(|(local, decl)| (decl.ty == original).then_some(local))
        .unwrap();
    let source_index = source.args_iter().next().unwrap();
    let mut source_state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; source.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; source.local_decls.len()],
        memory: Default::default(),
    };
    source_state.locals[table.as_usize()] = Some(Value::Elements(pointers.clone().into()));
    source_state.locals[source_index.as_usize()] = Some(index.clone());
    let before = (
        engine.function_pointers.borrow().len(),
        engine.steps,
        engine.next_symbol.get(),
    );
    let factory = engine
        .function_table_choice(
            original,
            &pointers,
            &index,
            &conditions,
            Some(TableSource {
                body: &source,
                prefix: Place::from(table),
                state: &source_state,
                index: source_index,
            }),
        )
        .unwrap();
    let enabled = certificate.argument.original == certificate.result.original
        || ENABLE_INTEGER_FUNCTION_TABLE_PAIRS;
    assert_eq!(factory.is_some(), enabled);
    if !enabled {
        assert_eq!(
            before,
            (
                engine.function_pointers.borrow().len(),
                engine.steps,
                engine.next_symbol.get()
            )
        );
    }
    let choice = engine
        .capture_function_table(original, &pointers, &index, &conditions)
        .unwrap()
        .unwrap();
    let Operand::Move(callback) = call.func else {
        panic!("callback Move absent")
    };
    let Operand::Move(word) = &call.args[0].node else {
        panic!("argument Move absent")
    };
    let raw_word = if certificate.argument.signed {
        1_u128 << (certificate.argument.bits - 1)
    } else {
        u128::MAX >> (128 - certificate.argument.bits)
    };
    let value = symbolic::integer(
        &engine.terms,
        raw_word,
        certificate.argument.bits,
        certificate.argument.signed,
    );
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.clone(),
        addresses: vec![None; body.local_decls.len()],
        memory: Default::default(),
    };
    state.locals[callback.local.as_usize()] = Some(choice);
    state.locals[word.local.as_usize()] = Some(value.clone());
    state.memory.byte_copy_opaque = true;
    let returns = engine
        .prepared_function_table_call(&state, actual_call(&body, &stack))
        .unwrap()
        .unwrap();
    assert_eq!(returns.len(), 2);
    for (position, (consumed, result)) in returns.iter().enumerate() {
        assert!(engine.operand(moved, &body, consumed, call.func).is_err());
        assert!(
            engine
                .operand(moved, &body, consumed, &call.args[0].node)
                .is_err()
        );
        assert!(consumed.memory.byte_copy_opaque && result.memory.byte_copy_opaque);
        let (term, bits, signed) = result.value.integer().unwrap();
        assert_eq!(
            (bits, signed),
            (certificate.result.bits, certificate.result.signed)
        );
        let mut expected = raw_word ^ position as u128;
        if certificate.argument.signed && bits > certificate.argument.bits {
            expected |= u128::MAX << certificate.argument.bits;
        }
        expected &= u128::MAX >> (128 - bits);
        let equal = engine
            .terms
            .apply(
                Op::Equal,
                &[term, engine.terms.bit_vector(expected, bits).unwrap()],
            )
            .unwrap();
        let mut bad = result.conditions.clone();
        bad.push(engine.terms.apply(Op::Not, &[equal]).unwrap());
        assert!(!engine.feasible(&bad).unwrap());
    }
    for helper in ["first", "second"] {
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function == format!("{helper}_{name}"))
        );
    }
    for (local, signature) in [
        (word.local, certificate.argument),
        (call.destination.local, certificate.result),
    ] {
        if let Some(peer) = same_sort_peer(tcx, signature) {
            assert_ne!(peer, signature.original);
            assert_eq!(
                engine.integer_type(peer),
                Some((signature.bits, signature.signed))
            );
            let mut forged = (*body).clone();
            forged.local_decls[local].ty = peer;
            assert!(
                engine
                    .prepared_function_table_call(&state, actual_call(&forged, &stack))
                    .is_err()
            );
        }
    }
    for invalid in [
        symbolic::integer(
            &engine.terms,
            1,
            certificate.result.bits,
            !certificate.result.signed,
        ),
        symbolic::integer(
            &Context::default(),
            1,
            certificate.result.bits,
            certificate.result.signed,
        ),
        Value::Unit,
    ] {
        assert!(
            engine
                .validate_table_result(&invalid, certificate.result)
                .is_err()
        );
    }
    let wrong_bits = if certificate.result.bits == 128 {
        64
    } else {
        128
    };
    assert!(
        engine
            .validate_table_result(
                &symbolic::integer(&engine.terms, 1, wrong_bits, certificate.result.signed),
                certificate.result
            )
            .is_err()
    );
    let mut masked = state.clone();
    masked
        .missing_places
        .consume(word.local.as_usize(), Vec::new())
        .unwrap();
    assert!(
        engine
            .prepared_function_table_call(&masked, actual_call(&body, &stack))
            .is_err()
    );
    let wrong_argument_bits = if certificate.argument.bits == 128 {
        64
    } else {
        128
    };
    for invalid in [
        symbolic::integer(
            &engine.terms,
            1,
            certificate.argument.bits,
            !certificate.argument.signed,
        ),
        symbolic::integer(
            &engine.terms,
            1,
            wrong_argument_bits,
            certificate.argument.signed,
        ),
        symbolic::integer(
            &Context::default(),
            1,
            certificate.argument.bits,
            certificate.argument.signed,
        ),
        Value::Unit,
    ] {
        let mut forged = state.clone();
        forged.locals[word.local.as_usize()] = Some(invalid);
        assert!(
            engine
                .prepared_function_table_call(&forged, actual_call(&body, &stack))
                .is_err()
        );
    }
    let (argument_name, result_name) = name.split_once("_to_").unwrap();
    let other_argument = if argument_name == "u8" { "u16" } else { "u8" };
    let other_result = if result_name == "u8" { "u16" } else { "u8" };
    for wrong_name in [
        format!("first_{other_argument}_to_{result_name}"),
        format!("first_{argument_name}_to_{other_result}"),
    ] {
        let wrong = tcx
            .mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == wrong_name
            })
            .unwrap()
            .to_def_id();
        let target = engine
            .resolve_function_item(wrong, tcx.mk_args(&[]))
            .unwrap();
        let id = engine
            .register_function_pointer(Target::Known {
                instance: target,
                signature: callable,
            })
            .unwrap();
        assert!(
            engine
                .capture_function_table(
                    original,
                    &[Value::FunctionPointer { id }, pointers[1].clone()],
                    &index,
                    &conditions
                )
                .is_err()
        );
    }
    check_pair_fields(
        &mut engine,
        find("copied"),
        &state,
        callback.local,
        value,
        certificate,
    );
}

fn check_pair_fields<'tcx>(
    engine: &mut Engine<'tcx>,
    copied: DefId,
    moved: &State,
    callback: rustc_middle::mir::Local,
    value: Value,
    certificate: IntegerCallSignature<'tcx>,
) {
    let tcx = engine.tcx;
    let instance = engine
        .resolve_function_item(copied, tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(instance).unwrap();
    let stack = [copied];
    let call = actual_call(&body, &stack);
    let Operand::Move(copy_callback) = call.func else {
        panic!("copy callback absent")
    };
    let Operand::Copy(field) = &call.args[0].node else {
        panic!("Copy field absent")
    };
    assert_eq!(call.destination.projection.len(), 1);
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        conditions: moved.conditions.clone(),
        addresses: vec![None; body.local_decls.len()],
        memory: moved.memory.clone(),
    };
    state.locals[copy_callback.local.as_usize()] = moved.locals[callback.as_usize()].clone();
    state.locals[field.local.as_usize()] = Some(Value::Tuple(vec![
        value,
        Value::Bool(engine.terms.boolean(true)),
    ]));
    assert_eq!(
        engine
            .prepared_function_table_call(&state, actual_call(&body, &stack))
            .unwrap()
            .unwrap()
            .len(),
        2
    );
    for (local, signature) in [
        (field.local, certificate.argument),
        (call.destination.local, certificate.result),
    ] {
        if let Some(peer) = same_sort_peer(tcx, signature) {
            let mut forged = (*body).clone();
            forged.local_decls[local].ty = Ty::new_tup(tcx, &[peer, tcx.types.bool]);
            assert!(
                engine
                    .prepared_function_table_call(&state, actual_call(&forged, &stack))
                    .is_err()
            );
        }
    }
}

fn check_result_refusals(tcx: TyCtxt<'_>) {
    let engine = super::tests::test_engine(tcx);
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
    for name in [
        "result_bool",
        "result_char",
        "result_float",
        "result_ref",
        "result_nz",
    ] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let signature = engine.call_poly_signature(instance).unwrap();
        assert_eq!(signature.skip_binder().inputs(), &[tcx.types.u16]);
        let callable = Ty::new_fn_ptr(tcx, signature);
        assert!(engine.integer_table_signature(callable).is_none());
    }
    let instance = engine
        .resolve_function_item(find("result_nz"), tcx.mk_args(&[]))
        .unwrap();
    let signature = engine.call_poly_signature(instance).unwrap();
    let mut pattern = signature.skip_binder().output();
    for _ in 0..2 {
        let ty::Adt(def, args) = pattern.kind() else {
            panic!("NZ wrapper absent")
        };
        assert_eq!(def.all_fields().count(), 1);
        pattern = tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                def.all_fields().next().unwrap().ty(tcx, args),
            )
            .unwrap();
    }
    assert!(matches!(pattern.kind(), ty::Pat(_, _)));
    assert_eq!(engine.integer_type(pattern), Some((16, false)));
    let patterned = Ty::new_fn_ptr(
        tcx,
        signature.map_bound(|sig| tcx.mk_fn_sig([tcx.types.u16], pattern, sig.fn_sig_kind)),
    );
    assert!(engine.integer_table_signature(patterned).is_none());
}
