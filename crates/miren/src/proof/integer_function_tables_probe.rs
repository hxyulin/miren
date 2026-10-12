use super::*;

const INTEGERS: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

#[test]
fn compiler_integer_function_table_signatures_and_actual_calls() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check_integer_calls(tcx);
            rustc_driver::Compilation::Stop
        }
    }
    let root = std::env::temp_dir().join(format!(
        "miren-integer-function-table-unit-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    let mut guest = String::from(
        "#![no_std]\n#![feature(custom_mir, core_intrinsics)]\n\
         use core::intrinsics::mir::*;\n\
         pub fn char_word(word: char) -> char {word}\n\
         pub fn bool_word(word: bool) -> bool {word}\n\
         pub fn float_word(word: f32) -> f32 {word}\n\
         pub fn nz_word(word: core::num::NonZeroU16) -> u16 {word.get()}\n",
    );
    for name in INTEGERS {
        guest.push_str(&format!(
            r#"
#[inline(never)] pub fn first_{name}(word: {name}) -> {name} {{word}}
#[inline(never)] pub fn second_{name}(word: {name}) -> {name} {{word ^ 1}}
pub fn selected_{name}(index: usize, word: {name}) -> {name} {{
    let table: [fn({name})->{name};2] = [first_{name},second_{name}];
    if index < 2 {{table[index](word)}} else {{word}}
}}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn copied_{name}(callback: fn({name})->{name}, record: ({name}, bool)) -> {name} {{
    mir! {{
        {{Call(RET = Move(callback)(record.0), ReturnTo(done), UnwindUnreachable())}}
        done = {{Return()}}
    }}
}}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn moved_{name}(callback: fn({name})->{name}, word: {name}) -> {name} {{
    mir! {{
        {{Call(RET = Move(callback)(Move(word)), ReturnTo(done), UnwindUnreachable())}}
        done = {{Return()}}
    }}
}}
"#
        ));
    }
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

fn check_integer_calls(tcx: TyCtxt<'_>) {
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
    for name in INTEGERS {
        let mut engine = super::tests::test_engine(tcx);
        let moved = find(&format!("moved_{name}"));
        let instance = engine
            .resolve_function_item(moved, tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        let (block, func, args, destination, target, span) = body
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                let term = data.terminator();
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } = &term.kind
                else {
                    return None;
                };
                Some((
                    block,
                    func,
                    args.as_ref(),
                    *destination,
                    *target,
                    term.source_info.span,
                ))
            })
            .unwrap();
        let callable = func.ty(&body.local_decls, tcx);
        let certificate = engine.integer_table_signature(callable).unwrap();
        assert!(certificate.argument == certificate.result);
        assert!(matches!(
            certificate.argument.original.kind(),
            ty::Int(_) | ty::Uint(_)
        ));
        assert_eq!(
            certificate.argument.original,
            args[0].node.ty(&body.local_decls, tcx)
        );
        assert_eq!(
            certificate.argument.original,
            destination.ty(&body.local_decls, tcx).ty
        );
        assert_eq!(
            engine.table_signature(callable),
            certificate.argument.original == tcx.types.u16 || ENABLE_INTEGER_FUNCTION_TABLES
        );
        let mut pointers = Vec::new();
        for helper in ["first", "second"] {
            let instance = engine
                .resolve_function_item(find(&format!("{helper}_{name}")), tcx.mk_args(&[]))
                .unwrap();
            let id = engine
                .register_function_pointer(Target::Known {
                    instance,
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
            .resolve_function_item(find(&format!("selected_{name}")), tcx.mk_args(&[]))
            .unwrap();
        let source_body = engine.instantiated_body(selected).unwrap();
        let table = source_body
            .local_decls
            .iter_enumerated()
            .find_map(|(local, decl)| (decl.ty == original).then_some(local))
            .unwrap();
        let source_index = source_body.args_iter().next().unwrap();
        let mut source_state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; source_body.local_decls.len()],
            missing_places: Default::default(),
            conditions: conditions.clone(),
            addresses: vec![None; source_body.local_decls.len()],
            memory: Default::default(),
        };
        source_state.locals[table.as_usize()] = Some(Value::Elements(pointers.clone().into()));
        source_state.locals[source_index.as_usize()] = Some(index.clone());
        let factory_count = engine.function_pointers.borrow().len();
        let factory = engine
            .function_table_choice(
                original,
                &pointers,
                &index,
                &conditions,
                Some(TableSource {
                    body: &source_body,
                    prefix: Place::from(table),
                    state: &source_state,
                    index: source_index,
                }),
            )
            .unwrap();
        if certificate.argument.original == tcx.types.u16 || ENABLE_INTEGER_FUNCTION_TABLES {
            assert!(factory.is_some());
        } else {
            assert!(factory.is_none());
            assert_eq!(engine.function_pointers.borrow().len(), factory_count);
        }
        let pointer = engine
            .capture_function_table(original, &pointers, &index, &conditions)
            .unwrap()
            .unwrap();
        let Operand::Move(callback) = func else {
            panic!("actual callback Move absent")
        };
        let Operand::Move(word) = &args[0].node else {
            panic!("actual word Move absent")
        };
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            missing_places: Default::default(),
            conditions: conditions.clone(),
            addresses: vec![None; body.local_decls.len()],
            memory: Default::default(),
        };
        state.locals[callback.local.as_usize()] = Some(pointer);
        let raw_word = if certificate.argument.signed {
            1_u128 << (certificate.argument.bits - 1)
        } else {
            u128::MAX >> (128 - certificate.argument.bits)
        };
        state.locals[word.local.as_usize()] = Some(symbolic::integer(
            &engine.terms,
            raw_word,
            certificate.argument.bits,
            certificate.argument.signed,
        ));
        let stack = [moved];
        let call = || TableCall {
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
            .prepared_function_table_call(&state, call())
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
            assert_eq!(
                (bits, signed),
                (certificate.argument.bits, certificate.argument.signed)
            );
            let expected = if position == 0 {
                raw_word
            } else {
                raw_word ^ 1
            };
            let wrong = engine
                .terms
                .apply(
                    Op::Not,
                    &[engine
                        .terms
                        .apply(
                            Op::Equal,
                            &[term, engine.terms.bit_vector(expected, bits).unwrap()],
                        )
                        .unwrap()],
                )
                .unwrap();
            let mut bad = result.conditions.clone();
            bad.push(wrong);
            assert!(!engine.feasible(&bad).unwrap());
        }
        assert!(engine.operand(moved, &body, &state, func).is_ok());
        assert!(engine.operand(moved, &body, &state, &args[0].node).is_ok());
        assert!(state.memory.owned_regions.is_empty());
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function == format!("first_{name}"))
        );
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function == format!("second_{name}"))
        );
        let mut wrong_sign = state.clone();
        wrong_sign.locals[word.local.as_usize()] = Some(symbolic::integer(
            &engine.terms,
            raw_word,
            certificate.argument.bits,
            !certificate.argument.signed,
        ));
        assert!(
            engine
                .prepared_function_table_call(&wrong_sign, call())
                .is_err()
        );
        let mut wrong_bits = state.clone();
        let bits = if certificate.argument.bits == 128 {
            64
        } else {
            128
        };
        wrong_bits.locals[word.local.as_usize()] = Some(symbolic::integer(
            &engine.terms,
            1,
            bits,
            certificate.argument.signed,
        ));
        assert!(
            engine
                .prepared_function_table_call(&wrong_bits, call())
                .is_err()
        );
        let mut foreign = state.clone();
        foreign.locals[word.local.as_usize()] = Some(symbolic::integer(
            &Context::default(),
            1,
            certificate.argument.bits,
            certificate.argument.signed,
        ));
        assert!(
            engine
                .prepared_function_table_call(&foreign, call())
                .is_err()
        );
        let mut masked = state.clone();
        masked
            .missing_places
            .consume(word.local.as_usize(), Vec::new())
            .unwrap();
        assert!(
            engine
                .prepared_function_table_call(&masked, call())
                .is_err()
        );
        let alternate = match name {
            "usize" => Some(if pointer_bits == 32 {
                tcx.types.u32
            } else {
                tcx.types.u64
            }),
            "u32" if pointer_bits == 32 => Some(tcx.types.usize),
            "u64" if pointer_bits == 64 => Some(tcx.types.usize),
            "isize" => Some(if pointer_bits == 32 {
                tcx.types.i32
            } else {
                tcx.types.i64
            }),
            "i32" if pointer_bits == 32 => Some(tcx.types.isize),
            "i64" if pointer_bits == 64 => Some(tcx.types.isize),
            _ => None,
        };
        if let Some(alternate) = alternate {
            assert_eq!(
                engine.integer_type(alternate),
                Some((certificate.argument.bits, certificate.argument.signed))
            );
            assert_ne!(alternate, certificate.argument.original);
            let mut forged = (*body).clone();
            forged.local_decls[word.local].ty = alternate;
            let term = forged.basic_blocks[block].terminator();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &term.kind
            else {
                unreachable!()
            };
            let forged_call = TableCall {
                body: &forged,
                block,
                func,
                args,
                destination: *destination,
                target: *target,
                stack: &stack,
                site: (moved, term.source_info.span),
            };
            assert!(
                engine
                    .prepared_function_table_call(&state, forged_call)
                    .is_err()
            );
            let mut forged = (*body).clone();
            forged.local_decls[destination.local].ty = alternate;
            let term = forged.basic_blocks[block].terminator();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &term.kind
            else {
                unreachable!()
            };
            let forged_call = TableCall {
                body: &forged,
                block,
                func,
                args,
                destination: *destination,
                target: *target,
                stack: &stack,
                site: (moved, term.source_info.span),
            };
            assert!(
                engine
                    .prepared_function_table_call(&state, forged_call)
                    .is_err()
            );
            let alternate_callable = Ty::new_fn_ptr(
                tcx,
                engine
                    .call_poly_signature(instance)
                    .unwrap()
                    .map_bound(|sig| tcx.mk_fn_sig([alternate], alternate, sig.fn_sig_kind)),
            );
            assert!(
                engine
                    .capture_function_table(
                        Ty::new_array(tcx, alternate_callable, 2),
                        &pointers,
                        &index,
                        &conditions
                    )
                    .is_err()
            );
            let copied = find(&format!("copied_{name}"));
            let copied_instance = engine
                .resolve_function_item(copied, tcx.mk_args(&[]))
                .unwrap();
            let copied_body = engine.instantiated_body(copied_instance).unwrap();
            let (copy_block, copy_func, copy_args, copy_dest, copy_target, copy_span) = copied_body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(block, data)| {
                    let term = data.terminator();
                    let TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target,
                        ..
                    } = &term.kind
                    else {
                        return None;
                    };
                    Some((
                        block,
                        func,
                        args.as_ref(),
                        *destination,
                        *target,
                        term.source_info.span,
                    ))
                })
                .unwrap();
            let Operand::Move(copy_callback) = copy_func else {
                panic!("Copy callback Move absent")
            };
            let Operand::Copy(record_field) = &copy_args[0].node else {
                panic!("actual Copy field absent")
            };
            let mut copied_state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; copied_body.local_decls.len()],
                missing_places: Default::default(),
                conditions: conditions.clone(),
                addresses: vec![None; copied_body.local_decls.len()],
                memory: Default::default(),
            };
            copied_state.locals[copy_callback.local.as_usize()] =
                state.locals[callback.local.as_usize()].clone();
            copied_state.locals[record_field.local.as_usize()] = Some(Value::Tuple(vec![
                state.locals[word.local.as_usize()].clone().unwrap(),
                Value::Bool(engine.terms.boolean(true)),
            ]));
            let copy_stack = [copied];
            let copy_call = TableCall {
                body: &copied_body,
                block: copy_block,
                func: copy_func,
                args: copy_args,
                destination: copy_dest,
                target: copy_target,
                stack: &copy_stack,
                site: (copied, copy_span),
            };
            assert_eq!(
                engine
                    .prepared_function_table_call(&copied_state, copy_call)
                    .unwrap()
                    .unwrap()
                    .len(),
                2
            );
            let mut forged = (*copied_body).clone();
            forged.local_decls[record_field.local].ty =
                Ty::new_tup(tcx, &[alternate, tcx.types.bool]);
            let term = forged.basic_blocks[copy_block].terminator();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &term.kind
            else {
                unreachable!()
            };
            let forged_call = TableCall {
                body: &forged,
                block: copy_block,
                func,
                args,
                destination: *destination,
                target: *target,
                stack: &copy_stack,
                site: (copied, term.source_info.span),
            };
            assert!(
                engine
                    .prepared_function_table_call(&copied_state, forged_call)
                    .is_err()
            );
        }
    }
    let engine = super::tests::test_engine(tcx);
    for name in ["char_word", "bool_word", "float_word", "nz_word"] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let callable = Ty::new_fn_ptr(tcx, engine.call_poly_signature(instance).unwrap());
        assert!(engine.integer_table_signature(callable).is_none());
    }
    let nz = engine
        .resolve_function_item(find("nz_word"), tcx.mk_args(&[]))
        .unwrap();
    let nz_signature = engine.call_poly_signature(nz).unwrap();
    let mut pattern = nz_signature.skip_binder().inputs()[0];
    for _ in 0..2 {
        let ty::Adt(def, args) = pattern.kind() else {
            panic!("original NZ wrapper absent")
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
        nz_signature.map_bound(|sig| tcx.mk_fn_sig([pattern], pattern, sig.fn_sig_kind)),
    );
    assert!(engine.integer_table_signature(patterned).is_none());
}
