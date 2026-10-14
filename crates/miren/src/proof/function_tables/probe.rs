//! Actual compiler inputs and hostile mutable registry controls for the nested route.
use super::super::tests::test_engine;
use super::*;
use rustc_middle::mir::Local;

#[test]
fn compiler_nested_choice_guards() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check(tcx);
            rustc_driver::Compilation::Stop
        }
    }
    static NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "miren-nested-choice-{}-{}",
        std::process::id(),
        NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
    ));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    let dependency = root.join("dependency.rs");
    std::fs::write(
        &dependency,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "#[inline(never)] pub fn unavailable(value:u16)->u16 { value }\n",
        ),
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir,core_intrinsics)]
use core::intrinsics::mir::*;
#[inline(never)] pub fn first(value:u16)->u16 { value }
#[inline(never)] pub fn second(value:u16)->u16 { value ^ 1 }
#[inline(never)] pub fn char_first(value:char)->char { value }
#[inline(never)] pub fn bool_first(value:bool)->bool { value }
#[inline(never)] pub fn float_first(value:f32)->f32 { value }
pub fn moved_char(callback:fn(char)->char,word:char)->char { callback(word) }
pub fn moved_bool(callback:fn(bool)->bool,word:bool)->bool { callback(word) }
pub fn moved_float(callback:fn(f32)->f32,word:f32)->f32 { callback(word) }
#[inline(never)] pub fn missing(value:u16)->u16 { nested_external::unavailable(value) }
#[custom_mir(dialect="runtime",phase="optimized")]
pub fn moved(callback:fn(u16)->u16,word:u16)->u16 {
    mir! {
        { Call(RET=Move(callback)(Move(word)),ReturnTo(done),UnwindUnreachable()) }
        done={Return()}
    }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = root.join(format!("{}-o{level}", target.unwrap_or("host")));
            std::fs::create_dir_all(&output).unwrap();
            let archive = output.join("libnested_external.rlib");
            let mut command = std::process::Command::new(
                std::path::Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"),
            );
            command
                .args([
                    "--crate-type=rlib",
                    "--crate-name=nested_external",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Zalways-encode-mir=no",
                    "-Copt-level=0",
                ])
                .arg(&dependency)
                .arg("-o")
                .arg(&archive);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let result = command.output().unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let mut arguments = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "--extern".into(),
                format!("nested_external={}", archive.display()),
            ];
            if let Some(target) = target {
                arguments.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&arguments, &mut Capture);
        }
    }
    std::fs::remove_dir_all(root).unwrap();
}

fn prepared<'tcx>(
    engine: &mut Engine<'tcx>,
    state: &State,
    body: &Body<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<Option<Vec<(State, Return)>>, String> {
    let (block, term) = body
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
    } = &term.kind
    else {
        unreachable!();
    };
    let stack = [instance.def_id()];
    engine.prepared_function_table_call(
        state,
        TableCall {
            body,
            block,
            func,
            args,
            destination: *destination,
            target: *target,
            stack: &stack,
            site: (instance.def_id(), term.source_info.span),
        },
    )
}

fn check<'tcx>(tcx: TyCtxt<'tcx>) {
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
    let caller = engine
        .resolve_function_item(find("moved"), tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(caller).unwrap();
    let first = engine
        .resolve_function_item(find("first"), tcx.mk_args(&[]))
        .unwrap();
    let second = engine
        .resolve_function_item(find("second"), tcx.mk_args(&[]))
        .unwrap();
    let signature = Ty::new_fn_ptr(tcx, engine.call_poly_signature(first).unwrap());
    let original = Ty::new_array(tcx, signature, 2);
    let first_id = engine
        .register_function_pointer(Target::Known {
            instance: first,
            signature,
        })
        .unwrap();
    let second_id = engine
        .register_function_pointer(Target::Known {
            instance: second,
            signature,
        })
        .unwrap();
    let bits = u32::from(tcx.sess.target.pointer_width);
    let i = engine.fresh(Sort::BitVec(bits));
    let j = engine.fresh(Sort::BitVec(bits));
    let inner = engine
        .register_function_pointer(Target::Choice(Choice {
            original,
            signature,
            index: i.clone(),
            targets: vec![first_id, second_id],
        }))
        .unwrap();
    let outer = engine
        .register_function_pointer(Target::Choice(Choice {
            original,
            signature,
            index: j.clone(),
            targets: vec![inner, first_id],
        }))
        .unwrap();
    let conditions = [i.clone(), j.clone()]
        .iter()
        .map(|index| {
            engine
                .terms
                .apply(
                    Op::BvUnsignedLt,
                    &[index.clone(), engine.terms.bit_vector(2, bits).unwrap()],
                )
                .unwrap()
        })
        .collect::<Vec<_>>();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        constant_receipts: Default::default(),
        missing_places: Default::default(),
        conditions,
        addresses: vec![None; body.local_decls.len()],
        memory: Default::default(),
    };
    let inputs = body.args_iter().collect::<Vec<_>>();
    state.locals[inputs[0].as_usize()] = Some(Value::FunctionPointer { id: outer });
    state.locals[inputs[1].as_usize()] = Some(symbolic::integer(&engine.terms, 129, 16, false));
    let returns = prepared(&mut engine, &state, &body, caller)
        .unwrap()
        .unwrap();
    assert_eq!(returns.len(), 3);
    let selected = engine
        .terms
        .apply(
            Op::And,
            &[
                engine
                    .terms
                    .apply(
                        Op::Equal,
                        &[i.clone(), engine.terms.bit_vector(1, bits).unwrap()],
                    )
                    .unwrap(),
                engine
                    .terms
                    .apply(
                        Op::Equal,
                        &[j.clone(), engine.terms.bit_vector(0, bits).unwrap()],
                    )
                    .unwrap(),
            ],
        )
        .unwrap();
    let expected = engine
        .terms
        .apply(
            Op::Ite,
            &[
                selected,
                engine.terms.bit_vector(128, 16).unwrap(),
                engine.terms.bit_vector(129, 16).unwrap(),
            ],
        )
        .unwrap();
    for (consumed, result) in &returns {
        assert!(
            consumed
                .missing_places
                .check(inputs[0].as_usize(), &[])
                .is_err()
        );
        assert!(
            consumed
                .missing_places
                .check(inputs[1].as_usize(), &[])
                .is_err()
        );
        let (value, width, signed) = result.value.integer().unwrap();
        assert_eq!((width, signed), (16, false));
        let wrong = engine
            .terms
            .apply(
                Op::Not,
                &[engine
                    .terms
                    .apply(Op::Equal, &[value, expected.clone()])
                    .unwrap()],
            )
            .unwrap();
        let mut conditions = result.conditions.clone();
        conditions.push(wrong);
        assert!(!engine.feasible(&conditions).unwrap());
    }
    assert!(state.locals[inputs[0].as_usize()].is_some());
    assert!(state.locals[inputs[1].as_usize()].is_some());
    let entries = engine.proof.body_entries.len();
    let genuine = engine.function_pointers.borrow()[inner].clone();
    for fault in 0..4 {
        let Target::Choice(mut wrong) = genuine.clone() else {
            unreachable!();
        };
        match fault {
            0 => wrong.index = Context::default().bit_vector(0, bits).unwrap(),
            1 => wrong.targets[0] = usize::MAX,
            2 => wrong.original = Ty::new_array(tcx, signature, 3),
            3 => wrong.targets[0] = inner,
            _ => unreachable!(),
        }
        engine.function_pointers.borrow_mut()[inner] = Target::Choice(wrong);
        engine.steps = 0;
        assert!(prepared(&mut engine, &state, &body, caller).is_err());
        assert_eq!(engine.proof.body_entries.len(), entries);
    }
    engine.function_pointers.borrow_mut()[inner] = genuine;
    for instance in [caller, first, second] {
        let original_signature = engine.call_poly_signature(instance).unwrap();
        for fault in 0..5 {
            let poisoned = match fault {
                0 => original_signature.map_bound(|s| s.set_safety(rustc_hir::Safety::Unsafe)),
                1 => original_signature.map_bound(|s| ty::FnSig {
                    fn_sig_kind: s
                        .fn_sig_kind
                        .set_abi(rustc_abi::ExternAbi::C { unwind: false }),
                    ..s
                }),
                2 => ty::Binder::bind_with_vars(
                    original_signature.skip_binder(),
                    tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Ty(
                        ty::BoundTyKind::Anon,
                    )]),
                ),
                3 | 4 => original_signature.map_bound(|s| {
                    let mut types = s.inputs_and_output.to_vec();
                    let selected = if fault == 3 { 0 } else { types.len() - 1 };
                    types[selected] = tcx.types.u8;
                    ty::FnSig {
                        inputs_and_output: tcx.mk_type_list(&types),
                        ..s
                    }
                }),
                _ => unreachable!(),
            };
            assert_ne!(poisoned, original_signature);
            engine
                .call_signatures
                .borrow_mut()
                .insert(instance, poisoned);
            engine.steps = 0;
            assert!(prepared(&mut engine, &state, &body, caller).is_err());
            assert_eq!(engine.proof.body_entries.len(), entries);
        }
        engine
            .call_signatures
            .borrow_mut()
            .insert(instance, original_signature);
    }
    for instance in [caller, first, second] {
        let actual = engine.instantiated_body(instance).unwrap();
        for fault in 0..4 {
            let mut wrong = actual.as_ref().clone();
            match fault {
                0 => wrong.local_decls[Local::from_usize(0)].ty = tcx.types.u8,
                1 => {
                    wrong.source.instance = if instance == caller {
                        first.def
                    } else {
                        caller.def
                    }
                }
                2 => wrong.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
                    .terminator_mut()
                    .attributes
                    .push(rustc_hir::attrs::AttributeKind::Cold),
                3 => wrong.arg_count += 1,
                _ => unreachable!(),
            }
            let wrong = std::rc::Rc::new(wrong);
            engine.bodies.borrow_mut().insert(instance, wrong.clone());
            engine.steps = 0;
            let source = if instance == caller { &wrong } else { &body };
            assert!(prepared(&mut engine, &state, source, caller).is_err());
            assert_eq!(engine.proof.body_entries.len(), entries);
            engine.bodies.borrow_mut().insert(instance, actual.clone());
        }
    }
    let mut ancestor = first_id;
    for _ in 0..MAX_INPUT_DEPTH {
        ancestor = engine
            .register_function_pointer(Target::Choice(Choice {
                original: Ty::new_array(tcx, signature, 1),
                signature,
                index: engine.terms.bit_vector(0, bits).unwrap(),
                targets: vec![ancestor],
            }))
            .unwrap();
    }
    let mut deep = state.clone();
    deep.locals[inputs[0].as_usize()] = Some(Value::FunctionPointer { id: ancestor });
    engine.steps = 0;
    let error = prepared(&mut engine, &deep, &body, caller).err().unwrap();
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    let old_limit = engine.limits.max_steps;
    engine.limits.max_steps = 1;
    engine.steps = 0;
    let error = prepared(&mut engine, &state, &body, caller).err().unwrap();
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    engine.limits.max_steps = old_limit;
    let mut foreign = state.clone();
    foreign.locals[inputs[1].as_usize()] =
        Some(symbolic::integer(&Context::default(), 129, 16, false));
    engine.steps = 0;
    assert!(prepared(&mut engine, &foreign, &body, caller).is_err());
    let mut foreign_condition = state.clone();
    foreign_condition
        .conditions
        .push(Context::default().boolean(true));
    engine.steps = 0;
    assert!(prepared(&mut engine, &foreign_condition, &body, caller).is_err());
    let mut partial = state.clone();
    partial
        .missing_places
        .consume(inputs[0].as_usize(), Vec::new())
        .unwrap();
    engine.steps = 0;
    assert!(prepared(&mut engine, &partial, &body, caller).is_err());
    let missing = engine
        .resolve_function_item(find("missing"), tcx.mk_args(&[]))
        .unwrap();
    let missing_id = engine
        .register_function_pointer(Target::Known {
            instance: missing,
            signature,
        })
        .unwrap();
    let genuine = engine.function_pointers.borrow()[inner].clone();
    let Target::Choice(mut wrong) = genuine.clone() else {
        unreachable!();
    };
    wrong.targets[1] = missing_id;
    // Rebuild append-only edges rather than forging a forward reference to the new missing leaf.
    let inner_missing = engine
        .register_function_pointer(Target::Choice(wrong))
        .unwrap();
    let outer_missing = engine
        .register_function_pointer(Target::Choice(Choice {
            original,
            signature,
            index: j,
            targets: vec![inner_missing, first_id],
        }))
        .unwrap();
    let mut missing_state = state.clone();
    missing_state.locals[inputs[0].as_usize()] = Some(Value::FunctionPointer { id: outer_missing });
    engine.steps = 0;
    let error = prepared(&mut engine, &missing_state, &body, caller)
        .err()
        .unwrap();
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::MissingCompilerEvidence)
    );
    assert_eq!(engine.proof.body_entries.len(), entries);
    primitive_controls(tcx);
    println!(
        concat!(
            "NestedChoice source12/fullsig15/registry4/Context/mask/depth/budget/MCE: ",
            "{} {:?}"
        ),
        tcx.sess.target.llvm_target, tcx.sess.opts.cg.opt_level
    );
}

fn primitive_controls(tcx: TyCtxt<'_>) {
    for domain in ["bool", "char", "float"] {
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
        let caller = engine
            .resolve_function_item(find(&format!("moved_{domain}")), tcx.mk_args(&[]))
            .unwrap();
        let leaf = engine
            .resolve_function_item(find(&format!("{domain}_first")), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(caller).unwrap();
        let signature = Ty::new_fn_ptr(tcx, engine.call_poly_signature(leaf).unwrap());
        let known = engine
            .register_function_pointer(Target::Known {
                instance: leaf,
                signature,
            })
            .unwrap();
        let original = Ty::new_array(tcx, signature, 2);
        let bits = u32::from(tcx.sess.target.pointer_width);
        let zero = engine.terms.bit_vector(0, bits).unwrap();
        let inner = engine
            .register_function_pointer(Target::Choice(Choice {
                original,
                signature,
                index: zero.clone(),
                targets: vec![known, known],
            }))
            .unwrap();
        let outer = engine
            .register_function_pointer(Target::Choice(Choice {
                original,
                signature,
                index: zero,
                targets: vec![inner, known],
            }))
            .unwrap();
        let inputs = body.args_iter().collect::<Vec<_>>();
        let value = match domain {
            "bool" => Value::Bool(engine.terms.boolean(true)),
            "char" => symbolic::integer(&engine.terms, 0x1f642, 32, false),
            "float" => symbolic::float(&engine.terms, 0x7fc0_1234, 32),
            _ => unreachable!(),
        };
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            constant_receipts: Default::default(),
            missing_places: Default::default(),
            conditions: Vec::new(),
            addresses: vec![None; body.local_decls.len()],
            memory: Default::default(),
        };
        state.locals[inputs[0].as_usize()] = Some(Value::FunctionPointer { id: outer });
        state.locals[inputs[1].as_usize()] = Some(value);
        assert!(
            prepared(&mut engine, &state, &body, caller)
                .unwrap()
                .is_some()
        );
        if domain == "float" {
            for fault in [
                FloatTableReturnFault::WrongWidth,
                FloatTableReturnFault::MissingRaw,
                FloatTableReturnFault::ForeignContext,
                FloatTableReturnFault::InconsistentRaw,
            ] {
                FLOAT_TABLE_RETURN_FAULT.with(|current| current.set(fault));
                FLOAT_TABLE_RETURN_OBSERVATIONS.with(|count| count.set(0));
                engine.steps = 0;
                let result = prepared(&mut engine, &state, &body, caller);
                FLOAT_TABLE_RETURN_FAULT.with(|current| current.set(FloatTableReturnFault::None));
                assert!(result.is_err());
                assert!(FLOAT_TABLE_RETURN_OBSERVATIONS.with(std::cell::Cell::get) > 0);
            }
        } else {
            for value in [0xd800, 0x110000] {
                let mut wrong = state.clone();
                wrong.locals[inputs[1].as_usize()] =
                    Some(symbolic::integer(&engine.terms, value, 32, false));
                engine.steps = 0;
                assert!(prepared(&mut engine, &wrong, &body, caller).is_err());
            }
        }
    }
    println!(
        "NestedChoice primitive Bool/Char/Float entry, Unicode and four Return encoding refusals"
    );
}
