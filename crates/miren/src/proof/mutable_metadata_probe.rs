use super::*;

#[test]
fn scalar_metadata_override_restores_nested_and_panicking_scopes() {
    assert!(!TEST_SCALAR_ENABLED.with(std::cell::Cell::get));
    assert_eq!(scalar_enabled(), SCALAR_IS_EMPTY_ENABLED);
    {
        let _outer = TestScalarEnabled::enable();
        assert!(scalar_enabled());
        assert!(TEST_SCALAR_ENABLED.with(std::cell::Cell::get));
        {
            let _inner = TestScalarEnabled::enable();
            assert!(scalar_enabled());
            assert!(TEST_SCALAR_ENABLED.with(std::cell::Cell::get));
        }
        let _ = std::panic::catch_unwind(|| {
            let _inner = TestScalarEnabled::enable();
            panic!("test");
        });
        assert!(scalar_enabled());
        assert!(TEST_SCALAR_ENABLED.with(std::cell::Cell::get));
    }
    assert!(!TEST_SCALAR_ENABLED.with(std::cell::Cell::get));
    assert_eq!(scalar_enabled(), SCALAR_IS_EMPTY_ENABLED);
}

#[test]
fn metadata_override_restores_nested_and_panicking_scopes() {
    assert!(!TEST_ENABLED.with(std::cell::Cell::get));
    assert_eq!(enabled(), IS_EMPTY_ENABLED);
    {
        let _outer = TestEnabled::enable();
        assert!(enabled());
        assert!(TEST_ENABLED.with(std::cell::Cell::get));
        {
            let _inner = TestEnabled::enable();
            assert!(enabled());
            assert!(TEST_ENABLED.with(std::cell::Cell::get));
        }
        assert!(enabled());
        assert!(TEST_ENABLED.with(std::cell::Cell::get));
        let _ = std::panic::catch_unwind(|| {
            let _inner = TestEnabled::enable();
            panic!("test");
        });
        assert!(enabled());
        assert!(TEST_ENABLED.with(std::cell::Cell::get));
    }
    assert!(!TEST_ENABLED.with(std::cell::Cell::get));
    assert_eq!(enabled(), IS_EMPTY_ENABLED);
}

#[test]
fn compiler_issued_is_empty_requires_exact_metadata_body_and_live_original_role() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut engine = test_engine(tcx);
            let id = tcx
                .mir_keys(())
                .iter()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "root"
                })
                .unwrap()
                .to_def_id();
            let caller = engine
                .instantiated_body(ty::Instance::mono(tcx, id))
                .unwrap();
            let selected = caller
                .basic_blocks
                .iter()
                .find_map(|block| {
                    if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                        && let ty::FnDef(id, args) = func.ty(&caller.local_decls, tcx).kind()
                        && tcx.def_kind(*id) == DefKind::AssocFn
                        && tcx.item_name(*id).as_str() == "is_empty"
                    {
                        return Some(
                            engine
                                .resolve_function_item(*id, args.skip_binder())
                                .unwrap(),
                        );
                    }
                    None
                })
                .unwrap();
            assert_eq!(
                engine.mutable_metadata_operation(selected),
                IS_EMPTY_ENABLED
            );
            let _enabled = TestEnabled::enable();
            check_actual_float_metadata(tcx, &mut engine);
            for element in [tcx.types.bool, tcx.types.char, tcx.types.f32, tcx.types.u8] {
                let other = engine
                    .resolve_function_item(selected.def_id(), tcx.mk_args(&[element.into()]))
                    .unwrap();
                let admitted = SCALAR_IS_EMPTY_ENABLED
                    && (matches!(element.kind(), ty::Bool | ty::Char)
                        || (super::super::float_pairs::ENABLE_MUTABLE_FLOAT
                            && matches!(element.kind(), ty::Float(ty::FloatTy::F32))));
                assert_eq!(engine.issued_is_empty_candidate(other), admitted);
                assert_eq!(engine.mutable_metadata_operation(other), admitted);
            }
            {
                let _scalar = TestScalarEnabled::enable();
                for element in [
                    tcx.types.i8,
                    tcx.types.i32,
                    tcx.types.usize,
                    tcx.types.u128,
                    tcx.types.bool,
                    tcx.types.char,
                ] {
                    let scalar = engine
                        .resolve_function_item(selected.def_id(), tcx.mk_args(&[element.into()]))
                        .unwrap();
                    assert!(engine.issued_is_empty_candidate(scalar));
                    engine.certify_issued_is_empty(scalar).unwrap();
                    let mut memory = Memory::default();
                    let mut conditions = Vec::new();
                    engine
                        .mutable_u16_input(element, &mut memory, &mut conditions)
                        .unwrap();
                    let state = State {
                        flow: activation_flow::Flow::Unarmed,
                        locals: vec![],
                        addresses: vec![],
                        missing_places: Default::default(),
                        conditions,
                        memory,
                    };
                    let metadata = Value::MutableU16 {
                        id: 0,
                        role: MutableU16Role::Metadata { generation: 0 },
                    };
                    assert!(engine.mutable_slice_is_empty(
                        scalar, std::slice::from_ref(&metadata), &state,
                    ).unwrap().is_some());
                    let mut wrong_codec = state.clone();
                    let bits = u32::from(tcx.sess.target.pointer_width);
                    let wrong_sort = if element == tcx.types.bool {
                        Sort::BitVec(8)
                    } else {
                        Sort::Bool
                    };
                    std::rc::Rc::make_mut(&mut wrong_codec.memory.mutable_u16)[0].data =
                        super::mutable_u16::Storage::Scalar(engine.fresh(Sort::Array(
                            Box::new(Sort::BitVec(bits)),
                            Box::new(wrong_sort),
                        )));
                    let unchanged = wrong_codec.memory.mutable_u16[0].data.clone();
                    assert!(
                        engine
                            .mutable_slice_is_empty(
                                scalar,
                                std::slice::from_ref(&metadata),
                                &wrong_codec,
                            )
                            .is_err()
                    );
                    assert_eq!(wrong_codec.memory.mutable_u16[0].data, unchanged);
                    let mut wrong_context = state.clone();
                    std::rc::Rc::make_mut(&mut wrong_context.memory.mutable_u16)[0].length =
                        Value::Int {
                            expression: Context::default().bit_vector(0, bits).unwrap(),
                            bits,
                            signed: false,
                        };
                    assert!(
                        engine
                            .mutable_slice_is_empty(
                                scalar,
                                std::slice::from_ref(&metadata),
                                &wrong_context,
                            )
                            .is_err()
                    );
                    let mut invalid = state.clone();
                    invalid
                        .memory
                        .missing_places
                        .consume(invalid.memory.mutable_u16[0].allocation, vec![])
                        .unwrap();
                    assert!(
                        engine
                            .mutable_slice_is_empty(
                                scalar,
                                std::slice::from_ref(&metadata),
                                &invalid,
                            )
                            .is_err()
                    );
                    assert!(
                        engine
                            .mutable_slice_is_empty(
                                scalar,
                                &[Value::MutableU16 {
                                    id: 0,
                                    role: MutableU16Role::Metadata { generation: 1 },
                                }],
                                &state,
                            )
                            .is_err()
                    );
                    let wrong_element = if element == tcx.types.i32 {
                        tcx.types.u32
                    } else {
                        tcx.types.i32
                    };
                    let wrong = engine
                        .resolve_function_item(
                            selected.def_id(),
                            tcx.mk_args(&[wrong_element.into()]),
                        )
                        .unwrap();
                    assert!(
                        engine
                            .mutable_slice_is_empty(wrong, std::slice::from_ref(&metadata), &state,)
                            .is_err()
                    );
                    let original = engine.instantiated_body(scalar).unwrap();
                    let mut forged = (*original).clone();
                    forged.local_decls[rustc_middle::mir::Local::from_usize(1)].ty =
                        Ty::new_imm_ref(
                            tcx,
                            tcx.lifetimes.re_erased,
                            Ty::new_slice(tcx, wrong_element),
                        );
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(scalar, std::rc::Rc::new(forged));
                    assert!(engine.certify_issued_is_empty(scalar).is_err());
                    engine.bodies.borrow_mut().insert(scalar, original);
                }
                let byte = engine
                    .resolve_function_item(selected.def_id(), tcx.mk_args(&[tcx.types.u8.into()]))
                    .unwrap();
                assert!(!engine.issued_is_empty_candidate(byte));
            }
            assert!(!engine.issued_is_empty_candidate(ty::Instance::mono(tcx, id)));
            let closure_body = tcx
                .mir_keys(())
                .iter()
                .find(|id| tcx.def_kind(id.to_def_id()) == DefKind::Closure)
                .unwrap()
                .to_def_id();
            let closure = ty::Instance::new_raw(
                closure_body,
                ty::GenericArgs::identity_for_item(tcx, closure_body),
            );
            assert!(!engine.issued_is_empty_candidate(closure));
            engine.certify_issued_is_empty(selected).unwrap();
            let original = engine.instantiated_body(selected).unwrap();
            for mutation in [
                "source",
                "coroutine",
                "return",
                "receiver",
                "temporary",
                "op",
                "operand",
                "effect",
                "zero",
                "cleanup",
                "control",
            ] {
                let mut changed = (*original).clone();
                match mutation {
                    "source" => {
                        changed.source.instance = ty::InstanceKind::Virtual(selected.def_id(), 0)
                    }
                    "coroutine" => {
                        changed.coroutine =
                            Some(Box::new(rustc_middle::mir::CoroutineInfo::initial(
                                rustc_hir::CoroutineKind::Coroutine(rustc_hir::Movability::Movable),
                                tcx.types.unit,
                                tcx.types.unit,
                            )))
                    }
                    "return" => {
                        changed.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.usize
                    }
                    "receiver" => {
                        changed.local_decls[rustc_middle::mir::Local::from_usize(1)].ty =
                            Ty::new_imm_ref(
                                tcx,
                                tcx.lifetimes.re_erased,
                                Ty::new_slice(tcx, tcx.types.i16),
                            )
                    }
                    "temporary" => {
                        changed.local_decls[rustc_middle::mir::Local::from_usize(2)].ty =
                            tcx.types.u16
                    }
                    "effect" => {
                        let statement = changed.basic_blocks[START_BLOCK].statements[0].clone();
                        changed.basic_blocks.as_mut()[START_BLOCK]
                            .statements
                            .push(statement);
                    }
                    "cleanup" => changed.basic_blocks.as_mut()[START_BLOCK].is_cleanup = true,
                    "control" => {
                        changed.basic_blocks.as_mut()[START_BLOCK]
                            .terminator_mut()
                            .kind = TerminatorKind::Unreachable
                    }
                    "op" | "operand" | "zero" => {
                        let StatementKind::Assign(assignment) =
                            &mut changed.basic_blocks.as_mut()[START_BLOCK].statements[2].kind
                        else {
                            panic!("equality")
                        };
                        if mutation == "op" {
                            let Rvalue::BinaryOp(op, _) = &mut assignment.1 else {
                                panic!("op")
                            };
                            *op = BinOp::Ne;
                        } else {
                            let Rvalue::BinaryOp(_, operands) = &mut assignment.1 else {
                                panic!("operand")
                            };
                            if mutation == "zero" {
                                let Operand::Constant(constant) = &mut operands.1 else {
                                    panic!("constant")
                                };
                                constant.const_ = rustc_middle::mir::Const::Val(
                                    rustc_middle::mir::ConstValue::Scalar(
                                        rustc_middle::mir::interpret::Scalar::from_target_usize(
                                            1, &tcx,
                                        ),
                                    ),
                                    tcx.types.usize,
                                );
                            } else {
                                operands.0 = Operand::Move(Place::from(
                                    rustc_middle::mir::Local::from_usize(1),
                                ));
                            }
                        }
                    }
                    _ => panic!("mutation"),
                }
                engine
                    .bodies
                    .borrow_mut()
                    .insert(selected, std::rc::Rc::new(changed));
                assert!(
                    engine.certify_issued_is_empty(selected).is_err(),
                    "{mutation}"
                );
                engine
                    .bodies
                    .borrow_mut()
                    .insert(selected, original.clone());
            }
            let mut memory = Memory::default();
            let mut conditions = Vec::new();
            engine
                .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                .unwrap();
            let metadata = Value::MutableU16 {
                id: 0,
                role: MutableU16Role::Metadata { generation: 0 },
            };
            let state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![],
                addresses: vec![],
                missing_places: Default::default(),
                conditions,
                memory,
            };
            assert!(
                engine
                    .mutable_slice_is_empty(selected, std::slice::from_ref(&metadata), &state)
                    .unwrap()
                    .is_some()
            );
            let mut dead = state.clone();
            let allocation = dead.memory.mutable_u16[0].allocation;
            dead.memory[allocation] = None;
            assert!(
                engine
                    .mutable_slice_is_empty(selected, std::slice::from_ref(&metadata), &dead)
                    .is_err()
            );
            let mut masked = state.clone();
            masked
                .memory
                .missing_places
                .consume(allocation, vec![])
                .unwrap();
            assert!(
                engine
                    .mutable_slice_is_empty(selected, std::slice::from_ref(&metadata), &masked)
                    .is_err()
            );
            let mut foreign_context = state.clone();
            std::rc::Rc::make_mut(&mut foreign_context.memory.mutable_u16)[0].length = Value::Int {
                expression: Context::default()
                    .bit_vector(0, u32::from(tcx.sess.target.pointer_width))
                    .unwrap(),
                bits: u32::from(tcx.sess.target.pointer_width),
                signed: false,
            };
            assert!(
                engine
                    .mutable_slice_is_empty(
                        selected,
                        std::slice::from_ref(&metadata),
                        &foreign_context
                    )
                    .is_err()
            );
            let mut other_memory = Memory::default();
            engine
                .mutable_u16_input(tcx.types.i16, &mut other_memory, &mut Vec::new())
                .unwrap();
            let mut wrong_type = state.clone();
            std::rc::Rc::make_mut(&mut wrong_type.memory.mutable_u16)[0].certificate =
                other_memory.mutable_u16[0].certificate;
            assert!(
                engine
                    .mutable_slice_is_empty(selected, std::slice::from_ref(&metadata), &wrong_type)
                    .is_err()
            );
            let stale = Value::MutableU16 {
                id: 0,
                role: MutableU16Role::Metadata { generation: 1 },
            };
            assert!(
                engine
                    .mutable_slice_is_empty(selected, &[stale], &state)
                    .is_err()
            );
            let ghost = engine
                .mutable_u16_snapshot(
                    &Value::MutableU16 {
                        id: 0,
                        role: MutableU16Role::Root,
                    },
                    &state.memory,
                )
                .unwrap();
            assert!(
                engine
                    .mutable_slice_is_empty(selected, std::slice::from_ref(&ghost), &state)
                    .is_err()
            );
            // The public call boundary must reject a Ghost and a consumed source handle.
            let mut boundary = (*original).clone();
            let local = rustc_middle::mir::Local::from_usize(1);
            let mut boundary_state = state.clone();
            boundary_state.locals = vec![Some(Value::Uninitialized), Some(ghost)];
            boundary_state.addresses = vec![None; 2];
            let args = [rustc_span::Spanned {
                node: Operand::Copy(Place::from(local)),
                span: rustc_span::DUMMY_SP,
            }];
            assert!(
                engine
                    .mutable_u16_call_allowed(&boundary, &boundary_state, selected, &args)
                    .is_err()
            );
            boundary_state.locals[1] = Some(metadata.clone());
            boundary_state.missing_places.consume(1, vec![]).unwrap();
            assert!(
                engine
                    .mutable_u16_call_allowed(&boundary, &boundary_state, selected, &args)
                    .is_err()
            );
            boundary_state.missing_places = Default::default();
            boundary.local_decls[local].ty = Ty::new_imm_ref(
                tcx,
                tcx.lifetimes.re_erased,
                Ty::new_slice(tcx, tcx.types.i16),
            );
            assert!(
                engine
                    .mutable_u16_call_allowed(&boundary, &boundary_state, selected, &args)
                    .is_err()
            );
            for name in [
                "root",
                "whole",
                "proper",
                "proper_empty",
                "len_anchor",
                "nested",
            ] {
                let mut engine = test_engine(tcx);
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap()
                    .to_def_id();
                let instance = ty::Instance::mono(tcx, id);
                let body = engine.instantiated_body(instance).unwrap();
                let mut memory = Memory::default();
                let mut conditions = Vec::new();
                let mut values = Vec::new();
                for local in body.args_iter() {
                    let original = body.local_decls[local].ty;
                    if matches!(original.kind(), ty::Ref(..)) {
                        values.push(
                            engine
                                .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                                .unwrap(),
                        );
                    } else {
                        let (bits, signed) = engine.integer_type(original).unwrap();
                        values.push(Value::Int {
                            expression: engine.fresh(Sort::BitVec(bits)),
                            bits,
                            signed,
                        });
                    }
                }
                engine
                    .execute_body(
                        instance,
                        values,
                        conditions,
                        memory,
                        &[],
                        activation_flow::Flow::Unarmed,
                    )
                    .unwrap();
                assert_eq!(engine.proof.status, ProofStatus::Proved, "{name}");
            }
            println!(
                "actual issued is_empty profile {} passed",
                tcx.sess.target.llvm_target
            );
            rustc_driver::Compilation::Stop
        }
    }
    let time = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "miren-stage210-compiler-lifecycle-{}-{time}",
        std::process::id(),
    ));
    // Exclusive creation refuses any collision rather than overwriting another invocation.
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("fixture.rs");
    std::fs::write(
        &source,
        format!(
            concat!(
                "{}\n",
                "pub fn float_root32(values:&mut [f32]) {{",
                " assert!(values.is_empty()==(values.len()==0)); }}\n",
                "pub fn float_root64(values:&mut [f64]) {{",
                " assert!(values.is_empty()==(values.len()==0)); }}\n",
                "pub fn closure_guard(value:u16)->u16 {{",
                " let callback=|word:u16|word; callback(value) }}\n",
                "#[inline(never)] pub fn intermediate(values: &mut [u16], value: u16) {{",
                " child(values, value); }}\n",
                "pub fn nested(values: &mut [u16], value: u16) {{ if values.len() > 0 {{",
                " intermediate(values, value); assert!(values[0] == value); }} }}\n",
            ),
            include_str!("../../../../tests/fixtures/issued_is_empty.rs"),
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let out = directory.join(format!("{}-{level}", target.unwrap_or("host")));
            std::fs::create_dir_all(&out).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                out.display().to_string(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "-Zmir-opt-level=0".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture);
        }
    }
}

fn check_actual_float_metadata<'tcx>(tcx: TyCtxt<'tcx>, engine: &mut Engine<'tcx>) {
    // The envelope comes from the existing actual scalar body, not an assertion-heavy
    // unsupported caller or a fabricated Float activation frame.
    let id = tcx
        .mir_keys(())
        .iter()
        .copied()
        .find(|id| {
            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && tcx.item_name(id.to_def_id()).as_str() == "word"
        })
        .unwrap()
        .to_def_id();
    let root = ty::Instance::mono(tcx, id);
    let root_body = engine.instantiated_body(root).unwrap();
    for (name, element) in [
        ("float_root32", tcx.types.f32),
        ("float_root64", tcx.types.f64),
    ] {
        let id = tcx
            .mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == name
            })
            .unwrap();
        let caller = engine
            .instantiated_body(ty::Instance::mono(tcx, id.to_def_id()))
            .unwrap();
        let instance = caller
            .basic_blocks
            .iter()
            .find_map(|block| {
                let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                    return None;
                };
                let ty::FnDef(id, args) = func.ty(&caller.local_decls, tcx).kind() else {
                    return None;
                };
                if tcx.item_name(*id).as_str() != "is_empty" {
                    return None;
                }
                Some(
                    engine
                        .resolve_function_item(*id, args.skip_binder())
                        .unwrap(),
                )
            })
            .unwrap();
        assert!(engine.issued_float_is_empty_candidate(instance));
        engine.certify_issued_is_empty(instance).unwrap();
        let mut memory = Memory::default();
        let mut conditions = Vec::new();
        let input = engine
            .mutable_u16_input(element, &mut memory, &mut conditions)
            .unwrap();
        let id = memory.mutable_u16.len() - 1;
        let state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: Vec::new(),
            missing_places: Default::default(),
            conditions,
            addresses: Vec::new(),
            memory,
        };
        let metadata = Value::MutableU16 {
            id,
            role: MutableU16Role::Metadata { generation: 0 },
        };
        let data = state.memory.mutable_u16[id].data.clone();
        let length = state.memory.mutable_u16[id].length.clone();
        let before_conditions = state.conditions.clone();
        let result = engine
            .mutable_slice_is_empty(instance, std::slice::from_ref(&metadata), &state)
            .unwrap()
            .unwrap();
        let bits = u32::from(tcx.sess.target.pointer_width);
        let expected = symbolic::binary(
            &engine.terms,
            "eq",
            length.clone(),
            symbolic::integer(&engine.terms, 0, bits, false),
        )
        .unwrap();
        assert_eq!(result.boolean().unwrap(), expected.boolean().unwrap());
        assert_eq!(state.conditions, before_conditions);
        assert_eq!(state.memory.mutable_u16[id].data, data);
        assert_eq!(
            state.memory.mutable_u16[id].length.integer().unwrap(),
            length.integer().unwrap()
        );
        assert_eq!(state.memory.mutable_u16[id].generation, 0);
        let stale = Value::MutableU16 {
            id,
            role: MutableU16Role::Metadata { generation: 1 },
        };
        assert!(
            engine
                .mutable_slice_is_empty(instance, &[stale], &state)
                .is_err()
        );
        assert!(
            engine
                .mutable_slice_is_empty(instance, std::slice::from_ref(&input), &state)
                .is_err()
        );
        let ghost = engine.mutable_u16_snapshot(&input, &state.memory).unwrap();
        assert!(
            engine
                .mutable_slice_is_empty(instance, &[ghost], &state)
                .is_err()
        );
        let mut masked = state.clone();
        masked
            .memory
            .missing_places
            .consume(masked.memory.mutable_u16[id].allocation, vec![])
            .unwrap();
        assert!(
            engine
                .mutable_slice_is_empty(instance, std::slice::from_ref(&metadata), &masked)
                .is_err()
        );
        let mut dead = state.clone();
        std::rc::Rc::make_mut(&mut dead.memory.mutable_u16).clear();
        assert!(
            engine
                .mutable_slice_is_empty(instance, std::slice::from_ref(&metadata), &dead)
                .is_err()
        );
        let mut foreign = state.clone();
        std::rc::Rc::make_mut(&mut foreign.memory.mutable_u16)[id].length =
            symbolic::integer(&Context::default(), 0, bits, false);
        assert!(
            engine
                .mutable_slice_is_empty(instance, std::slice::from_ref(&metadata), &foreign)
                .is_err()
        );
        let mut wrong_length = state.clone();
        std::rc::Rc::make_mut(&mut wrong_length.memory.mutable_u16)[id].length =
            symbolic::integer(&engine.terms, 0, bits, true);
        assert!(
            engine
                .mutable_slice_is_empty(instance, std::slice::from_ref(&metadata), &wrong_length)
                .is_err()
        );
        let other = if element == tcx.types.f32 {
            tcx.types.f64
        } else {
            tcx.types.f32
        };
        let different = engine
            .resolve_function_item(instance.def_id(), tcx.mk_args(&[other.into()]))
            .unwrap();
        assert!(
            engine
                .mutable_slice_is_empty(different, std::slice::from_ref(&metadata), &state)
                .is_err()
        );
        let body = engine.instantiated_body(instance).unwrap();
        let mut forged = (*body).clone();
        forged.local_decls[rustc_middle::mir::Local::from_usize(1)].ty =
            Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, Ty::new_slice(tcx, other));
        engine
            .bodies
            .borrow_mut()
            .insert(instance, std::rc::Rc::new(forged));
        assert!(engine.certify_issued_is_empty(instance).is_err());
        engine.bodies.borrow_mut().insert(instance, body);
        let armed = engine.activation_test_root(root, &root_body).unwrap();
        let mut armed_state = state.clone();
        armed_state.flow = armed;
        let cache = engine.bodies.borrow().len();
        let obligations = engine.proof.obligations.len();
        let before = engine.terms.bit_vector(0x51ee_3011, 64).unwrap();
        assert!(
            matches!(engine.activation_armed_call_route(&armed_state.flow, instance),
            Err(reason) if reason == "armed Float metadata adapter is not implemented")
        );
        assert!(
            matches!(engine.mutable_slice_is_empty(instance, &[metadata], &armed_state),
            Err(reason) if reason == "armed activation adapter is not implemented")
        );
        let after = engine.terms.bit_vector(0x51ee_3012, 64).unwrap();
        assert_eq!(after.id(), before.id() + 1);
        assert_eq!(engine.proof.obligations.len(), obligations);
        assert_eq!(engine.bodies.borrow().len(), cache);
        assert_eq!(armed_state.memory.mutable_u16[id].data, data);
        eprintln!("actual issued Float metadata {name}: current length only; Armed refused early");
    }
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
