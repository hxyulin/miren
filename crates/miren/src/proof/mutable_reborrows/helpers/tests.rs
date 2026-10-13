use super::*;

#[test]
fn actual_primitive_helper_lease_preserves_owner_and_rejects_hostile_state() {
    struct Check {
        done: bool,
        nested: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let config = miren::ContractConfig::default();
            let options = VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            };
            let mut engine = Engine::new(tcx, &config, options);
            let caller_id = tcx
                .mir_keys(())
                .iter()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str()
                            == if self.nested {
                                "nested_unknown"
                            } else {
                                "scalar"
                            }
                })
                .unwrap()
                .to_def_id();
            let caller = ty::Instance::mono(tcx, caller_id);
            let body = engine.instantiated_body(caller).unwrap();
            let calls = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target: Some(target),
                        ..
                    } = &data.terminator().kind
                    else {
                        return None;
                    };
                    let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
                        return None;
                    };
                    let callee = engine
                        .resolve_function_item(*id, generic.skip_binder())
                        .unwrap();
                    Some((block, callee, args.as_ref(), *destination, *target))
                })
                .collect::<Vec<_>>();
            let &(range_block, range, args, destination, target) = calls
                .iter()
                .find(|(_, i, _, _, _)| {
                    pure_comparison_templates::definition_key(i.def_id())
                        == "DefId(core::slice::index::{impl#1}::index_mut)"
                })
                .unwrap();
            let &(helper_block, helper, helper_args, helper_destination, helper_target) = calls
                .iter()
                .find(|(_, i, _, _, _)| {
                    tcx.item_name(i.def_id()).as_str()
                        == if self.nested { "nested_flip" } else { "flip" }
                })
                .unwrap();
            let mut memory = Memory::default();
            let mut conditions = Vec::new();
            let root = engine
                .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                .unwrap();
            Rc::make_mut(&mut memory.mutable_u16)[0].length = symbolic::integer(
                &engine.terms,
                2,
                u32::from(tcx.sess.target.pointer_width),
                false,
            );
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                missing_places: Default::default(),
                conditions,
                memory,
            };
            state.locals[1] = Some(root);
            state.locals[2] = Some(symbolic::integer(&engine.terms, 14, 16, false));
            for statement in &body.basic_blocks[range_block].statements {
                engine
                    .statement(caller, &body, &mut state, &statement.kind)
                    .unwrap();
            }
            let (_, mut state) = engine
                .mutable_retained_call(
                    &state,
                    ChildCall {
                        body: &body,
                        block: range_block,
                        instance: range,
                        args,
                        destination,
                        target: Some(target),
                        stack: &[],
                        site: (caller_id, body.span),
                    },
                )
                .unwrap()
                .unwrap();
            for statement in &body.basic_blocks[target].statements {
                engine
                    .statement(caller, &body, &mut state, &statement.kind)
                    .unwrap();
            }
            let &(len_block, len, len_args, len_destination, len_target) = calls
                .iter()
                .find(|(block, _, _, _, _)| *block == target)
                .unwrap();
            assert_eq!(len_block, target);
            engine.certify_mutable_u16_len(len).unwrap();
            let argument = engine
                .evaluate_operand(caller_id, &body, &mut state, &len_args[0].node)
                .unwrap();
            let length = engine.mutable_owner_length(&argument, &state).unwrap();
            engine.write(&mut state, len_destination, length).unwrap();
            for statement in &body.basic_blocks[len_target].statements {
                engine
                    .statement(caller, &body, &mut state, &statement.kind)
                    .unwrap();
            }
            for statement in &body.basic_blocks[helper_block].statements {
                engine
                    .statement(caller, &body, &mut state, &statement.kind)
                    .unwrap();
            }
            let signature = checked_signature(&mut engine, helper).unwrap();
            for mutation in 0..4 {
                let poisoned = match mutation {
                    0 => signature.map_bound(|s| s.set_safety(rustc_hir::Safety::Unsafe)),
                    1 => signature.map_bound(|s| ty::FnSig {
                        fn_sig_kind: s
                            .fn_sig_kind
                            .set_abi(rustc_abi::ExternAbi::C { unwind: false }),
                        ..s
                    }),
                    2 => ty::Binder::bind_with_vars(
                        signature.skip_binder(),
                        tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Ty(
                            ty::BoundTyKind::Anon,
                        )]),
                    ),
                    3 => signature.map_bound(|s| ty::FnSig {
                        inputs_and_output: tcx.mk_type_list(&[tcx.types.u8, tcx.types.u16]),
                        ..s
                    }),
                    _ => unreachable!(),
                };
                engine.call_signatures.borrow_mut().insert(helper, poisoned);
                let before = engine.steps;
                assert!(checked_signature(&mut engine, helper).is_err());
                assert!(engine.steps > before);
                let mut hostile = state.clone();
                assert!(
                    engine
                        .retained_primitive_helper_call(
                            caller,
                            &body,
                            &mut hostile,
                            ChildCall {
                                body: &body,
                                block: helper_block,
                                instance: helper,
                                args: helper_args,
                                destination: helper_destination,
                                target: Some(helper_target),
                                stack: &[],
                                site: (caller_id, body.span),
                            },
                            None,
                        )
                        .is_err()
                );
                engine
                    .call_signatures
                    .borrow_mut()
                    .insert(helper, signature);
            }
            let helper_body =
                array_iterator_constructors::steps::authenticated_helper_body(&mut engine, helper)
                    .unwrap();
            let lease = Invocation::capture(
                &mut engine,
                Site {
                    caller,
                    caller_body: body.clone(),
                    callee: helper,
                    callee_body: helper_body.clone(),
                    block: helper_block,
                    target: helper_target,
                    destination: helper_destination,
                },
                &state,
            )
            .unwrap();
            lease
                .check(&mut engine, &helper_body, &state.memory)
                .unwrap();
            let Phase::Retained { carrier, .. } = &state.memory.mutable_u16[0].phase else {
                unreachable!()
            };
            if !self.nested {
                assert!(
                    helper_body
                        .basic_blocks
                        .iter()
                        .flat_map(|b| &b.statements)
                        .any(|s| matches!(s.kind, StatementKind::StorageDead(local)
                        if local.as_usize() == *carrier)),
                    "actual callee local collision"
                );
            }
            assert!(lease.check(&mut engine, &body, &state.memory).is_err());
            let mut changed_body = helper_body.as_ref().clone();
            changed_body.basic_blocks.as_mut()[BasicBlock::from_usize(0)].statements[0].kind =
                StatementKind::Nop;
            engine
                .bodies
                .borrow_mut()
                .insert(helper, Rc::new(changed_body));
            assert!(
                lease
                    .check(&mut engine, &helper_body, &state.memory)
                    .is_err()
            );
            engine
                .bodies
                .borrow_mut()
                .insert(helper, helper_body.clone());
            let mut orphan = None;
            if self.nested {
                let (block, callee, destination, target) = helper_body
                    .basic_blocks
                    .iter_enumerated()
                    .find_map(|(block, data)| {
                        let TerminatorKind::Call {
                            func,
                            destination,
                            target: Some(target),
                            ..
                        } = &data.terminator().kind
                        else {
                            return None;
                        };
                        let ty::FnDef(id, generic) = func.ty(&helper_body.local_decls, tcx).kind()
                        else {
                            return None;
                        };
                        let callee = engine
                            .resolve_function_item(*id, generic.skip_binder())
                            .unwrap();
                        Some((block, callee, *destination, *target))
                    })
                    .unwrap();
                let nested_body = array_iterator_constructors::steps::authenticated_helper_body(
                    &mut engine,
                    callee,
                )
                .unwrap();
                let signature = checked_signature(&mut engine, callee).unwrap();
                let mut child = lease
                    .derive(
                        &mut engine,
                        Site {
                            caller: helper,
                            caller_body: helper_body.clone(),
                            callee,
                            callee_body: nested_body.clone(),
                            block,
                            target,
                            destination,
                        },
                        &state,
                        signature,
                    )
                    .unwrap();
                child
                    .check(&mut engine, &nested_body, &state.memory)
                    .unwrap();
                assert!(
                    child
                        .scope(&mut engine, &helper_body, &state.memory)
                        .is_err()
                );
                assert!(
                    lease
                        .derive(
                            &mut engine,
                            Site {
                                caller,
                                caller_body: body.clone(),
                                callee,
                                callee_body: nested_body.clone(),
                                block,
                                target,
                                destination,
                            },
                            &state,
                            signature
                        )
                        .is_err()
                );
                let original_signature = engine.call_signatures.borrow()[&helper];
                engine.call_signatures.borrow_mut().insert(
                    helper,
                    original_signature.map_bound(|s| s.set_safety(rustc_hir::Safety::Unsafe)),
                );
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                engine
                    .call_signatures
                    .borrow_mut()
                    .insert(helper, original_signature);
                for ancestor in [caller, helper] {
                    let original = engine.bodies.borrow()[&ancestor].clone();
                    let mut changed = original.as_ref().clone();
                    changed.basic_blocks.as_mut()[START_BLOCK].is_cleanup = true;
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(ancestor, Rc::new(changed));
                    assert!(
                        child
                            .scope(&mut engine, &nested_body, &state.memory)
                            .is_err()
                    );
                    engine.bodies.borrow_mut().insert(ancestor, original);
                }
                let edge = Rc::get_mut(&mut child.edge).unwrap();
                edge.occurrence ^= 1;
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                Rc::get_mut(&mut child.edge).unwrap().occurrence ^= 1;
                Rc::get_mut(&mut child.edge).unwrap().depth += 1;
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                Rc::get_mut(&mut child.edge).unwrap().depth -= 1;
                let ancestor_token = lease.token.clone();
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                drop(ancestor_token);
                let token = child.token.clone();
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                drop(token);
                child
                    .scope(&mut engine, &nested_body, &state.memory)
                    .unwrap();
                let limit = engine.limits.max_call_depth;
                engine.limits.max_call_depth = 1;
                assert!(
                    child
                        .scope(&mut engine, &nested_body, &state.memory)
                        .is_err()
                );
                engine.limits.max_call_depth = limit;
                let storage = state.memory.storage_slots();
                let mut full = state.clone();
                while full.memory.storage_slots() < MAX_INPUT_VALUES {
                    full.memory.push(Some(Value::Unit));
                }
                assert!(full.memory.storage_slots() > storage);
                assert!(
                    lease
                        .derive(
                            &mut engine,
                            Site {
                                caller: helper,
                                caller_body: helper_body.clone(),
                                callee,
                                callee_body: nested_body.clone(),
                                block,
                                target,
                                destination,
                            },
                            &full,
                            signature
                        )
                        .is_err()
                );
                orphan = Some(child);
                println!(
                    "Actual nested retained child/ancestor/cache/edge/token/depth/storage controls"
                );
            }
            for mutation in 0..5 {
                let mut changed = state.memory.clone();
                let backing = &mut Rc::make_mut(&mut changed.mutable_u16)[0];
                match mutation {
                    0 => backing.generation += 1,
                    1 => {
                        let Phase::Retained { carrier, .. } = &mut backing.phase else {
                            unreachable!()
                        };
                        *carrier += 1;
                    }
                    2 => {
                        backing.data = Storage::Scalar(
                            engine
                                .terms
                                .symbol(
                                    500,
                                    Sort::Array(
                                        Box::new(Sort::BitVec(u32::from(
                                            tcx.sess.target.pointer_width,
                                        ))),
                                        Box::new(Sort::BitVec(16)),
                                    ),
                                )
                                .unwrap(),
                        )
                    }
                    3 => {
                        let Phase::Retained { metadata, .. } = &mut backing.phase else {
                            unreachable!()
                        };
                        metadata[0].1 ^= 1;
                    }
                    4 => {
                        backing.length = symbolic::integer(
                            &engine.terms,
                            3,
                            u32::from(tcx.sess.target.pointer_width),
                            false,
                        )
                    }
                    _ => unreachable!(),
                }
                assert!(lease.check(&mut engine, &helper_body, &changed).is_err());
            }
            let mut missing = state.memory.clone();
            missing
                .missing_places
                .consume(lease.root.allocation, Vec::new())
                .unwrap();
            assert!(lease.check(&mut engine, &helper_body, &missing).is_err());
            let foreign = symbolic::Context::default();
            let mut changed = state.memory.clone();
            Rc::make_mut(&mut changed.mutable_u16)[0].length =
                symbolic::integer(&foreign, 2, u32::from(tcx.sess.target.pointer_width), false);
            assert!(lease.check(&mut engine, &helper_body, &changed).is_err());
            // An unrelated incoming reference remains subject to the ordinary graph check.
            let mut escaped = state.clone();
            let incoming = escaped.memory.len() + 1;
            escaped.memory.push(Some(Value::Reference {
                allocation: incoming,
                projection: Vec::new(),
                mutable: false,
            }));
            escaped.memory.push(Some(Value::Unit));
            lease
                .check(&mut engine, &helper_body, &escaped.memory)
                .unwrap();
            assert!(
                engine
                    .validate_frame_escape(&Value::Unit, &escaped, incoming)
                    .is_err()
            );
            for raw in [0xd800, 0xdfff, 0x110000] {
                let invalid = symbolic::integer(&engine.terms, raw, 32, false);
                assert!(primitive_value(&mut engine, tcx.types.char, &invalid, &[]).is_err());
            }
            let valid = symbolic::integer(&engine.terms, 0x10ffff, 32, false);
            primitive_value(&mut engine, tcx.types.char, &valid, &[]).unwrap();
            let bad_float = Value::Float {
                expression: engine.terms.boolean(true),
                bits: 32,
                raw_bits: Some(engine.terms.bit_vector(0, 32).unwrap()),
            };
            assert!(primitive_value(&mut engine, tcx.types.f32, &bad_float, &[]).is_err());
            let foreign_float = symbolic::float(&foreign, 0, 32);
            assert!(primitive_value(&mut engine, tcx.types.f32, &foreign_float, &[]).is_err());
            let mut mismatched = symbolic::float(&engine.terms, 0, 32);
            let Value::Float { raw_bits, .. } = &mut mismatched else {
                unreachable!()
            };
            *raw_bits = Some(engine.terms.bit_vector(0x3f80_0000, 32).unwrap());
            assert!(primitive_value(&mut engine, tcx.types.f32, &mismatched, &[]).is_err());
            let checked = match orphan {
                Some(child) => {
                    drop(lease);
                    let body = child.edge.callee_body.clone();
                    assert!(
                        child
                            .scope(&mut engine, &body, &state.memory)
                            .unwrap_err()
                            .contains("ancestor frame has ended")
                    );
                    println!("Actual dropped retained ancestor token refused");
                    child
                }
                None => lease,
            };
            let stopped = engine.steps;
            engine.limits.max_steps = stopped;
            let body = checked.edge.callee_body.clone();
            assert!(checked.check(&mut engine, &body, &state.memory).is_err());
            assert!(engine.steps > stopped);
            println!(
                "Actual retained helper signature/owner/body/metadata/escape/scalar validity controls"
            );
            self.done = true;
            rustc_driver::Compilation::Stop
        }
    }
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/retained_scalar_helpers.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            for nested in [false, true] {
                let mut callbacks = Check {
                    done: false,
                    nested,
                };
                let mut args = vec![
                    "rustc".into(),
                    source.display().to_string(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Cpanic=abort".into(),
                    "-Zmir-opt-level=0".into(),
                    format!("-Copt-level={level}"),
                    "--sysroot".into(),
                    env!("MIREN_SYSROOT").into(),
                ];
                if let Some(target) = target {
                    args.extend(["--target".into(), target.into()]);
                }
                rustc_driver::run_compiler(&args, &mut callbacks);
                assert!(callbacks.done);
            }
        }
    }
}

#[test]
fn actual_nested_function_trait_call_resolves_to_a_function_pointer_shim() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = super::super::super::nonzero_niches::test_engine(tcx);
            let id = tcx
                .mir_keys(())
                .iter()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "shim_middle"
                })
                .unwrap()
                .to_def_id();
            let body = engine
                .instantiated_body(ty::Instance::mono(tcx, id))
                .unwrap();
            let instance = body
                .basic_blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
                        return None;
                    };
                    Some(
                        engine
                            .resolve_function_item(*id, generic.skip_binder())
                            .unwrap(),
                    )
                })
                .unwrap();
            assert!(
                matches!(
                    instance.def,
                    ty::InstanceKind::Shim(ty::ShimKind::FnPtr(..))
                ),
                "{instance:?}"
            );
            println!("Actual nested Fn::call resolves to FnPtrShim: {instance:?}");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/nested_retained_scalar_shim.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                source.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut check = Check(false);
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}
