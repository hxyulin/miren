//! Actual root-issued storage transactions, separate from whole-program proof outcomes.
use super::super::mutable_u16::Storage;
use super::super::nonzero_niches::mutable_codec::input_descriptor;
use super::*;

fn original_places<'a, 'tcx>(
    body: &'a Body<'tcx>,
    original: Ty<'tcx>,
) -> (
    &'a StatementKind<'tcx>,
    &'a Operand<'tcx>,
    &'a StatementKind<'tcx>,
    Place<'tcx>,
) {
    let read = body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return None;
            };
            let Rvalue::Use(operand, _) = &assignment.1 else {
                return None;
            };
            let (Operand::Copy(place) | Operand::Move(place)) = operand else {
                return None;
            };
            let same_type = matches!(place.projection.last(),
                Some(ProjectionElem::Field(_, ty)) if *ty == original);
            (place.projection.len() >= 3 && same_type).then_some((&statement.kind, operand))
        })
        .expect("actual owner enum read");
    let store = body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return None;
            };
            let place = assignment.0;
            let same_type = matches!(place.projection.last(),
                Some(ProjectionElem::Field(_, ty)) if *ty == original);
            (place.projection.len() >= 3 && same_type).then_some((&statement.kind, place))
        })
        .expect("actual owner enum replacement");
    (read.0, read.1, store.0, store.1)
}

fn set_payload(value: &mut Value, context: &Context, word: u128) {
    match value {
        Value::Int { bits, signed, .. } => {
            *value = symbolic::integer(context, word, *bits, *signed)
        }
        Value::Adt { fields, .. } => {
            for (_, value) in fields.iter_mut() {
                set_payload(value, context, word);
            }
        }
        _ => panic!("expected compiler integer payload wrappers"),
    }
}

fn retained(before: &State, after: &State) {
    assert!(Rc::ptr_eq(
        &before.memory.mutable_u16,
        &after.memory.mutable_u16
    ));
    assert!(Rc::ptr_eq(
        &before.memory.initialized_owners,
        &after.memory.initialized_owners
    ));
    assert!(Rc::ptr_eq(
        &before.memory.owned_regions,
        &after.memory.owned_regions
    ));
    assert_eq!(
        before.memory.mutable_hierarchy,
        after.memory.mutable_hierarchy
    );
    assert_eq!(
        format!("{:?}", before.memory.missing_places),
        format!("{:?}", after.memory.missing_places)
    );
    assert_eq!(
        format!("{:?}", before.missing_places),
        format!("{:?}", after.missing_places)
    );
    assert_eq!(
        format!("{:?}", before.memory.mutable_u16),
        format!("{:?}", after.memory.mutable_u16)
    );
}

#[test]
fn actual_root_niche_owner_transactions_and_refusals() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let id = tcx
                .hir_body_owners()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "option_u8"
                })
                .unwrap()
                .to_def_id();
            let instance = ty::Instance::mono(tcx, id);
            for denial in 0..28 {
                let mut engine = super::super::nonzero_niches::test_engine(tcx);
                engine.limits.max_steps = 2_000_000;
                let body = engine.instantiated_body(instance).unwrap();
                let mut memory = Memory::default();
                let mut conditions = Vec::new();
                let phase = engine.niche_root_inputs.begin(id).unwrap();
                let token = input_descriptor::prepare_root(
                    &mut engine,
                    id,
                    &body,
                    rustc_middle::mir::Local::from_usize(1),
                    &memory,
                )
                .unwrap()
                .unwrap();
                let owner = engine
                    .mutable_product_niche_input(token, &mut memory, &mut conditions)
                    .unwrap();
                phase.close();
                assert!(
                    input_descriptor::prepare_root(
                        &mut engine,
                        id,
                        &body,
                        rustc_middle::mir::Local::from_usize(1),
                        &memory
                    )
                    .is_err()
                );
                let bits = u32::from(tcx.sess.target.pointer_width);
                let zero = symbolic::integer(&engine.terms, 0, bits, false);
                let length = memory.mutable_u16[0].length.integer().unwrap().0.clone();
                conditions.push(
                    engine
                        .terms
                        .apply(
                            Op::BvUnsignedLt,
                            &[zero.integer().unwrap().0.clone(), length],
                        )
                        .unwrap(),
                );
                let mut state = State {
                    flow: activation_flow::Flow::Unarmed,
                    locals: vec![Some(zero.clone()); body.local_decls.len()],
                    constant_receipts: Default::default(),
                    missing_places: Default::default(),
                    conditions,
                    addresses: vec![None; body.local_decls.len()],
                    memory,
                };
                state.locals[1] = Some(owner);
                let frame = engine.niche_frame_begin(&state.memory).unwrap().unwrap();
                let ty::Ref(_, slice, _) = body.local_decls
                    [rustc_middle::mir::Local::from_usize(1)]
                .ty
                .kind() else {
                    panic!("actual input reference");
                };
                let ty::Slice(product) = slice.kind() else {
                    panic!("actual input slice");
                };
                let ty::Tuple(fields) = product.kind() else {
                    panic!("actual product");
                };
                let (read, operand, store, place) = original_places(&body, fields[0]);
                engine
                    .niche_statement_scope(instance, &body, &state, read)
                    .unwrap();
                let mut value = engine
                    .evaluate_operand(id, &body, &mut state, operand)
                    .unwrap();
                engine
                    .niche_statement_scope(instance, &body, &state, store)
                    .unwrap();
                let mut before = state.clone();
                if matches!(denial, 0 | 22 | 23) {
                    let Value::Enum {
                        discriminant,
                        variants,
                        ..
                    } = &mut value
                    else {
                        panic!("compiler-bound original enum value");
                    };
                    **discriminant = symbolic::integer(&engine.terms, 1, bits, true);
                    set_payload(&mut variants[1], &engine.terms, 7);
                }
                match denial {
                    0 => {}
                    1 | 2 => {
                        let Value::Enum { discriminant, .. } = &mut value else {
                            panic!("correlated compiler enum");
                        };
                        let context = if denial == 1 {
                            &engine.terms
                        } else {
                            &Context::default()
                        };
                        **discriminant = symbolic::integer(context, 2, bits, true);
                    }
                    3 => {
                        engine
                            .niche_ledger
                            .current
                            .borrow_mut()
                            .as_mut()
                            .unwrap()
                            .value_work = 0
                    }
                    4 => {
                        engine
                            .niche_ledger
                            .current
                            .borrow_mut()
                            .as_mut()
                            .unwrap()
                            .remaining = 0
                    }
                    5 => {
                        engine
                            .bodies
                            .borrow_mut()
                            .insert(instance, Rc::new((*body).clone()));
                    }
                    6 => {
                        let held = engine.niche_ledger.current.borrow();
                        engine.niche_scope_end(true);
                        drop(held);
                        assert!(engine.niche_ledger.failed.get());
                        assert!(engine.niche_certificate_work(0).is_err());
                    }
                    7 => {
                        engine.limits.max_steps = engine.steps.used();
                        assert!(
                            engine
                                .niche_statement_scope(instance, &body, &state, store)
                                .is_err()
                        );
                        engine.niche_scope_end(true);
                    }
                    8 => {
                        let frames = engine.niche_ledger.frames.clone();
                        let held = frames.borrow_mut();
                        drop(frame);
                        drop(held);
                        assert!(engine.niche_certificate_work(0).is_err());
                        retained(&before, &state);
                        eprintln!(
                            "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                            tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                        );
                        continue;
                    }
                    9 => {
                        let foreign = Context::default();
                        let Storage::Product(columns) =
                            &mut Rc::make_mut(&mut state.memory.mutable_u16)[0].data
                        else {
                            panic!("actual product columns");
                        };
                        columns[0] = foreign.symbol(0, columns[0].sort().clone()).unwrap();
                        before = state.clone();
                    }
                    10 => {
                        let mut active = engine.niche_ledger.current.borrow_mut();
                        let scope = active.as_mut().unwrap();
                        let lookup = scope.leaves.len() * 24 + scope.conditions.len() + 32;
                        // Node and receipt lookup, then column clone fit; the separately
                        // consumed first Store construction does not. No COW has occurred.
                        scope.value_work = 128 + lookup + 2 * 32 + 64;
                    }
                    11 => {
                        let Value::Enum {
                            discriminant,
                            variants,
                            ..
                        } = &mut value
                        else {
                            panic!("correlated enum");
                        };
                        **discriminant = symbolic::integer(&engine.terms, 1, bits, true);
                        set_payload(&mut variants[1], &engine.terms, 0);
                    }
                    12 | 13 => {
                        let result = if denial == 12 {
                            let _held = engine.bodies.borrow_mut();
                            engine.mutable_product_store(&body, &mut state, place, &value)
                        } else {
                            let _held = engine.call_signatures.borrow_mut();
                            engine.mutable_product_store(&body, &mut state, place, &value)
                        };
                        assert!(result.is_err());
                        assert!(engine.niche_ledger.failed.get());
                        retained(&before, &state);
                        drop(frame);
                        eprintln!(
                            "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                            tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                        );
                        continue;
                    }
                    14 => {
                        engine.mutable_integer_types[0].alignment += 1;
                    }
                    15 | 16 => {
                        let frames = engine.niche_ledger.frames.clone();
                        let _held = frames.borrow_mut();
                        if denial == 15 {
                            assert!(
                                engine
                                    .mutable_product_store(&body, &mut state, place, &value)
                                    .is_err()
                            );
                        } else {
                            let previous = engine.call_chain.clone();
                            let error = engine
                                .execute(
                                    instance,
                                    Vec::new(),
                                    state.conditions.clone(),
                                    state.memory.clone(),
                                    &[],
                                )
                                .err()
                                .unwrap();
                            assert!(error.contains("niche frame registry borrowed"));
                            assert_eq!(engine.call_chain, previous);
                            assert_eq!(engine.failed_call_chain, Some(vec![id]));
                        }
                        assert!(engine.niche_ledger.failed.get());
                        retained(&before, &state);
                        drop(frame);
                        eprintln!(
                            "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                            tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                        );
                        continue;
                    }
                    17 => {
                        engine
                            .niche_ledger
                            .current
                            .borrow_mut()
                            .as_mut()
                            .unwrap()
                            .cow_ready = false;
                    }
                    18..=21 => {
                        let other = tcx
                            .hir_body_owners()
                            .find(|other| {
                                let id = other.to_def_id();
                                tcx.def_kind(id) == DefKind::Fn
                                    && id != instance.def_id()
                                    && !engine
                                        .bodies
                                        .borrow()
                                        .contains_key(&ty::Instance::mono(tcx, id))
                                    && !engine
                                        .call_signatures
                                        .borrow()
                                        .contains_key(&ty::Instance::mono(tcx, id))
                            })
                            .expect("distinct genuine compiler source for inventory growth")
                            .to_def_id();
                        let other = ty::Instance::mono(tcx, other);
                        let body_count = engine.bodies.borrow().len();
                        let signature_count = engine.call_signatures.borrow().len();
                        if denial % 2 == 0 {
                            engine.instantiated_body(other).unwrap();
                        } else {
                            let signature = mutable_hierarchy::products::niche_codec_signature(
                                &mut engine,
                                other,
                            )
                            .unwrap();
                            engine.call_signatures.borrow_mut().insert(other, signature);
                        }
                        if denial % 2 == 0 {
                            assert_eq!(engine.bodies.borrow().len(), body_count + 1);
                            assert_eq!(engine.call_signatures.borrow().len(), signature_count);
                        } else {
                            assert_eq!(engine.bodies.borrow().len(), body_count);
                            assert_eq!(engine.call_signatures.borrow().len(), signature_count + 1);
                        }
                        if denial >= 20 {
                            let error = engine.niche_origins[&0]
                                .verify(&engine, &engine.mutable_integer_types[0])
                                .unwrap_err();
                            assert!(error.contains("prepaid actual inventory"), "{error}");
                        } else {
                            let error = engine
                                .mutable_product_store(&body, &mut state, place, &value)
                                .unwrap_err();
                            assert!(error.contains("prepaid actual inventory"), "{error}");
                        }
                        assert!(engine.niche_ledger.failed.get());
                        // Removing genuinely acquired metadata cannot revive a failed session.
                        if denial % 2 == 0 {
                            engine.bodies.borrow_mut().remove(&other);
                        } else {
                            engine.call_signatures.borrow_mut().remove(&other);
                        }
                        assert!(engine.niche_certificate_work(0).is_err());
                        assert!(
                            engine.niche_origins[&0]
                                .verify(&engine, &engine.mutable_integer_types[0])
                                .is_err()
                        );
                        retained(&before, &state);
                        drop(frame);
                        eprintln!(
                            "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                            tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                        );
                        continue;
                    }
                    22..=27 => {
                        let other = tcx
                            .hir_body_owners()
                            .find(|other| {
                                let id = other.to_def_id();
                                tcx.def_kind(id) == DefKind::Fn
                                    && id != instance.def_id()
                                    && !engine
                                        .bodies
                                        .borrow()
                                        .contains_key(&ty::Instance::mono(tcx, id))
                                    && !engine
                                        .call_signatures
                                        .borrow()
                                        .contains_key(&ty::Instance::mono(tcx, id))
                            })
                            .expect("genuine compiler source for paid acquisition")
                            .to_def_id();
                        let other = ty::Instance::mono(tcx, other);
                        let body_count = engine.bodies.borrow().len();
                        let signature_count = engine.call_signatures.borrow().len();
                        engine.mutable_product_certificate(0).unwrap();
                        let (body_bound, signature_bound, remaining) = {
                            let active = engine.niche_ledger.current.borrow();
                            let scope = active.as_ref().unwrap();
                            (scope.body_bound, scope.signature_bound, scope.remaining)
                        };
                        if matches!(denial, 24 | 25) {
                            engine.limits.max_steps = engine.steps.used();
                        } else if denial >= 26 {
                            engine
                                .niche_ledger
                                .current
                                .borrow_mut()
                                .as_mut()
                                .unwrap()
                                .deny_replan = true;
                        }
                        let result = if denial % 2 == 0 {
                            engine.niche_length_body(other).map(|_| ())
                        } else {
                            engine.niche_call_signature_prepare(other)
                        };
                        if denial >= 24 {
                            let error = result.unwrap_err();
                            assert!(
                                error.contains("niche instruction shared step limit"),
                                "{error}"
                            );
                            assert_eq!(engine.bodies.borrow().len(), body_count);
                            assert_eq!(engine.call_signatures.borrow().len(), signature_count);
                            assert!(engine.niche_ledger.failed.get());
                            let active = engine.niche_ledger.current.borrow();
                            let scope = active.as_ref().unwrap();
                            assert_eq!(scope.body_bound, body_bound);
                            assert_eq!(scope.signature_bound, signature_bound);
                            assert_eq!(scope.remaining, remaining);
                            assert_eq!(remaining, 63);
                            if denial >= 26 {
                                assert_eq!(scope.denied_replan_work, Some(2 * remaining));
                                assert_eq!(engine.steps.used(), engine.limits.max_steps + 1);
                            } else {
                                assert_eq!(scope.denied_replan_work, None);
                            }
                            drop(active);
                            retained(&before, &state);
                            drop(frame);
                            eprintln!(
                                "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                                tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                            );
                            continue;
                        }
                        result.unwrap();
                        let active = engine.niche_ledger.current.borrow();
                        let scope = active.as_ref().unwrap();
                        if denial % 2 == 0 {
                            assert_eq!(engine.bodies.borrow().len(), body_count + 1);
                            assert_eq!(engine.call_signatures.borrow().len(), signature_count);
                            assert_eq!(scope.body_bound, body_count + 1);
                        } else {
                            assert_eq!(engine.bodies.borrow().len(), body_count);
                            assert_eq!(engine.call_signatures.borrow().len(), signature_count + 1);
                            assert_eq!(scope.signature_bound, signature_count + 1);
                        }
                        assert_eq!(scope.remaining, remaining);
                        drop(active);
                    }
                    _ => unreachable!(),
                }
                let result = engine.mutable_product_store(&body, &mut state, place, &value);
                if matches!(denial, 0 | 22 | 23) {
                    assert!(result.unwrap());
                    assert!(!Rc::ptr_eq(
                        &before.memory.mutable_u16,
                        &state.memory.mutable_u16
                    ));
                    let Storage::Product(before_columns) = &before.memory.mutable_u16[0].data
                    else {
                        panic!("original product columns");
                    };
                    let Storage::Product(after_columns) = &state.memory.mutable_u16[0].data else {
                        panic!("returned product columns");
                    };
                    assert_eq!(before_columns[1], after_columns[1]);
                    let raw = engine.terms.bit_vector(7, 8).unwrap();
                    let expected = engine
                        .terms
                        .apply(
                            Op::Store,
                            &[
                                before_columns[0].clone(),
                                zero.integer().unwrap().0.clone(),
                                raw.clone(),
                            ],
                        )
                        .unwrap();
                    let exact_store = engine
                        .terms
                        .apply(Op::Equal, &[after_columns[0].clone(), expected])
                        .unwrap();
                    assert!(!engine.feasible(&[symbolic::not(&exact_store)]).unwrap());
                    let observed = engine
                        .terms
                        .apply(
                            Op::Select,
                            &[after_columns[0].clone(), zero.integer().unwrap().0.clone()],
                        )
                        .unwrap();
                    let equal = engine.terms.apply(Op::Equal, &[raw, observed]).unwrap();
                    assert!(!engine.feasible(&[symbolic::not(&equal)]).unwrap());
                    let other = engine.terms.bit_vector(1, bits).unwrap();
                    let old_other = engine
                        .terms
                        .apply(Op::Select, &[before_columns[0].clone(), other.clone()])
                        .unwrap();
                    let new_other = engine
                        .terms
                        .apply(Op::Select, &[after_columns[0].clone(), other])
                        .unwrap();
                    let equal = engine
                        .terms
                        .apply(Op::Equal, &[old_other, new_other])
                        .unwrap();
                    assert!(!engine.feasible(&[symbolic::not(&equal)]).unwrap());
                    assert_eq!(
                        before.memory.mutable_u16[0].generation,
                        state.memory.mutable_u16[0].generation
                    );
                } else {
                    assert!(result.is_err(), "denial={denial}");
                    engine.niche_scope_end(true);
                    assert!(engine.niche_ledger.failed.get());
                    retained(&before, &state);
                }
                drop(frame);
                eprintln!(
                    "NICHE_OWNER_TRANSACTION denial={denial} target={} opt={:?}",
                    tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                );
            }
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_niche_codec.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-niche-owner-control".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}
