//! Actual compiler places with constructed host states; not guest execution proofs.
use super::*;
use std::rc::Rc;

fn make_engine(tcx: TyCtxt<'_>) -> Engine<'_> {
    Engine::new(
        tcx,
        &miren::ContractConfig::default(),
        VerificationOptions {
            all_failures: false,
            induction: false,
            startup: false,
            isolated_startup: false,
            async_entry: false,
            limits: miren::AnalysisLimits::default(),
        },
    )
}
fn actual_body<'tcx>(engine: &Engine<'tcx>, name: &str) -> (ty::Instance<'tcx>, Rc<Body<'tcx>>) {
    let id = engine
        .tcx
        .hir_body_owners()
        .find(|id| {
            engine.tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(id.to_def_id()).as_str() == name
        })
        .unwrap();
    let instance = engine
        .resolve_function_item(id.to_def_id(), engine.tcx.mk_args(&[]))
        .unwrap();
    (instance, engine.instantiated_body(instance).unwrap())
}
fn destination<'tcx>(body: &Body<'tcx>) -> Place<'tcx> {
    body.basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return None;
            };
            (assignment.0.local.as_usize() == 1
                && assignment.0.projection.first() == Some(&ProjectionElem::Deref)
                && assignment
                    .0
                    .projection
                    .iter()
                    .filter(|part| matches!(part, ProjectionElem::Index(_)))
                    .count()
                    >= 2)
                .then_some(assignment.0)
        })
        .unwrap()
}
fn host_state<'tcx>(engine: &mut Engine<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> State {
    let ty::Ref(_, slice, _) = body.local_decls[Local::from_usize(1)].ty.kind() else {
        panic!("actual mutable root argument");
    };
    let ty::Slice(original) = slice.kind() else {
        panic!("actual slice");
    };
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let owner = engine
        .mutable_product_input(*original, &mut memory, &mut conditions)
        .unwrap();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    Rc::make_mut(&mut memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 2, bits, false);
    let mut locals = vec![None; body.local_decls.len()];
    for (local, declaration) in body.local_decls.iter_enumerated() {
        if declaration.ty == engine.tcx.types.usize {
            locals[local.as_usize()] = Some(symbolic::integer(&engine.terms, 0, bits, false));
        }
    }
    locals[1] = Some(owner);
    let suffix = place
        .projection
        .iter()
        .filter_map(|part| {
            if let ProjectionElem::Index(local) = part {
                Some(local)
            } else {
                None
            }
        })
        .nth(1)
        .unwrap();
    let index = engine.fresh(Sort::BitVec(bits));
    locals[suffix.as_usize()] = Some(Value::Int {
        expression: index.clone(),
        bits,
        signed: false,
    });
    conditions.push(
        engine
            .terms
            .apply(
                Op::Equal,
                &[index, engine.terms.bit_vector(0, bits).unwrap()],
            )
            .unwrap(),
    );
    State {
        flow: activation_flow::Flow::Unarmed,
        locals,
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions,
        memory,
    }
}
fn retained(before: &Storage, state: &State) {
    assert_eq!(&state.memory.mutable_u16[0].data, before);
}
fn controls(tcx: TyCtxt<'_>) {
    let mut engine = make_engine(tcx);
    let (instance, body) = actual_body(&engine, "char_selected");
    let place = destination(&body);
    let state = host_state(&mut engine, &body, place);
    let before = state.memory.mutable_u16[0].data.clone();
    let valid = symbolic::integer(&engine.terms, 'λ' as u128, 32, false);
    let invalid = symbolic::integer(&engine.terms, 0xd800, 32, false);
    let mut changed = state.clone();
    assert!(
        engine
            .mutable_product_store(&body, &mut changed, place, &valid)
            .unwrap()
    );
    let observed = engine
        .mutable_product_read(Some(&body), &changed, place)
        .unwrap()
        .unwrap();
    let observed = observed.integer().unwrap().0;
    let expected = valid.integer().unwrap().0;
    let equal = engine
        .terms
        .apply(Op::Equal, &[observed, expected.clone()])
        .unwrap();
    assert!(
        !engine
            .feasible(&[changed.conditions.clone(), vec![symbolic::not(&equal)]].concat())
            .unwrap()
    );
    let mut bad = state.clone();
    assert!(
        engine
            .mutable_product_store(&body, &mut bad, place, &invalid)
            .is_err()
    );
    retained(&before, &bad);
    // Root caller/frame validation precedes all new symbolic projection work.
    let frame = engine.mutable_u16_register_frame(&body).unwrap();
    let mut active = state.clone();
    Rc::make_mut(&mut active.memory.mutable_u16)[0].generation = 1;
    Rc::make_mut(&mut active.memory.mutable_u16)[0].phase = Phase::Active {
        frames: vec![frame],
    };
    active.locals[1] = Some(Value::MutableU16 {
        id: 0,
        role: MutableU16Role::Child { generation: 1 },
    });
    let mut child = active.clone();
    assert!(
        engine
            .mutable_product_store(&body, &mut child, place, &valid)
            .unwrap()
    );
    let (_, other) = actual_body(&engine, "bool_selected");
    let mut wrong = active.clone();
    assert!(
        engine
            .mutable_product_store(&other, &mut wrong, place, &valid)
            .is_err()
    );
    retained(&before, &wrong);
    let mut stale = active.clone();
    stale.locals[1] = Some(Value::MutableU16 {
        id: 0,
        role: MutableU16Role::Child { generation: 0 },
    });
    assert!(
        engine
            .mutable_product_store(&body, &mut stale, place, &valid)
            .is_err()
    );
    retained(&before, &stale);
    engine
        .bodies
        .borrow_mut()
        .insert(instance, Rc::new(body.as_ref().clone()));
    let mut replaced = active.clone();
    assert!(
        engine
            .mutable_product_store(&body, &mut replaced, place, &valid)
            .is_err()
    );
    retained(&before, &replaced);
    engine.bodies.borrow_mut().insert(instance, body.clone());
    let (scalar, scalar_body) = actual_body(&engine, "scalar_seed");
    let mut armed = state.clone();
    armed.flow = engine.activation_test_root(scalar, &scalar_body).unwrap();
    assert!(
        engine
            .mutable_product_store(&body, &mut armed, place, &valid)
            .is_err()
    );
    retained(&before, &armed);
    let index = place
        .projection
        .iter()
        .filter_map(|part| {
            if let ProjectionElem::Index(local) = part {
                Some(local)
            } else {
                None
            }
        })
        .nth(1)
        .unwrap();
    let mut consumed = state.clone();
    consumed
        .missing_places
        .consume(index.as_usize(), vec![])
        .unwrap();
    assert!(
        engine
            .mutable_product_store(&body, &mut consumed, place, &valid)
            .is_err()
    );
    retained(&before, &consumed);
    let mut addressed = state.clone();
    let allocation = addressed.memory.len();
    addressed
        .memory
        .push(addressed.locals[index.as_usize()].clone());
    addressed.addresses[index.as_usize()] = Some(allocation);
    addressed.locals[index.as_usize()] = Some(symbolic::integer(
        &engine.terms,
        3,
        u32::from(tcx.sess.target.pointer_width),
        false,
    ));
    assert!(
        engine
            .mutable_product_store(&body, &mut addressed, place, &valid)
            .unwrap()
    );
    let mut dead = state.clone();
    let allocation = dead.memory.len();
    dead.memory.push(dead.locals[index.as_usize()].clone());
    dead.addresses[index.as_usize()] = Some(allocation);
    dead.memory
        .missing_places
        .consume(allocation, vec![])
        .unwrap();
    assert!(
        engine
            .mutable_product_store(&body, &mut dead, place, &valid)
            .is_err()
    );
    retained(&before, &dead);
    let context = Context::default();
    let mut foreign = state.clone();
    foreign.locals[index.as_usize()] = Some(Value::Int {
        expression: context
            .symbol(0, Sort::BitVec(u32::from(tcx.sess.target.pointer_width)))
            .unwrap(),
        bits: u32::from(tcx.sess.target.pointer_width),
        signed: false,
    });
    assert!(
        engine
            .mutable_product_store(&body, &mut foreign, place, &valid)
            .is_err()
    );
    retained(&before, &foreign);

    let mut wrong_width = state.clone();
    wrong_width.locals[index.as_usize()] = Some(Value::Int {
        expression: engine.fresh(Sort::BitVec(8)),
        bits: 8,
        signed: false,
    });
    assert!(
        engine
            .mutable_product_store(&body, &mut wrong_width, place, &valid)
            .is_err()
    );
    retained(&before, &wrong_width);
    let mut signed = state.clone();
    let (expression, bits, _) = signed.locals[index.as_usize()]
        .as_ref()
        .unwrap()
        .integer()
        .unwrap();
    signed.locals[index.as_usize()] = Some(Value::Int {
        expression,
        bits,
        signed: true,
    });
    assert!(
        engine
            .mutable_product_store(&body, &mut signed, place, &valid)
            .is_err()
    );
    retained(&before, &signed);
    let mut no_bounds = state.clone();
    no_bounds.conditions.clear();
    assert!(
        engine
            .mutable_product_store(&body, &mut no_bounds, place, &valid)
            .is_err()
    );
    retained(&before, &no_bounds);
    let (_, bool_body) = actual_body(&engine, "bool_selected");
    let bool_place = destination(&bool_body);
    let mut bool_state = host_state(&mut engine, &bool_body, bool_place);
    let bool_before = bool_state.memory.mutable_u16[0].data.clone();
    let wrong_bool = Value::Bool(engine.terms.bit_vector(1, 8).unwrap());
    assert!(
        engine
            .mutable_product_store(&bool_body, &mut bool_state, bool_place, &wrong_bool)
            .is_err()
    );
    retained(&bool_before, &bool_state);
    let (_, record_body) = actual_body(&engine, "record_fields");
    let record_place = destination(&record_body);
    let mut record_state = host_state(&mut engine, &record_body, record_place);
    let record_before = record_state.memory.mutable_u16[0].data.clone();
    let mut forged = record_place.projection.to_vec();
    let field = forged
        .iter_mut()
        .find(|part| matches!(part, ProjectionElem::Field(..)))
        .unwrap();
    let ProjectionElem::Field(field_index, _) = *field else {
        unreachable!();
    };
    *field = ProjectionElem::Field(field_index, Ty::new_array(tcx, tcx.types.bool, 2));
    let forged = Place {
        local: record_place.local,
        projection: tcx.mk_place_elems(&forged),
    };
    assert!(
        engine
            .mutable_product_store(
                &record_body,
                &mut record_state,
                forged,
                &symbolic::integer(&engine.terms, 37, 16, false)
            )
            .is_err()
    );
    retained(&record_before, &record_state);

    let (_, floats) = actual_body(&engine, "float_selected");
    let float_place = destination(&floats);
    let float_state = host_state(&mut engine, &floats, float_place);
    let float_before = float_state.memory.mutable_u16[0].data.clone();
    let good = symbolic::float_from_bits(
        &engine.terms,
        engine.terms.bit_vector(0x3f80_0000, 32).unwrap(),
        32,
    );
    let Value::Float { expression, .. } = good else {
        panic!("Float pair");
    };
    let bad_pair = Value::Float {
        expression,
        bits: 32,
        raw_bits: Some(engine.terms.bit_vector(0x4000_0000, 32).unwrap()),
    };
    let mut bad_float = float_state.clone();
    assert!(
        engine
            .mutable_product_store(&floats, &mut bad_float, float_place, &bad_pair)
            .is_err()
    );
    retained(&float_before, &bad_float);

    let (_, large) = actual_body(&engine, "whole_budget");
    let large_place = destination(&large);
    let mut large_state = host_state(&mut engine, &large, large_place);
    let large_before = large_state.memory.mutable_u16[0].data.clone();
    let packet = Value::Tuple(vec![
        symbolic::integer(&engine.terms, 37, 16, false),
        Value::Bool(engine.terms.boolean(true)),
        valid,
        symbolic::float_from_bits(
            &engine.terms,
            engine.terms.bit_vector(0x3f80_0000, 32).unwrap(),
            32,
        ),
        symbolic::float_from_bits(
            &engine.terms,
            engine.terms.bit_vector(0x3ff0_0000_0000_0000, 64).unwrap(),
            64,
        ),
    ]);
    let reason = engine
        .mutable_product_store(&large, &mut large_state, large_place, &packet)
        .unwrap_err();
    assert!(reason.contains("shared node or depth budget"), "{reason}");
    retained(&large_before, &large_state);
    eprintln!(
        "symbolic Product: current read/store/Child, Char/Float, index origin and atomic refusal"
    );
}
#[test]
fn actual_symbolic_product_places_and_atomic_current_storage() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            controls(tcx);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_symbolic_suffix.rs");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let out = std::env::temp_dir().join(format!(
        "miren-symbolic-product-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir(&out).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                out.display().to_string(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
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
