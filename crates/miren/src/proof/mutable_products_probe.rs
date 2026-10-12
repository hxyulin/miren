//! Current compiler-issued product owner and hostile storage/schema controls.
use super::*;
use rustc_middle::mir::Local;
use std::rc::Rc;

fn make_engine<'tcx>(tcx: TyCtxt<'tcx>) -> Engine<'tcx> {
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

fn body<'tcx>(engine: &mut Engine<'tcx>, name: &str) -> (ty::Instance<'tcx>, Rc<Body<'tcx>>) {
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

fn accounting(tcx: TyCtxt<'_>) {
    for (count, slots) in [(0, 2), (1, 2), (2, 3)] {
        let mut engine = make_engine(tcx);
        let original = Ty::new_array(tcx, tcx.types.f32, count);
        let mut memory = Memory::default();
        let mut conditions = Vec::new();
        engine
            .mutable_product_input(original, &mut memory, &mut conditions)
            .unwrap();
        assert_eq!(memory.len(), 1);
        assert_eq!(memory.storage_slots(), slots);
        assert_eq!(memory.mutable_u16.len(), 1);
        let mut engine = make_engine(tcx);
        let mut memory = Memory::default();
        for _ in 0..MAX_INPUT_VALUES - slots {
            memory.push(Some(Value::Unit));
        }
        let before = memory.len();
        engine
            .mutable_product_input(original, &mut memory, &mut Vec::new())
            .unwrap();
        assert_eq!(memory.len(), before + 1);
        assert_eq!(memory.storage_slots(), MAX_INPUT_VALUES);
        let mut engine = make_engine(tcx);
        let mut memory = Memory::default();
        for _ in 0..MAX_INPUT_VALUES - slots + 1 {
            memory.push(Some(Value::Unit));
        }
        let before = memory.len();
        let inputs = engine.input_values;
        let symbols = engine.next_symbol.get();
        assert!(
            engine
                .mutable_product_input(original, &mut memory, &mut Vec::new())
                .unwrap_err()
                .contains("existing input/storage budget")
        );
        assert_eq!(memory.len(), before);
        assert_eq!(engine.input_values, inputs);
        assert_eq!(engine.next_symbol.get(), symbols);
        assert!(memory.mutable_u16.is_empty());
    }
    eprintln!("mutable_product_accounting_targets=9");
}

fn check(tcx: TyCtxt<'_>) {
    accounting(tcx);
    let mut engine = make_engine(tcx);
    let (_, root_body) = body(&mut engine, "metadata32");
    let (_, store_body) = body(&mut engine, "store_nan");
    let original = Ty::new_array(tcx, tcx.types.f32, 2);
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let root = engine
        .mutable_product_input(original, &mut memory, &mut conditions)
        .unwrap();
    let bits = u32::from(tcx.sess.target.pointer_width);
    Rc::make_mut(&mut memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 2, bits, false);
    let mut metadata_state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; root_body.local_decls.len()],
        addresses: vec![None; root_body.local_decls.len()],
        conditions: conditions.clone(),
        memory: memory.clone(),
        missing_places: Default::default(),
    };
    metadata_state.locals[1] = Some(root.clone());
    let borrowed = root_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment) => match &assignment.1 {
                Rvalue::Ref(_, BorrowKind::Shared, place)
                    if place.local.as_usize() == 1
                        && place.projection.as_ref() == [ProjectionElem::Deref] =>
                {
                    Some(*place)
                }
                _ => None,
            },
            _ => None,
        })
        .unwrap();
    let metadata = engine
        .mutable_product_metadata(&root_body, &metadata_state, borrowed)
        .unwrap()
        .unwrap();
    assert!(
        engine
            .mutable_product_length(&metadata, &memory, &conditions)
            .is_ok()
    );
    let (copied_instance, copied_body) = body(&mut engine, "copied_helper");
    let (destination, fake) = copied_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment)
                if matches!(
                    assignment.1,
                    Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::FakeForPtrMetadata, _)
                ) =>
            {
                Some((assignment.0, assignment.1.clone()))
            }
            _ => None,
        })
        .unwrap();
    let mut copied_state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; copied_body.local_decls.len()],
        addresses: vec![None; copied_body.local_decls.len()],
        conditions: conditions.clone(),
        memory: memory.clone(),
        missing_places: Default::default(),
    };
    copied_state.locals[1] = Some(root.clone());
    let fake_metadata = engine
        .rvalue(
            copied_instance.def_id(),
            &copied_body,
            &mut copied_state,
            &fake,
        )
        .unwrap();
    assert!(matches!(
        fake_metadata,
        Value::MutableU16 {
            role: MutableU16Role::Metadata { generation: 0 },
            ..
        }
    ));
    assert!(
        engine
            .mutable_product_store_role(&copied_body, &copied_state, destination, &fake_metadata)
            .unwrap()
    );
    for wrong in [
        Ty::new_ptr(
            tcx,
            Ty::new_slice(tcx, tcx.types.u16),
            rustc_hir::Mutability::Not,
        ),
        Ty::new_ptr(
            tcx,
            Ty::new_slice(tcx, original),
            rustc_hir::Mutability::Mut,
        ),
    ] {
        let mut changed = (*copied_body).clone();
        changed.local_decls[destination.local].ty = wrong;
        assert!(
            engine
                .mutable_product_store_role(&changed, &copied_state, destination, &fake_metadata)
                .is_err()
        );
    }
    eprintln!("mutable_product_fake_metadata_targets=3");
    let issued = engine.mutable_integer_types[memory.mutable_u16[0].certificate].clone();
    let certificate = memory.mutable_u16[0].certificate;
    for wrong in [tcx.types.u32, Ty::new_array(tcx, tcx.types.f32, 3)] {
        engine.mutable_integer_types[certificate].original = wrong;
        assert!(engine.mutable_product_backing(0, &memory).is_err());
        engine.mutable_integer_types[certificate] = issued.clone();
    }
    let foreign = Context::default();
    for mode in 0..4 {
        let mut wrong = memory.clone();
        let Storage::Product(columns) = &mut Rc::make_mut(&mut wrong.mutable_u16)[0].data else {
            panic!("product");
        };
        match mode {
            0 => {
                columns.pop();
            }
            1 => {
                columns[0] = engine
                    .terms
                    .symbol(
                        990,
                        Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(64))),
                    )
                    .unwrap()
            }
            2 => {
                columns[0] = foreign
                    .symbol(
                        0,
                        Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
                    )
                    .unwrap()
            }
            3 => columns.push(columns[0].clone()),
            _ => unreachable!(),
        }
        assert!(
            engine
                .mutable_product_backing(0, &wrong)
                .unwrap_err()
                .contains(if mode == 0 || mode == 3 {
                    "column inventory differs"
                } else {
                    "current Context"
                })
        );
    }
    let mut dead = memory.clone();
    dead[0] = None;
    assert!(engine.mutable_product_backing(0, &dead).is_err());
    let mut stale = memory.clone();
    Rc::make_mut(&mut stale.mutable_u16)[0].generation = 1;
    assert!(
        engine
            .mutable_product_length(&metadata, &stale, &conditions)
            .is_err()
    );
    let stale_metadata = Value::MutableU16 {
        id: 0,
        role: MutableU16Role::Metadata { generation: 1 },
    };
    assert!(
        engine
            .mutable_product_length(&stale_metadata, &memory, &conditions)
            .is_err()
    );
    let mut extent = memory.clone();
    Rc::make_mut(&mut extent.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, u128::MAX >> (128 - bits), bits, false);
    assert!(
        engine
            .mutable_product_length(&root, &extent, &conditions)
            .unwrap_err()
            .contains("valid target allocation extent")
    );
    assert!(
        engine
            .snapshot(&root, &memory, &conditions, 0)
            .unwrap_err()
            .contains("Ghost")
    );
    assert!(matches!(
        engine.snapshot(&metadata, &memory, &conditions, 0).unwrap(),
        Value::MutableU16 {
            role: MutableU16Role::Metadata { generation: 0 },
            ..
        }
    ));
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; store_body.local_decls.len()],
        addresses: vec![None; store_body.local_decls.len()],
        conditions,
        memory,
        missing_places: Default::default(),
    };
    for (local, declaration) in store_body.local_decls.iter_enumerated() {
        if declaration.ty == tcx.types.usize {
            state.locals[local.as_usize()] = Some(symbolic::integer(&engine.terms, 0, bits, false));
        }
    }
    state.locals[1] = Some(root.clone());
    let place = store_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment)
                if assignment.0.projection.len() >= 3
                    && matches!(assignment.0.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                Some(assignment.0)
            }
            _ => None,
        })
        .unwrap();
    let good = symbolic::float_from_bits(
        &engine.terms,
        engine.terms.bit_vector(0x8000_0000, 32).unwrap(),
        32,
    );
    let before = state.memory.mutable_u16[0].data.clone();
    let mut positive = state.clone();
    assert!(
        engine
            .mutable_product_store(&store_body, &mut positive, place, &good)
            .unwrap()
    );
    let observed = engine
        .mutable_product_read(Some(&store_body), &positive, place)
        .unwrap()
        .unwrap();
    let Value::Float {
        raw_bits: Some(raw),
        bits: 32,
        ..
    } = observed
    else {
        panic!("encoded Float");
    };
    let valid = symbolic::binary(
        &engine.terms,
        "eq",
        Value::Int {
            expression: raw,
            bits: 32,
            signed: false,
        },
        symbolic::integer(&engine.terms, 0x8000_0000, 32, false),
    )
    .unwrap()
    .boolean()
    .unwrap();
    assert!(
        !engine
            .feasible(&[positive.conditions.clone(), vec![symbolic::not(&valid)]].concat())
            .unwrap()
    );
    assert_eq!(state.memory.mutable_u16[0].data, before);
    let Value::Float {
        expression: good_expression,
        ..
    } = &good
    else {
        panic!("Float");
    };
    for bad in [
        Value::Float {
            expression: good_expression.clone(),
            bits: 32,
            raw_bits: None,
        },
        Value::Float {
            expression: good_expression.clone(),
            bits: 32,
            raw_bits: Some(engine.terms.bit_vector(1, 32).unwrap()),
        },
    ] {
        let mut wrong = state.clone();
        assert!(
            engine
                .mutable_product_store(&store_body, &mut wrong, place, &bad)
                .is_err()
        );
        assert_eq!(wrong.memory.mutable_u16[0].data, before);
    }
    assert!(
        engine
            .mutable_product_read(None, &state, place)
            .unwrap_err()
            .contains("compiler Body")
    );
    let mut wrong_body = (*store_body).clone();
    wrong_body.local_decls[Local::from_usize(1)].ty = Ty::new_mut_ref(
        tcx,
        tcx.lifetimes.re_erased,
        Ty::new_slice(tcx, Ty::new_array(tcx, tcx.types.f64, 2)),
    );
    let mut wrong = state.clone();
    assert!(
        engine
            .mutable_product_store(&wrong_body, &mut wrong, place, &good)
            .is_err()
    );
    assert_eq!(wrong.memory.mutable_u16[0].data, before);
    let (_, tuple_body) = body(&mut engine, "tuple_pair");
    let ty::Ref(_, slice, _) = tuple_body.local_decls[Local::from_usize(1)].ty.kind() else {
        panic!("reference");
    };
    let ty::Slice(tuple) = slice.kind() else {
        panic!("slice");
    };
    let mut tuple_memory = Memory::default();
    let mut tuple_conditions = Vec::new();
    let tuple_root = engine
        .mutable_product_input(*tuple, &mut tuple_memory, &mut tuple_conditions)
        .unwrap();
    Rc::make_mut(&mut tuple_memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 2, bits, false);
    let mut tuple_state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; tuple_body.local_decls.len()],
        addresses: vec![None; tuple_body.local_decls.len()],
        conditions: tuple_conditions,
        memory: tuple_memory,
        missing_places: Default::default(),
    };
    for (local, declaration) in tuple_body.local_decls.iter_enumerated() {
        if declaration.ty == tcx.types.usize {
            tuple_state.locals[local.as_usize()] =
                Some(symbolic::integer(&engine.terms, 0, bits, false));
        }
    }
    tuple_state.locals[1] = Some(tuple_root);
    let whole = tuple_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment)
                if assignment.0.projection.len() == 2
                    && matches!(assignment.0.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                Some(assignment.0)
            }
            _ => None,
        })
        .unwrap();
    let before_tuple = tuple_state.memory.mutable_u16[0].data.clone();
    let invalid_char = Value::Tuple(vec![
        Value::Bool(engine.terms.boolean(true)),
        symbolic::integer(&engine.terms, 0xd800, 32, false),
    ]);
    assert!(
        engine
            .mutable_product_store(&tuple_body, &mut tuple_state, whole, &invalid_char)
            .is_err()
    );
    assert_eq!(tuple_state.memory.mutable_u16[0].data, before_tuple);
    let field = tuple_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment) => match &assignment.1 {
                Rvalue::Use(Operand::Copy(place), _) | Rvalue::Cast(_, Operand::Copy(place), _)
                    if place.projection.len() >= 3
                        && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                        && place.ty(&tuple_body.local_decls, tcx).ty == tcx.types.char =>
                {
                    Some(*place)
                }
                _ => None,
            },
            _ => None,
        })
        .unwrap();
    let mut changed_field = field.projection.to_vec();
    let ProjectionElem::Field(index, _) = *changed_field.last().unwrap() else {
        panic!("field");
    };
    *changed_field.last_mut().unwrap() = ProjectionElem::Field(index, tcx.types.u32);
    let changed_field = Place {
        local: field.local,
        projection: tcx.mk_place_elems(&changed_field),
    };
    assert!(
        engine
            .mutable_product_read(Some(&tuple_body), &tuple_state, changed_field)
            .unwrap_err()
            .contains("original FieldTy")
    );
    let len = root_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                && let ty::FnDef(id, args) = func.ty(&root_body.local_decls, tcx).kind()
                && Some(*id) == tcx.lang_items().get(LangItem::SliceLen)
            {
                Some(
                    engine
                        .resolve_function_item(*id, args.skip_binder())
                        .unwrap(),
                )
            } else {
                None
            }
        })
        .unwrap();
    engine.certify_mutable_u16_len(len).unwrap();
    let len_body = engine.instantiated_body(len).unwrap();
    let mut changed = (*len_body).clone();
    changed.basic_blocks_mut()[START_BLOCK]
        .terminator_mut()
        .kind = TerminatorKind::Unreachable;
    engine.bodies.borrow_mut().insert(len, Rc::new(changed));
    assert!(engine.certify_mutable_u16_len(len).is_err());
    engine.bodies.borrow_mut().insert(len, len_body);
    // This authenticates a real helper Body solely to test the hostile Armed gate.
    // It does not issue an Armed product root or authorize product execution.
    let (helper_instance, helper_body) = body(&mut engine, "observe_bits");
    let mut armed = state.clone();
    armed.flow = engine
        .activation_test_root(helper_instance, &helper_body)
        .unwrap();
    assert!(
        engine
            .mutable_product_read(Some(&store_body), &armed, place)
            .unwrap_err()
            .contains("armed activation adapter")
    );
    assert!(engine.proof.assumptions.is_empty() && engine.proof.entry_assumptions.is_empty());
    eprintln!("mutable_product_current_owner_projection_targets=20");
}

#[test]
fn compiler_mutable_product_current_owner_and_projection_controls() {
    struct Check {
        checked: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            check(tcx);
            self.checked = true;
            rustc_driver::Compilation::Stop
        }
    }
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_slices.rs");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let output = std::env::temp_dir().join(format!(
        "miren-product-probe-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir(&output).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check { checked: false };
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.checked);
        }
    }
    std::fs::remove_dir_all(output).unwrap();
}
