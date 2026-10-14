use super::*;

#[test]
fn actual_product_helper_source_and_failed_service_guards() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let helper = tcx
                .hir_body_owners()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "nested_tuple"
                })
                .unwrap();
            let instance = ty::Instance::mono(tcx, helper.to_def_id());
            let fresh = || super::super::nonzero_niches::test_engine(tcx);
            let mut engine = fresh();
            engine.limits.max_steps = 2_000_000;
            engine.instantiated_body(instance).unwrap();
            let actual = source(&mut engine, instance).unwrap();
            assert_eq!(actual.instance, instance);
            assert_eq!(actual.body.arg_count, 2);
            let leaf = tcx
                .hir_body_owners()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "integer_leaf"
                })
                .unwrap();
            let leaf = engine
                .instantiated_body(ty::Instance::mono(tcx, leaf.to_def_id()))
                .unwrap();
            let wrapping = leaf
                .basic_blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, args) = func.ty(&leaf.local_decls, tcx).kind() else {
                        return None;
                    };
                    (tcx.item_name(*id).as_str() == "wrapping_add").then(|| {
                        engine
                            .resolve_function_item(*id, args.skip_binder())
                            .unwrap()
                    })
                })
                .unwrap();
            let original_wrapping = source(&mut engine, wrapping).unwrap();
            eprintln!(
                "actual wrapping body: {:#?}",
                original_wrapping.body.basic_blocks
            );
            for mutation in 0..5 {
                let mut engine = fresh();
                engine.limits.max_steps = 2_000_000;
                engine.instantiated_body(instance).unwrap();
                let signature = actual.signature;
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
                        inputs_and_output: tcx.mk_type_list(&[tcx.types.u8, tcx.types.unit]),
                        ..s
                    }),
                    4 => signature.map_bound(|s| ty::FnSig {
                        inputs_and_output: tcx.mk_type_list(&[
                            s.inputs()[0],
                            s.inputs()[1],
                            tcx.types.bool,
                        ]),
                        ..s
                    }),
                    _ => unreachable!(),
                };
                engine
                    .call_signatures
                    .borrow_mut()
                    .insert(instance, poisoned);
                assert!(source(&mut engine, instance).is_err());
                assert!(engine.mutable_product_failed.get());
                engine
                    .call_signatures
                    .borrow_mut()
                    .insert(instance, signature);
                let used = engine.steps;
                assert!(source(&mut engine, instance).is_err());
                assert_eq!(engine.steps, used);
            }
            let mut engine = fresh();
            engine.limits.max_steps = 2_000_000;
            let mut poisoned = engine.instantiated_body(instance).unwrap().as_ref().clone();
            poisoned.arg_count = 1;
            engine
                .bodies
                .borrow_mut()
                .insert(instance, Rc::new(poisoned));
            assert!(source(&mut engine, instance).is_err());
            assert!(engine.mutable_product_failed.get());
            engine
                .bodies
                .borrow_mut()
                .insert(instance, actual.body.clone());
            let used = engine.steps;
            assert!(source(&mut engine, instance).is_err());
            assert_eq!(engine.steps, used);
            let mut engine = fresh();
            engine.limits.max_steps = 2_000_000;
            let mut poisoned = original_wrapping.body.as_ref().clone();
            let StatementKind::Assign(assignment) =
                &mut poisoned.basic_blocks_mut()[rustc_middle::mir::START_BLOCK].statements[0].kind
            else {
                panic!("actual wrapping assignment");
            };
            let Rvalue::BinaryOp(operation, _) = &mut assignment.1 else {
                panic!("actual wrapping binary operation");
            };
            assert_eq!(*operation, BinOp::Add);
            *operation = BinOp::Sub;
            engine
                .bodies
                .borrow_mut()
                .insert(wrapping, Rc::new(poisoned));
            assert!(source(&mut engine, wrapping).is_err());
            assert!(engine.mutable_product_failed.get());
            engine
                .bodies
                .borrow_mut()
                .insert(wrapping, original_wrapping.body.clone());
            let used = engine.steps;
            assert!(source(&mut engine, wrapping).is_err());
            assert_eq!(engine.steps, used);
            let mut engine = fresh();
            engine.mutable_product_failed.set(true);
            assert!(
                engine
                    .mutable_product_vector_work(&Memory::default(), 0)
                    .is_err()
            );
            assert_eq!(engine.steps, 0);
            let mut engine = fresh();
            engine.steps = engine.limits.max_steps;
            assert!(pay(&mut engine, 1).is_err());
            assert!(engine.mutable_product_failed.get());
            let used = engine.steps;
            assert!(pay(&mut engine, 0).is_err());
            assert_eq!(engine.steps, used);
            descriptor_reuse_controls(tcx);
            actual_owner_controls(tcx);
            eligibility_controls(tcx);
            inactive_retry_controls(tcx);
            ordinary_eligibility_exhaustion_controls(tcx);
            self.0 = true;
            eprintln!("product source controls: actual signature5/body2/sticky8");
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/nested_mutable_products.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "rustc".into(),
                fixture.display().to_string(),
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
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}

fn actual_owner_controls(tcx: TyCtxt<'_>) {
    for mutation in 0..31 {
        let mut engine = super::super::nonzero_niches::test_engine(tcx);
        engine.limits.max_steps = 2_000_000;
        let id = tcx
            .hir_body_owners()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == "nested_owner_unknown"
            })
            .unwrap();
        let caller = ty::Instance::mono(tcx, id.to_def_id());
        let body = engine.instantiated_body(caller).unwrap();
        let (block, instance, args, destination, target) = body
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } = &data.terminator().kind
                else {
                    return None;
                };
                let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
                    return None;
                };
                let instance = engine
                    .resolve_function_item(*id, generic.skip_binder())
                    .unwrap();
                (tcx.item_name(*id).as_str() == "nested_child").then_some((
                    block,
                    instance,
                    args.as_ref(),
                    *destination,
                    *target,
                ))
            })
            .unwrap();
        let mut memory = Memory::default();
        let mut conditions = Vec::new();
        let root = engine
            .mutable_product_input(
                Ty::new_array(tcx, tcx.types.f32, 2),
                &mut memory,
                &mut conditions,
            )
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
            conditions,
            memory,
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: Default::default(),
        };
        state.locals[1] = Some(root);
        state.locals[2] = Some(symbolic::integer(
            &engine.terms,
            0,
            u32::from(tcx.sess.target.pointer_width),
            false,
        ));
        for statement in &body.basic_blocks[block].statements {
            engine
                .statement(caller, &body, &mut state, &statement.kind)
                .unwrap();
        }
        let (Operand::Move(place) | Operand::Copy(place)) = args[0].node else {
            panic!("actual owner operand");
        };
        match mutation {
            0 => {}
            1 => state
                .missing_places
                .consume(place.local.as_usize(), Vec::new())
                .unwrap(),
            2 => {
                let Value::MutableU16 { role, .. } =
                    state.locals[place.local.as_usize()].as_mut().unwrap()
                else {
                    panic!("actual owner");
                };
                *role = MutableU16Role::HierarchyChild { lease: u64::MAX };
            }
            3 => Rc::make_mut(&mut state.memory.mutable_u16)[0].generation += 1,
            4 => {
                let mut other = super::super::nonzero_niches::test_engine(tcx);
                let mut other_memory = Memory::default();
                other
                    .mutable_product_input(
                        Ty::new_array(tcx, tcx.types.f32, 2),
                        &mut other_memory,
                        &mut Vec::new(),
                    )
                    .unwrap();
                Rc::make_mut(&mut state.memory.mutable_u16)[0].data =
                    other_memory.mutable_u16[0].data.clone();
            }
            5..=30 => {}
            _ => unreachable!(),
        }
        let result = engine.mutable_product_hierarchy_call(
            caller,
            &mut state,
            super::super::mutable_u16_children::ChildCall {
                body: &body,
                block,
                instance,
                args,
                destination,
                target,
                stack: &[],
                site: (
                    caller.def_id(),
                    body.basic_blocks[block].terminator().source_info.span,
                ),
            },
        );
        if mutation == 0 || mutation >= 5 {
            let mut returns = result.unwrap().unwrap();
            assert_eq!(returns.len(), 1);
            assert!(
                returns[0].memory.mutable_u16[0]
                    .hierarchy
                    .as_ref()
                    .unwrap()
                    .owners
                    .is_empty()
            );
            if mutation >= 5 {
                let memory = &mut returns[0].memory;
                engine
                    .mutable_product_access_begin(
                        &body,
                        std::ptr::from_ref(body.as_ref()) as usize,
                        memory,
                        16,
                    )
                    .unwrap();
                if mutation >= 27 {
                    length_body_growth_controls(&mut engine, &body, memory, mutation - 27);
                    continue;
                }
                if mutation >= 20 {
                    library_signature_growth_controls(&mut engine, &body, memory, mutation - 20);
                    continue;
                }
                if mutation >= 16 {
                    descriptor_source_growth_controls(&mut engine, memory, mutation - 16);
                    continue;
                }
                if mutation >= 10 {
                    active_retry_controls(&mut engine, mutation);
                    continue;
                }
                match mutation {
                    5 => {
                        Rc::make_mut(&mut memory.mutable_u16)[0]
                            .hierarchy
                            .as_mut()
                            .unwrap()
                            .epoch += 1
                    }
                    6 => {
                        let mut poisoned = body.as_ref().clone();
                        poisoned.arg_count = 1;
                        engine.bodies.borrow_mut().insert(caller, Rc::new(poisoned));
                    }
                    7 => assert!(
                        engine
                            .mutable_product_access_begin(&body, 1, memory, 16)
                            .is_err()
                    ),
                    8 => {
                        Rc::make_mut(&mut memory.mutable_u16)[0]
                            .hierarchy
                            .as_mut()
                            .unwrap()
                            .issued += 1
                    }
                    9 => memory
                        .missing_places
                        .consume(memory.mutable_u16[0].allocation, Vec::new())
                        .unwrap(),
                    _ => unreachable!(),
                }
                assert!(
                    engine.mutable_product_backing(0, memory).is_err(),
                    "post-return mutation {mutation}"
                );
                assert!(engine.mutable_product_failed.get());
            }
        } else {
            assert!(result.is_err(), "owner mutation {mutation}");
            assert!(engine.mutable_product_failed.get());
        }
    }
    eprintln!(concat!(
        "product owner controls: call6/masks2/lease1/generation1/Context1/",
        "epoch1/caller1/site1/issued1"
    ));
}

// Use the returned owner's genuine current instruction Access. These budgets deny each
// planner fee before the unified clone can return a path; they never issue a lease.
fn active_retry_controls(engine: &mut Engine<'_>, case: usize) {
    assert!(engine.mutable_product_access.borrow().is_some());
    let mut path = retry_frontiers::Path::default();
    for block in 0..if case == 15 { MAX_INPUT_VALUES + 1 } else { 2 } {
        path.note(rustc_middle::mir::BasicBlock::from_usize(block));
    }
    let before = engine.steps;
    let allowance = match case {
        10 => 0,
        11 => 3,
        12 => 4,
        13 => 23,
        14 => 24,
        15 => 2_000_000,
        _ => unreachable!(),
    };
    engine.limits.max_steps = before + allowance;
    let result = engine.executable_box_retry_clone(None, &path);
    let charged = engine.steps - before;
    if case == 14 {
        let mut cloned = result.unwrap();
        assert_eq!(charged, 24);
        assert_eq!(cloned.len(), 2);
        cloned.note(rustc_middle::mir::BasicBlock::from_usize(2));
        assert_eq!(cloned.len(), 3);
        assert_eq!(path.len(), 2);
        assert!(!engine.mutable_product_failed.get());
        engine.mutable_product_access_end(false);
    } else {
        let error = result
            .err()
            .expect("retry clone must not publish after denial");
        assert_eq!(charged, if case <= 11 || case == 15 { 4 } else { 24 });
        if case != 15 {
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::ResourceLimit)
            );
        }
        assert!(engine.mutable_product_failed.get());
        engine.limits.max_steps = 2_000_000;
        let spent = engine.steps;
        assert!(engine.executable_box_retry_clone(None, &path).is_err());
        assert_eq!(engine.steps, spent);
        assert!(engine.mutable_product_failed.get());
    }
    eprintln!("PRODUCT_RETRY_CONTROL case={case} allowance={allowance} charged={charged}");
}

fn inactive_retry_controls(tcx: TyCtxt<'_>) {
    let mut engine = super::super::nonzero_niches::test_engine(tcx);
    engine.limits.max_steps = 0;
    let mut path = retry_frontiers::Path::default();
    path.note(rustc_middle::mir::BasicBlock::from_usize(0));
    let mut cloned = engine.executable_box_retry_clone(None, &path).unwrap();
    assert_eq!(engine.steps, 0);
    cloned.note(rustc_middle::mir::BasicBlock::from_usize(1));
    assert_eq!(cloned.len(), 2);
    assert_eq!(path.len(), 1);
    engine.mutable_product_failed.set(true);
    assert!(engine.executable_box_retry_clone(None, &path).is_err());
    assert_eq!(engine.steps, 0);
    eprintln!("PRODUCT_RETRY_CONTROL inactive/free-clone/sticky");
}

// Exercise the public call boundary with an actual compiler Call, without a Product owner.
// Ordinary routing work exhaustion must not issue or fail Product authority.
fn ordinary_eligibility_exhaustion_controls(tcx: TyCtxt<'_>) {
    for scalar in [false, true] {
        let mut engine = super::super::nonzero_niches::test_engine(tcx);
        let id = tcx
            .hir_body_owners()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == "nested_tuple"
            })
            .unwrap();
        let caller = ty::Instance::mono(tcx, id.to_def_id());
        let body = engine.instantiated_body(caller).unwrap();
        let (block, instance, args, destination, target) = body
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } = &data.terminator().kind
                else {
                    return None;
                };
                let ty::FnDef(id, generic) = func.ty(&body.local_decls, tcx).kind() else {
                    return None;
                };
                let selected = engine
                    .resolve_function_item(*id, generic.skip_binder())
                    .unwrap();
                Some((block, selected, args.as_ref(), *destination, *target))
            })
            .unwrap();
        let mut memory = Memory::default();
        let mut conditions = Vec::new();
        if scalar {
            engine
                .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                .unwrap();
        }
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            addresses: vec![None; body.local_decls.len()],
            conditions,
            memory,
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: Default::default(),
        };
        let call = || super::super::mutable_u16_children::ChildCall {
            body: &body,
            block,
            instance,
            args,
            destination,
            target,
            stack: &[],
            site: (
                caller.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        };
        let before = engine.steps;
        engine.limits.max_steps = before;
        let error = engine
            .mutable_product_hierarchy_call(caller, &mut state, call())
            .err()
            .expect("ordinary eligibility must refuse before observing call arguments");
        assert_eq!(engine.steps, before + 1);
        assert_eq!(error, "symbolic execution step limit reached");
        assert_eq!(
            engine.unknown_causes.borrow().get(&error),
            Some(&UnknownCategory::ResourceLimit)
        );
        assert!(!engine.mutable_product_failed.get());
        assert!(engine.mutable_product_access.borrow().is_none());
        assert!(engine.mutable_product_sources.borrow().is_empty());
        engine.limits.max_steps = before + 2;
        assert!(
            engine
                .mutable_product_hierarchy_call(caller, &mut state, call())
                .unwrap()
                .is_none()
        );
        assert_eq!(engine.steps, before + 2);
        assert!(!engine.mutable_product_failed.get());
        assert!(engine.mutable_product_access.borrow().is_none());
        assert!(engine.mutable_product_sources.borrow().is_empty());
        eprintln!("PRODUCT_ELIGIBILITY ordinary scalar={scalar} paid1/no-product-poison");
    }
}

fn eligibility_controls(tcx: TyCtxt<'_>) {
    let fresh = || super::super::nonzero_niches::test_engine(tcx);
    let mut engine = fresh();
    assert!(
        !engine
            .product_catalogue_eligible(&Memory::default())
            .unwrap()
    );
    assert_eq!(engine.steps, 1);
    engine.mutable_product_failed.set(true);
    assert!(
        engine
            .product_catalogue_eligible(&Memory::default())
            .is_err()
    );
    assert_eq!(engine.steps, 1);
    let mut engine = fresh();
    let mut scalar = Memory::default();
    engine
        .mutable_u16_input(tcx.types.u16, &mut scalar, &mut Vec::new())
        .unwrap();
    let before = engine.steps;
    assert!(!engine.product_catalogue_eligible(&scalar).unwrap());
    assert_eq!(engine.steps, before + 1);
    let mut product = Memory::default();
    engine
        .mutable_product_input(
            Ty::new_array(tcx, tcx.types.f32, 2),
            &mut product,
            &mut Vec::new(),
        )
        .unwrap();
    assert!(engine.product_catalogue_eligible(&product).unwrap());
    Rc::make_mut(&mut product.mutable_u16)[0].data = scalar.mutable_u16[0].data.clone();
    assert!(engine.product_catalogue_eligible(&product).is_err());
    assert!(engine.mutable_product_failed.get());
    let mut engine = fresh();
    let id = tcx
        .hir_body_owners()
        .find(|id| {
            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && tcx.item_name(id.to_def_id()).as_str() == "nested_tuple"
        })
        .unwrap();
    engine.limits.max_steps = 2_000_000;
    let held = source(&mut engine, ty::Instance::mono(tcx, id.to_def_id())).unwrap();
    register_source(&mut engine, held).unwrap();
    assert!(
        engine
            .product_catalogue_eligible(&Memory::default())
            .is_err()
    );
    assert!(engine.mutable_product_failed.get());
    let mut engine = fresh();
    let mut scalar = Memory::default();
    engine
        .mutable_u16_input(tcx.types.u16, &mut scalar, &mut Vec::new())
        .unwrap();
    let mut product = Memory::default();
    engine
        .mutable_product_input(
            Ty::new_array(tcx, tcx.types.f32, 2),
            &mut product,
            &mut Vec::new(),
        )
        .unwrap();
    let product_certificate = product.mutable_u16[0].certificate;
    Rc::make_mut(&mut scalar.mutable_u16)[0].hierarchy = Some(Hierarchy {
        origin: Rc::new(Origin {
            certificate: product_certificate,
            allocation: scalar.mutable_u16[0].allocation,
            capacity: scalar.mutable_u16[0].length.clone(),
            data_context: product.mutable_u16[0].data.clone(),
        }),
        issued: 0,
        epoch: 0,
        owners: Vec::new(),
        pending: None,
    });
    assert!(engine.product_catalogue_eligible(&scalar).is_err());
    assert!(engine.mutable_product_failed.get());
    let mut engine = fresh();
    engine.mutable_product_access.borrow_mut().replace(Access {
        source_plan: Default::default(),
        source_bindings: 0,
        instruction_source: None,
        prepared: None,
        body: 1,
        frame: 1,
        occurrence: 1,
        owner: 0,
        origin: 1,
        issued: 0,
        epoch: 0,
        columns: 0,
        owners: 0,
        frames: 0,
        masks: 0,
        remaining: 1,
        descriptors: 1,
        original: tcx.types.u16,
        failed: false,
    });
    assert!(
        engine
            .product_catalogue_eligible(&Memory::default())
            .is_err()
    );
    assert!(engine.mutable_product_failed.get());
    eligibility_singleton_controls(tcx);
    eprintln!("product eligibility: paid1/empty/scalar/product/codec/origin/access/source/sticky");
}

fn eligibility_singleton_controls<'tcx>(tcx: TyCtxt<'tcx>) {
    let fresh = || super::super::nonzero_niches::test_engine(tcx);
    let scalar = |engine: &mut Engine<'tcx>| {
        let mut memory = Memory::default();
        engine
            .mutable_u16_input(tcx.types.u16, &mut memory, &mut Vec::new())
            .unwrap();
        memory
    };
    let mut engine = fresh();
    let memory = scalar(&mut engine);
    engine.mutable_product_access.borrow_mut().replace(Access {
        source_plan: Default::default(),
        source_bindings: 0,
        instruction_source: None,
        prepared: None,
        body: 1,
        frame: 1,
        occurrence: 1,
        owner: 0,
        origin: 1,
        issued: 0,
        epoch: 0,
        columns: 0,
        owners: 0,
        frames: 0,
        masks: 0,
        remaining: 1,
        descriptors: 1,
        original: tcx.types.u16,
        failed: false,
    });
    let before = engine.steps;
    assert!(engine.product_catalogue_eligible(&memory).is_err());
    assert_eq!(engine.steps, before + 1);
    assert!(engine.mutable_product_failed.get());
    assert!(engine.product_catalogue_eligible(&memory).is_err());
    assert_eq!(engine.steps, before + 1);

    let mut engine = fresh();
    let memory = scalar(&mut engine);
    let id = tcx
        .hir_body_owners()
        .find(|id| {
            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && tcx.item_name(id.to_def_id()).as_str() == "nested_tuple"
        })
        .unwrap();
    engine.limits.max_steps = 2_000_000;
    let held = source(&mut engine, ty::Instance::mono(tcx, id.to_def_id())).unwrap();
    register_source(&mut engine, held).unwrap();
    let before = engine.steps;
    assert!(engine.product_catalogue_eligible(&memory).is_err());
    assert_eq!(engine.steps, before + 1);
    assert!(engine.mutable_product_failed.get());

    let mut engine = fresh();
    let mut memory = scalar(&mut engine);
    Rc::make_mut(&mut memory.mutable_u16)[0].certificate = usize::MAX;
    assert!(engine.product_catalogue_eligible(&memory).is_err());
    assert!(engine.mutable_product_failed.get());

    // Eligibility does not authenticate a Scalar codec, layout or ordinary owner rights.
    // These malformed primitive headers remain subject to the original Scalar validator.
    for mutate_original in [false, true] {
        let mut engine = fresh();
        let memory = scalar(&mut engine);
        let certificate = memory.mutable_u16[0].certificate;
        if mutate_original {
            engine.mutable_integer_types[certificate].original = tcx.types.bool;
        } else {
            engine.mutable_integer_types[certificate].codec =
                super::super::mutable_u16::ElementCodec::Scalar(symbolic::ScalarSliceElement::Bool);
        }
        let before = engine.steps;
        assert!(!engine.product_catalogue_eligible(&memory).unwrap());
        assert_eq!(engine.steps, before + 1);
        assert!(engine.mutable_u16_backing(0, &memory).is_err());
    }
    eprintln!(
        "product singleton eligibility: access/source/missing/codec/type; Scalar guard retained"
    );
}

// Compiler metadata controls use the genuine helper Instance/input Local and its actual source.
// They exercise preparation and full mutable-certificate comparison, not owner admission.
fn descriptor_reuse_controls(tcx: TyCtxt<'_>) {
    use super::super::super::mutable_product_descriptors::{Binding, prepare};
    use super::super::super::mutable_u16::ElementCodec;
    let id = tcx
        .hir_body_owners()
        .find(|id| {
            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && tcx.item_name(id.to_def_id()).as_str() == "nested_tuple"
        })
        .unwrap();
    let instance = ty::Instance::mono(tcx, id.to_def_id());
    let setup = || {
        let mut engine = super::super::nonzero_niches::test_engine(tcx);
        engine.limits.max_steps = 2_000_000;
        engine.instantiated_body(instance).unwrap();
        let actual = source(&mut engine, instance).unwrap();
        let body = actual.body.clone();
        let signature = actual.signature;
        let frame = register_source(&mut engine, actual).unwrap();
        let ty::Ref(_, inner, _) = body.local_decls[body.args_iter().next().unwrap()].ty.kind()
        else {
            panic!("actual nested tuple input is not a reference")
        };
        let ty::Slice(original) = inner.kind() else {
            panic!("actual nested tuple input is not a slice")
        };
        let original = *original;
        let mut memory = Memory::default();
        engine
            .mutable_product_input(original, &mut memory, &mut Vec::new())
            .unwrap();
        let certificate = memory.mutable_u16[0].certificate;
        (
            engine,
            Binding {
                frame,
                instance,
                body,
                signature,
            },
            certificate,
            original,
        )
    };
    let (mut engine, binding, certificate, original) = setup();
    let start = engine.steps;
    let (prepared, publish) = prepare(&mut engine, binding, certificate, original).unwrap();
    let exact = engine.steps - start;
    assert!(publish);
    assert!(engine.mutable_product_descriptors.is_empty());
    engine.mutable_product_descriptors.push(prepared.clone());
    let signature = prepared_signature(&engine, instance);
    let body = engine.bodies.borrow().get(&instance).unwrap().clone();
    let frame = engine
        .mutable_product_sources
        .borrow()
        .keys()
        .next()
        .copied()
        .unwrap();
    let (warm, publish) = prepare(
        &mut engine,
        Binding {
            frame,
            instance,
            body,
            signature,
        },
        certificate,
        original,
    )
    .unwrap();
    assert!(!publish);
    assert!(Rc::ptr_eq(&prepared, &warm));
    assert_eq!(engine.mutable_product_descriptors.len(), 1);
    for delta in [exact - 1, exact] {
        let (mut engine, binding, certificate, original) = setup();
        engine.limits.max_steps = engine.steps + delta;
        let result = prepare(&mut engine, binding, certificate, original);
        assert_eq!(result.is_ok(), delta == exact);
        assert_eq!(engine.mutable_product_failed.get(), delta != exact);
        assert!(engine.mutable_product_descriptors.is_empty());
        if result.is_err() {
            let used = engine.steps;
            assert!(pay(&mut engine, 0).is_err());
            assert_eq!(engine.steps, used);
        }
    }
    // The dispatcher registry is optional. Actual compiler issuance populates it; clearing
    // it retains the independently authenticated full signature held by the source record.
    for retained in [false, true] {
        let (mut engine, binding, certificate, original) = setup();
        let frame = binding.frame;
        let body = binding.body.clone();
        let signature = binding.signature;
        assert_eq!(engine.call_poly_signature(instance).unwrap(), signature);
        assert!(engine.call_signatures.borrow().contains_key(&instance));
        if retained {
            let (prepared, publish) = prepare(&mut engine, binding, certificate, original).unwrap();
            assert!(publish);
            engine.mutable_product_descriptors.push(prepared);
        }
        engine.call_signatures.borrow_mut().clear();
        let (prepared, publish) = prepare(
            &mut engine,
            Binding {
                frame,
                instance,
                body,
                signature,
            },
            certificate,
            original,
        )
        .unwrap();
        assert_eq!(publish, !retained);
        prepared.validate_source(&engine).unwrap();
        assert!(engine.call_signatures.borrow().is_empty());
        assert!(!engine.mutable_product_failed.get());
    }
    for warm in [false, true] {
        for mutation in 0..14 {
            let (mut engine, binding, certificate, original) = setup();
            let frame = binding.frame;
            let body = binding.body.clone();
            let signature = binding.signature;
            if warm {
                let (prepared, publish) =
                    prepare(&mut engine, binding, certificate, original).unwrap();
                assert!(publish);
                engine.mutable_product_descriptors.push(prepared);
            }
            let binding = Binding {
                frame,
                instance,
                body: body.clone(),
                signature,
            };
            let issued = &mut engine.mutable_integer_types[certificate];
            match mutation {
                0 => issued.original = tcx.types.bool,
                1 => issued.bytes += 1,
                2 => issued.alignment += 1,
                3 => issued.codec = ElementCodec::Scalar(symbolic::ScalarSliceElement::Bool),
                4..=8 => {
                    let ElementCodec::Product(product) = &mut issued.codec else {
                        unreachable!()
                    };
                    match mutation {
                        4 => product.ty = tcx.types.bool,
                        5 => product.bytes += 1,
                        6 => product.leaves.clear(),
                        7 => {
                            let before = product.leaves[0];
                            product.leaves[0] = if before == symbolic::ScalarSliceElement::Bool {
                                symbolic::ScalarSliceElement::Char
                            } else {
                                symbolic::ScalarSliceElement::Bool
                            };
                            assert_ne!(product.leaves[0], before);
                        }
                        8 => {
                            product.shape =
                                super::super::super::composite_slices::CompositeShape::Tuple(
                                    Vec::new(),
                                )
                        }
                        _ => unreachable!(),
                    }
                }
                9 => {
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(instance, Rc::new((*body).clone()));
                }
                10 => {
                    engine.call_signatures.borrow_mut().insert(
                        instance,
                        signature.map_bound(|sig| sig.set_safety(rustc_hir::Safety::Unsafe)),
                    );
                }
                11 => {
                    engine
                        .mutable_product_sources
                        .borrow_mut()
                        .get_mut(&frame)
                        .unwrap()
                        .signature =
                        signature.map_bound(|sig| sig.set_safety(rustc_hir::Safety::Unsafe));
                }
                12 => {
                    engine.bodies.borrow_mut().remove(&instance);
                }
                13 => {
                    engine.mutable_product_sources.borrow_mut().remove(&frame);
                }
                _ => unreachable!(),
            }
            assert!(
                prepare(&mut engine, binding, certificate, original).is_err(),
                "mutable descriptor mutation {mutation}, warm={warm}"
            );
            assert!(engine.mutable_product_failed.get());
            assert_eq!(engine.mutable_product_descriptors.len(), usize::from(warm));
        }
    }
    eprintln!(
        "descriptor reuse: genuine input/cold+warm/exact fee/sticky/cache-clear/28 mutations"
    );
}

fn prepared_signature<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> ty::PolyFnSig<'tcx> {
    engine
        .mutable_product_sources
        .borrow()
        .values()
        .find(|source| source.instance == instance)
        .unwrap()
        .signature
}

fn descriptor_source_growth_controls<'tcx>(
    engine: &mut Engine<'tcx>,
    memory: &Memory,
    mode: usize,
) {
    let helper = engine
        .tcx
        .hir_body_owners()
        .find(|id| {
            engine.tcx.def_kind(id.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(id.to_def_id()).as_str() == "integer_leaf"
        })
        .unwrap();
    let actual = source(engine, ty::Instance::mono(engine.tcx, helper.to_def_id())).unwrap();
    let prior = engine
        .mutable_product_access
        .borrow()
        .as_ref()
        .unwrap()
        .source_plan
        .work()
        .unwrap();
    if mode == 1 {
        // A genuine compiler record and actual frame still cannot bypass paid publication.
        let frame = engine
            .activation_register_frame(&actual.body, &activation_flow::Flow::Unarmed)
            .unwrap();
        engine
            .mutable_product_sources
            .borrow_mut()
            .insert(frame, actual);
        let certificate = memory.mutable_u16[0].certificate;
        assert!(engine.mutable_product_certificate(certificate).is_err());
        assert!(engine.mutable_product_failed.get());
    } else {
        if mode >= 2 {
            let frames = engine.mutable_u16_frames.borrow().len();
            let count = engine.mutable_product_sources.borrow().len();
            let scope = engine.mutable_product_access.borrow();
            let access = scope.as_ref().unwrap();
            let fee = 4 + frames + 12 + count + 8 + access.descriptors * access.source_bindings;
            drop(scope);
            engine.limits.max_steps = engine.steps + fee - usize::from(mode == 2);
        }
        let published = engine.mutable_product_sources.borrow().len();
        let result = register_source(engine, actual);
        if mode == 2 {
            assert!(result.is_err());
            assert_eq!(engine.mutable_product_sources.borrow().len(), published);
            assert_eq!(
                engine
                    .mutable_product_access
                    .borrow()
                    .as_ref()
                    .unwrap()
                    .source_plan
                    .work()
                    .unwrap(),
                prior
            );
            assert!(engine.mutable_product_failed.get());
            let used = engine.steps;
            assert!(pay(engine, 0).is_err());
            assert_eq!(engine.steps, used);
            eprintln!("descriptor source growth: denied before source publication");
            return;
        }
        result.unwrap();
        if mode == 3 {
            assert_eq!(engine.steps, engine.limits.max_steps);
        }
        let next = engine
            .mutable_product_access
            .borrow()
            .as_ref()
            .unwrap()
            .source_plan
            .work()
            .unwrap();
        assert_eq!(next, prior + 1);
        engine
            .mutable_product_certificate(memory.mutable_u16[0].certificate)
            .unwrap();
        assert!(!engine.mutable_product_failed.get());
    }
    eprintln!("descriptor source growth: actual helper registration; mode={mode}");
}

#[test]
fn actual_impl_product_path_plans_precede_compiler_name_allocation() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            work::impl_path_controls(tcx);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_impl_paths.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "rustc".into(),
                fixture.display().to_string(),
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
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}

#[test]
fn actual_external_impl_paths_include_visible_reexports_and_explicit_aliases() {
    struct Check {
        complete: bool,
        oversized: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            work::external_path_controls(tcx, self.oversized);
            self.complete = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    let output = std::env::temp_dir().join(format!(
        "miren-product-external-name-controls-{}",
        std::process::id(),
    ));
    std::fs::create_dir_all(&output).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let archive = output.join(format!("libd-{}-o{level}.rlib", target.unwrap_or("host")));
            let compiler = std::path::Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
            let mut dependency = std::process::Command::new(compiler);
            dependency
                .args([
                    "--crate-type=rlib",
                    "--crate-name=d",
                    "--edition=2024",
                    "-Cpanic=abort",
                ])
                .arg(format!("-Copt-level={level}"))
                .arg(fixtures.join("mutable_product_external_names_dependency.rs"))
                .arg("-o")
                .arg(&archive);
            if let Some(target) = target {
                dependency.args(["--target", target]);
            }
            let compiled = dependency.output().unwrap();
            assert!(
                compiled.status.success(),
                "{}",
                String::from_utf8_lossy(&compiled.stderr)
            );
            let mut check = Check {
                complete: false,
                oversized: false,
            };
            let mut args = vec![
                "rustc".into(),
                fixtures
                    .join("mutable_product_external_impl_names.rs")
                    .display()
                    .to_string(),
                "--crate-name=e".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                "-Ztrim-diagnostic-paths=no".into(),
                format!("-Copt-level={level}"),
                "--extern".into(),
                format!("d={}", archive.display()),
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.complete);
            let original =
                std::fs::read_to_string(fixtures.join("mutable_product_external_impl_names.rs"))
                    .unwrap();
            let oversized = output.join("oversized_external_alias.rs");
            let name = format!("actual_external_alias_{}", "X".repeat(MAX_INPUT_VALUES));
            std::fs::write(
                &oversized,
                original.replace("actual_external_alias_for_printer", &name),
            )
            .unwrap();
            args[1] = oversized.display().to_string();
            let mut check = Check {
                complete: false,
                oversized: true,
            };
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.complete);
        }
    }
    std::fs::remove_dir_all(output).unwrap();
}

fn library_signature_growth_controls<'tcx>(
    engine: &mut Engine<'tcx>,
    body: &Body<'tcx>,
    memory: &Memory,
    mode: usize,
) {
    let len = engine.tcx.lang_items().get(LangItem::SliceLen).unwrap();
    // Select the real instantiated len target already called by the genuine owner helper.
    let instance = engine
        .call_signatures
        .borrow()
        .keys()
        .find(|instance| instance.def_id() == len)
        .copied()
        .unwrap();
    let original_signature = engine.call_signatures.borrow()[&instance];
    engine.mutable_product_access_end(false);
    engine.call_signatures.borrow_mut().remove(&instance);
    if mode == 3 {
        engine.call_signatures.borrow_mut().clear();
        for id in engine.tcx.hir_body_owners() {
            if engine.tcx.def_kind(id.to_def_id()) != DefKind::Fn
                || engine.tcx.generics_of(id).count() != 0
            {
                continue;
            }
            let selected = ty::Instance::mono(engine.tcx, id.to_def_id());
            let _ = engine.call_poly_signature(selected);
            if engine.call_signatures.borrow().len()
                == super::super::super::call_metadata::MAX_CALL_SIGNATURES
            {
                break;
            }
        }
        assert_eq!(engine.call_signatures.borrow().len(), 256);
        assert!(!engine.call_signatures.borrow().contains_key(&instance));
    }
    engine
        .mutable_product_access_begin(body, std::ptr::from_ref(body) as usize, memory, 16)
        .unwrap();
    let before = engine.call_signatures.borrow().len();
    let prior = engine
        .mutable_product_access
        .borrow()
        .as_ref()
        .unwrap()
        .source_plan
        .work()
        .unwrap();
    if mode == 3 {
        engine
            .mutable_product_call_signature_prepare(instance)
            .unwrap();
        assert_eq!(engine.call_signatures.borrow().len(), 256);
        assert!(!engine.call_signatures.borrow().contains_key(&instance));
        assert_eq!(
            engine.call_poly_signature(instance).unwrap(),
            original_signature
        );
        assert_eq!(engine.call_signatures.borrow().len(), 256);
        assert!(!engine.call_signatures.borrow().contains_key(&instance));
        engine
            .mutable_product_certificate(memory.mutable_u16[0].certificate)
            .unwrap();
        assert!(!engine.mutable_product_failed.get());
        eprintln!(
            "actual len cache full256: no publication/downstream original sig/descriptor live"
        );
        return;
    }
    if mode == 4 {
        // A safe held interior borrow can exercise &self descriptor lookup refusal. Rust's
        // exclusive Engine borrow prevents constructing this conflict for the &mut precursor.
        let held = engine.call_signatures.borrow_mut();
        assert!(
            engine
                .mutable_product_certificate(memory.mutable_u16[0].certificate)
                .is_err()
        );
        drop(held);
        assert_eq!(engine.call_signatures.borrow().len(), before);
        assert!(engine.mutable_product_failed.get());
        eprintln!("actual len signature registry: held borrow refused by selected descriptor");
        return;
    }
    if mode >= 5 {
        let begin = engine.steps;
        assert_eq!(
            signature::check(engine, instance).unwrap(),
            original_signature
        );
        let normalization = engine.steps - begin;
        let scope = engine.mutable_product_access.borrow();
        let access = scope.as_ref().unwrap();
        let remaining_lookup = access.descriptors * access.source_bindings;
        drop(scope);
        let exact = before + 12 + normalization + remaining_lookup + 8;
        engine.limits.max_steps = engine.steps + exact - usize::from(mode == 5);
        let result = engine.mutable_product_call_signature_prepare(instance);
        assert_eq!(result.is_ok(), mode == 6);
        assert_eq!(
            engine
                .mutable_product_access
                .borrow()
                .as_ref()
                .unwrap()
                .source_plan
                .work()
                .unwrap(),
            prior + 1
        );
        if mode == 5 {
            assert_eq!(engine.call_signatures.borrow().len(), before);
            assert!(!engine.call_signatures.borrow().contains_key(&instance));
            assert!(engine.mutable_product_failed.get());
            let used = engine.steps;
            assert!(
                engine
                    .mutable_product_call_signature_prepare(instance)
                    .is_err()
            );
            assert_eq!(engine.steps, used);
        } else {
            assert_eq!(engine.steps, engine.limits.max_steps);
            assert_eq!(engine.call_signatures.borrow().len(), before + 1);
            assert_eq!(
                engine.call_signatures.borrow()[&instance],
                original_signature
            );
            engine
                .mutable_product_certificate(memory.mutable_u16[0].certificate)
                .unwrap();
        }
        eprintln!("actual len insertion boundary: successful replan, exact={exact}, mode={mode}");
        return;
    }
    if mode == 1 {
        // Denial uses the unchanged real counter at the actual selected metadata boundary.
        engine.limits.max_steps = engine.steps;
        assert!(
            engine
                .mutable_product_call_signature_prepare(instance)
                .is_err()
        );
        assert_eq!(engine.call_signatures.borrow().len(), before);
        assert!(!engine.call_signatures.borrow().contains_key(&instance));
        assert!(engine.mutable_product_failed.get());
        let used = engine.steps;
        assert!(
            engine
                .mutable_product_call_signature_prepare(instance)
                .is_err()
        );
        assert_eq!(engine.steps, used);
    } else {
        engine
            .mutable_product_call_signature_prepare(instance)
            .unwrap();
        assert_eq!(engine.call_signatures.borrow().len(), before + 1);
        assert_eq!(
            engine.call_signatures.borrow()[&instance],
            original_signature
        );
        assert_eq!(
            engine
                .mutable_product_access
                .borrow()
                .as_ref()
                .unwrap()
                .source_plan
                .work()
                .unwrap(),
            prior + 1
        );
        let used = engine.steps;
        let count = engine.call_signatures.borrow().len();
        engine
            .mutable_product_call_signature_prepare(instance)
            .unwrap();
        assert!(engine.steps - used > count + 12);
        assert_eq!(engine.call_signatures.borrow().len(), count);
        engine
            .mutable_product_certificate(memory.mutable_u16[0].certificate)
            .unwrap();
        assert!(!engine.mutable_product_failed.get());
        if mode == 2 {
            engine.call_signatures.borrow_mut().insert(
                instance,
                original_signature.map_bound(|sig| sig.set_safety(rustc_hir::Safety::Unsafe)),
            );
            assert!(
                engine
                    .mutable_product_call_signature_prepare(instance)
                    .is_err()
            );
            assert!(engine.mutable_product_failed.get());
        }
    }
    eprintln!(
        "actual len signature growth: source plan before={prior}; signatures before={before}; mode={mode}"
    );
}

fn length_body_growth_controls<'tcx>(
    engine: &mut Engine<'tcx>,
    body: &Body<'tcx>,
    memory: &Memory,
    mode: usize,
) {
    let len = engine.tcx.lang_items().get(LangItem::SliceLen).unwrap();
    let instance = engine
        .bodies
        .borrow()
        .keys()
        .find(|instance| instance.def_id() == len)
        .copied()
        .unwrap();
    engine.mutable_product_access_end(false);
    engine.bodies.borrow_mut().remove(&instance);
    engine
        .mutable_product_access_begin(body, std::ptr::from_ref(body) as usize, memory, 16)
        .unwrap();
    let count = engine.bodies.borrow().len();
    assert!(count < 128);
    let (prior, exact) = {
        let scope = engine.mutable_product_access.borrow();
        let scope = scope.as_ref().unwrap();
        (
            scope.source_plan.work().unwrap(),
            count + 12 + scope.descriptors * scope.source_bindings,
        )
    };
    if mode == 1 {
        engine.limits.max_steps = engine.steps;
    } else if mode >= 2 {
        engine.limits.max_steps = engine.steps + exact - usize::from(mode == 2);
    }
    // The observed scope fields above do not carry authority across the actual mutation.
    let result = engine.mutable_product_length_body(instance);
    if mode == 1 || mode == 2 {
        assert!(result.is_err());
        assert_eq!(engine.bodies.borrow().len(), count);
        assert!(!engine.bodies.borrow().contains_key(&instance));
        assert!(engine.mutable_product_failed.get());
        let used = engine.steps;
        assert!(engine.mutable_product_length_body(instance).is_err());
        assert_eq!(engine.steps, used);
    } else {
        let actual = result.unwrap();
        assert_eq!(actual.source.instance, instance.def);
        assert_eq!(engine.bodies.borrow().len(), count + 1);
        assert!(Rc::ptr_eq(&actual, &engine.bodies.borrow()[&instance]));
        assert_eq!(
            engine
                .mutable_product_access
                .borrow()
                .as_ref()
                .unwrap()
                .source_plan
                .work()
                .unwrap(),
            prior + 1,
        );
        if mode == 3 {
            assert_eq!(engine.steps, engine.limits.max_steps);
        }
        engine
            .mutable_product_certificate(memory.mutable_u16[0].certificate)
            .unwrap();
        if mode == 0 {
            let used = engine.steps;
            let warm = engine.mutable_product_length_body(instance).unwrap();
            assert!(Rc::ptr_eq(&actual, &warm));
            assert_eq!(engine.steps - used, count + 13);
            assert_eq!(engine.bodies.borrow().len(), count + 1);
        }
        assert!(!engine.mutable_product_failed.get());
    }
    eprintln!("actual SliceLen Body growth: count={count}, exact={exact}, mode={mode}");
}
