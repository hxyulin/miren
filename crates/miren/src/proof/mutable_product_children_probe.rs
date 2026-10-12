//! Actual issued staging/frame controls; standalone compiler controls, not survey guest proofs.
use super::*;
use rustc_middle::mir::Local;
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
fn body<'tcx>(engine: &Engine<'tcx>, name: &str) -> (ty::Instance<'tcx>, Rc<Body<'tcx>>) {
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
fn state<'tcx>(
    engine: &Engine<'tcx>,
    body: &Body<'tcx>,
    memory: Memory,
    conditions: Vec<Term>,
    owner: Value,
) -> State {
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let mut locals = vec![None; body.local_decls.len()];
    for (local, declaration) in body.local_decls.iter_enumerated() {
        if declaration.ty == engine.tcx.types.usize {
            locals[local.as_usize()] = Some(symbolic::integer(&engine.terms, 0, bits, false));
        }
    }
    locals[1] = Some(owner);
    State {
        flow: activation_flow::Flow::Unarmed,
        locals,
        addresses: vec![None; body.local_decls.len()],
        conditions,
        memory,
        missing_places: Default::default(),
    }
}
fn controls(tcx: TyCtxt<'_>) {
    let mut engine = make_engine(tcx);
    let (caller, caller_body) = body(&engine, "float_call");
    let (selected, selected_body) = body(&engine, "write_float");
    let original = Ty::new_array(tcx, tcx.types.f32, 2);
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let root = engine
        .mutable_product_input(original, &mut memory, &mut conditions)
        .unwrap();
    let bits = u32::from(tcx.sess.target.pointer_width);
    Rc::make_mut(&mut memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 2, bits, false);
    let initial = state(
        &engine,
        &caller_body,
        memory.clone(),
        conditions.clone(),
        root.clone(),
    );
    let (destination, rvalue, occurrence) = caller_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return None;
            };
            if matches!(&assignment.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                if place.local.as_usize() == 1
                    && place.projection.as_ref() == [ProjectionElem::Deref])
            {
                Some((assignment.0, &assignment.1, &statement.kind))
            } else {
                None
            }
        })
        .unwrap();
    let mut pending = initial.clone();
    assert!(
        engine
            .mutable_u16_stage(&caller_body, &mut pending, destination, rvalue, occurrence)
            .unwrap()
    );
    assert!(matches!(
        pending.memory.mutable_u16[0].phase,
        Phase::Pending { .. }
    ));
    let child = pending.locals[destination.local.as_usize()]
        .as_ref()
        .unwrap()
        .clone();
    assert!(
        engine
            .mutable_product_length(&root, &pending.memory, &pending.conditions)
            .is_err()
    );
    assert!(
        engine
            .mutable_product_length(&child, &pending.memory, &pending.conditions)
            .is_err()
    );
    engine
        .mutable_u16_staging_tip(&caller_body, &pending, destination.local.as_usize(), 0, 1)
        .unwrap();
    let mut wrong_body = (*caller_body).clone();
    assert!(
        engine
            .mutable_u16_staging_tip(&wrong_body, &pending, destination.local.as_usize(), 0, 1)
            .is_err()
    );
    assert!(
        engine
            .mutable_u16_exit(&caller_body, std::slice::from_ref(&root), &pending.memory)
            .is_err()
    );
    let (block, args, result, target) = caller_body
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
            if matches!(func.ty(&caller_body.local_decls, tcx).kind(), ty::FnDef(id, _)
                if *id == selected.def_id())
            {
                Some((block, args.as_ref(), *destination, *target))
            } else {
                None
            }
        })
        .unwrap();
    let mut invoked = pending.clone();
    let returns = engine
        .mutable_u16_child_call(
            &mut invoked,
            super::super::mutable_u16_children::ChildCall {
                body: &caller_body,
                block,
                instance: selected,
                args,
                destination: result,
                target,
                stack: &[caller.def_id()],
                site: (caller.def_id(), caller_body.span),
            },
        )
        .unwrap()
        .unwrap();
    assert!(!returns.is_empty());
    assert!(returns.iter().all(|r| matches!(r.value, Value::Unit)));
    for returned in &returns {
        assert_eq!(returned.memory.mutable_u16[0].phase, Phase::Idle);
        assert_eq!(returned.memory.mutable_u16[0].generation, 1);
        assert!(
            engine
                .mutable_product_length(
                    &Value::MutableU16 {
                        id: 0,
                        role: MutableU16Role::Metadata { generation: 0 },
                    },
                    &returned.memory,
                    &returned.conditions
                )
                .is_err()
        );
        engine
            .mutable_product_length(&root, &returned.memory, &returned.conditions)
            .unwrap();
        let post = state(
            &engine,
            &caller_body,
            returned.memory.clone(),
            returned.conditions.clone(),
            root.clone(),
        );
        let place = Place {
            local: Local::from_usize(1),
            projection: tcx.mk_place_elems(&[
                ProjectionElem::Deref,
                ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: 1,
                    from_end: false,
                },
                ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: 2,
                    from_end: false,
                },
            ]),
        };
        let observed = engine
            .mutable_product_read(Some(&caller_body), &post, place)
            .unwrap()
            .unwrap();
        let Value::Float {
            raw_bits: Some(raw),
            ..
        } = observed
        else {
            panic!("exact Float");
        };
        let equal = engine
            .terms
            .apply(
                Op::Equal,
                &[raw, engine.terms.bit_vector(0x7fc0_1234, 32).unwrap()],
            )
            .unwrap();
        let mut bad = returned.conditions.clone();
        bad.push(symbolic::not(&equal));
        assert!(!engine.feasible(&bad).unwrap());
    }
    // These returned-memory facts came from the actual child execution, not a manual update.
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|b| b.function == "write_float")
    );
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|b| b.function == "stored_float")
    );
    let mut active = state(
        &engine,
        &selected_body,
        invoked.memory.clone(),
        invoked.conditions.clone(),
        child.clone(),
    );
    // Authenticate the actual intercepted core call, not just its name or MIR text.
    let (_, storage_body) = body(&engine, "stored_float");
    let (bits_block, bits_instance, bits_args, bits_destination, bits_target) = storage_body
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
            let ty::FnDef(definition, arguments) = func.ty(&storage_body.local_decls, tcx).kind()
            else {
                return None;
            };
            Some((
                block,
                engine
                    .resolve_function_item(*definition, arguments.skip_binder())
                    .unwrap(),
                args.as_ref(),
                *destination,
                *target,
            ))
        })
        .unwrap();
    let signature = engine.call_signature(bits_instance).unwrap();
    assert_eq!(tcx.def_kind(bits_instance.def_id()), DefKind::AssocFn);
    assert!(matches!(bits_instance.def, ty::InstanceKind::Item(_)));
    assert_eq!(signature.safety(), rustc_hir::Safety::Safe);
    assert_eq!(signature.abi(), rustc_abi::ExternAbi::Rust);
    assert_eq!(signature.inputs(), &[tcx.types.u32]);
    assert_eq!(signature.output(), tcx.types.f32);
    assert_eq!(
        engine.float_bits_operation(bits_instance.def_id(), bits_instance.args, signature),
        Some(super::super::builtins::FloatBitsOperation::Construct(32))
    );
    let (impostor, _) = body(&engine, "from_bits");
    assert!(
        engine
            .float_bits_operation(impostor.def_id(), impostor.args, signature)
            .is_none()
    );
    let mut wrong_signature = signature;
    wrong_signature.inputs_and_output = tcx.mk_type_list(&[tcx.types.u64, tcx.types.f32]);
    assert!(
        engine
            .float_bits_operation(bits_instance.def_id(), bits_instance.args, wrong_signature)
            .is_none()
    );
    let bits_call = mutable_u16_children::ChildCall {
        body: &storage_body,
        block: bits_block,
        instance: bits_instance,
        args: bits_args,
        destination: bits_destination,
        target: bits_target,
        stack: &[],
        site: (bits_instance.def_id(), Span::default()),
    };
    let mut bits_state = active.clone();
    let storage_frame = engine.mutable_u16_register_frame(&storage_body).unwrap();
    let Phase::Active { frames } = &mut Rc::make_mut(&mut bits_state.memory.mutable_u16)[0].phase
    else {
        panic!("active Product");
    };
    frames.push(storage_frame);
    assert!(
        engine
            .mutable_product_float_bits_route(&bits_state, &bits_call, 0, 1)
            .unwrap()
    );
    assert!(
        engine
            .mutable_product_float_bits_route(&active, &bits_call, 0, 1)
            .is_err()
    );
    assert!(
        engine
            .mutable_product_float_bits_route(&bits_state, &bits_call, 0, 0)
            .is_err()
    );
    let (scalar_seed, scalar_seed_body) = body(&engine, "scalar_seed");
    let mut armed_bits = bits_state.clone();
    armed_bits.flow = engine
        .activation_test_root(scalar_seed, &scalar_seed_body)
        .unwrap();
    assert!(
        engine
            .mutable_product_float_bits_route(&armed_bits, &bits_call, 0, 1)
            .unwrap_err()
            .contains("armed activation adapter")
    );
    eprintln!(
        "whole Product float route: actual core Instance/signature; impostor/width/frame/Armed"
    );
    engine
        .mutable_product_frame(
            &selected_body,
            0,
            &MutableU16Role::Child { generation: 1 },
            &active.memory,
        )
        .unwrap();
    assert!(
        engine
            .mutable_product_frame(
                &caller_body,
                0,
                &MutableU16Role::Child { generation: 1 },
                &active.memory
            )
            .unwrap_err()
            .contains("ancestor frame identity")
    );
    assert!(
        engine
            .mutable_product_length(&root, &active.memory, &active.conditions)
            .is_err()
    );
    assert!(
        engine
            .mutable_product_length(
                &Value::MutableU16 {
                    id: 0,
                    role: MutableU16Role::Child { generation: 0 },
                },
                &active.memory,
                &active.conditions
            )
            .is_err()
    );
    let operand = Operand::Copy(Place::from(Local::from_usize(1)));
    engine
        .mutable_u16_direct_metadata(&selected_body, &active, &operand)
        .unwrap()
        .unwrap();
    assert!(
        engine
            .mutable_u16_direct_metadata(&caller_body, &active, &operand)
            .unwrap_err()
            .contains("ancestor frame identity")
    );
    let metadata_call = selected_body.basic_blocks.iter().find_map(|block| {
        let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else {
            return None;
        };
        if let ty::FnDef(id, arguments) = func.ty(&selected_body.local_decls, tcx).kind()
            && Some(*id) == tcx.lang_items().get(LangItem::SliceLen)
        {
            assert!(arguments.bound_vars().is_empty());
            Some((
                engine
                    .resolve_function_item(*id, arguments.skip_binder())
                    .unwrap(),
                args.as_ref(),
            ))
        } else {
            None
        }
    });
    let wanted =
        metadata_call
            .as_ref()
            .and_then(|(_, args)| match args.first().map(|arg| &arg.node) {
                Some(Operand::Copy(place) | Operand::Move(place)) => Some(place.local),
                Some(Operand::Constant(_) | Operand::RuntimeChecks(_)) | None => None,
            });
    let (metadata_destination, original_rvalue, borrowed) = selected_body
        .basic_blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(assignment) = &statement.kind else {
                return None;
            };
            let place = match &assignment.1 {
                Rvalue::Ref(_, BorrowKind::Shared, place)
                | Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::FakeForPtrMetadata, place)
                    if place.local.as_usize() == 1
                        && place.projection.as_ref() == [ProjectionElem::Deref]
                        && wanted.is_none_or(|local| local == assignment.0.local) =>
                {
                    *place
                }
                _ => return None,
            };
            Some((assignment.0, assignment.1.clone(), place))
        })
        .unwrap();
    let metadata = engine
        .rvalue(
            selected.def_id(),
            &selected_body,
            &mut active,
            &original_rvalue,
        )
        .unwrap();
    assert!(matches!(
        metadata,
        Value::MutableU16 {
            role: MutableU16Role::ChildMetadata { generation: 1 },
            ..
        }
    ));
    assert!(
        engine
            .mutable_product_metadata(&caller_body, &active, borrowed)
            .unwrap_err()
            .contains("ancestor frame identity")
    );
    assert!(
        engine
            .mutable_product_store_role(&selected_body, &active, metadata_destination, &metadata)
            .unwrap()
    );
    active.locals[metadata_destination.local.as_usize()] = Some(metadata.clone());
    if let Some((metadata_instance, metadata_args)) = metadata_call {
        engine
            .mutable_u16_call_allowed(&selected_body, &active, metadata_instance, metadata_args)
            .unwrap();
        assert!(
            engine
                .mutable_u16_call_allowed(&caller_body, &active, metadata_instance, metadata_args)
                .unwrap_err()
                .contains("ancestor frame identity")
        );
        eprintln!("whole Product metadata: actual SliceLen Call preflight reached");
    } else {
        let metadata_rvalue = selected_body
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| {
                let StatementKind::Assign(assignment) = &statement.kind else {
                    return None;
                };
                if matches!(&assignment.1, Rvalue::UnaryOp(UnOp::PtrMetadata,
                    Operand::Copy(place) | Operand::Move(place))
                    if place.local == metadata_destination.local)
                {
                    Some(assignment.1.clone())
                } else {
                    None
                }
            })
            .unwrap();
        let mut positive = active.clone();
        let observed = engine
            .rvalue(
                selected.def_id(),
                &selected_body,
                &mut positive,
                &metadata_rvalue,
            )
            .unwrap();
        assert_eq!(
            symbolic::constant(&observed.integer().unwrap().0),
            Some(symbolic::Constant::BitVec { value: 2, bits })
        );
        let mut hostile = active.clone();
        assert!(
            engine
                .rvalue(
                    caller.def_id(),
                    &caller_body,
                    &mut hostile,
                    &metadata_rvalue
                )
                .unwrap_err()
                .contains("ancestor frame identity")
        );
        eprintln!("whole Product metadata: actual PtrMetadata observation reached");
    }
    // Internal length and live-metadata snapshots are observations, not current-caller permits.
    engine.mutable_owner_length(&metadata, &active).unwrap();
    engine
        .snapshot(&metadata, &active.memory, &active.conditions, 0)
        .unwrap();
    assert!(
        engine
            .snapshot(&child, &active.memory, &active.conditions, 0)
            .is_err()
    );
    let wrong = engine.mutable_u16_register_frame(&caller_body).unwrap();
    let mut non_top = active.clone();
    Rc::make_mut(&mut non_top.memory.mutable_u16)[0].phase = Phase::Active {
        frames: vec![wrong],
    };
    assert!(
        engine
            .mutable_product_frame(
                &selected_body,
                0,
                &MutableU16Role::Child { generation: 1 },
                &non_top.memory
            )
            .is_err()
    );
    engine
        .bodies
        .borrow_mut()
        .insert(selected, Rc::new((*selected_body).clone()));
    assert!(
        engine
            .mutable_owner_length(&metadata, &active)
            .unwrap_err()
            .contains("replaced")
    );
    engine
        .bodies
        .borrow_mut()
        .insert(selected, selected_body.clone());
    let mut dead = active.clone();
    dead.memory[0] = None;
    assert!(
        engine
            .mutable_product_frame(
                &selected_body,
                0,
                &MutableU16Role::Child { generation: 1 },
                &dead.memory
            )
            .is_err()
    );
    let mut corrupt = active.clone();
    let Storage::Product(columns) = &mut Rc::make_mut(&mut corrupt.memory.mutable_u16)[0].data
    else {
        panic!("Product");
    };
    columns.pop();
    assert!(engine.mutable_product_backing(0, &corrupt.memory).is_err());
    assert!(engine.mutable_product_backing(0, &active.memory).is_ok());
    let mut foreign = active.clone();
    let Storage::Product(columns) = &mut Rc::make_mut(&mut foreign.memory.mutable_u16)[0].data
    else {
        panic!("Product");
    };
    let context = Context::default();
    columns[0] = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
        )
        .unwrap();
    assert!(engine.mutable_product_backing(0, &foreign.memory).is_err());
    let mut extent = active.clone();
    Rc::make_mut(&mut extent.memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, u128::MAX >> (128 - bits), bits, false);
    assert!(engine.mutable_owner_length(&metadata, &extent).is_err());
    let mut outstanding = active.clone();
    Rc::make_mut(&mut outstanding.memory.mutable_u16)[0].phase = Phase::Active {
        frames: vec![wrong, wrong],
    };
    assert!(
        engine
            .mutable_u16_exit(
                &selected_body,
                std::slice::from_ref(&child),
                &outstanding.memory
            )
            .is_err()
    );
    // Genuine weak-frame expiry uses an independently issued Engine/current-context owner.
    let mut expired_engine = make_engine(tcx);
    let (_, expiring) = body(&expired_engine, "write_float");
    let frame = expired_engine
        .mutable_u16_register_frame(&expiring)
        .unwrap();
    let mut expired_memory = Memory::default();
    let mut expired_conditions = Vec::new();
    expired_engine
        .mutable_product_input(original, &mut expired_memory, &mut expired_conditions)
        .unwrap();
    expired_engine.bodies.borrow_mut().remove(&selected);
    drop(expiring);
    let backing = &mut Rc::make_mut(&mut expired_memory.mutable_u16)[0];
    backing.generation = 1;
    backing.phase = Phase::Active {
        frames: vec![frame],
    };
    assert!(
        expired_engine
            .mutable_product_frame(
                &selected_body,
                0,
                &MutableU16Role::Child { generation: 1 },
                &expired_memory
            )
            .unwrap_err()
            .contains("expired")
    );
    let (scalar, scalar_body) = body(&engine, "scalar_seed");
    let mut armed = active.clone();
    armed.flow = engine.activation_test_root(scalar, &scalar_body).unwrap();
    assert!(
        engine
            .mutable_u16_direct_metadata(&selected_body, &armed, &operand)
            .unwrap_err()
            .contains("armed activation adapter")
    );
    wrong_body.local_decls[Local::from_usize(1)].ty = tcx.types.u32;
    assert!(
        engine
            .mutable_u16_staging_tip(&wrong_body, &pending, destination.local.as_usize(), 0, 1)
            .is_err()
    );
    assert_eq!(memory.mutable_u16[0].phase, Phase::Idle);
    assert_eq!(memory.mutable_u16[0].generation, 0);
    assert!(engine.proof.assumptions.is_empty() && engine.proof.entry_assumptions.is_empty());
    eprintln!("whole Product: actual staging/call/Return, current frame/Memory, hostile controls");
}
#[test]
fn actual_whole_product_staging_frames_and_current_memory() {
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
        .join("../../tests/fixtures/mutable_product_children.rs");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let out = std::env::temp_dir().join(format!(
        "miren-product-child-probe-{}-{nonce}",
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
    std::fs::remove_dir_all(out).unwrap();
}
