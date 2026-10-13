//! Real compiler-owned issuance/reborrow/release and hostile lease controls.
use super::*;

#[test]
fn actual_retained_local_lease_revokes_aliases_and_preserves_typed_backing() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let options = || VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            };
            let config = miren::ContractConfig::default();
            let mut engine = Engine::new(tcx, &config, options());
            let id = tcx
                .mir_keys(())
                .iter()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "wrong_extent"
                })
                .unwrap()
                .to_def_id();
            let instance = ty::Instance::mono(tcx, id);
            let body = engine.instantiated_body(instance).unwrap();
            let (block, args, destination, target, selected) = body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(bb, data)| {
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
                    if pure_comparison_templates::definition_key(selected.def_id())
                        != "DefId(core::slice::index::{impl#1}::index_mut)"
                    {
                        return None;
                    }
                    Some((bb, args.as_ref(), *destination, *target, selected))
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
            let bits = u32::from(tcx.sess.target.pointer_width);
            Rc::make_mut(&mut memory.mutable_u16)[0].length =
                symbolic::integer(&engine.terms, 2, bits, false);
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                missing_places: Default::default(),
                conditions,
                memory,
            };
            state.locals[1] = Some(root.clone());
            for statement in &body.basic_blocks[block].statements {
                engine
                    .statement(instance, &body, &mut state, &statement.kind)
                    .unwrap();
            }
            // Issuance must reject prior whole/metadata carriers before any child observation.
            let receiver = match args[0].node {
                Operand::Move(p) => p.local.as_usize(),
                _ => unreachable!(),
            };
            for role in [
                MutableU16Role::Child { generation: 1 },
                MutableU16Role::ChildMetadata { generation: 1 },
            ] {
                let mut alias = state.clone();
                alias.locals[0] = Some(Value::MutableU16 { id: 0, role });
                assert!(
                    engine
                        .retained_exclusive_receiver(&alias, receiver)
                        .is_err()
                );
            }
            let child = state.locals[receiver].clone().unwrap();
            let mut partial = state.clone();
            partial.locals[0] = Some(Value::Tuple(vec![child.clone(), Value::Unit]));
            partial
                .missing_places
                .consume(0, vec![initialized_places::Step::Field(1)])
                .unwrap();
            assert!(
                engine
                    .retained_exclusive_receiver(&partial, receiver)
                    .is_err()
            );
            let mut addressed = state.clone();
            let allocation = addressed.memory.len();
            addressed.memory.push(Some(child.clone()));
            addressed.addresses[0] = Some(allocation);
            assert!(
                engine
                    .retained_exclusive_receiver(&addressed, receiver)
                    .is_err()
            );
            addressed.addresses[0] = None;
            assert!(
                engine
                    .retained_exclusive_receiver(&addressed, receiver)
                    .is_err()
            );
            let mut copied = args.to_vec();
            copied[0].node = Operand::Copy(Place::from(Local::from_usize(receiver)));
            assert!(
                engine
                    .mutable_retained_call(
                        &state,
                        ChildCall {
                            body: &body,
                            block,
                            instance: selected,
                            args: &copied,
                            destination,
                            target,
                            stack: &[],
                            site: (id, body.span),
                        }
                    )
                    .is_err()
            );
            let before = state.memory.storage_slots();
            let call = || ChildCall {
                body: &body,
                block,
                instance: selected,
                args,
                destination,
                target,
                stack: &[],
                site: (id, body.span),
            };
            let (_, mut active) = engine
                .mutable_retained_call(&state, call())
                .unwrap()
                .unwrap();
            assert_eq!(active.memory.storage_slots(), before + 8);
            assert!(
                engine
                    .mutable_u16_role_live(0, &MutableU16Role::Root, &active.memory)
                    .is_err()
            );
            let target = target.unwrap();
            for statement in &body.basic_blocks[target].statements {
                let StatementKind::Assign(pair) = &statement.kind else {
                    continue;
                };
                if let Rvalue::Ref(_, BorrowKind::Mut { .. }, _) = &pair.1 {
                    assert!(
                        engine
                            .mutable_retained_stage(
                                &body,
                                &mut active,
                                pair.0,
                                &pair.1,
                                &statement.kind
                            )
                            .unwrap()
                    );
                    break;
                }
            }
            let Phase::Retained { carrier, .. } = active.memory.mutable_u16[0].phase else {
                unreachable!()
            };
            let carrier = Local::from_usize(carrier);
            let leaf = Place {
                local: carrier,
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
            engine
                .mutable_product_read(Some(&body), &active, leaf)
                .unwrap()
                .unwrap();
            let mut alias = active.clone();
            alias.locals[0] = alias.locals[carrier.as_usize()].clone();
            let earlier = Place {
                local: Local::from_usize(0),
                projection: leaf.projection,
            };
            assert!(
                engine
                    .mutable_product_read(Some(&body), &alias, earlier)
                    .is_err()
            );
            alias.locals[0] = Some(Value::MutableU16 {
                id: 0,
                role: MutableU16Role::ChildMetadata { generation: 1 },
            });
            assert!(
                engine
                    .mutable_retained_operand(
                        &body,
                        &alias,
                        0,
                        0,
                        &MutableU16Role::ChildMetadata { generation: 1 }
                    )
                    .is_err()
            );
            let mut addressed = active.clone();
            let allocation = addressed.memory.len();
            addressed
                .memory
                .push(addressed.locals[carrier.as_usize()].clone());
            addressed.addresses[carrier.as_usize()] = Some(allocation);
            assert!(
                engine
                    .mutable_product_read(Some(&body), &addressed, leaf)
                    .is_err()
            );

            let shared = body.basic_blocks[target]
                .statements
                .iter()
                .find(|s| {
                    matches!(&s.kind, StatementKind::Assign(pair)
                    if matches!(&pair.1, Rvalue::Ref(_, BorrowKind::Shared, source)
                        if source.local == carrier
                            && source.projection.as_ref() == [ProjectionElem::Deref]))
                })
                .unwrap();
            let StatementKind::Assign(pair) = &shared.kind else {
                unreachable!()
            };
            let mut readonly = active.clone();
            assert!(
                engine
                    .mutable_retained_shared_stage(
                        &body,
                        &mut readonly,
                        pair.0,
                        &pair.1,
                        &shared.kind
                    )
                    .unwrap()
            );
            engine
                .mutable_product_read(Some(&body), &readonly, pair.0)
                .unwrap()
                .unwrap();
            let mut dead_metadata = readonly.clone();
            dead_metadata
                .missing_places
                .consume(pair.0.local.as_usize(), Vec::new())
                .unwrap();
            assert!(
                engine
                    .mutable_product_read(Some(&body), &dead_metadata, pair.0)
                    .is_err()
            );
            let mut forged_metadata = readonly.clone();
            let Phase::Retained { metadata, .. } =
                &mut Rc::make_mut(&mut forged_metadata.memory.mutable_u16)[0].phase
            else {
                unreachable!()
            };
            metadata[0].1 ^= 1;
            assert!(
                engine
                    .mutable_product_backing(0, &forged_metadata.memory)
                    .is_err()
            );
            let metadata = readonly.locals[pair.0.local.as_usize()].as_ref().unwrap();
            assert!(
                engine
                    .mutable_product_store_role(&body, &readonly, pair.0, metadata)
                    .is_err()
            );
            let forged = StatementKind::Assign(pair.clone());
            assert!(
                engine
                    .mutable_retained_shared_stage(
                        &body,
                        &mut active.clone(),
                        pair.0,
                        &pair.1,
                        &forged
                    )
                    .is_err()
            );
            assert!(
                engine
                    .mutable_u16_role_live(
                        0,
                        &MutableU16Role::Child { generation: 2 },
                        &active.memory
                    )
                    .is_err()
            );
            let mut wrong = active.clone();
            let Phase::Retained { offset, .. } =
                &mut Rc::make_mut(&mut wrong.memory.mutable_u16)[0].phase
            else {
                unreachable!()
            };
            *offset = engine.iterator_index(1).integer().unwrap().0;
            assert!(engine.mutable_product_backing(0, &wrong.memory).is_err());
            let mut consumed = active.clone();
            consumed
                .memory
                .missing_places
                .consume(0, Vec::new())
                .unwrap();
            assert!(engine.mutable_product_backing(0, &consumed.memory).is_err());
            let mut missing = active.clone();
            missing
                .missing_places
                .consume(carrier.as_usize(), Vec::new())
                .unwrap();
            assert!(
                engine
                    .mutable_product_read(Some(&body), &missing, leaf)
                    .is_err()
            );
            let mut incomplete = active.clone();
            incomplete.locals[0] = Some(Value::Tuple(vec![
                incomplete.locals[carrier.as_usize()].clone().unwrap(),
                Value::Unit,
            ]));
            incomplete
                .missing_places
                .consume(0, vec![initialized_places::Step::Field(1)])
                .unwrap();
            let endpoint = body
                .basic_blocks
                .iter()
                .flat_map(|b| &b.statements)
                .find(|s| matches!(s.kind,StatementKind::StorageDead(local) if local == carrier))
                .unwrap();
            assert!(
                engine
                    .mutable_retained_release(&body, &mut incomplete, carrier, &endpoint.kind)
                    .is_err()
            );
            let invalid_suffix = Place {
                local: carrier,
                projection: tcx.mk_place_elems(&[
                    ProjectionElem::Deref,
                    ProjectionElem::ConstantIndex {
                        offset: 0,
                        min_length: 1,
                        from_end: false,
                    },
                    ProjectionElem::Field(rustc_abi::FieldIdx::from_usize(0), tcx.types.bool),
                ]),
            };
            assert!(
                engine
                    .mutable_product_read(Some(&body), &active, invalid_suffix)
                    .is_err()
            );
            let pointer = Rvalue::RawPtr(
                rustc_middle::mir::RawPtrKind::Mut,
                Place {
                    local: carrier,
                    projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                },
            );
            assert!(
                engine
                    .rvalue(id, &body, &mut active.clone(), &pointer)
                    .is_err()
            );
            assert!(
                engine
                    .mutable_u16_snapshot(
                        active.locals[carrier.as_usize()].as_ref().unwrap(),
                        &active.memory
                    )
                    .is_err()
            );
            let mut changed = body.as_ref().clone();
            changed.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
            engine
                .bodies
                .borrow_mut()
                .insert(instance, Rc::new(changed));
            assert!(engine.mutable_product_backing(0, &active.memory).is_err());
            engine.bodies.borrow_mut().insert(instance, body.clone());
            let mut foreign = Engine::new(tcx, &config, options());
            foreign.mutable_integer_types = engine.mutable_integer_types.clone();
            *foreign.mutable_retained.borrow_mut() = engine.mutable_retained.borrow().clone();
            foreign.bodies.borrow_mut().insert(instance, body.clone());
            assert!(foreign.mutable_product_backing(0, &active.memory).is_err());
            let endpoint = body
                .basic_blocks
                .iter()
                .flat_map(|b| &b.statements)
                .find(|s| matches!(s.kind,StatementKind::StorageDead(local) if local==carrier))
                .unwrap();
            let forged = StatementKind::StorageDead(carrier);
            assert!(
                engine
                    .mutable_retained_release(&body, &mut active.clone(), carrier, &forged)
                    .is_err()
            );
            let mut duplicate = active.clone();
            duplicate.locals[0] = duplicate.locals[carrier.as_usize()].clone();
            assert!(
                engine
                    .mutable_retained_release(&body, &mut duplicate, carrier, &endpoint.kind)
                    .is_err()
            );
            let mut duplicate = active.clone();
            let allocation = duplicate.memory.len();
            duplicate
                .memory
                .push(duplicate.locals[carrier.as_usize()].clone());
            duplicate.addresses[0] = Some(allocation);
            assert!(
                engine
                    .mutable_retained_release(&body, &mut duplicate, carrier, &endpoint.kind)
                    .is_err()
            );
            let mut armed = active.clone();
            let seed = tcx
                .mir_keys(())
                .iter()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "identity"
                })
                .unwrap()
                .to_def_id();
            let seed = ty::Instance::mono(tcx, seed);
            let seed_body = engine.instantiated_body(seed).unwrap();
            armed.flow = engine.activation_test_root(seed, &seed_body).unwrap();
            assert!(
                engine
                    .mutable_retained_release(&body, &mut armed, carrier, &endpoint.kind)
                    .is_err()
            );
            assert!(active.memory.activation_storage_slots(&armed.flow).is_err());
            let mut wrong = active.clone();
            wrong.conditions.clear();
            // The fixed root extent and literal interval remain valid with no path premises.
            assert!(
                engine
                    .mutable_retained_extent(0, &wrong.memory.mutable_u16[0], &wrong.conditions)
                    .unwrap()
                    .is_some()
            );
            // Keep the real eligible prefix, then make its complete body oversized.
            let mut oversized = body.as_ref().clone();
            let mut nop = endpoint.clone();
            nop.kind = StatementKind::Nop;
            oversized.basic_blocks.as_mut()[target]
                .statements
                .extend(vec![nop; MAX_INPUT_VALUES]);
            let oversized = Rc::new(oversized);
            engine
                .bodies
                .borrow_mut()
                .insert(instance, oversized.clone());
            let TerminatorKind::Call {
                args: big_args,
                destination: big_dst,
                target: big_target,
                ..
            } = &oversized.basic_blocks[block].terminator().kind
            else {
                unreachable!()
            };
            let big_call = ChildCall {
                body: &oversized,
                block,
                instance: selected,
                args: big_args,
                destination: *big_dst,
                target: *big_target,
                stack: &[],
                site: (id, body.span),
            };
            assert!(
                engine
                    .mutable_retained_call(&state, big_call)
                    .err()
                    .unwrap()
                    .contains("existing 512-node budget")
            );
            assert!(
                engine
                    .mutable_retained_release(
                        &oversized,
                        &mut active.clone(),
                        carrier,
                        &endpoint.kind
                    )
                    .unwrap_err()
                    .contains("existing 512-node budget")
            );
            engine.bodies.borrow_mut().insert(instance, body.clone());
            let registry = engine.bodies.borrow().clone();
            for count in 0..MAX_INPUT_VALUES {
                let key = ty::Instance::new_raw(
                    id,
                    tcx.mk_args(&[Ty::new_array(tcx, tcx.types.u16, count as u64).into()]),
                );
                engine.bodies.borrow_mut().insert(key, body.clone());
            }
            assert!(
                engine
                    .retained_body(&body, &mut Work(0))
                    .err()
                    .unwrap()
                    .contains("existing 512-node budget")
            );
            *engine.bodies.borrow_mut() = registry;
            let facts = engine.mutable_retained.borrow().clone();
            engine
                .mutable_retained
                .borrow_mut()
                .resize(MAX_INPUT_VALUES, facts[0].clone());
            assert!(
                engine
                    .mutable_retained_call(&state, call())
                    .err()
                    .unwrap()
                    .contains("storage/certificate budget")
            );
            *engine.mutable_retained.borrow_mut() = facts;
            println!(
                "retained oversized eligible Call/release prefix and registry/issuer limits refused"
            );
            let stale = active.locals[carrier.as_usize()].clone().unwrap();
            let data = active.memory.mutable_u16[0].data.clone();
            engine
                .mutable_retained_release(&body, &mut active, carrier, &endpoint.kind)
                .unwrap();
            assert_eq!(active.memory.mutable_u16[0].data, data);
            assert_eq!(active.memory.mutable_u16[0].phase, Phase::Idle);
            assert_eq!(active.memory.mutable_u16[0].generation, 2);
            assert!(
                engine
                    .mutable_u16_role_live(0, &MutableU16Role::Root, &active.memory)
                    .is_ok()
            );
            let Value::MutableU16 { role, .. } = stale else {
                unreachable!()
            };
            assert!(
                engine
                    .mutable_u16_role_live(0, &role, &active.memory)
                    .is_err()
            );
            assert!(
                engine
                    .mutable_u16_exit(&body, &[root], &active.memory)
                    .is_ok()
            );
            println!("retained caller/call/reborrow/dead, Context, masks, aliases and revocation");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory =
        std::env::temp_dir().join(format!("miren-retained-lease-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/retained_mutable_views.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "-Zmir-opt-level=0".into(),
                format!("-Copt-level={level}"),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
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
    std::fs::remove_dir_all(directory).unwrap();
}
