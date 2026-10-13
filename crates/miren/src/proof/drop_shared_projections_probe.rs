//! Actual compiler-owned path and hostile storage controls; assertions are prospective.
use super::*;
use std::path::Path;

#[test]
fn actual_drop_borrow_masks_source_identity_and_scalar_boundaries() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let config = miren::ContractConfig::default();
            let options = || VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            };
            let mut engine = Engine::new(tcx, &config, options());
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id())
                            == rustc_span::Symbol::intern("probe_borrow")
                })
                .unwrap()
                .to_def_id();
            let instance = ty::Instance::mono(tcx, id);
            let body = engine.instantiated_body(instance).unwrap();
            let place = body
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| {
                    let StatementKind::Assign(pair) = &statement.kind else {
                        return None;
                    };
                    let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place) = &pair.1
                    else {
                        return None;
                    };
                    matches!(place.projection.first(), Some(ProjectionElem::Index(_)))
                        .then_some(*place)
                })
                .unwrap();
            let ProjectionElem::Index(index) = place.projection[0] else {
                unreachable!()
            };
            let original = body.local_decls[place.local].ty;
            let ty::Array(child, count) = original.kind() else {
                unreachable!()
            };
            assert_eq!(count.try_to_target_usize(tcx), Some(2));
            let ty::Adt(def, args) = child.kind() else {
                unreachable!()
            };
            assert!(def.destructor(tcx).is_some());
            let word = def
                .non_enum_variant()
                .fields
                .iter_enumerated()
                .find(|(_, field)| field.name == rustc_span::Symbol::intern("word"))
                .unwrap()
                .0;
            assert_eq!(
                def.non_enum_variant().fields[word]
                    .ty(tcx, args)
                    .skip_norm_wip(),
                tcx.types.u16
            );
            let mut conditions = Vec::new();
            let selected = engine
                .argument(id, tcx.types.usize, &mut conditions)
                .unwrap();
            let bound = symbolic::binary(
                &engine.terms,
                "lt",
                selected.clone(),
                engine.iterator_index(2),
            )
            .unwrap()
            .boolean()
            .unwrap();
            conditions.push(bound);
            let values = [3, 7]
                .into_iter()
                .map(|number| Value::Adt {
                    name: tcx.def_path_str(def.did()),
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields: def
                        .non_enum_variant()
                        .fields
                        .iter()
                        .map(|field| {
                            assert_eq!(field.ty(tcx, args).skip_norm_wip(), tcx.types.u16);
                            (
                                field.name.to_string(),
                                symbolic::integer(
                                    &engine.terms,
                                    if field.name.as_str() == "word" {
                                        number
                                    } else {
                                        7
                                    },
                                    16,
                                    false,
                                ),
                            )
                        })
                        .collect::<Vec<_>>()
                        .into(),
                })
                .collect::<Vec<_>>();
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                conditions,
                memory: Memory::default(),
                missing_places: initialized_places::MissingPlaces::default(),
            };
            state.locals[place.local.as_usize()] = Some(Value::Elements(values.into()));
            state.locals[index.as_usize()] = Some(selected.clone());
            let before = state.clone();
            let view = engine
                .borrow_drop_shared_place(&body, &mut state, place)
                .unwrap()
                .unwrap();
            let Value::Reference {
                allocation,
                projection,
                ..
            } = &view
            else {
                unreachable!()
            };
            let allocation = *allocation;
            assert!(state.locals[place.local.as_usize()].is_none());
            assert!(
                engine
                    .reference_value(&view, &state.memory, &state.conditions)
                    .unwrap_err()
                    .contains("cannot materialize or copy a non-Copy owner")
            );
            let mut fields = projection.clone();
            fields.push(MemoryProjection::Field(word.as_usize()));
            let scalar_view = Value::Reference {
                allocation,
                projection: fields.clone(),
                mutable: false,
            };
            let reborrow_place = body
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| {
                    let StatementKind::Assign(pair) = &statement.kind else {
                        return None;
                    };
                    let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place) = &pair.1
                    else {
                        return None;
                    };
                    (matches!(place.projection.first(), Some(ProjectionElem::Deref))
                        && matches!(place.projection.last(), Some(ProjectionElem::Field(..))))
                    .then_some(*place)
                })
                .unwrap();
            let carrier = reborrow_place.local.as_usize();
            state.locals[carrier] = Some(view.clone());
            let reborrowed = engine
                .reborrow_drop_shared_view(&body, &state, reborrow_place)
                .unwrap()
                .unwrap();
            let Value::Reference {
                allocation: reborrowed_allocation,
                projection: reborrowed_path,
                mutable: false,
            } = &reborrowed
            else {
                unreachable!()
            };
            assert_eq!(*reborrowed_allocation, allocation);
            assert_eq!(reborrowed_path.len(), fields.len());
            engine
                .reference_value(&reborrowed, &state.memory, &state.conditions)
                .unwrap();
            let whole = Place {
                local: reborrow_place.local,
                projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
            };
            let whole_view = engine
                .reborrow_drop_shared_view(&body, &state, whole)
                .unwrap()
                .unwrap();
            assert!(matches!(
                whole_view,
                Value::Reference { mutable: false, .. }
            ));
            assert!(
                engine
                    .reference_value(&whole_view, &state.memory, &state.conditions)
                    .unwrap_err()
                    .contains("cannot materialize or copy a non-Copy owner")
            );
            let mut stale_carrier = state.clone();
            stale_carrier
                .missing_places
                .consume(carrier, Vec::new())
                .unwrap();
            assert!(
                engine
                    .reborrow_drop_shared_view(&body, &stale_carrier, reborrow_place)
                    .is_err()
            );
            let value = engine
                .reference_value(&scalar_view, &state.memory, &state.conditions)
                .unwrap();
            let equal = symbolic::binary(
                &engine.terms,
                "ne",
                value,
                symbolic::integer(&engine.terms, 0, 16, false),
            )
            .unwrap()
            .boolean()
            .unwrap();
            let mut counterexample = state.conditions.clone();
            counterexample.push(symbolic::not(&equal));
            assert!(!engine.feasible(&counterexample).unwrap());
            let mut incomplete = state.clone();
            incomplete
                .memory
                .missing_places
                .consume(allocation, vec![Step::Element(0)])
                .unwrap();
            assert!(
                engine
                    .reference_value(&scalar_view, &incomplete.memory, &incomplete.conditions)
                    .is_err()
            );
            let one = symbolic::binary(
                &engine.terms,
                "eq",
                selected.clone(),
                engine.iterator_index(1),
            )
            .unwrap()
            .boolean()
            .unwrap();
            incomplete.conditions.push(one);
            engine
                .reference_value(&scalar_view, &incomplete.memory, &incomplete.conditions)
                .unwrap();
            assert!(
                engine
                    .check_memory_initialization(&incomplete.memory, allocation, &fields)
                    .is_err()
            );
            assert!(
                engine
                    .check_drop_shared_reference(
                        allocation,
                        &fields,
                        &incomplete.memory,
                        &incomplete.conditions,
                    )
                    .unwrap()
            );
            assert!(state.memory.missing_places.is_empty());
            let mut retired = state.clone();
            retired.memory.retire_initialized_owner(allocation);
            retired.memory[allocation] = None;
            assert!(
                engine
                    .reference_value(&scalar_view, &retired.memory, &retired.conditions)
                    .is_err()
            );
            let mut foreign = Engine::new(tcx, &config, options());
            foreign.owned_projection_certificates = engine.owned_projection_certificates.clone();
            foreign.bodies.borrow_mut().insert(instance, body.clone());
            assert!(
                foreign
                    .reference_value(&scalar_view, &state.memory, &state.conditions)
                    .is_err()
            );
            let mut mutable = scalar_view.clone();
            let Value::Reference { mutable: flag, .. } = &mut mutable else {
                unreachable!()
            };
            *flag = true;
            assert!(
                engine
                    .reference_value(&mutable, &state.memory, &state.conditions)
                    .is_err()
            );
            assert!(engine.return_value(scalar_view.clone(), &state, 0).is_err());
            retired.memory[allocation] = state.memory[allocation].clone();
            assert!(
                engine
                    .reference_value(&scalar_view, &retired.memory, &retired.conditions)
                    .is_err()
            );
            let seed = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "activation_seed"
                })
                .unwrap()
                .to_def_id();
            let seed = ty::Instance::mono(tcx, seed);
            let seed_body = engine.instantiated_body(seed).unwrap();
            let mut armed = before.clone();
            armed.flow = engine.activation_test_root(seed, &seed_body).unwrap();
            assert!(
                engine
                    .borrow_drop_shared_place(&body, &mut armed, place)
                    .is_err()
            );
            let mut capacity = before.clone();
            while capacity.memory.storage_slots() < memory::MAX_ALLOCATIONS {
                capacity.memory.push(Some(Value::Unit));
            }
            assert!(
                engine
                    .borrow_drop_shared_place(&body, &mut capacity, place)
                    .is_err()
            );
            assert!(capacity.addresses[place.local.as_usize()].is_none());
            let mut wrong_index = before.clone();
            let other = Context::default();
            wrong_index.locals[index.as_usize()] = Some(symbolic::integer(
                &other,
                0,
                u32::from(tcx.sess.target.pointer_width),
                false,
            ));
            assert!(
                engine
                    .borrow_drop_shared_place(&body, &mut wrong_index, place)
                    .is_err()
            );
            assert!(wrong_index.addresses[place.local.as_usize()].is_none());
            let mut signed = before.clone();
            signed.locals[index.as_usize()] = Some(symbolic::integer(
                &engine.terms,
                0,
                u32::from(tcx.sess.target.pointer_width),
                true,
            ));
            assert!(
                engine
                    .borrow_drop_shared_place(&body, &mut signed, place)
                    .is_err()
            );
            let forged = Place {
                local: place.local,
                projection: tcx.mk_place_elems(&[
                    ProjectionElem::Index(index),
                    ProjectionElem::Field(word, tcx.types.bool),
                ]),
            };
            assert!(
                engine
                    .read_drop_shared_place(&body, &before, forged)
                    .is_err()
            );
            let MemoryProjection::TypedIndex { certificate, .. } = fields[0] else {
                unreachable!()
            };
            let saved = engine.owned_projection_certificates[certificate]
                .drop_shared
                .clone()
                .unwrap();
            let unavailable = ty::Instance::mono(tcx, def.did());
            assert!(!tcx.is_mir_available(unavailable.def_id()));
            engine.bodies.borrow_mut().insert(unavailable, body.clone());
            engine.owned_projection_certificates[certificate]
                .drop_shared
                .as_mut()
                .unwrap()
                .instance = unavailable;
            assert!(
                engine
                    .reference_value(&scalar_view, &state.memory, &state.conditions)
                    .unwrap_err()
                    .contains("MIR body unavailable")
            );
            engine.bodies.borrow_mut().remove(&unavailable);
            engine.owned_projection_certificates[certificate].drop_shared = Some(saved);
            let mut wrong_source = body.as_ref().clone();
            wrong_source.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
            engine
                .bodies
                .borrow_mut()
                .insert(instance, Rc::new(wrong_source));
            assert!(
                engine
                    .reference_value(&scalar_view, &state.memory, &state.conditions)
                    .is_err()
            );
            engine.bodies.borrow_mut().insert(instance, body.clone());
            engine
                .reference_value(&scalar_view, &state.memory, &state.conditions)
                .unwrap();
            assert!(
                engine
                    .write_projection(
                        &mut state.memory[allocation].clone().unwrap(),
                        &fields,
                        symbolic::integer(&engine.terms, 19, 16, false),
                        &state.conditions
                    )
                    .is_err()
            );
            println!(
                "Drop shared projection: actual path, complete receiver, masks and source controls"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory =
        std::env::temp_dir().join(format!("miren-drop-view-tcx-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/drop_shared_projections.rs");
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

#[test]
fn observe_actual_fieldless_drop_storage_and_bodies() {
    struct Observe(bool);
    impl rustc_driver::Callbacks for Observe {
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
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "drop_zero"
                })
                .unwrap()
                .to_def_id();
            let instance = ty::Instance::mono(tcx, id);
            let body = engine.instantiated_body(instance).unwrap();
            let original = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            let ty::Array(child, count) = original.kind() else {
                panic!("actual original array");
            };
            let ty::Adt(def, _) = child.kind() else {
                panic!("actual original struct");
            };
            let layout = tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(*child))
                .unwrap();
            let mut conditions = Vec::new();
            let value = engine.argument(id, original, &mut conditions).unwrap();
            println!("original={original:?}; child={child:?}; count={count:?}");
            println!(
                "fields={}; size={}; alignment={}; Freeze={}; needsDrop={}",
                def.non_enum_variant().fields.len(),
                layout.size.bytes(),
                layout.align.abi.bytes(),
                child.is_freeze(tcx, ty::TypingEnv::fully_monomorphized()),
                child.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
            );
            println!("actual argument={value:?}; conditions={conditions:?}");
            let Value::Elements(elements) = &value else {
                panic!("actual original array storage");
            };
            for (index, element) in elements.iter().enumerate() {
                println!(
                    "element{index} raw={element:?}; decoded={:?}",
                    element.materialize()
                );
            }
            let slice = Ty::new_slice(tcx, *child);
            let destructor = ty::Instance::mono(tcx, def.destructor(tcx).unwrap().did);
            for actual in [
                instance,
                ty::Instance::resolve_drop_glue(tcx, original),
                ty::Instance::resolve_drop_glue(tcx, slice),
                ty::Instance::resolve_drop_glue(tcx, *child),
                destructor,
            ] {
                println!("Instance={actual:?}");
                println!("raw Body={:#?}", tcx.instance_mir(actual.def));
                println!(
                    "current Body={:#?}",
                    engine.instantiated_body(actual).unwrap()
                );
            }
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!("miren-unit-drop-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/deferred_zero_products.rs");
    let args = vec![
        "rustc".into(),
        source.to_str().unwrap().into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "-Cpanic=abort".into(),
        "-Zmir-opt-level=0".into(),
        "-Copt-level=0".into(),
        "--out-dir".into(),
        directory.to_str().unwrap().into(),
        "--sysroot".into(),
        env!("MIREN_SYSROOT").into(),
    ];
    let mut check = Observe(false);
    rustc_driver::run_compiler(&args, &mut check);
    assert!(check.0);
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn actual_fieldless_lazy_views_check_types_descriptors_context_and_masks() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let config = miren::ContractConfig::default();
            let options = || VerificationOptions {
                all_failures: false,
                induction: false,
                startup: false,
                isolated_startup: false,
                async_entry: false,
                limits: miren::AnalysisLimits::default(),
            };
            let mut engine = Engine::new(tcx, &config, options());
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "incoming"
                })
                .unwrap()
                .to_def_id();
            let instance = ty::Instance::mono(tcx, id);
            let body = engine.instantiated_body(instance).unwrap();
            let place = body
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| {
                    let StatementKind::Assign(pair) = &statement.kind else {
                        return None;
                    };
                    let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place) = &pair.1
                    else {
                        return None;
                    };
                    matches!(place.projection.first(), Some(ProjectionElem::Index(_)))
                        .then_some(*place)
                })
                .unwrap();
            let ProjectionElem::Index(index) = place.projection[0] else {
                unreachable!()
            };
            let original = body.local_decls[place.local].ty;
            let ty::Array(child, count) = original.kind() else {
                unreachable!()
            };
            assert_eq!(count.try_to_target_usize(tcx), Some(2));
            let ty::Adt(def, _) = child.kind() else {
                unreachable!()
            };
            assert!(def.non_enum_variant().fields.is_empty());
            let mut conditions = Vec::new();
            let value = engine.argument(id, original, &mut conditions).unwrap();
            let selected = engine
                .argument(id, tcx.types.usize, &mut conditions)
                .unwrap();
            conditions.push(
                symbolic::binary(
                    &engine.terms,
                    "lt",
                    selected.clone(),
                    engine.iterator_index(2),
                )
                .unwrap()
                .boolean()
                .unwrap(),
            );
            let Value::Elements(elements) = &value else {
                unreachable!()
            };
            let Value::Input(input) = &elements[0] else {
                unreachable!()
            };
            engine
                .validate_drop_storage(*child, &elements[0], &conditions, &mut Work(0))
                .unwrap();
            assert!(
                engine
                    .validate_drop_storage(*child, &Value::Unit, &conditions, &mut Work(0))
                    .is_err()
            );
            assert!(
                engine
                    .validate_drop_storage(tcx.types.u16, &elements[0], &conditions, &mut Work(0))
                    .is_err()
            );
            let mut foreign = Engine::new(tcx, &config, options());
            let foreign_value = foreign.argument(id, original, &mut Vec::new()).unwrap();
            let Value::Elements(foreign_elements) = &foreign_value else {
                unreachable!()
            };
            assert!(
                engine
                    .validate_drop_storage(*child, &foreign_elements[0], &conditions, &mut Work(0))
                    .is_err()
            );
            let mut wrong_context = input.clone();
            wrong_context.seed = foreign.terms.boolean(false);
            assert!(
                engine
                    .validate_drop_storage(
                        *child,
                        &Value::Input(wrong_context),
                        &conditions,
                        &mut Work(0)
                    )
                    .is_err()
            );
            let actual = engine.zero_sized_inputs.get(child).unwrap().clone();
            let mut malformed = actual.as_ref().clone();
            malformed.slots = 1;
            let malformed = Rc::new(malformed);
            engine.zero_sized_inputs.insert(*child, malformed.clone());
            let mut forged = input.clone();
            forged.shape = malformed;
            assert!(
                engine
                    .validate_drop_storage(*child, &Value::Input(forged), &conditions, &mut Work(0))
                    .is_err()
            );
            engine.zero_sized_inputs.insert(*child, actual);
            let probe_id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "probe_borrow"
                })
                .unwrap()
                .to_def_id();
            let probe_body = engine
                .instantiated_body(ty::Instance::mono(tcx, probe_id))
                .unwrap();
            let nonzero = probe_body
                .local_decls
                .iter()
                .find_map(|decl| {
                    if let ty::Array(element, _) = decl.ty.kind() {
                        Some(*element)
                    } else {
                        None
                    }
                })
                .unwrap();
            assert!(
                tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(nonzero))
                    .unwrap()
                    .size
                    .bytes()
                    > 0
            );
            assert!(
                engine
                    .validate_drop_storage(nonzero, &elements[0], &conditions, &mut Work(0))
                    .is_err()
            );
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                conditions,
                memory: Memory::default(),
                missing_places: initialized_places::MissingPlaces::default(),
            };
            state.locals[place.local.as_usize()] = Some(value);
            state.locals[index.as_usize()] = Some(selected.clone());
            let view = engine
                .borrow_drop_shared_place(&body, &mut state, place)
                .unwrap()
                .unwrap();
            let Value::Reference {
                allocation,
                projection,
                ..
            } = view
            else {
                unreachable!()
            };
            assert!(
                engine
                    .check_drop_shared_reference(
                        allocation,
                        &projection,
                        &state.memory,
                        &state.conditions
                    )
                    .unwrap()
            );
            foreign.owned_projection_certificates = engine.owned_projection_certificates.clone();
            foreign.bodies.borrow_mut().insert(instance, body.clone());
            foreign.zero_sized_inputs = engine.zero_sized_inputs.clone();
            assert!(
                foreign
                    .check_drop_shared_reference(
                        allocation,
                        &projection,
                        &state.memory,
                        &state.conditions
                    )
                    .is_err()
            );
            let mut incomplete = state.clone();
            incomplete
                .memory
                .missing_places
                .consume(allocation, vec![Step::Element(0)])
                .unwrap();
            assert!(
                engine
                    .check_drop_shared_reference(
                        allocation,
                        &projection,
                        &incomplete.memory,
                        &incomplete.conditions
                    )
                    .is_err()
            );
            incomplete.conditions.push(
                symbolic::binary(&engine.terms, "eq", selected, engine.iterator_index(1))
                    .unwrap()
                    .boolean()
                    .unwrap(),
            );
            assert!(
                engine
                    .check_drop_shared_reference(
                        allocation,
                        &projection,
                        &incomplete.memory,
                        &incomplete.conditions
                    )
                    .unwrap()
            );
            state.memory.retire_initialized_owner(allocation);
            assert!(
                engine
                    .check_drop_shared_reference(
                        allocation,
                        &projection,
                        &state.memory,
                        &state.conditions
                    )
                    .is_err()
            );
            println!("fieldless lazy Drop: actual cache, original type, Context and masks checked");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!("miren-lazy-drop-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/drop_shared_projections.rs");
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

#[test]
fn actual_issued_lazy_drop_descriptors_preserve_namespace_and_initialized_paths() {
    struct Check(bool);
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
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "reserved"
                })
                .unwrap()
                .to_def_id();
            let body = engine
                .instantiated_body(ty::Instance::mono(tcx, id))
                .unwrap();
            let input_cost = body.args_iter().fold(0_usize, |cost, local| {
                cost.saturating_add(engine.root_input_cost(body.local_decls[local].ty))
            });
            assert!(input_cost > MAX_INPUT_VALUES);
            engine.prefer_lazy_inputs = input_cost > MAX_INPUT_VALUES;
            let mut conditions = Vec::new();
            let mut args = Vec::new();
            for local in body.args_iter() {
                args.push(
                    engine
                        .argument(id, body.local_decls[local].ty, &mut conditions)
                        .unwrap(),
                );
            }
            let original = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            let Value::Input(input) = &args[0] else {
                panic!("actual root must be lazy");
            };
            assert_eq!(engine.input_reservations.len(), 3);
            let mut exhausted = Work(511);
            exhausted.charge(1).unwrap();
            assert!(exhausted.charge(1).is_err());
            assert!(exhausted.charge(0).is_err());
            let mut type_work = Work(0);
            domain(tcx, original, 0, &mut type_work).unwrap();
            assert_eq!(type_work.0, 4);
            println!("uniform array domain: 4 actual type nodes; previous repeated walk used 193");
            let mut work = Work(0);
            engine
                .validate_issued_drop_storage(original, input, &mut work)
                .unwrap();
            println!("lazy Drop root actual authentication charge={}", work.0);
            assert!(engine.validate_issued_product(original, input).is_err());
            for bad in [
                InputValue {
                    shape: Rc::new((*input.shape).clone()),
                    ..input.clone()
                },
                InputValue {
                    start: input.start + 1,
                    ..input.clone()
                },
                InputValue {
                    seed: symbolic::Context::default().boolean(false),
                    ..input.clone()
                },
                InputValue {
                    seed: engine.input_reservations[1].reservation.seed.clone(),
                    ..input.clone()
                },
                InputValue {
                    start: engine.input_reservations[1].reservation.start,
                    shape: engine.input_reservations[1].reservation.shape.clone(),
                    ..input.clone()
                },
            ] {
                assert!(
                    engine
                        .validate_issued_drop_storage(original, &bad, &mut Work(0))
                        .is_err()
                );
            }
            assert!(
                engine
                    .validate_issued_drop_storage(tcx.types.u32, input, &mut Work(0))
                    .is_err()
            );
            let mut malformed = (*input.shape).clone();
            malformed.height += 1;
            assert!(
                engine
                    .validate_drop_input_descriptor(original, &malformed, &mut Work(0))
                    .is_err()
            );
            let InputKind::Array { element, .. } = &input.shape.kind else {
                unreachable!()
            };
            let mut bad_element = (**element).clone();
            let InputKind::Struct { fields, .. } = &mut bad_element.kind else {
                unreachable!()
            };
            let mut wrong_field = (*fields[0].1).clone();
            wrong_field.kind = InputKind::Integer {
                bits: 32,
                signed: false,
            };
            fields[0].1 = Rc::new(wrong_field);
            let mut wrong_root = (*input.shape).clone();
            let InputKind::Array { element, .. } = &mut wrong_root.kind else {
                unreachable!()
            };
            *element = Rc::new(bad_element);
            assert!(
                engine
                    .validate_drop_input_descriptor(original, &wrong_root, &mut Work(0))
                    .is_err()
            );
            let saved = std::mem::take(&mut engine.input_reservations);
            assert!(
                engine
                    .validate_issued_drop_storage(original, input, &mut Work(0))
                    .is_err()
            );
            engine.input_reservations = saved;
            let path = vec![
                MemoryProjection::Index(Box::new(engine.iterator_index(1))),
                MemoryProjection::Field(0),
            ];
            let candidates = engine
                .drop_projection_candidates(original, &args[0], &path, None, None, &conditions)
                .unwrap();
            assert_eq!(candidates.len(), 1);
            engine
                .drop_projection_scalar(&candidates, &conditions)
                .unwrap();
            let mut memory = Memory::default();
            memory.push(Some(args[0].clone()));
            memory
                .missing_places
                .consume(0, vec![Step::Element(1)])
                .unwrap();
            assert!(
                engine
                    .drop_projection_candidates(
                        original,
                        &args[0],
                        &path,
                        Some((&memory, 0)),
                        None,
                        &conditions,
                    )
                    .is_err()
            );
            let selected = args[3].clone();
            conditions.push(
                symbolic::binary(
                    &engine.terms,
                    "lt",
                    selected.clone(),
                    engine.iterator_index(64),
                )
                .unwrap()
                .boolean()
                .unwrap(),
            );
            let path = vec![
                MemoryProjection::Index(Box::new(selected)),
                MemoryProjection::Field(0),
            ];
            let candidates = engine
                .drop_projection_candidates(original, &args[0], &path, None, None, &conditions)
                .unwrap();
            assert_eq!(candidates.len(), 64);
            engine
                .drop_projection_scalar(&candidates, &conditions)
                .unwrap();
            let char_id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "char_eager_pressure"
                })
                .unwrap()
                .to_def_id();
            let char_body = engine
                .instantiated_body(ty::Instance::mono(tcx, char_id))
                .unwrap();
            let char_original = char_body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            let eager = engine
                .argument(char_id, char_original, &mut Vec::new())
                .unwrap();
            assert!(matches!(eager, Value::Elements(_)));
            let invalid_char = InputShape {
                kind: InputKind::Integer {
                    bits: 32,
                    signed: false,
                },
                slots: 1,
                height: 1,
            };
            assert!(
                engine
                    .validate_drop_input_descriptor(tcx.types.char, &invalid_char, &mut Work(0),)
                    .is_err()
            );
            println!(
                "Char retains eager validity; an integer descriptor grants no lazy Char codec"
            );
            println!("lazy Drop: 64 feasible initialized scalar candidates checked");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory =
        std::env::temp_dir().join(format!("miren-issued-lazy-drop-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/incoming_drop_observations.rs");
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
