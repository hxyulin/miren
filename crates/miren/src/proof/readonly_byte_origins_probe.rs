//! Standalone TCX observations and hostile storage/call controls, not guest Body proofs.
use super::*;
use std::path::PathBuf;

fn controls<'tcx>(tcx: TyCtxt<'tcx>, root: DefId) {
    let mut engine = nonzero_niches::test_engine(tcx);
    let caller = ty::Instance::mono(tcx, root);
    let body = engine.instantiated_body(caller).unwrap();
    let (block, selected, original, slice_first) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let first = args[0].node.ty(&body.local_decls, tcx);
            let second = args[1].node.ty(&body.local_decls, tcx);
            let (original, slice_first) = match (first.kind(), second.kind()) {
                (
                    ty::Ref(_, slice, rustc_hir::Mutability::Not),
                    ty::Ref(_, needle, rustc_hir::Mutability::Not),
                ) => match (slice.kind(), needle.kind()) {
                    (ty::Slice(original), _) if *original == *needle => (*original, true),
                    (_, ty::Slice(original)) if *original == *slice => (*original, false),
                    _ => return None,
                },
                _ => return None,
            };
            let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                return None;
            };
            assert!(args.bound_vars().is_empty());
            Some((
                block,
                engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap(),
                original,
                slice_first,
            ))
        })
        .unwrap();
    let mut conditions = Vec::new();
    let slice = engine
        .composite_slice_input(root, original, &mut conditions)
        .unwrap();
    let needle = Value::Adt {
        name: tcx.def_path_str(match original.kind() {
            ty::Adt(def, _) => def.did(),
            _ => panic!("actual original Option"),
        }),
        variant: 0,
        is_option: true,
        discriminant: 0,
        fields: Vec::new().into(),
    };
    // Evaluated shared references survive a moved carrier local. No operand is evaluated here
    // or in observe(); only the real selected Call and its original operand types are inspected.
    let state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        memory: Memory::from(vec![Some(slice.clone()), Some(needle.clone())]),
        conditions,
    };
    let mut raw = [
        Value::Reference {
            allocation: 0,
            projection: Vec::new(),
            mutable: false,
        },
        Value::Reference {
            allocation: 1,
            projection: Vec::new(),
            mutable: false,
        },
    ];
    if !slice_first {
        raw.swap(0, 1);
    }
    let source_index = usize::from(!slice_first);
    let call = CallOccurrence::new(caller, &body, block, &raw);
    let inputs = Inputs {
        selected,
        slice_first,
        raw: &raw,
        slice: &slice,
        needle: &needle,
    };
    let origin = observe(&engine, &call, &inputs, &state).unwrap();
    assert_eq!(origin.original, original);
    assert_eq!(origin.slice_allocation, 0);
    assert_eq!(origin.needle_allocation, 1);
    assert_eq!(
        origin.offset,
        engine
            .terms
            .bit_vector(0, u32::from(tcx.sess.target.pointer_width))
            .unwrap()
    );
    assert!(state.locals.iter().all(Option::is_none));
    origin.validate_current(&engine, &call, &state).unwrap();
    let other_call = CallOccurrence::new(caller, &body, block, &raw);
    assert!(
        origin
            .validate_current(&engine, &other_call, &state)
            .unwrap_err()
            .contains("another invocation")
    );
    let cloned_state = state.clone();
    assert!(
        origin
            .validate_current(&engine, &call, &cloned_state)
            .unwrap_err()
            .contains("another invocation")
    );
    let other_engine = nonzero_niches::test_engine(tcx);
    assert!(
        origin
            .validate_current(&other_engine, &call, &state)
            .unwrap_err()
            .contains("another invocation")
    );
    engine
        .bodies
        .borrow_mut()
        .insert(caller, Rc::new((*body).clone()));
    assert!(
        origin
            .validate_current(&engine, &call, &state)
            .unwrap_err()
            .contains("replaced or unavailable")
    );
    engine.bodies.borrow_mut().insert(caller, body.clone());
    // This asserts only the new live relation. It grants no search, pointer or helper theorem.
    let relation = observe(&engine, &call, &inputs, &state)
        .unwrap()
        .relation()
        .unwrap();
    assert_eq!(relation.encoding, engine.terms.bit_vector(0, 8).unwrap());
    assert_eq!(
        relation.length,
        usize_term(
            &engine,
            match &slice {
                Value::CompositeSlice { length, .. } => length,
                _ => unreachable!(),
            }
        )
        .unwrap()
    );
    let carried = relation
        .into_work(&engine, original, selected, &slice, &needle, &state)
        .unwrap();
    assert!(carried > 0 && carried < 131_072);
    let relation = observe(&engine, &call, &inputs, &state)
        .unwrap()
        .relation()
        .unwrap();
    assert!(
        relation
            .into_work(&engine, original, selected, &slice, &needle, &cloned_state,)
            .unwrap_err()
            .contains("another live invocation")
    );
    let relation = observe(&engine, &call, &inputs, &state)
        .unwrap()
        .relation()
        .unwrap();
    engine
        .bodies
        .borrow_mut()
        .insert(caller, Rc::new((*body).clone()));
    assert!(
        relation
            .into_work(&engine, original, selected, &slice, &needle, &state)
            .unwrap_err()
            .contains("Body was replaced or unavailable")
    );
    engine.bodies.borrow_mut().insert(caller, body.clone());
    let guarded = observe(&engine, &call, &inputs, &state).unwrap();
    let exclusive = engine.bodies.borrow_mut();
    assert!(
        guarded
            .relation()
            .err()
            .unwrap()
            .contains("registry is mutably borrowed")
    );
    drop(exclusive);
    let mut excessive = observe(&engine, &call, &inputs, &state).unwrap();
    excessive.offset = engine
        .terms
        .bit_vector(
            (1u128 << tcx.sess.target.pointer_width) - 1,
            u32::from(tcx.sess.target.pointer_width),
        )
        .unwrap();
    assert!(
        excessive
            .relation()
            .err()
            .unwrap()
            .contains("projected extent exceeds its current allocation")
    );
    eprintln!(
        "byte relation: live encoding/extent, carried work, foreign invocation/extent refusal"
    );
    drop(origin);

    let bits = u32::from(tcx.sess.target.pointer_width);
    let mut projected_raw = raw.clone();
    let Value::Reference { projection, .. } = &mut projected_raw[source_index] else {
        unreachable!()
    };
    let step = symbolic::MemoryProjection::Slice {
        offset: Box::new(symbolic::integer(&engine.terms, 0, bits, false)),
        length: Box::new(symbolic::integer(&engine.terms, 0, bits, false)),
    };
    projection.push(step.clone());
    let projected = engine
        .memory_projection(slice.clone(), &step, &state.conditions)
        .unwrap();
    let projected_call = CallOccurrence::new(caller, &body, block, &projected_raw);
    let projected_inputs = Inputs {
        raw: &projected_raw,
        slice: &projected,
        ..inputs
    };
    let projected_origin = observe(&engine, &projected_call, &projected_inputs, &state).unwrap();
    projected_origin
        .validate_current(&engine, &projected_call, &state)
        .unwrap();
    drop(projected_origin);

    let copied_raw = raw.clone();
    let changed = Inputs {
        raw: &copied_raw,
        ..inputs
    };
    assert!(
        observe(&engine, &call, &changed, &state)
            .err()
            .unwrap()
            .contains("raw-argument occurrence witness")
    );
    let wrong_selection = Inputs {
        selected: caller,
        ..inputs
    };
    assert!(
        observe(&engine, &call, &wrong_selection, &state)
            .err()
            .unwrap()
            .contains("selected Instance differs")
    );
    let bad_block = CallOccurrence::new(
        caller,
        &body,
        BasicBlock::from_usize(body.basic_blocks.len()),
        &raw,
    );
    assert!(observe(&engine, &bad_block, &inputs, &state).is_err());
    let mut swapped = (*body).clone();
    let TerminatorKind::Call { args, .. } =
        &mut swapped.basic_blocks.as_mut()[block].terminator_mut().kind
    else {
        panic!("actual Call");
    };
    args.swap(0, 1);
    let swapped = Rc::new(swapped);
    engine.bodies.borrow_mut().insert(caller, swapped.clone());
    let swapped_call = CallOccurrence::new(caller, &swapped, block, &raw);
    assert!(
        observe(&engine, &swapped_call, &inputs, &state)
            .err()
            .unwrap()
            .contains("not a Rust slice")
    );
    engine.bodies.borrow_mut().insert(caller, body.clone());

    let mut dead = state.clone();
    dead.memory[0] = None;
    assert!(observe(&engine, &call, &inputs, &dead).is_err());
    let mut dead_needle = state.clone();
    dead_needle.memory[1] = None;
    assert!(observe(&engine, &call, &inputs, &dead_needle).is_err());
    let mut wrong_carrier = state.clone();
    wrong_carrier.memory[0] = Some(Value::Unit);
    assert!(observe(&engine, &call, &inputs, &wrong_carrier).is_err());
    let mut missing = state.clone();
    missing.memory.missing_places.consume(0, vec![]).unwrap();
    assert!(observe(&engine, &call, &inputs, &missing).is_err());
    // This is a standalone hostile Armed flow, not activation issuance for the Option8 root.
    let scalar = tcx
        .mir_keys(())
        .iter()
        .copied()
        .find(|id| {
            tcx.def_kind(*id) == DefKind::Fn
                && tcx.item_name(id.to_def_id()).as_str() == "scalar_seed"
        })
        .unwrap();
    let scalar = ty::Instance::mono(tcx, scalar.to_def_id());
    let scalar_body = engine.instantiated_body(scalar).unwrap();
    let mut armed = state.clone();
    armed.flow = engine.activation_test_root(scalar, &scalar_body).unwrap();
    assert_eq!(
        observe(&engine, &call, &inputs, &armed).err().unwrap(),
        "armed activation adapter is not implemented"
    );

    let mut foreign = slice.clone();
    let Value::CompositeSlice { length, leaves, .. } = &mut foreign else {
        unreachable!()
    };
    let context = Context::default();
    let bits = u32::from(tcx.sess.target.pointer_width);
    **length = symbolic::integer(&context, 1, bits, false);
    leaves[0] = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8))),
        )
        .unwrap();
    let changed = Inputs {
        slice: &foreign,
        ..inputs
    };
    assert!(observe(&engine, &call, &changed, &state).is_err());
    let mut changed_needle = needle.clone();
    let Value::Adt { name, .. } = &mut changed_needle else {
        unreachable!()
    };
    name.push_str("changed");
    let changed = Inputs {
        needle: &changed_needle,
        ..inputs
    };
    assert!(observe(&engine, &call, &changed, &state).is_err());

    let mut mutable_raw = raw.clone();
    let Value::Reference { mutable, .. } = &mut mutable_raw[source_index] else {
        unreachable!()
    };
    *mutable = true;
    let mutable_call = CallOccurrence::new(caller, &body, block, &mutable_raw);
    let changed = Inputs {
        raw: &mutable_raw,
        ..inputs
    };
    assert!(observe(&engine, &mutable_call, &changed, &state).is_err());
    let mut numeric_raw = raw.clone();
    numeric_raw[source_index] = Value::RawPointer {
        address: engine.terms.bit_vector(1, bits).unwrap(),
        bits,
    };
    let numeric_call = CallOccurrence::new(caller, &body, block, &numeric_raw);
    let changed = Inputs {
        raw: &numeric_raw,
        ..inputs
    };
    assert!(observe(&engine, &numeric_call, &changed, &state).is_err());
    let mut wrong_width = raw.clone();
    let Value::Reference { projection, .. } = &mut wrong_width[source_index] else {
        unreachable!()
    };
    projection.push(symbolic::MemoryProjection::Slice {
        offset: Box::new(symbolic::integer(&engine.terms, 0, 8, false)),
        length: Box::new(symbolic::integer(&engine.terms, 0, bits, false)),
    });
    let width_call = CallOccurrence::new(caller, &body, block, &wrong_width);
    let changed = Inputs {
        raw: &wrong_width,
        ..inputs
    };
    assert!(observe(&engine, &width_call, &changed, &state).is_err());
    // Observed origins are deliberately disconnected from helper semantic authority.
    let error = engine
        .exact_niche_membership(original, selected, &slice, &needle, &state)
        .unwrap_err();
    assert_eq!(error, "byte source statement debug payload is unsupported");
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::Semantics)
    );
    eprintln!(
        "readonly byte origin: moved carrier, current Call/storage, hostile scope/context controls"
    );
}

#[test]
fn actual_readonly_origin_facts_and_hostile_occurrences() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let root = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "origin"
                })
                .unwrap();
            controls(tcx, root.to_def_id());
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = PathBuf::from(format!(
        "/tmp/miren-readonly-origin-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("guest.rs");
    std::fs::write(
        &source,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        #[inline(never)] pub fn origin(v:&[Option<core::num::NonZeroU8>],\n\
        n:&Option<core::num::NonZeroU8>)->bool{v.contains(n)}\n\
        pub fn scalar_seed(x:u16)->u16{x}\n",
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimization in [0, 2] {
            let mut args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={optimization}"),
                "--sysroot".into(),
                sysroot.trim().into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut check = Check(false);
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
            eprintln!(
                "byte relation callback complete: {} O{optimization}",
                target.unwrap_or("host"),
            );
        }
    }
}
