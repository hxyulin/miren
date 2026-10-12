//! Actual original-Ty compiler tests for the separately disabled ConstantIndex route.
use super::*;

fn engine<'tcx>(tcx: TyCtxt<'tcx>) -> Engine<'tcx> {
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

fn snapshot(state: &State) -> String {
    format!(
        "{:?}",
        (
            &state.locals,
            &state.memory[..],
            &state.memory.mutable_u16,
            &state.memory.mutable_hierarchy,
            &state.memory.owned_regions,
            &state.memory.missing_places,
            &state.conditions,
            &state.addresses,
            &state.missing_places
        )
    )
}

fn constant<'tcx>(tcx: TyCtxt<'tcx>, offset: u64, minimum: u64, from_end: bool) -> Place<'tcx> {
    Place {
        local: rustc_middle::mir::Local::from_usize(1),
        projection: tcx.mk_place_elems(&[
            ProjectionElem::Deref,
            ProjectionElem::ConstantIndex {
                offset,
                min_length: minimum,
                from_end,
            },
        ]),
    }
}

fn selected<'tcx>(engine: &mut Engine<'tcx>, name: &str) -> std::rc::Rc<Body<'tcx>> {
    let id = engine
        .tcx
        .hir_body_owners()
        .find(|owner| {
            engine.tcx.def_kind(owner.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(owner.to_def_id()).as_str() == name
        })
        .unwrap();
    let instance = engine
        .resolve_function_item(id.to_def_id(), engine.tcx.mk_args(&[]))
        .unwrap();
    engine.instantiated_body(instance).unwrap()
}

fn state_for<'tcx>(engine: &mut Engine<'tcx>, body: &Body<'tcx>, original: Ty<'tcx>) -> State {
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let root = engine
        .mutable_u16_input(original, &mut memory, &mut conditions)
        .unwrap();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    std::rc::Rc::make_mut(&mut memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 3, bits, false);
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        conditions,
        memory,
        missing_places: Default::default(),
    };
    state.locals[1] = Some(root);
    state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
    state
}

fn refuse_store<'tcx>(
    engine: &Engine<'tcx>,
    body: &Body<'tcx>,
    state: &mut State,
    place: Place<'tcx>,
    replacement: &Value,
) {
    let before = snapshot(state);
    let bindings = engine.float_encodings.clone();
    let symbols = engine.next_symbol.get();
    let frames = engine.mutable_u16_frames.borrow().len();
    assert!(
        engine
            .mutable_u16_store(body, state, place, replacement)
            .is_err()
    );
    assert_eq!(snapshot(state), before);
    assert_eq!(engine.float_encodings, bindings);
    assert_eq!(engine.next_symbol.get(), symbols);
    assert_eq!(engine.mutable_u16_frames.borrow().len(), frames);
}

fn check_interval<'tcx>(tcx: TyCtxt<'tcx>, name: &str, original: Ty<'tcx>) {
    let mut engine = engine(tcx);
    let body = selected(&mut engine, name);
    let root = match body.source.instance {
        ty::InstanceKind::Item(id) => id,
        _ => panic!("original interval item"),
    };
    let (block, args, destination, target, instance) = body
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
            if tcx.def_kind(*id) != DefKind::AssocFn {
                return None;
            }
            let instance = engine
                .resolve_function_item(*id, generic.skip_binder())
                .unwrap();
            (pure_comparison_templates::definition_key(instance.def_id())
                == "DefId(core::slice::index::{impl#1}::index_mut)")
                .then_some((block, args.as_ref(), *destination, *target, instance))
        })
        .unwrap();
    let bits = u32::from(tcx.sess.target.pointer_width);
    for end in [3, 1] {
        let mut memory = Memory::default();
        let mut conditions = Vec::new();
        let value = engine
            .mutable_u16_input(original, &mut memory, &mut conditions)
            .unwrap();
        let id = memory.mutable_u16.len() - 1;
        std::rc::Rc::make_mut(&mut memory.mutable_u16)[id].length =
            symbolic::integer(&engine.terms, 4, bits, false);
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            addresses: vec![None; body.local_decls.len()],
            memory,
            conditions,
            missing_places: Default::default(),
        };
        state.locals[1] = Some(value);
        state.locals[2] = Some(symbolic::integer(&engine.terms, 1, bits, false));
        state.locals[3] = Some(symbolic::integer(&engine.terms, end, bits, false));
        for statement in &body.basic_blocks[block].statements {
            if let StatementKind::Assign(assignment) = &statement.kind {
                if engine
                    .mutable_u16_stage(
                        &body,
                        &mut state,
                        assignment.0,
                        &assignment.1,
                        &statement.kind,
                    )
                    .unwrap()
                {
                    continue;
                }
                let value = engine
                    .rvalue(root, &body, &mut state, &assignment.1)
                    .unwrap();
                engine.write(&mut state, assignment.0, value).unwrap();
            }
        }
        let (_, mut view) = engine
            .mutable_interval_call(
                &state,
                super::super::mutable_u16_children::ChildCall {
                    body: &body,
                    block,
                    instance,
                    args,
                    destination,
                    target,
                    stack: &[],
                    site: (root, body.span),
                },
            )
            .unwrap()
            .unwrap();
        let backing = &mut std::rc::Rc::make_mut(&mut view.memory.mutable_u16)[id];
        let generation = backing.generation;
        backing.phase = super::super::mutable_u16_children::Phase::Active { frames: vec![0] };
        view.locals[1] = Some(Value::MutableU16 {
            id,
            role: MutableU16Role::Child { generation },
        });
        let typed = selected(
            &mut engine,
            if original == tcx.types.u16 {
                "u16_probe"
            } else if original == tcx.types.i32 {
                "i32_probe"
            } else {
                "usize_probe"
            },
        );
        let width = if original == tcx.types.u16 {
            16
        } else if original == tcx.types.i32 {
            32
        } else {
            bits
        };
        let word = symbolic::integer(&engine.terms, 17, width, original == tcx.types.i32);
        let first = constant(tcx, 0, 1, false);
        if end == 1 {
            refuse_store(&engine, &typed, &mut view, first, &word);
            assert!(engine.mutable_u16_read(Some(&typed), &view, first).is_err());
            continue;
        }
        for place in [first, constant(tcx, 1, 1, true)] {
            assert!(
                engine
                    .mutable_u16_store(&typed, &mut view, place, &word)
                    .unwrap()
            );
            let observed = engine
                .mutable_u16_read(Some(&typed), &view, place)
                .unwrap()
                .unwrap();
            assert!(
                !engine
                    .feasible(&[
                        symbolic::binary(&engine.terms, "ne", observed, word.clone())
                            .unwrap()
                            .boolean()
                            .unwrap()
                    ])
                    .unwrap()
            );
        }
        refuse_store(
            &engine,
            &typed,
            &mut view,
            constant(tcx, 0, 3, false),
            &word,
        );
        refuse_store(&engine, &typed, &mut view, constant(tcx, 3, 3, true), &word);
        let mut stale = view.clone();
        std::rc::Rc::make_mut(&mut stale.memory.mutable_u16)[id].generation += 1;
        refuse_store(&engine, &typed, &mut stale, first, &word);
    }
}

fn check<'tcx>(tcx: TyCtxt<'tcx>) {
    let mut engine = engine(tcx);
    let body = selected(&mut engine, "u16_probe");
    let mut state = state_for(&mut engine, &body, tcx.types.u16);
    let word = symbolic::integer(&engine.terms, 17, 16, false);
    let first = constant(tcx, 0, 1, false);
    assert_eq!(constant_index_enabled(), CONSTANT_INDEX_ENABLED);
    if CONSTANT_INDEX_ENABLED {
        assert!(engine.mutable_u16_read(Some(&body), &state, first).is_ok());
        assert!(
            engine
                .mutable_u16_store(&body, &mut state, first, &word)
                .unwrap()
        );
    } else {
        assert!(engine.mutable_u16_read(Some(&body), &state, first).is_err());
        refuse_store(&engine, &body, &mut state, first, &word);
    }
    let enabled = ConstantIndexTestEnabled::enable();
    for place in [
        first,
        constant(tcx, 2, 3, false),
        constant(tcx, 1, 1, true),
        constant(tcx, 3, 3, true),
    ] {
        assert!(
            engine
                .mutable_u16_store(&body, &mut state, place, &word)
                .unwrap()
        );
        let observed = engine
            .mutable_u16_read(Some(&body), &state, place)
            .unwrap()
            .unwrap();
        assert!(
            !engine
                .feasible(&[
                    symbolic::binary(&engine.terms, "ne", observed, word.clone())
                        .unwrap()
                        .boolean()
                        .unwrap()
                ])
                .unwrap()
        );
    }
    let preserved = state.clone();
    let replacement = symbolic::integer(&engine.terms, 31, 16, false);
    assert!(
        engine
            .mutable_u16_store(&body, &mut state, first, &replacement)
            .unwrap()
    );
    let observed = engine
        .mutable_u16_read(Some(&body), &state, first)
        .unwrap()
        .unwrap();
    assert!(
        !engine
            .feasible(
                &[symbolic::binary(&engine.terms, "ne", observed, replacement)
                    .unwrap()
                    .boolean()
                    .unwrap()]
            )
            .unwrap()
    );
    assert_ne!(
        preserved.memory.mutable_u16[0].data,
        state.memory.mutable_u16[0].data
    );
    for place in [
        constant(tcx, 1, 1, false),
        constant(tcx, 0, 1, true),
        constant(tcx, 2, 1, true),
        constant(tcx, 0, 4, false),
        constant(tcx, 1, 4, true),
    ] {
        assert!(engine.mutable_u16_read(Some(&body), &state, place).is_err());
        refuse_store(&engine, &body, &mut state, place, &word);
    }
    if tcx.sess.target.pointer_width == 32 {
        for place in [
            constant(tcx, 1_u64 << 32, (1_u64 << 32) + 1, false),
            constant(tcx, 0, 1_u64 << 32, false),
        ] {
            refuse_store(&engine, &body, &mut state, place, &word);
        }
    }
    let mut empty = state.clone();
    let bits = u32::from(tcx.sess.target.pointer_width);
    std::rc::Rc::make_mut(&mut empty.memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 0, bits, false);
    refuse_store(&engine, &body, &mut empty, first, &word);
    let mut symbolic_length = state.clone();
    std::rc::Rc::make_mut(&mut symbolic_length.memory.mutable_u16)[0].length = Value::Int {
        expression: engine.terms.symbol(901, Sort::BitVec(bits)).unwrap(),
        bits,
        signed: false,
    };
    refuse_store(&engine, &body, &mut symbolic_length, first, &word);
    assert!(engine.mutable_u16_read(None, &state, first).is_err());
    let extra = Place {
        local: first.local,
        projection: tcx.mk_place_elems(&[
            ProjectionElem::Deref,
            ProjectionElem::ConstantIndex {
                offset: 0,
                min_length: 1,
                from_end: false,
            },
            ProjectionElem::Field(rustc_abi::FieldIdx::from_usize(0), tcx.types.u16),
        ]),
    };
    refuse_store(&engine, &body, &mut state, extra, &word);
    for original in [tcx.types.i16, tcx.types.u32] {
        let mut forged = (*body).clone();
        forged.local_decls[first.local].ty =
            Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, Ty::new_slice(tcx, original));
        refuse_store(&engine, &forged, &mut state, first, &word);
    }
    let foreign = Context::default();
    let mut wrong_context = state.clone();
    std::rc::Rc::make_mut(&mut wrong_context.memory.mutable_u16)[0].length =
        symbolic::integer(&foreign, 3, bits, false);
    refuse_store(&engine, &body, &mut wrong_context, first, &word);
    let mut wrong_codec = state.clone();
    std::rc::Rc::make_mut(&mut wrong_codec.memory.mutable_u16)[0].data = engine
        .terms
        .symbol(
            902,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::Bool)),
        )
        .unwrap();
    refuse_store(&engine, &body, &mut wrong_codec, first, &word);
    for wrong in [
        symbolic::integer(&engine.terms, 17, 16, true),
        symbolic::integer(&engine.terms, 17, 32, false),
        symbolic::integer(&foreign, 17, 16, false),
    ] {
        refuse_store(&engine, &body, &mut state, first, &wrong);
    }
    let mut dead = state.clone();
    let allocation = dead.memory.mutable_u16[0].allocation;
    dead.memory[allocation] = None;
    refuse_store(&engine, &body, &mut dead, first, &word);
    let mut masked = state.clone();
    masked.missing_places.consume(1, Vec::new()).unwrap();
    refuse_store(&engine, &body, &mut masked, first, &word);
    let mut masked_memory = state.clone();
    masked_memory
        .memory
        .missing_places
        .consume(allocation, Vec::new())
        .unwrap();
    refuse_store(&engine, &body, &mut masked_memory, first, &word);
    let mut stale = state.clone();
    std::rc::Rc::make_mut(&mut stale.memory.mutable_u16)[0].phase =
        super::super::mutable_u16_children::Phase::Active { frames: vec![0] };
    stale.locals[1] = Some(Value::MutableU16 {
        id: 0,
        role: MutableU16Role::Child { generation: 1 },
    });
    refuse_store(&engine, &body, &mut stale, first, &word);
    let ghost = engine
        .mutable_u16_snapshot(state.locals[1].as_ref().unwrap(), &state.memory)
        .unwrap();
    let mut detached = state.clone();
    detached.locals[1] = Some(ghost);
    refuse_store(&engine, &body, &mut detached, first, &word);
    for (name, original) in [
        ("char_probe", tcx.types.char),
        ("fp32_probe", tcx.types.f32),
        ("fp64_probe", tcx.types.f64),
    ] {
        let typed = selected(&mut engine, name);
        let mut target = state_for(&mut engine, &typed, original);
        if original == tcx.types.char {
            for raw in [0xd800, 0xdfff, 0x110000] {
                let invalid = symbolic::integer(&engine.terms, raw, 32, false);
                refuse_store(&engine, &typed, &mut target, first, &invalid);
            }
            let unresolved = Value::Int {
                expression: engine.terms.symbol(903, Sort::BitVec(32)).unwrap(),
                bits: 32,
                signed: false,
            };
            refuse_store(&engine, &typed, &mut target, first, &unresolved);
            let valid = symbolic::integer(&engine.terms, 0x10ffff, 32, false);
            assert!(
                engine
                    .mutable_u16_store(&typed, &mut target, first, &valid)
                    .unwrap()
            );
        } else {
            let width = if original == tcx.types.f32 { 32 } else { 64 };
            let nan = if width == 32 {
                0x7fc0_0017
            } else {
                0x7ff8_0000_0000_0017
            };
            let valid = symbolic::float_from_bits(
                &engine.terms,
                engine.terms.bit_vector(nan, width).unwrap(),
                width,
            );
            let mut forged = valid.clone();
            if let Value::Float { raw_bits, .. } = &mut forged {
                *raw_bits = Some(engine.terms.bit_vector(nan + 1, width).unwrap());
            }
            refuse_store(&engine, &typed, &mut target, first, &forged);
            let mut missing = valid.clone();
            if let Value::Float { raw_bits, .. } = &mut missing {
                *raw_bits = None;
            }
            refuse_store(&engine, &typed, &mut target, first, &missing);
            assert!(
                engine
                    .mutable_u16_store(&typed, &mut target, first, &valid)
                    .unwrap()
            );
        }
    }
    for (name, original) in [
        ("interval_u16", tcx.types.u16),
        ("interval_i32", tcx.types.i32),
        ("interval_usize", tcx.types.usize),
    ] {
        check_interval(tcx, name, original);
    }
    drop(enabled);
    assert_eq!(constant_index_enabled(), CONSTANT_INDEX_ENABLED);
}

#[test]
fn constant_index_scope_is_restored_on_nesting_and_unwind() {
    assert_eq!(constant_index_enabled(), CONSTANT_INDEX_ENABLED);
    assert!(!CONSTANT_INDEX_TEST_ENABLED.with(std::cell::Cell::get));
    let guard = ConstantIndexTestEnabled::enable();
    {
        let nested = ConstantIndexTestEnabled::enable();
        drop(nested);
        assert!(CONSTANT_INDEX_TEST_ENABLED.with(std::cell::Cell::get));
    }
    assert!(constant_index_enabled());
    assert!(
        std::panic::catch_unwind(|| {
            let _nested = ConstantIndexTestEnabled::enable();
            panic!("scope probe");
        })
        .is_err()
    );
    assert!(constant_index_enabled());
    drop(guard);
    assert!(!CONSTANT_INDEX_TEST_ENABLED.with(std::cell::Cell::get));
    assert_eq!(constant_index_enabled(), CONSTANT_INDEX_ENABLED);
}

#[test]
fn compiler_typed_constant_indices_preserve_validity_and_transactions() {
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
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("miren-stage213-{}-{now}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("guest.rs");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "pub fn u16_probe(v:&mut[u16],i:usize,w:u16){if i<v.len(){v[i]=w;}}\n",
            "pub fn char_probe(v:&mut[char],i:usize,w:char){if i<v.len(){v[i]=w;}}\n",
            "pub fn fp32_probe(v:&mut[f32],i:usize,w:f32){if i<v.len(){v[i]=w;}}\n",
            "pub fn fp64_probe(v:&mut[f64],i:usize,w:f64){if i<v.len(){v[i]=w;}}\n",
            "pub fn i32_probe(v:&mut[i32],i:usize,w:i32){if i<v.len(){v[i]=w;}}\n",
            "pub fn usize_probe(v:&mut[usize],i:usize,w:usize){if i<v.len(){v[i]=w;}}\n",
            "pub fn interval_u16(v:&mut[u16],a:usize,b:usize){update_u16(&mut v[a..b]);}\n",
            "#[inline(never)] fn update_u16(v:&mut[u16]){if v.len()>0{v[0]=17;}}\n",
            "pub fn interval_i32(v:&mut[i32],a:usize,b:usize){update_i32(&mut v[a..b]);}\n",
            "#[inline(never)] fn update_i32(v:&mut[i32]){if v.len()>0{v[0]=17;}}\n",
            "pub fn interval_usize(v:&mut[usize],a:usize,b:usize){update_usize(&mut v[a..b]);}\n",
            "#[inline(never)] fn update_usize(v:&mut[usize]){if v.len()>0{v[0]=17;}}\n"
        ),
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            let mut arguments = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "-Zmir-opt-level=0".into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout.clone())
                    .unwrap()
                    .trim()
                    .into(),
            ];
            if let Some(target) = target {
                arguments.extend(["--target".into(), target.into()]);
            }
            let mut callback = Check { checked: false };
            rustc_driver::run_compiler(&arguments, &mut callback);
            assert!(callback.checked);
            println!("stage213 actual callback {target:?} O{level} complete");
        }
    }
}
