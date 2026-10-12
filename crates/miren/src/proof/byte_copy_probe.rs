use super::*;

#[test]
fn compiler_byte_copy_selected_family_probe() {
    struct Capture {
        output: std::path::PathBuf,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let root = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| tcx.item_name(id.to_def_id()).as_str() == "probe")
                .unwrap();
            let root = ty::Instance::new_raw(root.to_def_id(), tcx.mk_args(&[]));
            let fixed = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| tcx.item_name(id.to_def_id()).as_str() == "fixed")
                .unwrap();
            std::fs::write(
                self.output.join("caller-fixed.txt"),
                format!("{:#?}", tcx.optimized_mir(fixed)),
            )
            .unwrap();
            check_current_destination(tcx, root.def_id(), fixed.to_def_id());
            let over = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| tcx.item_name(id.to_def_id()).as_str() == "over")
                .unwrap();
            let over = tcx.optimized_mir(over);
            let mut over_found = false;
            for (block, data) in over.basic_blocks.iter_enumerated() {
                if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                    && let ty::FnDef(id, _) = func.ty(&over.local_decls, tcx).kind()
                    && tcx.item_name(*id).as_str() == "copy_from_slice"
                {
                    assert_eq!(
                        byte_copy_origins::original_source(tcx, over, block, &args[1].node)
                            .unwrap_err()
                            .category,
                        UnknownCategory::ResourceLimit
                    );
                    over_found = true;
                }
            }
            assert!(over_found);
            let core = tcx.lang_items().sized_trait().unwrap().krate;
            let mut oversized = tcx.optimized_mir(fixed).clone();
            while oversized.local_decls.len() <= 512 {
                oversized
                    .local_decls
                    .push(oversized.local_decls[rustc_middle::mir::Local::from_usize(0)].clone());
            }
            assert_eq!(
                pure_comparison_templates::encode_byte_copy_template(tcx, &oversized, core)
                    .unwrap_err()
                    .category,
                UnknownCategory::ResourceLimit
            );
            assert!(
                pure_comparison_templates::encode_template(tcx, &oversized, core)
                    .unwrap_err()
                    .contains("supported body domain")
            );
            let fixed_body = tcx.optimized_mir(fixed);
            let mut origin_found = false;
            for (block, data) in fixed_body.basic_blocks.iter_enumerated() {
                if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                    && let ty::FnDef(id, _) = func.ty(&fixed_body.local_decls, tcx).kind()
                    && tcx.item_name(*id).as_str() == "copy_from_slice"
                {
                    assert_eq!(
                        super::byte_copy_origins::original_source(
                            tcx,
                            fixed_body,
                            block,
                            &args[1].node
                        )
                        .unwrap(),
                        [17, 19]
                    );
                    origin_found = true;
                }
            }
            assert!(origin_found);
            let core = tcx.lang_items().sized_trait().unwrap().krate;
            let mut pending = vec![root];
            let mut seen = std::collections::HashSet::new();
            while let Some(instance) = pending.pop() {
                if !seen.insert(instance) {
                    continue;
                }
                assert!(seen.len() < 128);
                let name = tcx.def_path_str(instance.def_id());
                if !matches!(instance.def, ty::InstanceKind::Item(_))
                    || !tcx.is_mir_available(instance.def_id())
                {
                    continue;
                }
                if tcx.item_name(instance.def_id()).as_str() == "copy_from_slice" {
                    super::byte_copy_templates::certify(tcx, instance, 2).unwrap();
                    super::byte_copy_templates::certify(tcx, instance, 0).unwrap();
                    assert!(super::byte_copy_templates::certify(tcx, instance, 129).is_err());
                }
                let generic = tcx.instance_mir(instance.def);
                if tcx.item_name(instance.def_id()).as_str() == "copy_from_slice_impl" {
                    super::byte_copy_templates::mutation_guard(tcx, generic, core);
                }
                let body = instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(tcx, generic.clone()),
                    )
                    .unwrap();
                let index = seen.len();
                std::fs::write(
                    self.output.join(format!("{index}-key.txt")),
                    pure_comparison_templates::definition_key(instance.def_id()),
                )
                .unwrap();
                std::fs::write(
                    self.output.join(format!("{index}-mono.txt")),
                    format!("{name}\n{body:#?}"),
                )
                .unwrap();
                let encoded =
                    pure_comparison_templates::encode_byte_copy_template(tcx, generic, core);
                std::fs::write(
                    self.output.join(format!("{index}-generic.txt")),
                    format!("{name}\n{encoded:?}"),
                )
                .unwrap();
                for block in body.basic_blocks.iter() {
                    if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                        && let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind()
                    {
                        pending.push(
                            ty::Instance::try_resolve(
                                tcx,
                                ty::TypingEnv::fully_monomorphized(),
                                *id,
                                args.skip_binder(),
                            )
                            .unwrap()
                            .unwrap(),
                        );
                    }
                }
            }
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::path::PathBuf::from("/tmp/miren-stage193-copy-prototype");
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("probe.rs");
    std::fs::write(
        &source,
        "#![no_std]\npub fn probe(x:&mut[u8],y:&[u8]){x.copy_from_slice(y)}\n\
         pub fn fixed(x:&mut[u8]){if x.len()>=2{x[..2].copy_from_slice(&[17,19])}}\n\
         pub fn over(x:&mut[u8]){if x.len()>=129{x[..129].copy_from_slice(&[7;129])}}\n",
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in ["0", "2"] {
            let output = directory.join(format!("{}-{opt}", target.unwrap_or("host")));
            std::fs::create_dir_all(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                source.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "--crate-name=byte_probe".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={opt}"),
                "-Zmir-opt-level=0".into(),
                "--out-dir".into(),
                output.display().to_string(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout.clone())
                    .unwrap()
                    .trim()
                    .to_owned(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut Capture { output });
        }
    }
}

fn check_current_destination<'tcx>(tcx: TyCtxt<'tcx>, root: DefId, fixed: DefId) {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    let mut engine = Engine::new(
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
    );
    assert!(!engine.incoming_byte_copy_root(root, tcx.optimized_mir(root)));
    assert!(engine.incoming_byte_copy_root(fixed, tcx.optimized_mir(fixed)));
    let bits = u32::from(tcx.sess.target.pointer_width);
    let capacity_term = engine.fresh(Sort::BitVec(bits));
    let capacity = Value::Int {
        expression: capacity_term.clone(),
        bits,
        signed: false,
    };
    let data = engine
        .terms
        .apply(
            Op::ConstArray { index_bits: bits },
            &[engine.terms.bit_vector(0, 8).unwrap()],
        )
        .unwrap();
    let current = Value::Bytes {
        length: Box::new(capacity.clone()),
        data,
    };
    let mut memory = Memory::from(vec![Some(current)]);
    memory
        .incoming_byte_roots
        .push(super::byte_copy_provenance::IncomingByteRoot {
            allocation: 0,
            capacity,
        });
    let reference = Value::Reference {
        allocation: 0,
        mutable: true,
        projection: vec![symbolic::MemoryProjection::Slice {
            offset: Box::new(symbolic::integer(&engine.terms, 0, bits, false)),
            length: Box::new(symbolic::integer(&engine.terms, 2, bits, false)),
        }],
    };
    let state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![],
        addresses: vec![],
        missing_places: Default::default(),
        memory,
        conditions: vec![
            engine
                .terms
                .apply(
                    Op::BvUnsignedLe,
                    &[
                        engine.terms.bit_vector(4, bits).unwrap(),
                        capacity_term.clone(),
                    ],
                )
                .unwrap(),
            engine
                .terms
                .apply(
                    Op::BvUnsignedLe,
                    &[
                        capacity_term.clone(),
                        engine
                            .terms
                            .bit_vector((1_u128 << (bits - 1)) - 1, bits)
                            .unwrap(),
                    ],
                )
                .unwrap(),
        ],
    };
    assert!(
        engine
            .byte_copy_current_destination(&reference, &state)
            .is_ok()
    );
    let fixed_body = tcx.optimized_mir(fixed);
    let source_place = Place {
        local: rustc_middle::mir::Local::from_usize(1),
        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
    };
    let mut metadata_state = state.clone();
    metadata_state.locals = vec![
        Some(Value::Unit),
        Some(Value::Reference {
            allocation: 0,
            projection: vec![],
            mutable: true,
        }),
    ];
    metadata_state.addresses = vec![None; 2];
    let metadata = engine
        .rvalue(
            fixed,
            fixed_body,
            &mut metadata_state,
            &Rvalue::RawPtr(
                rustc_middle::mir::RawPtrKind::FakeForPtrMetadata,
                source_place,
            ),
        )
        .unwrap();
    assert!(matches!(metadata, Value::MetadataPointer(_)));
    assert!(!metadata_state.memory.byte_copy_opaque);
    let mut raw_state = metadata_state.clone();
    let _ = engine.rvalue(
        fixed,
        fixed_body,
        &mut raw_state,
        &Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::Mut, source_place),
    );
    assert!(raw_state.memory.byte_copy_opaque);
    let mut wrong_body = fixed_body.clone();
    wrong_body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty = Ty::new_ref(
        tcx,
        tcx.lifetimes.re_erased,
        Ty::new_slice(tcx, tcx.types.u16),
        rustc_hir::Mutability::Mut,
    );
    let mut wrong_metadata = metadata_state.clone();
    let _ = engine.rvalue(
        fixed,
        &wrong_body,
        &mut wrong_metadata,
        &Rvalue::RawPtr(
            rustc_middle::mir::RawPtrKind::FakeForPtrMetadata,
            source_place,
        ),
    );
    assert!(wrong_metadata.memory.byte_copy_opaque);
    let mut cast_state = metadata_state.clone();
    cast_state.locals.push(Some(metadata));
    cast_state.addresses.push(None);
    let _ = engine.rvalue(
        fixed,
        fixed_body,
        &mut cast_state,
        &Rvalue::Cast(
            CastKind::PtrToPtr,
            Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(2))),
            Ty::new_ptr(tcx, tcx.types.u8, rustc_hir::Mutability::Not),
        ),
    );
    assert!(cast_state.memory.byte_copy_opaque);
    let mut branch = state.clone();
    branch.memory.byte_copy_opaque = true;
    assert!(
        engine
            .byte_copy_current_destination(&reference, &branch)
            .is_err()
    );
    assert!(
        engine
            .byte_copy_current_destination(&reference, &state)
            .is_ok()
    );
    branch = state.clone();
    branch.memory.incoming_byte_roots.clear();
    assert!(
        engine
            .byte_copy_current_destination(&reference, &branch)
            .is_err()
    );
    branch = state.clone();
    branch.memory[0] = None;
    assert!(
        engine
            .byte_copy_current_destination(&reference, &branch)
            .is_err()
    );
    branch = state.clone();
    branch.memory.missing_places.consume(0, vec![]).unwrap();
    assert!(
        engine
            .byte_copy_current_destination(&reference, &branch)
            .is_err()
    );
    for capacity in [
        symbolic::integer(&engine.terms, 5, bits, false),
        symbolic::integer(&engine.terms, 4, bits, true),
        symbolic::integer(&Context::default(), 4, bits, false),
    ] {
        branch = state.clone();
        let Value::Bytes { length, .. } = branch.memory[0].as_mut().unwrap() else {
            panic!("bytes")
        };
        **length = capacity;
        assert!(
            engine
                .byte_copy_current_destination(&reference, &branch)
                .is_err()
        );
    }
    branch = state.clone();
    let other = Context::default();
    let Value::Bytes { data, .. } = branch.memory[0].as_mut().unwrap() else {
        panic!("bytes")
    };
    *data = other
        .apply(
            Op::ConstArray { index_bits: bits },
            &[other.bit_vector(0, 8).unwrap()],
        )
        .unwrap();
    assert!(
        engine
            .byte_copy_current_destination(&reference, &branch)
            .is_err()
    );
    let mut shared = reference.clone();
    let Value::Reference { mutable, .. } = &mut shared else {
        panic!("reference")
    };
    *mutable = false;
    assert!(
        engine
            .byte_copy_current_destination(&shared, &state)
            .is_err()
    );
    let body = tcx.optimized_mir(fixed);
    let block = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                && let ty::FnDef(id, _) = func.ty(&body.local_decls, tcx).kind()
                && tcx.item_name(*id).as_str() == "copy_from_slice"
            {
                Some(block)
            } else {
                None
            }
        })
        .unwrap();
    let mut source_data = engine
        .terms
        .apply(
            Op::ConstArray { index_bits: bits },
            &[engine.terms.bit_vector(0, 8).unwrap()],
        )
        .unwrap();
    for (index, byte) in [17_u128, 19].into_iter().enumerate() {
        source_data = engine
            .terms
            .apply(
                Op::Store,
                &[
                    source_data,
                    engine.terms.bit_vector(index as u128, bits).unwrap(),
                    engine.terms.bit_vector(byte, 8).unwrap(),
                ],
            )
            .unwrap();
    }
    let source = Value::Bytes {
        length: Box::new(symbolic::integer(&engine.terms, 2, bits, false)),
        data: source_data,
    };
    let mut copied = state.clone();
    engine
        .finite_byte_copy(fixed, body, block, &reference, &source, &mut copied)
        .unwrap();
    let Value::Bytes { length, data } = copied.memory[0].as_ref().unwrap() else {
        panic!("bytes")
    };
    assert_eq!(length.integer().unwrap().0, capacity_term);
    for (index, expected) in [17_u128, 19, 0, 0].into_iter().enumerate() {
        let actual = engine
            .terms
            .apply(
                Op::Select,
                &[
                    data.clone(),
                    engine.terms.bit_vector(index as u128, bits).unwrap(),
                ],
            )
            .unwrap();
        let equal = engine
            .terms
            .apply(
                Op::Equal,
                &[actual, engine.terms.bit_vector(expected, 8).unwrap()],
            )
            .unwrap();
        assert!(!engine.feasible(&[symbolic::not(&equal)]).unwrap());
    }
    assert!(!state.memory.byte_copy_opaque);
    let mut failed = state.clone();
    failed.memory.byte_copy_opaque = true;
    assert!(
        engine
            .finite_byte_copy(fixed, body, block, &reference, &source, &mut failed)
            .is_err()
    );
    let Value::Bytes { data, .. } = failed.memory[0].as_ref().unwrap() else {
        panic!("bytes")
    };
    let Value::Bytes { data: original, .. } = state.memory[0].as_ref().unwrap() else {
        panic!("bytes")
    };
    assert_eq!(data, original);
    let mut wrong_body = body.clone();
    let TerminatorKind::Call { args, .. } =
        &mut wrong_body.basic_blocks_mut()[block].terminator_mut().kind
    else {
        panic!("call")
    };
    args[1].node = args[0].node.clone();
    let mut rejected = state.clone();
    assert!(
        engine
            .finite_byte_copy(
                fixed,
                &wrong_body,
                block,
                &reference,
                &source,
                &mut rejected
            )
            .is_err()
    );
    let mut wrong_source = source.clone();
    let Value::Bytes { data, .. } = &mut wrong_source else {
        panic!("bytes")
    };
    *data = engine
        .terms
        .apply(
            Op::Store,
            &[
                data.clone(),
                engine.terms.bit_vector(0, bits).unwrap(),
                engine.terms.bit_vector(20, 8).unwrap(),
            ],
        )
        .unwrap();
    assert!(
        engine
            .finite_byte_copy(fixed, body, block, &reference, &wrong_source, &mut rejected)
            .is_err()
    );
    wrong_body = body.clone();
    let TerminatorKind::Call { target, .. } =
        &mut wrong_body.basic_blocks_mut()[block].terminator_mut().kind
    else {
        panic!("call")
    };
    *target = None;
    assert!(
        engine
            .finite_byte_copy(
                fixed,
                &wrong_body,
                block,
                &reference,
                &source,
                &mut rejected
            )
            .is_err()
    );
    let Value::Bytes { data, .. } = rejected.memory[0].as_ref().unwrap() else {
        panic!("bytes")
    };
    assert_eq!(data, original);
}
