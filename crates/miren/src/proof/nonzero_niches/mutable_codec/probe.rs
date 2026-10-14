//! Compiler-bound codec controls, not supported mutable owner outcomes.
use super::*;

fn site<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    original: Ty<'tcx>,
    kind: Use,
) -> Site<'tcx> {
    let body = engine.instantiated_body(instance).unwrap();
    let (block, statement) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .find_map(|(statement, actual)| {
                    let StatementKind::Assign(assignment) = &actual.kind else {
                        return None;
                    };
                    let place = match kind {
                        Use::Encode => assignment.0,
                        Use::Decode => match &assignment.1 {
                            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) => *place,
                            _ => return None,
                        },
                    };
                    (place.projection.len() >= 3
                        && place.ty(&body.local_decls, engine.tcx).ty == original)
                        .then_some((block, statement))
                })
        })
        .unwrap_or_else(|| {
            panic!(
                "actual niche instruction absent instance={instance:?} kind={kind:?} target={} \
                 opt={:?} original={original:?} current_body={body:#?}",
                engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.optimize
            )
        });
    Site {
        instance,
        block,
        statement,
        ordinal: 0,
        terminator: false,
        kind,
    }
}

#[test]
fn actual_compiler_bound_paid_niche_codec_roundtrip_and_refusals() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut count = 0;
            let mut name_controls = 0;
            for id in tcx.hir_body_owners() {
                if tcx.def_kind(id.to_def_id()) != DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(id.to_def_id()).to_string();
                if !name.starts_with("name_bound_")
                    && !name.starts_with("option_")
                    && !name.starts_with("empty_")
                    && !name.starts_with("payload_")
                {
                    continue;
                }
                let mut engine = super::super::test_engine(tcx);
                engine.limits.max_steps = 2_000_000;
                let instance = ty::Instance::mono(tcx, id.to_def_id());
                let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                let ty::Ref(_, slice, _) = signature.inputs()[0].kind() else {
                    panic!("slice reference")
                };
                let ty::Slice(product) = slice.kind() else {
                    panic!("original slice")
                };
                let ty::Tuple(fields) = product.kind() else {
                    panic!("original tuple")
                };
                let original = fields[0];
                if name.starts_with("name_bound_") {
                    let current = site(&engine, instance, original, Use::Encode);
                    let session = Rc::new(Session::default());
                    let result = prepare(&mut engine, &session, original, current, &[]);
                    if name == "name_bound_unicode" {
                        assert!(result.unwrap().is_some());
                        assert!(!session.0.get());
                    } else {
                        let error = result.err().unwrap();
                        assert!(error.contains("exceeds128 bytes"));
                        assert!(session.0.get());
                        assert!(engine.call_signatures.borrow().is_empty());
                    }
                    assert!(!engine.mutable_product_failed.get());
                    name_controls += 1;
                    continue;
                }
                let input_session = Rc::new(Session::default());
                let issued = input_descriptor::prepare(
                    &mut engine,
                    &input_session,
                    instance,
                    rustc_middle::mir::Local::from_usize(1),
                )
                .unwrap()
                .consume(&engine)
                .unwrap();
                assert_eq!(issued.descriptor().ty, *product);
                assert_eq!(issued.descriptor().leaves.len(), 2);
                assert_eq!(
                    issued.alignment(),
                    engine.static_layout(*product).unwrap().align.abi.bytes()
                );
                assert!(!input_session.0.get());
                for alignment in [false, true] {
                    let corrupt_session = Rc::new(Session::default());
                    let mut pending = input_descriptor::prepare(
                        &mut engine,
                        &corrupt_session,
                        instance,
                        rustc_middle::mir::Local::from_usize(1),
                    )
                    .unwrap();
                    pending.corrupt_for_test(alignment);
                    let error = pending.consume(&engine).err().unwrap();
                    assert!(error.contains("full descriptor/layout differs"));
                    assert!(corrupt_session.0.get());
                    assert!(!engine.mutable_product_failed.get());
                }
                let certificate = certify(tcx, original).unwrap();
                let width = certificate.facts.payload_bits;
                let pointer = u32::from(tcx.sess.target.pointer_width);
                let array = engine.fresh(Sort::Array(
                    Box::new(Sort::BitVec(pointer)),
                    Box::new(Sort::BitVec(width)),
                ));
                let index = engine.terms.bit_vector(1, pointer).unwrap();
                let session = Rc::new(Session::default());
                let decode = prepare(
                    &mut engine,
                    &session,
                    original,
                    site(
                        &super::super::test_engine(tcx),
                        instance,
                        original,
                        Use::Decode,
                    ),
                    &[],
                )
                .unwrap()
                .unwrap();
                let value = decode
                    .decode(
                        &engine,
                        site(&engine, instance, original, Use::Decode),
                        &[],
                        &array,
                        &index,
                    )
                    .unwrap();
                let encode = prepare(
                    &mut engine,
                    &session,
                    original,
                    site(
                        &super::super::test_engine(tcx),
                        instance,
                        original,
                        Use::Encode,
                    ),
                    &[],
                )
                .unwrap()
                .unwrap();
                let replacement = encode
                    .encode(
                        &engine,
                        site(&engine, instance, original, Use::Encode),
                        &[],
                        &value,
                    )
                    .unwrap();
                let raw = engine
                    .terms
                    .apply(Op::Select, &[array.clone(), index.clone()])
                    .unwrap();
                let equal = engine
                    .terms
                    .apply(Op::Equal, &[replacement.clone(), raw])
                    .unwrap();
                assert!(!engine.feasible(&[symbolic::not(&equal)]).unwrap());
                let stored = engine
                    .terms
                    .apply(Op::Store, &[array.clone(), index.clone(), replacement])
                    .unwrap();
                let other = engine.terms.bit_vector(0, pointer).unwrap();
                let old = engine
                    .terms
                    .apply(Op::Select, &[array, other.clone()])
                    .unwrap();
                let new = engine.terms.apply(Op::Select, &[stored, other]).unwrap();
                let equal = engine.terms.apply(Op::Equal, &[old, new]).unwrap();
                assert!(!engine.feasible(&[symbolic::not(&equal)]).unwrap());
                for registry in 0..2 {
                    let blocked_session = Rc::new(Session::default());
                    let current = site(&engine, instance, original, Use::Encode);
                    let prepared = prepare(&mut engine, &blocked_session, original, current, &[])
                        .unwrap()
                        .unwrap();
                    let error = match registry {
                        0 => {
                            let _held = engine.bodies.borrow_mut();
                            prepared.encode(&engine, current, &[], &value).unwrap_err()
                        }
                        1 => {
                            let _held = engine.call_signatures.borrow_mut();
                            prepared.encode(&engine, current, &[], &value).unwrap_err()
                        }
                        _ => unreachable!(),
                    };
                    assert!(error.contains("registry is mutably borrowed"));
                    assert!(blocked_session.0.get());
                    assert!(!engine.mutable_product_failed.get());
                    assert_eq!(
                        engine.unknown_causes.borrow().get(&error),
                        Some(&UnknownCategory::Semantics)
                    );
                }
                let mut denied = super::super::test_engine(tcx);
                denied.limits.max_steps = 0;
                let error =
                    super::super::super::mutable_hierarchy::products::niche_codec_signature(
                        &mut denied,
                        instance,
                    )
                    .unwrap_err();
                assert_eq!(
                    denied.unknown_causes.borrow().get(&error),
                    Some(&UnknownCategory::ResourceLimit)
                );
                assert!(!denied.mutable_product_failed.get());
                assert!(denied.call_signatures.borrow().is_empty());
                for failure in 0..6 {
                    let other_session = Rc::new(Session::default());
                    let expected = site(&engine, instance, original, Use::Encode);
                    let mut encode = prepare(&mut engine, &other_session, original, expected, &[])
                        .unwrap()
                        .unwrap();
                    let mut candidate = value.clone();
                    let mut current = expected;
                    let mut conditions = Vec::new();
                    match failure {
                        0 => {
                            let Value::Enum { variants, .. } = &candidate else {
                                unreachable!()
                            };
                            candidate = variants[certificate.payload_variant].clone();
                        }
                        1 => {
                            let Value::Enum { variants, .. } = &mut candidate else {
                                unreachable!()
                            };
                            let Value::Adt { name, .. } =
                                &mut variants[certificate.payload_variant]
                            else {
                                unreachable!()
                            };
                            *name = "Lookalike".into();
                        }
                        2 => current.kind = Use::Decode,
                        3 => conditions.push(engine.terms.boolean(true)),
                        4 => {
                            let Value::Enum { discriminant, .. } = &mut candidate else {
                                unreachable!()
                            };
                            let foreign = Context::default();
                            **discriminant = symbolic::integer(&foreign, 0, pointer, true);
                        }
                        5 => {
                            encode.retag = Some(match encode.retag.unwrap() {
                                rustc_middle::mir::WithRetag::Yes => {
                                    rustc_middle::mir::WithRetag::No
                                }
                                rustc_middle::mir::WithRetag::No => {
                                    rustc_middle::mir::WithRetag::Yes
                                }
                            });
                        }
                        _ => unreachable!(),
                    }
                    let error = encode
                        .encode(&engine, current, &conditions, &candidate)
                        .unwrap_err();
                    assert!(other_session.0.get());
                    assert_eq!(
                        engine.unknown_causes.borrow().get(&error),
                        Some(&UnknownCategory::Semantics)
                    );
                    assert!(!engine.mutable_product_failed.get());
                }
                let mut wrong = value.clone();
                let Value::Enum { discriminant, .. } = &mut wrong else {
                    panic!("correlated enum")
                };
                **discriminant = symbolic::integer(&engine.terms, 2, pointer, true);
                let encode = prepare(
                    &mut engine,
                    &session,
                    original,
                    site(
                        &super::super::test_engine(tcx),
                        instance,
                        original,
                        Use::Encode,
                    ),
                    &[],
                )
                .unwrap()
                .unwrap();
                let error = encode
                    .encode(
                        &engine,
                        site(&engine, instance, original, Use::Encode),
                        &[],
                        &wrong,
                    )
                    .unwrap_err();
                assert!(error.contains("symbolic tag validity"));
                assert!(session.0.get());
                let spent = engine.steps.used();
                assert!(
                    prepare(
                        &mut engine,
                        &session,
                        original,
                        site(
                            &super::super::test_engine(tcx),
                            instance,
                            original,
                            Use::Encode
                        ),
                        &[]
                    )
                    .is_err()
                );
                // Only the outside routing classifier may charge after a failed selected session.
                assert!(engine.steps.used() >= spent);
                let unselected = site(&engine, instance, original, Use::Encode);
                let noop = prepare(&mut engine, &session, tcx.types.u32, unselected, &[]).unwrap();
                assert!(noop.is_none());
                assert!(!engine.mutable_product_failed.get());
                assert!(engine.mutable_product_shape(*product).unwrap().is_none());
                assert!(engine.proof.assumptions.is_empty());
                eprintln!(
                    concat!(
                        "MUTABLE_NICHE_CODEC name={} width={} target={} ",
                        "opt={:?} codec_only=true"
                    ),
                    name, width, tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                );
                count += 1;
            }
            assert_eq!(count, 36);
            assert_eq!(name_controls, 2);
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
                "miren-niche-codec".into(),
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
                args.extend(["--target".into(), target.into()])
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}

#[test]
fn actual_compiler_niche_codec_source_diagnostic() {
    struct Capture(bool);
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = super::super::test_engine(tcx);
            let mut count = 0;
            for id in tcx.hir_body_owners() {
                if tcx.def_kind(id.to_def_id()) != DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(id.to_def_id()).to_string();
                if !["option_", "empty_", "payload_", "name_bound_"]
                    .iter()
                    .any(|prefix| name.starts_with(prefix))
                {
                    continue;
                }
                let instance = ty::Instance::mono(tcx, id.to_def_id());
                let body = engine.instantiated_body(instance).unwrap();
                eprintln!(
                    "NICHE_CODEC_SOURCE name={name} target={} opt={:?} \
                     signature={:?} original={:#?} current={body:#?}",
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                    tcx.fn_sig(id).instantiate_identity(),
                    tcx.instance_mir(instance.def)
                );
                for (block, data) in body.basic_blocks.iter_enumerated() {
                    for (statement, actual) in data.statements.iter().enumerate() {
                        if let StatementKind::Assign(assignment) = &actual.kind
                            && let Rvalue::Use(operand, retag) = &assignment.1
                        {
                            eprintln!(
                                "NICHE_CODEC_USE name={name} block={block:?} \
                                 statement={statement} operand={operand:?} retag={retag:?}"
                            );
                        }
                    }
                }
                count += 1;
            }
            assert_eq!(count, 38);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_niche_codec.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut capture = Capture(false);
            let mut args = vec![
                "miren-niche-codec-diagnostic".into(),
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
            rustc_driver::run_compiler(&args, &mut capture);
            assert!(capture.0);
        }
    }
}
