//! Actual local integer enum layout, zero partition and current getter controls.
use super::*;
use std::path::Path;

fn getter<'tcx>(tcx: TyCtxt<'tcx>, receiver: Ty<'tcx>) -> ty::Instance<'tcx> {
    let ty::Adt(def, args) = receiver.kind() else {
        unreachable!()
    };
    let selected = tcx
        .inherent_impls(def.did())
        .iter()
        .find_map(|implementation| {
            tcx.associated_items(*implementation)
                .in_definition_order()
                .find(|item| item.name() == rustc_span::Symbol::intern("get"))
                .map(|item| item.def_id)
        })
        .unwrap();
    ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), selected, args)
        .unwrap()
        .unwrap()
}

fn current_getter<'tcx>(engine: &Engine<'tcx>, certificate: &Certificate<'tcx>) {
    let instance = getter(engine.tcx, certificate.nonzero);
    engine
        .nonzero_get_body_certificate(instance, certificate.nonzero)
        .unwrap();
    let original = engine.instantiated_body(instance).unwrap();
    let mut wrong = original.as_ref().clone();
    wrong.local_decls[Local::from_usize(0)].ty = engine.tcx.types.bool;
    engine
        .bodies
        .borrow_mut()
        .insert(instance, std::rc::Rc::new(wrong));
    assert_eq!(
        engine
            .nonzero_get_body_certificate(instance, certificate.nonzero)
            .unwrap_err(),
        "NonZero getter body has unsupported receiver or CFG"
    );
    engine
        .bodies
        .borrow_mut()
        .insert(instance, original.clone());
    if matches!(
        certificate.primitive.kind(),
        ty::Int(ty::IntTy::Isize) | ty::Uint(ty::UintTy::Usize)
    ) {
        let fixed = match (
            engine.tcx.sess.target.pointer_width,
            certificate.facts.payload_signed(),
        ) {
            (32, false) => engine.tcx.types.u32,
            (64, false) => engine.tcx.types.u64,
            (32, true) => engine.tcx.types.i32,
            (64, true) => engine.tcx.types.i64,
            _ => unreachable!(),
        };
        assert_ne!(fixed, certificate.primitive);
        let mut wrong = original.as_ref().clone();
        wrong.local_decls[Local::from_usize(0)].ty = fixed;
        engine
            .bodies
            .borrow_mut()
            .insert(instance, std::rc::Rc::new(wrong));
        assert_eq!(
            engine
                .nonzero_get_body_certificate(instance, certificate.nonzero)
                .unwrap_err(),
            "NonZero getter body has unsupported receiver or CFG"
        );
    }
    engine.bodies.borrow_mut().insert(instance, original);
    engine
        .nonzero_get_body_certificate(instance, certificate.nonzero)
        .unwrap();
}

fn observations<'tcx>(engine: &Engine<'tcx>, certificate: &Certificate<'tcx>) {
    let context = &engine.terms;
    let bits = certificate.facts.payload_bits;
    let max = match bits {
        128 => u128::MAX,
        1..=127 => (1_u128 << bits) - 1,
        _ => unreachable!(),
    };
    let schema = schema(engine.tcx, certificate.clone()).unwrap();
    let index = context.bit_vector(0, certificate.bits).unwrap();
    for raw in [0, 1, 1_u128 << (bits - 1), max] {
        let scalar = context.bit_vector(raw, bits).unwrap();
        let array = context
            .apply(
                Op::ConstArray {
                    index_bits: certificate.bits,
                },
                std::slice::from_ref(&scalar),
            )
            .unwrap();
        let mut cursor = 0;
        let value = schema
            .observe(context, std::slice::from_ref(&array), &index, &mut cursor)
            .unwrap();
        assert_eq!(cursor, 1);
        let Value::Enum {
            discriminant,
            variants,
            ..
        } = value
        else {
            unreachable!()
        };
        let selected = if raw == 0 {
            1 - certificate.payload_variant
        } else {
            certificate.payload_variant
        };
        let expected = symbolic::integer(
            context,
            certificate.tags[selected],
            certificate.bits,
            certificate.signed,
        );
        let equal = context
            .apply(
                Op::Equal,
                &[
                    discriminant.integer().unwrap().0.clone(),
                    expected.integer().unwrap().0.clone(),
                ],
            )
            .unwrap();
        let query =
            Query::from_terms(context, &[], &symbolic::not(&equal), &BTreeMap::new()).unwrap();
        assert!(matches!(
            Solver::default().check_query(&query),
            Answer::Unsat
        ));
        let Value::Adt { fields, .. } = &variants[certificate.payload_variant] else {
            unreachable!()
        };
        let payload = &fields[0].1;
        let observed = engine.nonzero_niche_checked_value(certificate.nonzero, payload, &[]);
        if raw == 0 {
            assert!(observed.is_err());
        } else {
            let value = observed.unwrap();
            let (actual, actual_bits, signed) = value.integer().unwrap();
            assert_eq!(actual, scalar);
            assert_eq!(actual_bits, bits);
            assert_eq!(signed, certificate.facts.payload_signed());
            let mut wrong = payload.clone();
            let Value::Adt { fields, .. } = &mut wrong else {
                unreachable!()
            };
            let Value::Adt { fields, .. } = &mut fields[0].1 else {
                unreachable!()
            };
            let Value::Int { signed, .. } = &mut fields[0].1 else {
                unreachable!()
            };
            *signed = !*signed;
            assert!(
                engine
                    .nonzero_niche_checked_value(certificate.nonzero, &wrong, &[])
                    .is_err()
            );
        }
        let mut cursor = 0;
        assert_eq!(
            schema
                .observe(
                    &Context::default(),
                    std::slice::from_ref(&array),
                    &index,
                    &mut cursor,
                )
                .unwrap_err(),
            "NonZero niche observation current Context mismatch"
        );
        assert_eq!(cursor, 0);
    }
}

#[test]
fn actual_local_integer_niche_variant_orders_layout_values_and_getter_controls() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = test_engine(tcx);
            let mut checked = 0;
            for id in tcx.mir_keys(()).iter().copied() {
                if tcx.def_kind(id) != DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(id.to_def_id());
                let name = name.as_str();
                let suffix = if let Some(suffix) = name.strip_prefix("read_") {
                    suffix
                } else if let Some(suffix) = name.strip_prefix("reverse_") {
                    suffix
                } else {
                    continue;
                };
                let primitive = match suffix {
                    "u8" => tcx.types.u8,
                    "u16" => tcx.types.u16,
                    "u32" => tcx.types.u32,
                    "u64" => tcx.types.u64,
                    "u128" => tcx.types.u128,
                    "usize" => tcx.types.usize,
                    "i8" => tcx.types.i8,
                    "i16" => tcx.types.i16,
                    "i32" => tcx.types.i32,
                    "i64" => tcx.types.i64,
                    "i128" => tcx.types.i128,
                    "isize" => tcx.types.isize,
                    _ => unreachable!(),
                };
                let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                let ty::Ref(_, slice, rustc_hir::Mutability::Not) = signature.inputs()[0].kind()
                else {
                    unreachable!()
                };
                let ty::Slice(original) = slice.kind() else {
                    unreachable!()
                };
                let certificate = certify(tcx, *original).unwrap();
                assert_eq!(certificate.primitive, primitive);
                assert_eq!(
                    certificate.payload_variant,
                    usize::from(name.starts_with("read_"))
                );
                let ty::Adt(def, _) = original.kind() else {
                    unreachable!()
                };
                assert!(def.did().is_local());
                assert_ne!(tcx.lang_items().get(LangItem::Option), Some(def.did()));
                let mut nodes = 0;
                assert_eq!(shape(tcx, *original, 0, &mut nodes).unwrap().columns(), 1);
                assert_eq!(nodes, 6);
                assert!(shape(tcx, *original, 0, &mut 507).is_err());
                assert!(shape(tcx, *original, 13, &mut 0).is_err());
                assert!(facts_match(&certificate.facts));
                let mut wrong = certificate.facts.clone();
                wrong.niche_start = 1;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.payload_bits = if wrong.payload_bits == 32 { 16 } else { 32 };
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.payload_offset = 1;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.primitive_align *= 2;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.niche_first = wrong.untagged;
                assert!(!facts_match(&wrong));
                observations(&engine, &certificate);
                current_getter(&engine, &certificate);
                checked += 1;
            }
            assert_eq!(checked, 24);
            for name in ["extra_unknown", "drop_unknown"] {
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(*id) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap();
                let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                let ty::Ref(_, slice, _) = signature.inputs()[0].kind() else {
                    unreachable!()
                };
                let ty::Slice(original) = slice.kind() else {
                    unreachable!()
                };
                assert!(certify(tcx, *original).is_err());
            }
            eprintln!("local integer niche: 24 variant-order layouts and current storage controls");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let scratch = std::env::temp_dir().join(format!("miren-local-niche-{}", std::process::id()));
    std::fs::create_dir(&scratch).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/local_integer_nonzero_niches.rs");
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
                "--sysroot".into(),
                env!("MIREN_SYSROOT").into(),
                "--out-dir".into(),
                scratch.to_str().unwrap().into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut check = Check(false);
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
    std::fs::remove_dir_all(scratch).unwrap();
}
