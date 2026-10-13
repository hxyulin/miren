//! Actual compiler full integer niche layouts, target widths and current getter controls.
use super::*;
use std::path::Path;

#[test]
fn actual_full_integer_layout_target_identity_and_current_getter_controls() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = test_engine(tcx);
            let pointer_bits = u32::from(tcx.sess.target.pointer_width);
            assert!(matches!(pointer_bits, 32 | 64));
            let mut checked = 0;
            for id in tcx.mir_keys(()).iter().copied() {
                if tcx.def_kind(id) != DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(id.to_def_id());
                let (bits, primitive, signed) = match name.as_str() {
                    "niche_u64" => (64, tcx.types.u64, false),
                    "niche_u128" => (128, tcx.types.u128, false),
                    "niche_usize" => (pointer_bits, tcx.types.usize, false),
                    "niche_i64" => (64, tcx.types.i64, true),
                    "niche_i128" => (128, tcx.types.i128, true),
                    "niche_isize" => (pointer_bits, tcx.types.isize, true),
                    _ => continue,
                };
                let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                let ty::Ref(_, slice, _) = signature.inputs()[0].kind() else {
                    unreachable!()
                };
                let ty::Slice(original) = slice.kind() else {
                    unreachable!()
                };
                let certificate = certify(tcx, *original).unwrap();
                assert_eq!(certificate.primitive, primitive);
                assert_eq!(certificate.facts.payload_bits, bits);
                assert_eq!(certificate.facts.payload_signed(), signed);
                assert_eq!(
                    super::super::nonzero_options::readonly_niche_integer_type(tcx, primitive),
                    Some((bits, signed))
                );
                assert!(
                    super::super::nonzero_options::readonly_niche_unsigned_bits(primitive)
                        .is_none()
                );
                let ty::Adt(inner, arguments) = certificate.inner.kind() else {
                    unreachable!()
                };
                let raw_pat = inner.non_enum_variant().fields[FieldIdx::from_usize(0)]
                    .ty(tcx, arguments)
                    .skip_norm_wip();
                assert!(matches!(raw_pat.kind(), ty::Pat(base, _) if *base == primitive));
                assert!(
                    super::super::nonzero_options::readonly_niche_integer_type(tcx, raw_pat)
                        .is_none()
                );
                let reference = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, primitive);
                assert!(
                    super::super::nonzero_options::readonly_niche_integer_type(tcx, reference)
                        .is_none()
                );
                assert_eq!(certificate.bits, pointer_bits);
                assert!(facts_match(&certificate.facts));
                let max = match bits {
                    128 => u128::MAX,
                    1..=127 => (1_u128 << bits) - 1,
                    _ => unreachable!(),
                };
                assert!(scalar_range(certificate.facts.primitive, bits, signed, 0));
                assert!(!scalar_range(certificate.facts.primitive, bits, !signed, 0));
                assert!(!scalar_range(certificate.facts.primitive, 0, signed, 0));
                let mut wrong = certificate.facts.clone();
                wrong.payload_bits = if bits == 32 { 64 } else { 32 };
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.niche_start = 1;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.inner_offset = 1;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.primitive_align *= 2;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                let BackendRepr::Scalar(Scalar::Initialized { value, .. }) = wrong.primitive else {
                    unreachable!()
                };
                wrong.primitive = BackendRepr::Scalar(Scalar::Initialized {
                    value,
                    valid_range: rustc_abi::WrappingRange {
                        start: 0,
                        end: max - 1,
                    },
                });
                assert!(!facts_match(&wrong));
                let schema = schema(tcx, certificate.clone()).unwrap();
                let index = engine.terms.bit_vector(0, pointer_bits).unwrap();
                for raw in [0, 1, 1_u128 << (bits - 1), max] {
                    let term = engine.terms.bit_vector(raw, bits).unwrap();
                    let array = engine
                        .terms
                        .apply(
                            Op::ConstArray {
                                index_bits: pointer_bits,
                            },
                            std::slice::from_ref(&term),
                        )
                        .unwrap();
                    let observed = schema
                        .observe(&engine.terms, std::slice::from_ref(&array), &index, &mut 0)
                        .unwrap();
                    let Value::Enum {
                        discriminant,
                        variants,
                        ..
                    } = observed
                    else {
                        unreachable!()
                    };
                    let Value::Adt { fields, .. } = &variants[certificate.payload_variant] else {
                        unreachable!()
                    };
                    let expected_tag = certificate.tags[if raw == 0 {
                        1 - certificate.payload_variant
                    } else {
                        certificate.payload_variant
                    }];
                    let (actual_tag, _, _) = discriminant.integer().unwrap();
                    let equal = engine
                        .terms
                        .apply(
                            Op::Equal,
                            &[
                                actual_tag.clone(),
                                engine.terms.bit_vector(expected_tag, pointer_bits).unwrap(),
                            ],
                        )
                        .unwrap();
                    let query = Query::from_terms(
                        &engine.terms,
                        &[],
                        &symbolic::not(&equal),
                        &BTreeMap::new(),
                    )
                    .unwrap();
                    assert!(matches!(
                        Solver::default().check_query(&query),
                        Answer::Unsat
                    ));
                    if raw != 0 {
                        let scalar = engine
                            .nonzero_niche_checked_value(certificate.nonzero, &fields[0].1, &[])
                            .unwrap();
                        let (actual, actual_bits, actual_signed) = scalar.integer().unwrap();
                        assert_eq!(actual, term);
                        assert_eq!((actual_bits, actual_signed), (bits, signed));
                    }
                    let foreign = Context::default();
                    assert_eq!(
                        schema
                            .observe(&foreign, std::slice::from_ref(&array), &index, &mut 0)
                            .unwrap_err(),
                        "NonZero niche observation current Context mismatch"
                    );
                }
                let ty::Adt(def, args) = certificate.nonzero.kind() else {
                    unreachable!()
                };
                let getter = tcx
                    .inherent_impls(def.did())
                    .iter()
                    .find_map(|implementation| {
                        tcx.associated_items(*implementation)
                            .in_definition_order()
                            .find(|item| item.name() == rustc_span::Symbol::intern("get"))
                            .map(|item| item.def_id)
                    })
                    .unwrap();
                let getter = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    getter,
                    args,
                )
                .unwrap()
                .unwrap();
                engine
                    .nonzero_get_body_certificate(getter, certificate.nonzero)
                    .unwrap();
                let current = engine.instantiated_body(getter).unwrap();
                let mut changed = current.as_ref().clone();
                changed.source.instance = ty::InstanceKind::Item(id.to_def_id());
                engine
                    .bodies
                    .borrow_mut()
                    .insert(getter, std::rc::Rc::new(changed));
                assert_eq!(
                    engine
                        .nonzero_get_body_certificate(getter, certificate.nonzero)
                        .unwrap_err(),
                    "signed NonZero getter current source Instance mismatch"
                );
                engine.bodies.borrow_mut().insert(getter, current.clone());
                let mut changed = current.as_ref().clone();
                changed.local_decls[Local::from_usize(0)].ty = tcx.types.bool;
                engine
                    .bodies
                    .borrow_mut()
                    .insert(getter, std::rc::Rc::new(changed));
                assert!(
                    engine
                        .nonzero_get_body_certificate(getter, certificate.nonzero)
                        .is_err()
                );
                if matches!(
                    primitive.kind(),
                    ty::Uint(ty::UintTy::Usize) | ty::Int(ty::IntTy::Isize)
                ) {
                    let fixed = match (pointer_bits, signed) {
                        (32, false) => tcx.types.u32,
                        (64, false) => tcx.types.u64,
                        (32, true) => tcx.types.i32,
                        (64, true) => tcx.types.i64,
                        _ => unreachable!(),
                    };
                    assert_ne!(fixed, primitive);
                    let mut changed = current.as_ref().clone();
                    changed.local_decls[Local::from_usize(0)].ty = fixed;
                    engine
                        .bodies
                        .borrow_mut()
                        .insert(getter, std::rc::Rc::new(changed));
                    assert_eq!(
                        engine
                            .nonzero_get_body_certificate(getter, certificate.nonzero)
                            .unwrap_err(),
                        "NonZero getter body has unsupported receiver or CFG"
                    );
                }
                engine.bodies.borrow_mut().insert(getter, current);
                engine
                    .nonzero_get_body_certificate(getter, certificate.nonzero)
                    .unwrap();
                let member_name = format!(
                    "actual_member_{}",
                    name.as_str().strip_prefix("niche_").unwrap()
                );
                let member = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(*id) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == member_name
                    })
                    .unwrap();
                let member_body = engine
                    .instantiated_body(ty::Instance::mono(tcx, member.to_def_id()))
                    .unwrap();
                let outer = member_body
                    .basic_blocks
                    .iter()
                    .find_map(|block| {
                        let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                            return None;
                        };
                        let ty::FnDef(id, args) = func.ty(&member_body.local_decls, tcx).kind()
                        else {
                            return None;
                        };
                        ty::Instance::try_resolve(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            *id,
                            args.skip_binder(),
                        )
                        .unwrap()
                    })
                    .unwrap();
                comparisons::signed_current_comparison_control(&engine, *original, outer);
                checked += 1;
            }
            assert_eq!(checked, 6);
            for original in [tcx.types.bool, tcx.types.char, tcx.types.f32, tcx.types.f64] {
                assert!(
                    super::super::nonzero_options::readonly_niche_integer_type(tcx, original)
                        .is_none()
                );
            }
            eprintln!(
                "full integer niche: six layouts width={pointer_bits}, max/Context/Body gates"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!(
        "miren-full-niche-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/full_integer_nonzero_niches.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let output = directory.join(format!("{}-{level}", target.unwrap_or("host")));
            std::fs::create_dir(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                fixture.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "--sysroot".into(),
                sysroot.trim().into(),
                "--out-dir".into(),
                output.to_str().unwrap().into(),
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
