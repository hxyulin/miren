//! Genuine compiler signed-width, negative representation and source coupling controls.
use super::*;
use std::path::Path;

#[test]
fn actual_signed_niche_layout_negative_payload_and_current_body_controls() {
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
                let (bits, primitive) = match name.as_str() {
                    "correlated8" => (8, tcx.types.i8),
                    "correlated16" => (16, tcx.types.i16),
                    "correlated32" => (32, tcx.types.i32),
                    _ => continue,
                };
                let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                let ty::Ref(_, slice, _) = signature.inputs()[0].kind() else {
                    unreachable!()
                };
                let ty::Slice(original) = slice.kind() else {
                    unreachable!()
                };
                let caller = engine
                    .instantiated_body(ty::Instance::mono(tcx, id.to_def_id()))
                    .unwrap();
                let payload_place = caller
                    .basic_blocks
                    .iter()
                    .flat_map(|block| block.statements.iter())
                    .find_map(|statement| {
                        let StatementKind::Assign(assignment) = &statement.kind else {
                            return None;
                        };
                        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) =
                            &assignment.1
                        else {
                            return None;
                        };
                        place
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Field(..)))
                            .then_some(*place)
                    })
                    .unwrap();
                authenticate_operand_path(tcx, &caller, payload_place).unwrap();
                let mut path = payload_place.projection.to_vec();
                let field = path
                    .iter_mut()
                    .find(|p| matches!(p, ProjectionElem::Field(..)))
                    .unwrap();
                let ProjectionElem::Field(_, ty) = field else {
                    unreachable!()
                };
                *ty = tcx.types.bool;
                let forged = Place {
                    local: payload_place.local,
                    projection: tcx.mk_place_elems(&path),
                };
                let refusal = authenticate_operand_path(tcx, &caller, forged).unwrap_err();
                assert!(!refusal.contains("budget"));
                let certificate = certify(tcx, *original).unwrap();
                assert_eq!(certificate.primitive, primitive);
                assert_eq!(certificate.facts.payload_bits, bits);
                assert!(certificate.facts.payload_signed());
                assert!(facts_match(&certificate.facts));
                let mut wrong = certificate.facts.clone();
                wrong.primitive = BackendRepr::Scalar(Scalar::Initialized {
                    value: Primitive::Int(
                        match bits {
                            8 => Integer::I8,
                            16 => Integer::I16,
                            32 => Integer::I32,
                            _ => unreachable!(),
                        },
                        false,
                    ),
                    valid_range: rustc_abi::WrappingRange {
                        start: 0,
                        end: (1_u128 << bits) - 1,
                    },
                });
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.niche_start = 1;
                assert!(!facts_match(&wrong));
                wrong = certificate.facts.clone();
                wrong.inner_offset = 1;
                assert!(!facts_match(&wrong));
                let schema = schema(tcx, certificate.clone()).unwrap();
                assert_eq!(
                    schema.payload_element(),
                    ScalarSliceElement::Integer { bits, signed: true }
                );
                let index = engine.terms.bit_vector(0, certificate.bits).unwrap();
                let negative = engine.terms.bit_vector(1_u128 << (bits - 1), bits).unwrap();
                let array = engine
                    .terms
                    .apply(
                        Op::ConstArray {
                            index_bits: certificate.bits,
                        },
                        std::slice::from_ref(&negative),
                    )
                    .unwrap();
                let observed = schema
                    .observe(&engine.terms, std::slice::from_ref(&array), &index, &mut 0)
                    .unwrap();
                let Value::Enum { variants, .. } = &observed else {
                    unreachable!()
                };
                let Value::Adt { fields, .. } = &variants[certificate.payload_variant] else {
                    unreachable!()
                };
                let nonzero = &fields[0].1;
                let scalar = engine
                    .nonzero_niche_checked_value(certificate.nonzero, nonzero, &[])
                    .unwrap();
                let (actual, actual_bits, signed) = scalar.integer().unwrap();
                assert_eq!(actual, negative);
                assert_eq!(actual_bits, bits);
                assert!(signed);
                let foreign = Context::default();
                assert_eq!(
                    schema
                        .observe(&foreign, std::slice::from_ref(&array), &index, &mut 0)
                        .unwrap_err(),
                    "NonZero niche observation current Context mismatch"
                );
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
                changed.local_decls[Local::from_usize(0)].ty = tcx.types.u32;
                engine
                    .bodies
                    .borrow_mut()
                    .insert(getter, std::rc::Rc::new(changed));
                assert!(
                    engine
                        .nonzero_get_body_certificate(getter, certificate.nonzero)
                        .is_err()
                );
                engine.bodies.borrow_mut().insert(getter, current);
                engine
                    .nonzero_get_body_certificate(getter, certificate.nonzero)
                    .unwrap();
                checked += 1;
            }
            assert_eq!(checked, 3);
            assert_eq!(
                super::super::nonzero_options::readonly_niche_unsigned_bits(tcx.types.i16),
                None
            );
            for refused in [
                tcx.types.bool,
                tcx.types.char,
                tcx.types.i64,
                tcx.types.isize,
            ] {
                assert!(
                    super::super::nonzero_options::readonly_niche_integer_type(refused).is_none()
                );
            }
            let member = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "actual_member16"
                })
                .unwrap();
            let member = ty::Instance::mono(tcx, member.to_def_id());
            let member_body = engine.instantiated_body(member).unwrap();
            let outer = member_body
                .basic_blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, args) = func.ty(&member_body.local_decls, tcx).kind() else {
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
            let ty::Ref(_, slice, _) = member_body.local_decls[Local::from_usize(1)].ty.kind()
            else {
                unreachable!()
            };
            let ty::Slice(original) = slice.kind() else {
                unreachable!()
            };
            comparisons::signed_current_comparison_control(&engine, *original, outer);
            eprintln!(
                "signed niche: three widths, negative bits, layout/Context/getter/current law"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let dir = std::env::temp_dir().join(format!("miren-signed-niche-tcx-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/signed_nonzero_niche_slices.rs");
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert_eq!(sysroot.status.code(), Some(0));
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
                dir.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout.clone())
                    .unwrap()
                    .trim()
                    .into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut check = Check(false);
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
