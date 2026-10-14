//! Genuine compiler roots and independent fixed-shape numeric planning oracles.
use super::*;

#[test]
fn actual_immutable_origin_planning_and_refusals() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            for name in [
                "tuple_plan",
                "array_struct_plan",
                "oversized_array_plan",
                "noncopy_array_plan",
            ] {
                let id = tcx
                    .hir_body_owners()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap()
                    .to_def_id();
                let instance = ty::Instance::mono(tcx, id);
                for denial in 0..2 {
                    let mut engine = nonzero_niches::test_engine(tcx);
                    engine.limits.max_steps = 2_000_000;
                    let body = engine.instantiated_body(instance).unwrap();
                    let mut memory = Memory::default();
                    let mut conditions = Vec::new();
                    let phase = engine.niche_root_inputs.begin(id).unwrap();
                    let input = prepare_root(&mut engine, id, &body, Local::from_usize(1), &memory);
                    if matches!(name, "oversized_array_plan" | "noncopy_array_plan") {
                        let error = input.err().unwrap();
                        if name == "oversized_array_plan" {
                            assert!(error.contains("array exceeds128"), "{error}");
                        } else {
                            let ty::Ref(_, slice, _) =
                                body.local_decls[Local::from_usize(1)].ty.kind()
                            else {
                                panic!("genuine mutable slice parameter");
                            };
                            let ty::Slice(original) = slice.kind() else {
                                panic!("genuine array slice element");
                            };
                            assert!(!tcx.type_is_copy_modulo_regions(
                                ty::TypingEnv::fully_monomorphized(),
                                *original
                            ));
                            assert!(error.contains("original shape is unsupported"), "{error}");
                        }
                        assert!(engine.niche_origins.is_empty());
                        assert!(engine.mutable_integer_types.is_empty());
                        assert!(memory.is_empty() && memory.mutable_u16.is_empty());
                        phase.close();
                        eprintln!(
                            "ORIGIN_PLAN_CONTROL name={name} denial={denial} target={} opt={:?}",
                            tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                        );
                        continue;
                    }
                    let mut input = input.unwrap().unwrap();
                    if denial == 1 {
                        input.deny_origin_plan = true;
                        let error = input.consume(&mut engine, &memory).err().unwrap();
                        assert!(
                            error.contains("niche codec shared execution step limit"),
                            "{error}"
                        );
                        assert_eq!(engine.steps.used(), engine.limits.max_steps + 1);
                        assert!(engine.niche_origins.is_empty());
                        assert!(engine.mutable_integer_types.is_empty());
                        assert!(memory.is_empty() && memory.mutable_u16.is_empty());
                    } else {
                        engine
                            .mutable_product_niche_input(input, &mut memory, &mut conditions)
                            .unwrap();
                        let origin = &engine.niche_origins[&0];
                        if name == "tuple_plan" {
                            assert_eq!(origin.compare_work(), 291);
                            assert_eq!(origin.value_work(37).unwrap(), 834 + 37);
                        } else {
                            // Seven nodes: array, two nonempty structs, two niches and two bools.
                            // Four columns and two niche receipts; names come from this fixture.
                            let ty::Ref(_, slice, _) =
                                body.local_decls[Local::from_usize(1)].ty.kind()
                            else {
                                panic!("genuine mutable slice parameter");
                            };
                            let ty::Slice(original) = slice.kind() else {
                                panic!("genuine slice element");
                            };
                            let ty::Array(element, _) = original.kind() else {
                                panic!("genuine array element");
                            };
                            let ty::Adt(def, _) = element.kind() else {
                                panic!("genuine struct element");
                            };
                            assert_eq!(tcx.def_path_str(def.did()), "OriginProduct");
                            let name_bytes = "OriginProduct".len();
                            assert_eq!(origin.compare_work(), 544 + 2 * name_bytes);
                            assert_eq!(origin.value_work(37).unwrap(), 1824 + 2 * name_bytes + 74);
                        }
                        let before = engine.steps.used();
                        for _ in 0..3 {
                            origin.compare_work();
                            origin.value_work(37).unwrap();
                        }
                        assert_eq!(engine.steps.used(), before);
                        engine
                            .niche_entry_scope(instance, &body, &memory, &conditions)
                            .unwrap();
                        let retained = memory.mutable_u16.clone();
                        engine.mutable_integer_types[0].alignment += 1;
                        assert!(engine.mutable_product_certificate(0).is_err());
                        assert!(
                            engine
                                .niche_certificate_work(0)
                                .unwrap_err()
                                .contains("failed niche execution")
                        );
                        assert!(Rc::ptr_eq(&retained, &memory.mutable_u16));
                    }
                    phase.close();
                    assert!(
                        prepare_root(&mut engine, id, &body, Local::from_usize(1), &memory)
                            .is_err()
                    );
                    eprintln!(
                        "ORIGIN_PLAN_CONTROL name={name} denial={denial} target={} opt={:?}",
                        tcx.sess.target.llvm_target, tcx.sess.opts.optimize
                    );
                }
            }
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/niche_origin_planning.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-origin-plan".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}
