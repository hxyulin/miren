//! Diagnostic constructor-only source load. No ownership or execution is issued.
use super::*;

#[test]
fn actual_box_constructor_source_planner_frontier() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
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
                limits: miren::AnalysisLimits {
                    max_steps: 60000,
                    ..Default::default()
                },
            };
            let explore = Engine::new(tcx, &config, options());
            let payload = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find_map(|id| {
                    let id = id.to_def_id();
                    (tcx.def_kind(id) == DefKind::AssocFn && tcx.item_name(id).as_str() == "drop")
                        .then(|| tcx.fn_sig(id).instantiate_identity().skip_binder().inputs()[0])
                        .and_then(|original| match original.kind() {
                            ty::Ref(_, child, _)
                                if matches!(child.kind(), ty::Adt(def,_)
                            if tcx.item_name(def.did()).as_str()=="Panicking") =>
                            {
                                Some(*child)
                            }
                            _ => None,
                        })
                })
                .unwrap();
            let constructor = explore
                .resolve_function_item(
                    tcx.get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
                        .unwrap(),
                    tcx.mk_args(&[payload.into()]),
                )
                .unwrap();
            let mut constructor_engine = Engine::new(
                tcx,
                &config,
                VerificationOptions {
                    all_failures: false,
                    induction: false,
                    startup: false,
                    isolated_startup: false,
                    async_entry: false,
                    limits: miren::AnalysisLimits {
                        max_steps: 2_000_000,
                        ..Default::default()
                    },
                },
            );
            let certificate =
                owned_box_constructor_source::prepare(&mut constructor_engine, constructor)
                    .unwrap();
            println!(
                "BOX_CONSTRUCTOR_PREPARED paid={}",
                constructor_engine.steps.used()
            );
            certificate.validate(&mut constructor_engine).unwrap();
            let mut pending = vec![constructor];
            let mut seen = std::collections::HashSet::new();
            while let Some(instance) = pending.pop() {
                if !seen.insert(instance) {
                    continue;
                }
                let mut engine = Engine::new(tcx, &config, options());
                let result = compiler_evidence::load_item(&mut engine, instance);
                println!(
                    "BOX_SOURCE_PLAN {instance:?} steps={} result={:?}",
                    engine.steps.used(),
                    result.as_ref().map(|e| e.current.local_decls.len())
                );
                let body = explore.instantiated_body(instance).unwrap();
                let indices: &[usize] = if instance == constructor
                    || (body.local_decls.len() == 9 && body.basic_blocks.len() == 5)
                {
                    &[0]
                } else if body.local_decls.len() == 41 && body.basic_blocks.len() == 23 {
                    &[8]
                } else {
                    &[]
                };
                for index in indices {
                    let TerminatorKind::Call {
                        func: Operand::Constant(function),
                        ..
                    } = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(*index)]
                        .terminator()
                        .kind
                    else {
                        panic!("actual source Call");
                    };
                    let ty::FnDef(id, args) = function.const_.ty().kind() else {
                        unreachable!()
                    };
                    pending.push(
                        explore
                            .resolve_function_item(*id, args.skip_binder())
                            .unwrap(),
                    );
                }
            }
            rustc_driver::Compilation::Stop
        }
    }
    let directory =
        std::env::temp_dir().join(format!("miren-box-source-plan-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let args = vec![
        "rustc".into(),
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/effect_free_zst_box_drop.rs"
        )
        .into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "-Cpanic=abort".into(),
        "-Coverflow-checks=yes".into(),
        "-Zmir-opt-level=0".into(),
        "-Copt-level=0".into(),
        "--out-dir".into(),
        directory.to_str().unwrap().into(),
        "--sysroot".into(),
        String::from_utf8(sysroot.stdout).unwrap().trim().into(),
    ];
    rustc_driver::run_compiler(&args, &mut Capture);
    std::fs::remove_dir_all(directory).unwrap();
}
