//! Compiler evidence for the bounded Unit Box constructor and drop protocol.
use super::*;

#[test]
fn selected_owned_box_compiler_templates_are_available() {
    struct Capture {
        output: std::path::PathBuf,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owned = tcx.lang_items().owned_box().expect("actual Box lang item");
            let core = tcx
                .lang_items()
                .sized_trait()
                .expect("actual core Sized")
                .krate;
            assert_ne!(core, owned.krate);
            let constructor = tcx
                .get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
                .expect("actual Box constructor diagnostic");
            let constructor = ty::Instance::try_resolve(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                constructor,
                tcx.mk_args(&[tcx.types.unit.into()]),
            )
            .unwrap()
            .unwrap();
            owned_box_templates::certify_unit_protocol(tcx, constructor)
                .expect("complete selected unit constructor protocol");
            let mut pending = Vec::new();
            for local in tcx.mir_keys(()).iter().copied() {
                if tcx.item_name(local.to_def_id()) == rustc_span::Symbol::intern("zero") {
                    pending.push(ty::Instance::mono(tcx, local.to_def_id()));
                }
            }
            let mut seen = std::collections::HashSet::new();
            let output = &self.output;
            std::fs::create_dir_all(output).unwrap();
            let mut ledger = Vec::new();
            while let Some(instance) = pending.pop() {
                if !seen.insert(instance) {
                    continue;
                }
                assert!(seen.len() <= 96, "bounded evidence traversal");
                if matches!(instance.def, ty::InstanceKind::Item(_))
                    && !tcx.is_mir_available(instance.def_id())
                {
                    ledger.push(format!("unavailable {instance:?}"));
                    continue;
                }
                if !matches!(
                    instance.def,
                    ty::InstanceKind::Item(_) | ty::InstanceKind::Shim(_)
                ) {
                    ledger.push(format!("non-MIR adapter {instance:?}"));
                    continue;
                }
                let is_owner_glue = match instance.def {
                    ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(t))) => {
                        matches!(t.kind(), ty::Adt(def, args)
                            if def.did() == owned && args.type_at(0).is_unit())
                    }
                    _ => false,
                };
                if pure_comparison_templates::owned_definition_key(instance.def_id())
                    == "DefId(core::mem::drop)"
                    || is_owner_glue
                {
                    owned_box_templates::certify_unit_protocol(tcx, instance)
                        .expect("complete selected unit owner drop protocol");
                }
                let generic = tcx.instance_mir(instance.def);
                if instance.def_id().krate == core || instance.def_id().krate == owned.krate {
                    let number = ledger.len();
                    match pure_comparison_templates::encode_template_with_alloc(
                        tcx,
                        generic,
                        core,
                        Some(owned.krate),
                    ) {
                        Ok(encoded) => {
                            std::fs::write(output.join(format!("body-{number}.mir")), encoded)
                                .unwrap();
                            ledger.push(format!("body-{number}.mir {instance:?}"));
                        }
                        Err(reason) => {
                            std::fs::write(
                                output.join(format!("refused-{number}.txt")),
                                format!("{generic:#?}"),
                            )
                            .unwrap();
                            ledger.push(format!("refused {instance:?}: {reason}"));
                        }
                    }
                }
                let body = instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(tcx, generic.clone()),
                    )
                    .unwrap();
                let mono = std::rc::Rc::new(body);
                if instance.def_id().is_local() {
                    let box_type = tcx
                        .fn_sig(constructor.def_id())
                        .instantiate(tcx, constructor.args)
                        .skip_binder()
                        .output();
                    for (block, data) in mono.basic_blocks.iter_enumerated() {
                        if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                            && matches!(func.ty(&mono.local_decls, tcx).kind(), ty::FnDef(id, _)
                                if pure_comparison_templates::owned_definition_key(*id)
                                    == "DefId(alloc::boxed::box_new_uninit)")
                        {
                            let proof = owned_box_constructors::certify_inlined(
                                tcx, &mono, block, box_type,
                            )
                            .expect("complete current inlined Unit transport");
                            assert!(proof.body.upgrade().is_some());
                            assert!(
                                owned_box_constructors::certify_inlined(
                                    tcx,
                                    &mono,
                                    block,
                                    tcx.types.unit,
                                )
                                .is_err()
                            );
                            let mut changed = (*mono).clone();
                            let seal = &mut changed.basic_blocks.as_mut()[proof.seal.block]
                                .statements[proof.seal.statement_index];
                            let StatementKind::Assign(assignment) = &mut seal.kind else {
                                unreachable!()
                            };
                            let Rvalue::Cast(_, _, target) = &mut assignment.1 else {
                                unreachable!()
                            };
                            *target = tcx.types.unit;
                            assert!(
                                owned_box_constructors::certify_inlined(
                                    tcx,
                                    &std::rc::Rc::new(changed),
                                    block,
                                    box_type,
                                )
                                .is_err()
                            );
                            let mut oversized = (*mono).clone();
                            let statements =
                                &mut oversized.basic_blocks.as_mut()[proof.seal.block].statements;
                            let mut extra = statements[0].clone();
                            extra.kind = StatementKind::Nop;
                            statements.resize(513, extra);
                            assert!(
                                owned_box_constructors::certify_inlined(
                                    tcx,
                                    &std::rc::Rc::new(oversized),
                                    block,
                                    box_type,
                                )
                                .is_err()
                            );
                        }
                    }
                }
                let body = &mono;
                for block in body.basic_blocks.iter() {
                    let next = match &block.terminator().kind {
                        TerminatorKind::Call { func, .. } => {
                            if let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() {
                                ty::Instance::try_resolve(
                                    tcx,
                                    ty::TypingEnv::fully_monomorphized(),
                                    *id,
                                    args.skip_binder(),
                                )
                                .unwrap()
                            } else {
                                None
                            }
                        }
                        TerminatorKind::Drop { place, .. } => {
                            Some(ty::Instance::resolve_drop_glue(
                                tcx,
                                place.ty(&body.local_decls, tcx).ty,
                            ))
                        }
                        _ => None,
                    };
                    if let Some(next) = next {
                        pending.push(next);
                    }
                }
            }
            std::fs::write(output.join("ledger.txt"), ledger.join("\n")).unwrap();
            rustc_driver::Compilation::Stop
        }
    }
    let persistent = std::env::var_os("MIREN_BOX_CAPTURE");
    let directory = persistent
        .as_ref()
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("miren-unit-box-certificate-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("fixture.rs");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\nextern crate alloc;\npub fn zero() {\n",
            "let owner = alloc::boxed::Box::new(());\n",
            "let _borrow = &*owner;\ncore::mem::drop(owner);\n}\n",
        ),
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let mut args = vec![
        "rustc".into(),
        source.to_str().unwrap().into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--crate-name=box_evidence".into(),
        "-Cpanic=abort".into(),
        format!(
            "-Zmir-opt-level={}",
            std::env::var("MIREN_BOX_CAPTURE_MIR_OPT").unwrap_or_else(|_| "0".into())
        ),
        format!(
            "-Copt-level={}",
            std::env::var("MIREN_BOX_CAPTURE_OPT").unwrap_or_else(|_| "0".into())
        ),
        "--out-dir".into(),
        directory.to_str().unwrap().into(),
        "--sysroot".into(),
        String::from_utf8(sysroot.stdout).unwrap().trim().into(),
    ];
    if let Ok(target) = std::env::var("MIREN_BOX_CAPTURE_TARGET") {
        args.extend(["--target".into(), target]);
    }
    rustc_driver::run_compiler(
        &args,
        &mut Capture {
            output: directory.clone(),
        },
    );
    if persistent.is_none() {
        std::fs::remove_dir_all(directory).unwrap();
    }
}
