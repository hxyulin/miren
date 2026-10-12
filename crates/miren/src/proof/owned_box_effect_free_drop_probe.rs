//! Actual compiler body and owner lifecycle controls; no executable receiver is synthesized.
use super::*;
use std::path::Path;

#[test]
fn actual_effect_free_box_drop_original_current_and_retirement_controls() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let config = miren::ContractConfig::default();
            let mut engine = Engine::new(
                tcx,
                &config,
                VerificationOptions {
                    all_failures: false,
                    induction: false,
                    startup: false,
                    isolated_startup: false,
                    async_entry: false,
                    limits: miren::AnalysisLimits::default(),
                },
            );
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    matches!(tcx.def_kind(*id), rustc_hir::def::DefKind::Fn)
                        && tcx.item_name(id.to_def_id()).as_str() == "implicit"
                })
                .unwrap();
            let entry = ty::Instance::mono(tcx, id.to_def_id());
            let body = engine.instantiated_body(entry).unwrap();
            let (block, constructor) = body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(block, data)| {
                    let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                        return None;
                    };
                    let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                        return None;
                    };
                    if Some(*id) != tcx.get_diagnostic_item(rustc_span::Symbol::intern("box_new")) {
                        return None;
                    }
                    Some((
                        block,
                        ty::Instance::try_resolve(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            *id,
                            args.skip_binder(),
                        )
                        .unwrap()
                        .unwrap(),
                    ))
                })
                .unwrap();
            let payload = constructor.args.type_at(0);
            let certificate = certify_type(tcx, payload).unwrap();
            assert_eq!(certificate.layout.alignment(), 4096);
            let destructor = engine.instantiated_body(certificate.destructor).unwrap();
            // Actual compiler Unit return metadata is not a receiver/reference transport.
            let actual_return = &destructor.basic_blocks
                [rustc_middle::mir::BasicBlock::from_usize(0)]
            .statements[0];
            assert!(
                matches!(&actual_return.kind, StatementKind::Assign(assignment)
                if matches!(&assignment.1, Rvalue::Use(Operand::Constant(constant),
                    rustc_middle::mir::WithRetag::Yes)
                    if constant.const_.ty() == tcx.types.unit))
            );
            destructor_body(tcx, certificate.destructor, &destructor, &certificate).unwrap();
            let shim = ty::Instance::resolve_drop_glue(tcx, payload);
            let shim_body = engine.instantiated_body(shim).unwrap();
            assert_eq!(shim_body.local_decls.len(), 4);
            assert_eq!(
                shim_body.local_decls[rustc_middle::mir::Local::from_usize(3)].ty,
                tcx.types.unit
            );
            assert!(matches!(&shim_body.basic_blocks[
                rustc_middle::mir::BasicBlock::from_usize(0)].terminator().kind,
                TerminatorKind::Call {destination, ..}
                    if local(*destination, 3)));
            payload_glue(tcx, shim, &shim_body, &certificate).unwrap();
            engine
                .certify_owned_box_protocol(constructor, payload)
                .unwrap();
            let ty::Adt(def, _) = payload.kind() else {
                unreachable!()
            };
            let value = Value::Adt {
                name: tcx.def_path_str(def.did()),
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields: Vec::new().into(),
            };
            validate_value(tcx, &certificate, &value).unwrap();
            assert!(validate_value(tcx, &certificate, &Value::Unit).is_err());
            let mut wrong = value.clone();
            let Value::Adt { name, .. } = &mut wrong else {
                unreachable!()
            };
            *name = "impostor::Marker".into();
            assert!(validate_value(tcx, &certificate, &wrong).is_err());
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; body.local_decls.len()],
                addresses: vec![None; body.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                conditions: Vec::new(),
                memory: Memory::default(),
                missing_places: initialized_places::MissingPlaces::default(),
            };
            let owner = engine
                .owned_box_call(&body, block, constructor, &[value], &mut state)
                .unwrap()
                .unwrap();
            let original = engine.original_box_type(payload).unwrap();
            engine.validate_owned_region(&owner, &state.memory).unwrap();
            let before = state.memory.clone();
            let mut changed_source = destructor.as_ref().clone();
            changed_source.source.instance = entry.def;
            assert!(
                destructor_body(tcx, certificate.destructor, &changed_source, &certificate)
                    .is_err()
            );
            engine
                .bodies
                .borrow_mut()
                .insert(certificate.destructor, std::rc::Rc::new(changed_source));
            assert!(
                engine
                    .owned_box_drop(original, &owner, &mut state, id.to_def_id())
                    .is_err()
            );
            engine.validate_owned_region(&owner, &state.memory).unwrap();
            engine
                .bodies
                .borrow_mut()
                .insert(certificate.destructor, destructor.clone());

            let mut changed = destructor.as_ref().clone();
            changed.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(0)]
                .terminator_mut()
                .kind = TerminatorKind::Unreachable;
            assert!(destructor_body(tcx, certificate.destructor, &changed, &certificate).is_err());
            engine
                .bodies
                .borrow_mut()
                .insert(certificate.destructor, std::rc::Rc::new(changed));
            assert!(
                engine
                    .owned_box_drop(original, &owner, &mut state, id.to_def_id())
                    .is_err()
            );
            engine.validate_owned_region(&owner, &state.memory).unwrap();
            engine
                .bodies
                .borrow_mut()
                .insert(certificate.destructor, destructor.clone());
            let mut changed = destructor.as_ref().clone();
            changed.local_decls[rustc_middle::mir::Local::from_usize(1)].ty = tcx.types.unit;
            assert!(destructor_body(tcx, certificate.destructor, &changed, &certificate).is_err());
            let mut changed = shim_body.as_ref().clone();
            let TerminatorKind::Call { target, .. } = &mut changed.basic_blocks.as_mut()
                [rustc_middle::mir::BasicBlock::from_usize(0)]
            .terminator_mut()
            .kind
            else {
                unreachable!()
            };
            *target = Some(rustc_middle::mir::BasicBlock::from_usize(0));
            assert!(payload_glue(tcx, shim, &changed, &certificate).is_err());
            let owner_shim = ty::Instance::resolve_drop_glue(tcx, original);
            let owner_body = engine.instantiated_body(owner_shim).unwrap();
            let mut changed = owner_body.as_ref().clone();
            changed.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(2)]
                .terminator_mut()
                .kind = TerminatorKind::Unreachable;
            engine
                .bodies
                .borrow_mut()
                .insert(owner_shim, std::rc::Rc::new(changed));
            assert!(
                engine
                    .owned_box_drop(original, &owner, &mut state, id.to_def_id())
                    .is_err()
            );
            engine.validate_owned_region(&owner, &state.memory).unwrap();
            engine.bodies.borrow_mut().insert(owner_shim, owner_body);
            let fake_destructor = Certificate {
                original: payload,
                destructor: entry,
                layout: certificate.layout,
            };
            assert!(
                owned_box_templates::certify_effect_free_protocol(
                    &engine,
                    constructor,
                    &fake_destructor,
                )
                .is_err()
            );
            let wrong_alignment = Certificate {
                original: payload,
                destructor: certificate.destructor,
                layout: owned_box_payloads::ZeroLayout::for_type(tcx, tcx.types.unit).unwrap(),
            };
            assert!(
                owned_box_templates::certify_effect_free_protocol(
                    &engine,
                    constructor,
                    &wrong_alignment
                )
                .is_err()
            );
            let mut borrowed = owner.clone();
            let Value::OwnedRegion { kind, .. } = &mut borrowed else {
                unreachable!()
            };
            *kind = symbolic::OwnedRegionKind::BorrowedOwner;
            assert!(
                engine
                    .owned_box_drop(original, &borrowed, &mut state, id.to_def_id())
                    .is_err()
            );
            engine.validate_owned_region(&owner, &state.memory).unwrap();
            assert!(
                engine
                    .owned_box_drop(original, &owner, &mut state, id.to_def_id())
                    .unwrap()
            );
            assert!(
                engine
                    .owned_box_drop(original, &owner, &mut state, id.to_def_id())
                    .is_err()
            );
            assert!(engine.validate_owned_region(&owner, &before).is_ok());
            eprintln!(
                "effect-free Drop: actual type/Body/shim/owner, hostile cache and retirement"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let dir =
        std::env::temp_dir().join(format!("miren-effect-free-drop-tcx-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effect_free_zst_box_drop.rs");
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
