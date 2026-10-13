//! Actual whole-owner Call/Return and hostile current lineage controls.
use super::*;
use std::cell::{Cell, RefCell};
use std::path::Path;

std::thread_local! {
    static ENABLED: Cell<bool> = const { Cell::new(false) };
    static OBSERVED: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

struct Active(bool);
impl Active {
    fn enter() -> Self {
        Self(ENABLED.with(|flag| flag.replace(true)))
    }
}
impl Drop for Active {
    fn drop(&mut self) {
        ENABLED.with(|flag| flag.set(self.0));
    }
}

pub(super) fn actual_return_controls<'tcx>(
    engine: &Engine<'tcx>,
    selected: &Body<'tcx>,
    id: usize,
    ticket: &Ticket,
    result: &Return,
) {
    if !ENABLED.with(Cell::get) {
        return;
    }
    let backing = engine.mutable_u16_backing(id, &result.memory).unwrap();
    let hierarchy = backing.hierarchy.as_ref().unwrap();
    if hierarchy.owners.len() < 3 {
        return;
    }
    let depth = hierarchy.lineage_depth().unwrap();
    assert!((3..=MAX_INPUT_DEPTH).contains(&depth));
    let owner = hierarchy.owners.last().unwrap();
    engine
        .mutable_u16_frame_top(selected, &owner.frames)
        .unwrap();
    hierarchy.access(owner.lease).unwrap();
    for ancestor in &hierarchy.owners[..hierarchy.owners.len() - 1] {
        assert!(hierarchy.access(ancestor.lease).is_err());
        hierarchy.lifetime(ancestor.lease).unwrap();
    }
    assert!(hierarchy.access(0).is_err());
    let metadata = hierarchy.metadata(owner.lease).unwrap();
    hierarchy.observe(metadata).unwrap();
    assert!(
        hierarchy
            .observe(Metadata {
                epoch: metadata.epoch - 1,
                ..metadata
            })
            .is_err()
    );

    let mut wrong = result.memory.clone();
    Rc::make_mut(&mut wrong.mutable_u16)[id]
        .hierarchy
        .as_mut()
        .unwrap()
        .owners
        .last_mut()
        .unwrap()
        .parent = 0;
    assert!(
        engine
            .mutable_u16_backing(id, &wrong)
            .unwrap_err()
            .contains("hierarchy owner parent/lease/frame lineage differs")
    );
    let mut missing = result.memory.clone();
    missing
        .missing_places
        .consume(backing.allocation, Vec::new())
        .unwrap();
    assert!(engine.mutable_u16_backing(id, &missing).is_err());
    let mut no_namespace = result.memory.clone();
    no_namespace.mutable_hierarchy = None;
    assert_eq!(
        engine.mutable_u16_backing(id, &no_namespace).unwrap_err(),
        "hierarchy backing has no authenticated Memory namespace"
    );

    let mut pending = hierarchy.clone();
    let tip = Tip {
        frame: ticket.frame,
        statement: 1,
        local: 1,
    };
    pending
        .issue(owner.lease, tip, result.memory.storage_slots())
        .unwrap();
    assert!(pending.access(owner.lease).is_err());
    assert!(pending.release(ticket).is_err());
    let mut pending_wrong = pending.clone();
    pending_wrong.pending.as_mut().unwrap().parent = 0;
    assert!(pending_wrong.lineage_depth().is_err());

    let mut wrong_ticket = Ticket {
        origin: ticket.origin.clone(),
        lease: ticket.lease,
        issued_floor: ticket.issued_floor,
        epoch_floor: ticket.epoch_floor,
        prefix: ticket.prefix.clone(),
        frame: ticket.frame,
    };
    wrong_ticket.prefix.last_mut().unwrap().parent = u64::MAX;
    let mut released = hierarchy.clone();
    assert_eq!(
        released.release(&wrong_ticket).unwrap_err(),
        "returned Memory rollback/top/prefix"
    );
    let mut rollback = hierarchy.clone();
    rollback.epoch = ticket.epoch_floor - 1;
    assert_eq!(
        rollback.release(ticket).unwrap_err(),
        "returned Memory rollback/top/prefix"
    );
    let mut issued_rollback = hierarchy.clone();
    issued_rollback.issued = ticket.issued_floor - 1;
    assert!(
        issued_rollback
            .release(ticket)
            .unwrap_err()
            .contains("hierarchy owner parent/lease/frame lineage differs")
    );

    let held = Rc::new(selected.clone());
    let wrong_body = engine
        .mutable_u16_frame_top(&held, &owner.frames)
        .unwrap_err();
    assert!(wrong_body.contains("mutable u16 ancestor frame identity differs"));
    assert!(!wrong_body.contains("resource"));
    let expired = engine.mutable_u16_register_frame(&held).unwrap();
    drop(held);
    let mut expired_memory = result.memory.clone();
    Rc::make_mut(&mut expired_memory.mutable_u16)[id]
        .hierarchy
        .as_mut()
        .unwrap()
        .owners
        .last_mut()
        .unwrap()
        .frames = vec![expired];
    assert!(
        engine
            .mutable_u16_backing(id, &expired_memory)
            .unwrap_err()
            .contains("disabled hierarchy lineage differs")
    );

    let mut too_deep = hierarchy.clone();
    too_deep.owners.last_mut().unwrap().frames = vec![ticket.frame; MAX_INPUT_DEPTH];
    assert!(matches!(
        too_deep.lineage_depth(),
        Err(TransitionError::Resource(_))
    ));
    let mut exhausted = hierarchy.clone();
    assert!(matches!(
        exhausted.issue(
            owner.lease,
            Tip {
                frame: ticket.frame,
                statement: 1,
                local: 1
            },
            MAX_INPUT_VALUES
        ),
        Err(TransitionError::Resource(_))
    ));
    OBSERVED.with(|rows| rows.borrow_mut().push(depth));
}

#[test]
fn actual_deeper_whole_owner_frames_current_memory_and_prefix_controls() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut engine = super::super::nonzero_niches::test_engine(tcx);
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(*id) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "probe_root"
                })
                .unwrap();
            let root = engine
                .instantiated_body(ty::Instance::mono(tcx, id.to_def_id()))
                .unwrap();
            let (block, data) = root
                .basic_blocks
                .iter_enumerated()
                .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
                .unwrap();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } = &data.terminator().kind
            else {
                unreachable!()
            };
            let ty::FnDef(definition, generic) = func.ty(&root.local_decls, tcx).kind() else {
                unreachable!()
            };
            let instance = engine
                .resolve_function_item(*definition, generic.skip_binder())
                .unwrap();
            let mut memory = Memory::default();
            let mut conditions = Vec::new();
            let value = engine
                .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                .unwrap();
            let mut state = State {
                flow: activation_flow::Flow::Unarmed,
                locals: vec![None; root.local_decls.len()],
                addresses: vec![None; root.local_decls.len()],
                constant_receipts: constant_reference_receipts::Slots::default(),
                missing_places: Default::default(),
                conditions,
                memory,
            };
            state.locals[1] = Some(value);
            for statement in &data.statements {
                if let StatementKind::Assign(a) = &statement.kind
                    && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
                {
                    assert!(
                        engine
                            .mutable_u16_stage(&root, &mut state, a.0, &a.1, &statement.kind)
                            .unwrap()
                    );
                }
            }
            let moved_root = matches!(args[0].node, Operand::Move(_));
            if moved_root {
                let Operand::Move(source) = args[0].node else {
                    unreachable!()
                };
                let id = 0;
                let backing = engine.mutable_u16_backing(id, &state.memory).unwrap();
                engine
                    .mutable_hierarchy_move_root(&state, source, id, backing)
                    .unwrap();
                let mut alias = state.clone();
                alias.locals[0] = alias.locals[source.local.as_usize()].clone();
                assert_eq!(
                    engine
                        .mutable_hierarchy_move_root(&alias, source, id, backing)
                        .unwrap_err(),
                    "hierarchy moved Root has another executable carrier"
                );
                let mut allocation_alias = state.clone();
                allocation_alias
                    .memory
                    .push(allocation_alias.locals[source.local.as_usize()].clone());
                assert_eq!(
                    engine
                        .mutable_hierarchy_move_root(&allocation_alias, source, id, backing)
                        .unwrap_err(),
                    "hierarchy moved Root has another executable carrier"
                );
                let mut consumed = state.clone();
                consumed
                    .missing_places
                    .consume(source.local.as_usize(), Vec::new())
                    .unwrap();
                assert_eq!(
                    engine
                        .mutable_hierarchy_move_root(&consumed, source, id, backing)
                        .unwrap_err(),
                    "place initialization is unavailable after ownership consumption"
                );
                let mut wrong_body = (*root).clone();
                wrong_body.local_decls[source.local].ty = tcx.types.usize;
                let TerminatorKind::Call {
                    args: wrong_args, ..
                } = &wrong_body.basic_blocks[block].terminator().kind
                else {
                    unreachable!()
                };
                let mut wrong_type = state.clone();
                assert_eq!(
                    engine
                        .mutable_hierarchy_call_transaction(
                            &mut wrong_type,
                            super::super::mutable_u16_children::ChildCall {
                                body: &wrong_body,
                                block,
                                instance,
                                args: wrong_args,
                                destination: *destination,
                                target: *target,
                                stack: &[],
                                site: (
                                    wrong_body.source.def_id(),
                                    data.terminator().source_info.span
                                ),
                            },
                        )
                        .err()
                        .unwrap(),
                    "hierarchy source original type/address differs"
                );
                let mut wrong = state.clone();
                wrong.locals[source.local.as_usize()] = Some(Value::Unit);
                assert_eq!(
                    engine
                        .mutable_hierarchy_move_root(&wrong, source, id, backing)
                        .unwrap_err(),
                    "hierarchy moved Root lacks dormant unique scalar origin"
                );
            }
            let before = state.memory.mutable_u16[0].data.clone();
            OBSERVED.with(|rows| rows.borrow_mut().clear());
            let active = Active::enter();
            let results = engine
                .mutable_hierarchy_call(
                    &mut state,
                    super::super::mutable_u16_children::ChildCall {
                        body: &root,
                        block,
                        instance,
                        args,
                        destination: *destination,
                        target: *target,
                        stack: &[],
                        site: (root.source.def_id(), data.terminator().source_info.span),
                    },
                )
                .unwrap()
                .unwrap();
            drop(active);
            if moved_root {
                let Operand::Move(source) = args[0].node else {
                    unreachable!()
                };
                assert!(engine.local(&state, source.local.as_usize()).is_err());
                for result in &results {
                    let mut restored = state.clone();
                    restored.memory = result.memory.clone();
                    assert!(engine.local(&restored, source.local.as_usize()).is_err());
                }
                eprintln!("deeper scopes: actual Root Move retains consumed caller through Return");
            }
            assert!(!results.is_empty());
            assert!(
                results
                    .iter()
                    .any(|result| result.memory.mutable_u16[0].data != before)
            );
            for result in &results {
                let backing = engine.mutable_u16_backing(0, &result.memory).unwrap();
                let hierarchy = backing.hierarchy.as_ref().unwrap();
                assert!(hierarchy.owners.is_empty() && hierarchy.pending.is_none());
                assert!(hierarchy.issued >= 4);
                hierarchy.access(0).unwrap();
                assert!(hierarchy.access(hierarchy.issued).is_err());
            }
            let rows = OBSERVED.with(|rows| rows.borrow().clone());
            assert!(rows.contains(&3) && rows.contains(&4));
            for name in ["probe_level3", "probe_level2", "probe_level1", "probe_leaf"] {
                assert!(
                    engine
                        .proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == name)
                );
            }
            eprintln!("deeper scopes: actual depth3/4 Call/Return and prefix/Memory controls");
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!(
        "miren-deeper-scope-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/deeper_mutable_scopes.rs");
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert_eq!(sysroot.status.code(), Some(0));
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
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
