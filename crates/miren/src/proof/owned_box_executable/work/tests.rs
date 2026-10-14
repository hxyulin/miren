//! Compiler denial controls. The fault budget applies only after a genuine private frame
//! has reached the selected service; it never issues an owner or substitutes a body.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Phase {
    Frame,
    Switch,
    Incoming,
    Requires,
    FinalArguments,
    Result,
}

struct Probe {
    phase: Phase,
    hit: bool,
    before: usize,
    masks: usize,
    publications: usize,
    frame_locals: usize,
}

thread_local! {
    static PROBE: std::cell::RefCell<Option<Probe>> = const {
        std::cell::RefCell::new(None)
    };
}

pub(super) fn near_limit(
    engine: &mut Engine<'_>,
    phase: Phase,
    kind: Option<Kind>,
    state: Option<&State>,
) {
    PROBE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(probe) = slot.as_mut() else { return };
        let expected = match phase {
            Phase::Frame
            | Phase::Incoming
            | Phase::Requires
            | Phase::FinalArguments
            | Phase::Result => Kind::Helper,
            Phase::Switch => Kind::BoxDrop,
        };
        if probe.phase == phase && kind == Some(expected) && !probe.hit {
            probe.hit = true;
            probe.before = engine.steps;
            probe.masks = state.map_or(0, |state| state.memory.missing_places.entries().len());
            // Explicit fault injection at an actual occurrence, not a default-budget claim.
            // The next prepaid operation must refuse before its guest-visible publication.
            engine.limits.max_steps = engine.steps;
        }
    });
}

fn contract_phase(phase: Option<u8>) -> Option<Phase> {
    match phase {
        None => None,
        Some(0) => Some(Phase::Requires),
        Some(1) => Some(Phase::FinalArguments),
        Some(2) => Some(Phase::Result),
        Some(_) => unreachable!("closed contract observation tag"),
    }
}

pub(super) fn contract_near_limit(engine: &mut Engine<'_>, phase: Option<u8>) {
    if let Some(phase) = contract_phase(phase) {
        near_limit(engine, phase, Some(Kind::Helper), None);
    }
}

pub(super) fn contract_publication(phase: Option<u8>) {
    if let Some(phase) = contract_phase(phase) {
        publication(phase);
    }
}

pub(super) fn frame_count(kind: Kind, locals: usize) {
    PROBE.with(|slot| {
        if let Some(probe) = slot.borrow_mut().as_mut()
            && probe.phase == Phase::Frame
            && kind == Kind::Helper
            && probe.hit
        {
            probe.frame_locals = locals;
        }
    });
}

pub(super) fn publication(phase: Phase) {
    PROBE.with(|slot| {
        if let Some(probe) = slot.borrow_mut().as_mut()
            && probe.phase == phase
            && probe.hit
        {
            probe.publications += 1;
        }
    });
}

#[test]
fn actual_box_frames_switches_and_incoming_graphs_refuse_before_unpaid_work() {
    struct Check {
        optimized: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let expected = if self.optimized {
                rustc_session::config::OptLevel::More
            } else {
                rustc_session::config::OptLevel::No
            };
            assert_eq!(tcx.sess.opts.optimize, expected);
            for phase in [
                Phase::Frame,
                Phase::Switch,
                Phase::Incoming,
                Phase::Requires,
                Phase::FinalArguments,
                Phase::Result,
            ] {
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == "work_probe_box"
                    })
                    .unwrap()
                    .to_def_id();
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
                        limits: miren::AnalysisLimits {
                            max_steps: 2_000_000,
                            ..Default::default()
                        },
                    },
                );
                PROBE.with(|slot| {
                    *slot.borrow_mut() = Some(Probe {
                        phase,
                        hit: false,
                        before: 0,
                        masks: 0,
                        publications: 0,
                        frame_locals: 0,
                    })
                });
                let error = engine.root(id, false).unwrap_err();
                let probe = PROBE.with(|slot| slot.borrow_mut().take().unwrap());
                assert!(probe.hit, "actual {phase:?} boundary not reached: {error}");
                assert_eq!(
                    engine.unknown_causes.borrow().get(&error),
                    Some(&UnknownCategory::ResourceLimit)
                );
                if phase == Phase::Frame {
                    assert!(
                        probe.frame_locals > 0,
                        "actual compiled frame count missing"
                    );
                }
                assert_eq!(
                    probe.publications, 0,
                    "{phase:?} crossed unpaid publication"
                );
                assert!(engine.steps > probe.before);
                let spent = engine.steps;
                assert!(pay(&mut engine, 1).is_err());
                assert_eq!(engine.steps, spent + 1);
                assert!(engine.proof.assumptions.is_empty());
                println!(
                    "BOX_WORK_DENIAL phase={phase:?} target={} opt={:?} steps={} masks={} \
                     frame_locals={}",
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                    engine.steps,
                    probe.masks,
                    probe.frame_locals
                );
            }
            rustc_driver::Compilation::Stop
        }
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effectful_zst_box_work.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut arguments = vec![
                "miren-box-work-probe".into(),
                path.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Coverflow-checks=yes".into(),
                "-Cpanic=abort".into(),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                arguments.extend(["--target".into(), target.into()]);
            }
            arguments.push(if optimized {
                "-Copt-level=2".into()
            } else {
                "-Copt-level=0".into()
            });
            rustc_driver::run_compiler(&arguments, &mut Check { optimized });
        }
    }
}

#[test]
fn original_arithmetic_helper_remains_source_limit_unknown_without_owner_publication() {
    struct Check {
        optimized: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let expected = if self.optimized {
                rustc_session::config::OptLevel::More
            } else {
                rustc_session::config::OptLevel::No
            };
            assert_eq!(tcx.sess.opts.optimize, expected);
            let id = tcx
                .mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "work_probe_box"
                })
                .unwrap()
                .to_def_id();
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
                    limits: miren::AnalysisLimits {
                        max_steps: 2_000_000,
                        ..Default::default()
                    },
                },
            );
            let error = engine.root(id, false).unwrap_err();
            assert_eq!(
                error,
                "IntoIter clone plan exceeds the existing 512-node limit"
            );
            assert_eq!(
                engine.unknown_causes.borrow().get(&error),
                Some(&UnknownCategory::ResourceLimit)
            );
            assert!(engine.owned_box_types.is_empty());
            assert!(engine.executable_box_sources.is_empty());
            assert_eq!(engine.next_owned_region, 0);
            assert!(engine.proof.assumptions.is_empty());
            println!(
                "BOX_SOURCE_LIMIT target={} opt={:?} owner_publication=0 reason={error}",
                tcx.sess.target.llvm_target, tcx.sess.opts.optimize
            );
            rustc_driver::Compilation::Stop
        }
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effectful_zst_box_work_source_limit.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut arguments = vec![
                "miren-box-source-limit-probe".into(),
                path.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Coverflow-checks=yes".into(),
                "-Cpanic=abort".into(),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                arguments.extend(["--target".into(), target.into()]);
            }
            arguments.push(if optimized {
                "-Copt-level=2".into()
            } else {
                "-Copt-level=0".into()
            });
            rustc_driver::run_compiler(&arguments, &mut Check { optimized });
        }
    }
}
