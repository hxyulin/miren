//! Faults at actual Product services; probes neither issue Access nor replace guest execution.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::proof) enum Phase {
    EntrySnapshots,
    Bindings,
    BindingClone,
    FinalSnapshots,
    FinalInsert,
    ResultSnapshots,
    ResultInsert,
    Adopt,
    CallerAccess,
}

struct Probe {
    phase: Phase,
    deny: Option<usize>,
    hit: bool,
    active: bool,
    before: usize,
    payments: usize,
    publications: usize,
    access_at_begin: bool,
}

thread_local! {
    static PROBE: std::cell::RefCell<Option<Probe>> = const {
        std::cell::RefCell::new(None)
    };
}

pub(in crate::proof) fn begin(engine: &Engine<'_>, phase: Phase, memory: &Memory) {
    if !engine.mutable_product_hierarchy_active(memory) {
        return;
    }
    PROBE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(probe) = slot.as_mut()
            && probe.phase == phase
            && !probe.hit
        {
            probe.hit = true;
            probe.active = true;
            probe.before = engine.steps.used();
            probe.access_at_begin = engine.mutable_product_access.borrow().is_some();
        }
    });
}

pub(super) fn payment(engine: &mut Engine<'_>) {
    PROBE.with(|slot| {
        if let Some(probe) = slot.borrow_mut().as_mut()
            && probe.active
        {
            probe.payments += 1;
            if probe.deny == Some(probe.payments) {
                engine.limits.max_steps = engine.steps.used();
            }
        }
    });
}

pub(in crate::proof) fn publication(phase: Phase) {
    PROBE.with(|slot| {
        if let Some(probe) = slot.borrow_mut().as_mut()
            && probe.phase == phase
            && probe.active
        {
            probe.publications += 1;
            probe.active = false;
        }
    });
}

fn install(phase: Phase, deny: Option<usize>) {
    PROBE.with(|slot| {
        assert!(slot.borrow().is_none());
        *slot.borrow_mut() = Some(Probe {
            phase,
            deny,
            hit: false,
            active: false,
            before: 0,
            payments: 0,
            publications: 0,
            access_at_begin: false,
        });
    });
}

fn take() -> Probe {
    PROBE.with(|slot| slot.borrow_mut().take().unwrap())
}

#[test]
fn actual_product_contract_and_return_services_refuse_before_publication() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let id = tcx
                .hir_body_owners()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "root"
                })
                .unwrap()
                .to_def_id();
            let config = miren::ContractConfig::default();
            let fresh = || {
                Engine::new(
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
                )
            };
            for phase in [
                Phase::EntrySnapshots,
                Phase::Bindings,
                Phase::BindingClone,
                Phase::FinalSnapshots,
                Phase::FinalInsert,
                Phase::ResultSnapshots,
                Phase::ResultInsert,
                Phase::Adopt,
                Phase::CallerAccess,
            ] {
                let mut engine = fresh();
                install(phase, None);
                let result = engine.root(id, false);
                let baseline = take();
                assert!(
                    baseline.hit,
                    "actual {phase:?} service not reached: {result:?}"
                );
                result.unwrap();
                assert!(!engine.proof.obligations.is_empty());
                assert!(
                    engine
                        .proof
                        .obligations
                        .iter()
                        .all(|obligation| { obligation.status == ProofStatus::Proved })
                );
                assert_eq!(baseline.publications, 1, "{phase:?}");
                assert!(baseline.payments > 0, "{phase:?} has no genuine payments");
                assert!(engine.proof.assumptions.is_empty());
                assert!(engine.proof.trusted_calls.is_empty());
                assert!(engine.mutable_product_access.borrow().is_none());
                assert!(!engine.mutable_product_failed.get());
                assert!(
                    engine
                        .proof
                        .analyzed_bodies
                        .iter()
                        .any(|body| body.contains("scalar"))
                );
                for deny in 1..=baseline.payments {
                    let mut engine = fresh();
                    install(phase, Some(deny));
                    let result = engine.root(id, false);
                    let probe = take();
                    assert!(probe.hit, "{phase:?} payment{deny} did not reach service");
                    let error = result.expect_err("denied payment must abort actual execution");
                    assert_eq!(probe.payments, deny, "{phase:?}");
                    assert_eq!(
                        probe.publications, 0,
                        "{phase:?} crossed unpaid publication"
                    );
                    assert!(engine.steps.used() > probe.before);
                    assert!(engine.mutable_product_failed.get());
                    assert!(
                        engine
                            .mutable_product_access
                            .borrow()
                            .as_ref()
                            .is_none_or(|access| access.failed)
                    );
                    assert!(
                        engine
                            .unknown_causes
                            .borrow()
                            .values()
                            .any(|cause| { *cause == UnknownCategory::ResourceLimit }),
                        "{phase:?} payment{deny}: {error}"
                    );
                    engine.limits.max_steps = 2_000_000;
                    let spent = engine.steps.used();
                    assert!(
                        engine
                            .mutable_product_vector_work(&Memory::default(), 0)
                            .is_err()
                    );
                    assert_eq!(engine.steps.used(), spent);
                    assert!(engine.proof.assumptions.is_empty());
                    assert!(engine.proof.trusted_calls.is_empty());
                }
                eprintln!(
                    "PRODUCT_WORK_CONTROL phase={phase:?} payments={} denied={} access={} target={}",
                    baseline.payments,
                    baseline.payments,
                    baseline.access_at_begin,
                    tcx.sess.target.llvm_target,
                );
            }
            let wrong = tcx
                .hir_body_owners()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == "wrong"
                })
                .unwrap()
                .to_def_id();
            let mut engine = fresh();
            let _ = engine.root(wrong, false);
            assert!(engine.proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted && obligation.model.is_some()
            }));
            let mut engine = fresh();
            engine.limits.max_steps = 8192;
            assert!(engine.root(id, false).is_err());
            assert!(
                engine
                    .unknown_causes
                    .borrow()
                    .values()
                    .any(|cause| { *cause == UnknownCategory::ResourceLimit })
            );
            eprintln!(
                "PRODUCT_WORK_BASELINE actual_root_proved/wrong_refuted/default_resource_unknown"
            );
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_work.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut arguments = vec![
                "miren-product-work".into(),
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
                arguments.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&arguments, &mut check);
            assert!(check.0);
        }
    }
}
