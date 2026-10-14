//! Paid hostile observations at genuine postpublication lease and normal-return boundaries.
use super::*;

thread_local! {
    static ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static HITS: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

fn copy_invocation<'tcx>(
    engine: &mut Engine<'tcx>,
    original: &Invocation<'tcx>,
) -> Result<Invocation<'tcx>, String> {
    pay(engine, 32)?;
    Ok(Invocation {
        key: original.key,
        certificate: original.certificate,
        source: original.source.clone(),
        entry: original.entry.clone(),
        box_allocation: original.box_allocation,
        instance: original.instance,
        body: original.body.clone(),
        kind: original.kind,
    })
}

fn cache_payment(engine: &mut Engine<'_>) -> Result<(), String> {
    let bodies = engine.bodies.borrow().len();
    let signatures = engine.call_signatures.borrow().len();
    pay(engine, 8 + 3 * (bodies + signatures))
}

fn refusal(
    engine: &mut Engine<'_>,
    result: Result<(), String>,
    expected: &str,
    case: &str,
) -> Result<(), String> {
    let error = match result {
        Ok(()) => panic!("{case}: hostile gate unexpectedly succeeded"),
        Err(error) => error,
    };
    let categories = engine.unknown_causes.borrow().len();
    pay(
        engine,
        4 + categories + error.len() + expected.len() + case.len(),
    )?;
    assert_ne!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit),
        "{case}: budget denial is not authority refusal"
    );
    assert_eq!(error, expected, "{case}: wrong refusal boundary");
    println!(
        "BOX_LIFECYCLE_REFUSAL case={case} target={} opt={:?} reason={error}",
        engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.optimize
    );
    Ok(())
}

pub(super) fn leased<'tcx>(
    engine: &mut Engine<'tcx>,
    parent: &Invocation<'tcx>,
    child: &Invocation<'tcx>,
    state: &mut State,
    block: BasicBlock,
) -> Result<(), String> {
    if !ACTIVE.with(std::cell::Cell::get) || HITS.with(std::cell::Cell::get) != 0 {
        return Ok(());
    }
    HITS.with(|hits| hits.set(1));
    assert!(!engine.owned_box_types.is_empty());
    let generation = engine.next_owned_region;
    parent.check(engine, state)?;
    child.check(engine, state)?;
    let phase = state
        .memory
        .owned_region(parent.key, parent.certificate)?
        .execution
        .as_ref()
        .unwrap()
        .phase;
    let Phase::PayloadLeased(allocation) = phase else {
        panic!("actual payload lease boundary not reached");
    };
    assert!(
        state
            .memory
            .owned_region(parent.key, parent.certificate)?
            .payload
            .is_none()
    );
    assert!(
        state
            .memory
            .get(allocation)
            .and_then(Option::as_ref)
            .is_some()
    );
    state.memory.missing_places.check(allocation, &[])?;

    // Remove the actual upcoming payload glue cache entry, then restore that same Rc.
    cache_payment(engine)?;
    let original = engine.bodies.borrow_mut().remove(&child.instance).unwrap();
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "executable Box current Body/full signature source changed",
        "missing-child-current",
    )?;
    cache_payment(engine)?;
    engine
        .bodies
        .borrow_mut()
        .insert(child.instance, original.clone());
    // Replace the upcoming child with another retained actual compiler Body. No full Body
    // clone or unsupported auxiliary metadata allocation is performed by this control.
    pay(engine, 8)?;
    assert!(!Rc::ptr_eq(&parent.body, &original));
    let replacement = parent.body.clone();
    cache_payment(engine)?;
    engine
        .bodies
        .borrow_mut()
        .insert(child.instance, replacement.clone());
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "executable Box current Body/full signature source changed",
        "replaced-child-current",
    )?;
    cache_payment(engine)?;
    engine.bodies.borrow_mut().insert(child.instance, original);

    // Poison an actual upcoming helper's cached full signature; original source stays fixed.
    pay(engine, parent.source.bodies.len() + 4)?;
    let helper = parent
        .source
        .bodies
        .iter()
        .find(|source| source.kind == Kind::Helper)
        .unwrap();
    let signature = helper.signature.unwrap();
    pay(engine, 8 + 2 * signature.skip_binder().inputs().len())?;
    let wrong = signature.map_bound(|sig| {
        engine.tcx.mk_fn_sig(
            sig.inputs().iter().copied(),
            engine.tcx.types.bool,
            sig.fn_sig_kind,
        )
    });
    assert_ne!(wrong, signature);
    cache_payment(engine)?;
    let previous = engine
        .call_signatures
        .borrow_mut()
        .insert(helper.instance, wrong);
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "executable Box current Body/full signature source changed",
        "helper-signature",
    )?;
    cache_payment(engine)?;
    match previous {
        Some(previous) => {
            engine
                .call_signatures
                .borrow_mut()
                .insert(helper.instance, previous);
        }
        None => {
            engine.call_signatures.borrow_mut().remove(&helper.instance);
        }
    }

    let mut hostile = copy_invocation(engine, child)?;
    hostile.key = u64::MAX;
    let denied = hostile.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "owned region is unavailable or has different type identity",
        "wrong-invocation-key",
    )?;
    hostile.key = child.key;
    pay(engine, 4)?;
    hostile.entry = Rc::new(());
    let denied = hostile.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "Box invocation owner/type/entry identity differs",
        "wrong-invocation-entry",
    )?;
    pay(engine, 2)?;
    hostile.entry = child.entry.clone();
    hostile.body = replacement;
    let denied = hostile.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "Box invocation current full Instance/Body differs",
        "wrong-invocation-body",
    )?;
    pay(engine, 2)?;
    hostile.body = child.body.clone();
    hostile.instance = parent.instance;
    let denied = hostile.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "Box invocation current full Instance/Body differs",
        "wrong-invocation-instance",
    )?;

    pay(engine, 34)?;
    let context = std::mem::take(&mut engine.terms);
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "executable Box immutable source Context differs",
        "wrong-context",
    )?;
    engine.terms = context;

    prepay_memory_mutation(engine, &state.memory)?;
    let owner = state.memory[parent.box_allocation].take();
    state.memory[parent.box_allocation] = Some(Value::OwnedRegion {
        key: u64::MAX,
        certificate: parent.certificate,
        kind: symbolic::OwnedRegionKind::Owner,
    });
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "Box invocation tracked original owner differs",
        "wrong-tracked-owner",
    )?;
    prepay_memory_mutation(engine, &state.memory)?;
    state.memory[parent.box_allocation] = owner;
    prepay_memory_mutation(engine, &state.memory)?;
    state
        .memory
        .owned_region_mut(parent.key, parent.certificate)?
        .execution
        .as_mut()
        .unwrap()
        .phase = Phase::PayloadLeased(parent.box_allocation);
    let denied = child.check(engine, state).map(|_| ());
    refusal(
        engine,
        denied,
        "Box lease duplicates its payload owner",
        "wrong-active-lease",
    )?;
    prepay_memory_mutation(engine, &state.memory)?;
    state
        .memory
        .owned_region_mut(parent.key, parent.certificate)?
        .execution
        .as_mut()
        .unwrap()
        .phase = phase;

    // Re-enter the actual lease API while its initialized payload has already moved once.
    let denied = parent.lease_payload(engine, state, block).map(|_| ());
    refusal(
        engine,
        denied,
        "Box payload lease requires the actual once-only T Drop occurrence",
        "second-lease",
    )?;
    parent.check(engine, state)?;
    child.check(engine, state)?;
    assert_eq!(engine.next_owned_region, generation);
    println!(
        "BOX_LIFECYCLE phase=leased target={} opt={:?} owner_present=true",
        engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.optimize
    );
    Ok(())
}

pub(super) fn consumed<'tcx>(
    engine: &mut Engine<'tcx>,
    invocation: &Invocation<'tcx>,
    result: &mut Return,
) -> Result<(), String> {
    if !ACTIVE.with(std::cell::Cell::get) || HITS.with(std::cell::Cell::get) != 1 {
        return Ok(());
    }
    HITS.with(|hits| hits.set(2));
    let Phase::PayloadDropped(allocation) = result
        .memory
        .owned_region(invocation.key, invocation.certificate)?
        .execution
        .as_ref()
        .unwrap()
        .phase
    else {
        panic!("actual normal child consumption not reached");
    };
    assert!(
        result
            .memory
            .get(allocation)
            .and_then(Option::as_ref)
            .is_none()
    );
    let denied = result
        .memory
        .missing_places
        .check(allocation, &[])
        .map(|_| ());
    refusal(
        engine,
        denied,
        "place initialization is unavailable after ownership consumption",
        "consumed-payload-mask",
    )?;
    let denied = invocation.finish_payload(engine, result).map(|_| ());
    refusal(
        engine,
        denied,
        "Box payload normal return lacks its active lease",
        "second-consumption",
    )?;
    println!(
        "BOX_LIFECYCLE phase=consumed target={} opt={:?} replay_refused=true",
        engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.optimize
    );
    Ok(())
}

pub(super) fn retired<'tcx>(
    engine: &mut Engine<'tcx>,
    invocation: &Invocation<'tcx>,
    result: &mut Return,
) -> Result<(), String> {
    if !ACTIVE.with(std::cell::Cell::get) || HITS.with(std::cell::Cell::get) != 2 {
        return Ok(());
    }
    HITS.with(|hits| hits.set(3));
    pay(engine, result.memory.owned_regions.len() + 4)?;
    let region = result
        .memory
        .owned_regions
        .iter()
        .find(|region| region.key == invocation.key && region.certificate == invocation.certificate)
        .unwrap();
    assert!(!region.live && region.payload.is_none());
    assert!(matches!(
        region.execution.as_ref().unwrap().phase,
        Phase::Retired
    ));
    let denied = invocation.retire_consumed(engine, result).map(|_| ());
    refusal(
        engine,
        denied,
        "owned region is unavailable or has different type identity",
        "stale-retirement",
    )?;
    println!(
        "BOX_LIFECYCLE phase=retired target={} opt={:?} stale_refused=true",
        engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.optimize
    );
    Ok(())
}

#[test]
fn actual_postpublication_box_lifecycle_rejects_hostile_views_and_replay() {
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
                        && tcx.item_name(id.to_def_id()).as_str() == "helper_box"
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
            ACTIVE.with(|active| active.set(true));
            HITS.with(|hits| hits.set(0));
            let result = engine.root(id, false);
            ACTIVE.with(|active| active.set(false));
            assert!(result.is_ok(), "{result:?}");
            assert_eq!(HITS.with(std::cell::Cell::get), 3);
            assert!(engine.proof.assumptions.is_empty() && engine.proof.trusted_calls.is_empty());
            println!(
                "BOX_LIFECYCLE complete target={} opt={:?}",
                tcx.sess.target.llvm_target, tcx.sess.opts.optimize
            );
            rustc_driver::Compilation::Stop
        }
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effect_free_zst_box_drop.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut arguments = vec![
                "miren-box-lifecycle-probe".into(),
                path.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Coverflow-checks=yes".into(),
                "-Cpanic=abort".into(),
                "-o".into(),
                "/dev/null".into(),
                if optimized {
                    "-Copt-level=2".into()
                } else {
                    "-Copt-level=0".into()
                },
            ];
            if let Some(target) = target {
                arguments.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&arguments, &mut Check { optimized });
        }
    }
}
