//! Paid hostile observations of a genuine constructor occurrence before any owner publication.
use super::*;

thread_local! {
    static ARMED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static HITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(super) fn controls<'tcx>(
    engine: &mut Engine<'tcx>,
    mut receipt: Occurrence<'tcx>,
    body: &Rc<Body<'tcx>>,
    block: BasicBlock,
    callee: ty::Instance<'tcx>,
    value: &Value,
    state: &mut State,
) -> Result<Occurrence<'tcx>, String> {
    if !ARMED.with(|armed| armed.replace(false)) {
        return Ok(receipt);
    }
    HITS.with(|hits| hits.set(hits.get() + 1));
    assert!(state.locals[receipt.local].is_some());
    assert!(state.missing_places.check(receipt.local, &[]).is_err());
    assert!(engine.owned_box_types.is_empty());
    assert!(state.memory.owned_regions.is_empty());
    let generation = engine.next_owned_region;
    receipt.after(engine, body, block, callee, value, state)?;

    // The exact actual caller cannot recreate an initialized receipt after its Move.
    assert!(
        engine
            .box_occurrence_before(body, block, callee, state)
            .is_err()
    );

    let masks = array_iterator_constructors::box_clone_masks(engine, &state.missing_places)?;
    pay(engine, state.missing_places.entries().len() + 4)?;
    state.missing_places.initialize(receipt.local, &[]);
    assert!(
        receipt
            .after(engine, body, block, callee, value, state)
            .is_err()
    );
    state.missing_places = masks;

    // The actual evaluated payload stays untouched while retained inaccessible bytes change.
    let residual = state.locals[receipt.local].take();
    pay(engine, 4)?;
    state.locals[receipt.local] = Some(Value::Bool(engine.terms.boolean(false)));
    assert!(
        receipt
            .after(engine, body, block, callee, value, state)
            .is_err()
    );
    state.locals[receipt.local] = residual;

    pay(engine, 34)?;
    let context = receipt.context.clone();
    receipt.context = Context::default().boolean(true);
    assert!(
        receipt
            .after(engine, body, block, callee, value, state)
            .is_err()
    );
    receipt.context = context;

    pay(engine, 2)?;
    let original_state = receipt.state;
    receipt.state = std::ptr::null();
    assert!(
        receipt
            .after(engine, body, block, callee, value, state)
            .is_err()
    );
    receipt.state = original_state;

    let work = array_iterator_constructors::box_receipt_current_clone_work(engine, body)?;
    pay(engine, work + 8)?;
    let replacement = Rc::new(body.as_ref().clone());
    assert!(
        receipt
            .after(engine, &replacement, block, callee, value, state)
            .is_err()
    );
    let entries = engine.bodies.borrow().len();
    pay(engine, 8 + 3 * entries)?;
    let previous = engine
        .bodies
        .borrow_mut()
        .insert(receipt.caller, replacement);
    assert!(
        receipt
            .after(engine, body, block, callee, value, state)
            .is_err()
    );
    let entries = engine.bodies.borrow().len();
    pay(engine, 8 + 3 * entries)?;
    engine
        .bodies
        .borrow_mut()
        .insert(receipt.caller, previous.unwrap());

    receipt.after(engine, body, block, callee, value, state)?;
    assert!(engine.owned_box_types.is_empty());
    assert!(state.memory.owned_regions.is_empty());
    assert_eq!(engine.next_owned_region, generation);
    println!(
        "BOX_RECEIPT_CONTROLS target={} retained=true consumed=true owner_publication=0",
        engine.tcx.sess.target.llvm_target
    );
    // A deliberate test-only stop prevents these source/receipt controls from being
    // interpreted as executable constructor/Drop behavior or application success.
    Err(engine.categorized_error(
        UnknownCategory::Semantics,
        "test-only actual Box receipt controls complete before owner publication".into(),
    ))
}

#[test]
fn actual_consumed_constructor_receipt_preserves_residual_and_rejects_hostile_views() {
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
            println!(
                "BOX_RECEIPT_PROFILE target={} opt={:?}",
                tcx.sess.target.llvm_target, tcx.sess.opts.optimize
            );
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
            ARMED.with(|armed| armed.set(true));
            HITS.with(|hits| hits.set(0));
            let error = engine.root(id, false).unwrap_err();
            assert_eq!(HITS.with(std::cell::Cell::get), 1);
            assert!(
                error.contains("receipt controls complete before owner publication"),
                "{error}"
            );
            assert!(engine.owned_box_types.is_empty());
            assert_eq!(engine.next_owned_region, 0);
            assert!(engine.proof.assumptions.is_empty());
            rustc_driver::Compilation::Stop
        }
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/effectful_zst_box_work.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut arguments = vec![
                "miren-box-receipt-probe".into(),
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
