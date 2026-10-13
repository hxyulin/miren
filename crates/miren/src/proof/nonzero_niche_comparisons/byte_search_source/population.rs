//! Body-derived population-count fact, never a raw-reference or full-search certificate.
use super::*;
use crate::solver::{Answer, Query, Solver};
use miren::smt::{Context, Op, Sort};

// Source guards keep actual current Body and signature evidence immutable through consumption.
struct PopulationCertificate<'a, 'tcx> {
    source: SourceObservation<'a, 'tcx>,
    query: Query,
}

fn direct(place: Place<'_>, local: usize) -> bool {
    place.local == Local::from_usize(local) && place.projection.is_empty()
}

fn shape(source: &mut SourceObservation<'_, '_>) -> Result<u32, Failure> {
    source.work.charge(48)?;
    let engine = source.engine;
    let signature = source
        .signatures
        .get(&source.instance)
        .ok_or("population source lost its actual signature")?
        .skip_binder();
    let body = source
        .bodies
        .get(&source.instance)
        .ok_or("population source lost its actual Body")?;
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    if !matches!(bits, 32 | 64)
        || !source.instance.args.is_empty()
        || signature.inputs() != [engine.tcx.types.usize]
        || signature.output() != engine.tcx.types.u32
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || body.arg_count != 1
        || body.local_decls.len() != 2
        || body.basic_blocks.len() != 2
        || source.helpers.len() != 1
        || body.local_decls[Local::from_usize(0)].ty != engine.tcx.types.u32
        || body.local_decls[Local::from_usize(1)].ty != engine.tcx.types.usize
        || !matches!(source.helpers[0].kind, HelperKind::PopulationCount)
    {
        return Err("population wrapper original type/helper inventory differs".into());
    }
    let first = &body.basic_blocks[rustc_middle::mir::START_BLOCK];
    let last = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(1)];
    if first.is_cleanup
        || last.is_cleanup
        || !first.statements.is_empty()
        || !last.statements.is_empty()
        || !matches!(last.terminator().kind, TerminatorKind::Return)
    {
        return Err("population wrapper complete block/Return shape differs".into());
    }
    let TerminatorKind::Call {
        args,
        destination,
        target,
        unwind,
        call_source,
        ..
    } = &first.terminator().kind
    else {
        return Err("population wrapper does not execute its actual primitive Call".into());
    };
    if args.len() != 1
        || !matches!(&args[0].node, Operand::Copy(place) if direct(*place, 1))
        || !direct(*destination, 0)
        || *target != Some(rustc_middle::mir::BasicBlock::from_usize(1))
        || *unwind != rustc_middle::mir::UnwindAction::Unreachable
        || *call_source != rustc_middle::mir::CallSource::Normal
    {
        return Err("population wrapper actual operand/result/continuation differs".into());
    }
    Ok(bits)
}

fn mathematical_query(bits: u32, limits: miren::AnalysisLimits) -> Result<Query, Failure> {
    let context = Context::default();
    let mut valid = context.boolean(true);
    let input = context.symbol(0, Sort::BitVec(bits))?;
    let result = crate::proof::builtins::population_count_expression(&context, &input, bits)?;
    // Independent observable facts used by byte alignment; no source address is assumed.
    let maximum = u128::MAX >> (128 - bits);
    for (value, expected) in [
        (0, 0),
        (1, 1),
        (u128::from(bits / 8), 1),
        (maximum, u128::from(bits)),
    ] {
        let selected = context.bit_vector(value, bits)?;
        let matches = context.apply(Op::Equal, &[input.clone(), selected])?;
        let outside = context.apply(Op::Not, &[matches])?;
        let expected = context.bit_vector(expected, 32)?;
        let correct = context.apply(Op::Equal, &[result.clone(), expected])?;
        let implication = context.apply(Op::Or, &[outside, correct])?;
        valid = context.apply(Op::And, &[valid, implication])?;
    }
    let failure = context.apply(Op::Not, &[valid])?;
    Query::from_terms_with_limits(&context, &[], &failure, &Default::default(), limits)
        .map_err(Into::into)
}

fn certify<'a, 'tcx>(
    mut source: SourceObservation<'a, 'tcx>,
) -> Result<PopulationCertificate<'a, 'tcx>, Failure> {
    let bits = shape(&mut source)?;
    // Four target-width expression trees, vector construction/relocation and query services.
    source.work.charge(192 + 64 * bits as usize)?;
    let engine = source.engine;
    let query = mathematical_query(bits, engine.limits)?;
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "population certificate reached existing root deadline".into(),
        });
    }
    let answer = Solver::with_limits(engine.limits).check_query(&query);
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "population certificate reached existing root deadline".into(),
        });
    }
    match answer {
        Answer::Unsat => Ok(PopulationCertificate { source, query }),
        Answer::Sat(_) => Err("population helper observable facts are refuted".into()),
        Answer::Unknown(reason) => Err(Failure {
            category: UnknownCategory::Solver,
            reason: format!("population helper observable facts remain unknown: {reason}"),
        }),
    }
}

pub(super) fn reject(mut source: SourceObservation<'_, '_>) -> Result<(), String> {
    let engine = source.engine;
    source
        .work
        .charge(6)
        .map_err(|error| engine.categorized_error(error.category, error.reason))?;
    let candidate = source
        .signatures
        .get(&source.instance)
        .is_some_and(|signature| {
            let signature = signature.skip_binder();
            signature.inputs() == [engine.tcx.types.usize]
                && signature.output() == engine.tcx.types.u32
        });
    if !candidate {
        return word::reject(source);
    }
    let certificate =
        certify(source).map_err(|error| engine.categorized_error(error.category, error.reason))?;
    let _query = certificate.query;
    let _source = certificate.source;
    Err(engine.categorized_error(
        UnknownCategory::Semantics,
        "authenticated population fact does not establish complete byte search".into(),
    ))
}

#[cfg(test)]
pub(super) fn compiler_controls<'tcx>(
    engine: &Engine<'tcx>,
    selected: ty::Instance<'tcx>,
    alternate: ty::Instance<'tcx>,
    retained: bool,
) {
    if !retained {
        let error = certify(observe_inner(engine, selected, 0, 0).unwrap())
            .err()
            .expect("ordinary prebuilt core unexpectedly matched retained wrapper shape");
        eprintln!("POPULATION ordinary-prebuilt-source-refusal: {error:?}");
        assert_eq!(error.category, UnknownCategory::Semantics);
        assert_eq!(
            error.reason,
            "population wrapper actual operand/result/continuation differs"
        );
        return;
    }
    let certificate = certify(observe_inner(engine, selected, 0, 0).unwrap()).unwrap();
    eprintln!("POPULATION ACTUAL QUERY\n{}", certificate.query.text());
    assert!(engine.bodies.try_borrow_mut().is_err());
    assert!(engine.call_signatures.try_borrow_mut().is_err());
    eprintln!("POPULATION actual-original-wrapper-semantic-facts-unsat");
    eprintln!("POPULATION actual-source-registries-frozen-through-fact");
    drop(certificate);
    let original = engine.instantiated_body(selected).unwrap();
    let alternative = engine.instantiated_body(alternate).unwrap();
    let mut work = Work::new(0).unwrap();
    let original_work = inventory(
        engine,
        selected,
        &original,
        SourcePhase::Normalized,
        &mut work,
    )
    .unwrap();
    work.charge(3 * original_work + 6).unwrap();
    let mut wrong = original.as_ref().clone();
    wrong.local_decls[Local::from_usize(1)].ty = if engine.tcx.sess.target.pointer_width == 64 {
        engine.tcx.types.u64
    } else {
        engine.tcx.types.u32
    };
    engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
    let error = observe_inner(engine, selected, 0, 0).err().unwrap();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source current local differs from original compiler local"
    );
    engine
        .bodies
        .borrow_mut()
        .insert(selected, original.clone());
    eprintln!("POPULATION actual-target-sized-source-type-mutation-refused");
    let TerminatorKind::Call {
        func: alternative_func,
        ..
    } = &alternative.basic_blocks[rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        panic!("actual trailing-zero intrinsic Call disappeared")
    };
    let ty::FnDef(alternative_id, alternative_args) = alternative_func
        .ty(&alternative.local_decls, engine.tcx)
        .kind()
    else {
        panic!("actual trailing-zero intrinsic identity disappeared")
    };
    assert!(
        engine
            .tcx
            .is_intrinsic(*alternative_id, rustc_span::Symbol::intern("cttz"))
    );
    let alternate_signature = engine
        .tcx
        .fn_sig(*alternative_id)
        .instantiate(engine.tcx, alternative_args.skip_binder())
        .skip_binder();
    assert_eq!(alternate_signature.inputs(), [engine.tcx.types.usize]);
    assert_eq!(alternate_signature.output(), engine.tcx.types.u32);
    assert_eq!(
        engine.population_count_type(*alternative_id, alternate_signature),
        None
    );
    work.charge(3 * original_work + 10).unwrap();
    let mut wrong = original.as_ref().clone();
    let TerminatorKind::Call { func, .. } = &mut wrong.basic_blocks.as_mut()
        [rustc_middle::mir::START_BLOCK]
        .terminator_mut()
        .kind
    else {
        panic!("original population primitive Call disappeared")
    };
    *func = alternative_func.clone();
    engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
    let error = observe_inner(engine, selected, 0, 0).err().unwrap();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source current CFG differs from original compiler CFG"
    );
    engine.bodies.borrow_mut().insert(selected, original);
    eprintln!("POPULATION actual-same-signature-different-intrinsic-refused");
    let error = observe_inner(engine, alternate, 0, 0).err().unwrap();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source primitive is not exact original target-usize ctpop"
    );
    eprintln!("POPULATION original-nonpopulation-intrinsic-remains-unsupported");
    let error = reject(observe_inner(engine, selected, 0, 0).unwrap()).unwrap_err();
    assert_eq!(
        error,
        "authenticated population fact does not establish complete byte search"
    );
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::Semantics)
    );
    eprintln!("POPULATION restored-semantic-fact-full-search-still-unknown");
}
