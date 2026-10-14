//! Source-derived size-one allocation bound only, not a raw-parts or search permit.
use super::*;
use crate::solver::{Answer, Query, Solver};
use rustc_middle::mir::{AssertKind, BasicBlock, BinOp, CastKind, UnwindAction};

fn direct(place: Place<'_>, local: usize) -> bool {
    place.projection.is_empty() && place.local == Local::from_usize(local)
}

fn local(operand: &Operand<'_>, expected: usize) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => direct(*place, expected),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => false,
    }
}

fn constant<'tcx>(
    engine: &Engine<'tcx>,
    operand: &Operand<'tcx>,
    ty: Ty<'tcx>,
    value: u128,
) -> bool {
    let Operand::Constant(constant) = operand else {
        return false;
    };
    constant.const_.ty() == ty
        && constant
            .const_
            .try_eval_bits(engine.tcx, ty::TypingEnv::fully_monomorphized())
            == Some(value)
}

fn assignment<'a, 'tcx>(
    statement: &'a rustc_middle::mir::Statement<'tcx>,
    expected: usize,
) -> Result<&'a Rvalue<'tcx>, Failure> {
    let StatementKind::Assign(value) = &statement.kind else {
        return Err("allocation-size helper has a non-assignment statement".into());
    };
    if !direct(value.0, expected) {
        return Err("allocation-size helper assignment destination differs".into());
    }
    Ok(&value.1)
}

fn shape<'tcx>(source: &SourceObservation<'_, 'tcx>, work: &mut Work) -> Result<u32, Failure> {
    work.charge(2)?; // New wrapper dispatch and actual guarded Body lookup, before use.
    shape_in_body(
        source,
        source
            .bodies
            .get(&source.instance)
            .ok_or("allocation-size helper lost its guarded Body")?,
        work,
    )
}

fn shape_in_body<'tcx>(
    source: &SourceObservation<'_, 'tcx>,
    body: &Body<'tcx>,
    work: &mut Work,
) -> Result<u32, Failure> {
    // Complete eight-local/five-block inventory, seven statements, constants, branches and Assert.
    // Separate from the already paid original/current source and full-signature authentication.
    work.charge(256)?;
    let engine = source.engine;
    let signature = source
        .signatures
        .get(&source.instance)
        .ok_or("allocation-size helper lost its guarded signature")?
        .skip_binder();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    if !matches!(bits, 32 | 64)
        || !source.instance.args.is_empty()
        || !source.helpers.is_empty()
        || signature.inputs() != [engine.tcx.types.usize, engine.tcx.types.usize]
        || signature.output() != engine.tcx.types.bool
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || body.arg_count != 2
        || body.local_decls.len() != 8
        || body.basic_blocks.len() != 5
    {
        return Err("allocation-size helper original signature/inventory differs".into());
    }
    for (index, declaration) in body.local_decls.iter().enumerate() {
        let expected = if matches!(index, 0 | 4 | 6) {
            engine.tcx.types.bool
        } else {
            engine.tcx.types.usize
        };
        if declaration.ty != expected {
            return Err("allocation-size helper original local types differ".into());
        }
    }
    let blocks = &body.basic_blocks;
    for (index, block) in blocks.iter().enumerate() {
        let statements = [1, 1, 2, 1, 2][index];
        if block.is_cleanup || block.statements.len() != statements {
            return Err("allocation-size helper complete statement inventory differs".into());
        }
    }
    let usize_ty = engine.tcx.types.usize;
    let zero_test = |value: &Rvalue<'tcx>| {
        matches!(value,
        Rvalue::BinaryOp(BinOp::Eq, operands)
            if local(&operands.0, 1) && constant(engine, &operands.1, usize_ty, 0))
    };
    if !zero_test(assignment(
        &blocks[BasicBlock::from_usize(0)].statements[0],
        4,
    )?) || !zero_test(assignment(
        &blocks[BasicBlock::from_usize(2)].statements[1],
        6,
    )?) {
        return Err("allocation-size helper actual size-zero predicates differ".into());
    }
    let maximum = (1u128 << bits) - 1;
    let signed_maximum = (1u128 << (bits - 1)) - 1;
    if !matches!(assignment(&blocks[BasicBlock::from_usize(1)].statements[0], 3)?,
        Rvalue::Use(value, _) if constant(engine, value, usize_ty, maximum))
        || !matches!(assignment(&blocks[BasicBlock::from_usize(2)].statements[0], 5)?,
            Rvalue::Cast(CastKind::IntToInt, value, target)
                if *target == usize_ty
                    && constant(engine, value, engine.tcx.types.isize, signed_maximum))
        || !matches!(assignment(&blocks[BasicBlock::from_usize(3)].statements[0], 3)?,
            Rvalue::BinaryOp(BinOp::Div, operands)
                if local(&operands.0, 5) && local(&operands.1, 1))
        || !matches!(assignment(&blocks[BasicBlock::from_usize(4)].statements[0], 7)?,
            Rvalue::Use(value, _) if local(value, 3))
        || !matches!(assignment(&blocks[BasicBlock::from_usize(4)].statements[1], 0)?,
            Rvalue::BinaryOp(BinOp::Le, operands)
                if local(&operands.0, 2) && local(&operands.1, 7))
    {
        return Err("allocation-size helper actual bound/division/result differs".into());
    }
    if !matches!(&blocks[BasicBlock::from_usize(0)].terminator().kind,
        TerminatorKind::SwitchInt { discr, targets }
            if local(discr, 4) && targets.as_static_if()
                == Some((0, BasicBlock::from_usize(2), BasicBlock::from_usize(1))))
        || !matches!(&blocks[BasicBlock::from_usize(2)].terminator().kind,
            TerminatorKind::Assert { cond, expected: false, msg, target, unwind }
                if local(cond, 6) && *target == BasicBlock::from_usize(3)
                    && *unwind == UnwindAction::Unreachable
                    && matches!(msg.as_ref(), AssertKind::DivisionByZero(value) if local(value, 5)))
        || !matches!(
            blocks[BasicBlock::from_usize(4)].terminator().kind,
            TerminatorKind::Return
        )
    {
        return Err("allocation-size helper actual branch/Assert/Return differs".into());
    }
    for index in [1, 3] {
        if !matches!(blocks[BasicBlock::from_usize(index)].terminator().kind,
            TerminatorKind::Goto { target } if target == BasicBlock::from_usize(4))
        {
            return Err("allocation-size helper actual bound merge differs".into());
        }
    }
    Ok(bits)
}

fn size_one_query(bits: u32, limits: miren::AnalysisLimits) -> Result<Query, Failure> {
    allocation_query(bits, (1u128 << (bits - 1)) - 1, limits)
}

fn allocation_query(
    bits: u32,
    actual_bound: u128,
    limits: miren::AnalysisLimits,
) -> Result<Query, Failure> {
    let context = Context::default();
    let length = context.symbol(0, Sort::BitVec(bits))?;
    let maximum = context.bit_vector((1u128 << (bits - 1)) - 1, bits)?;
    let zero = context.bit_vector(0, bits)?;
    let size = context.bit_vector(1, bits)?;
    let selected_bound = context.bit_vector(actual_bound, bits)?;
    let bound = context.apply(Op::BvUnsignedDiv, &[selected_bound, size.clone()])?;
    let premise = context.apply(Op::BvUnsignedLe, &[length.clone(), maximum])?;
    let zero_divisor = context.apply(Op::Equal, &[size, zero])?;
    let result_false = context.apply(Op::BvUnsignedGt, &[length, bound])?;
    let failure = context.apply(Op::Or, &[zero_divisor, result_false])?;
    Query::from_terms_with_limits(&context, &[premise], &failure, &Default::default(), limits)
        .map_err(Into::into)
}

pub(super) fn size_one_fact(
    source: &SourceObservation<'_, '_>,
    work: &mut Work,
) -> Result<(), Failure> {
    let bits = shape(source, work)?;
    work.charge(128 + 8 * bits as usize)?;
    work.charge(4)?; // New explicit-bound query dispatch/construction; old query fee stays literal.
    let query = size_one_query(bits, source.engine.limits)?;
    check_query(source.engine, &query)
}

fn check_query(engine: &Engine<'_>, query: &Query) -> Result<(), Failure> {
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "allocation-size fact reached existing root deadline".into(),
        });
    }
    let answer = Solver::with_limits(engine.limits).check_query(query);
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "allocation-size fact reached existing root deadline".into(),
        });
    }
    classify_answer(answer)
}

fn classify_answer(answer: Answer) -> Result<(), Failure> {
    match answer {
        Answer::Unsat => Ok(()),
        Answer::Sat(_) => Err("allocation-size helper size-one fact is refuted".into()),
        Answer::Unknown(reason) => Err(Failure {
            category: UnknownCategory::Solver,
            reason: format!("allocation-size helper size-one fact remains unknown: {reason}"),
        }),
    }
}

#[cfg(test)]
pub(super) fn compiler_controls<'tcx>(engine: &Engine<'tcx>, selected: ty::Instance<'tcx>) {
    let prepared = preparation::prepare(engine, selected, 0).unwrap();
    let cold_work = prepared.used();
    let mut held = prepared.revalidate(engine, selected, cold_work).unwrap();
    held.check_held().unwrap();
    let fact_work = held.size_one_helper_fact(held.used()).unwrap();
    assert!(fact_work > cold_work && fact_work < NICHE_GRAPH_WORK);
    assert!(engine.bodies.try_borrow_mut().is_err());
    assert!(engine.call_signatures.try_borrow_mut().is_err());
    eprintln!("ALLOCATION SIZE cold-full-source-size1-fact used={fact_work}");
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let query = size_one_query(bits, engine.limits).unwrap();
    eprintln!(
        "ALLOCATION SIZE QUERY START\n{}ALLOCATION SIZE QUERY END",
        query.text()
    );
    assert!(matches!(
        Solver::with_limits(engine.limits).check_query(&query),
        Answer::Unsat
    ));
    drop(held);
    // An independently named warm service starts at0; this is not a continuation after failure.
    let warm = preparation::prepare(engine, selected, 0).unwrap();
    let used = warm.used();
    let mut held = warm.revalidate(engine, selected, used).unwrap();
    held.size_one_helper_fact(held.used()).unwrap();
    drop(held);
    eprintln!("ALLOCATION SIZE independent-warm-service");
    for (control, category) in [
        (FailureProbe::Schema, UnknownCategory::Semantics),
        (FailureProbe::SolverProtocol, UnknownCategory::Solver),
        (FailureProbe::SolverUnknown, UnknownCategory::Solver),
    ] {
        let fresh = super::super::super::super::nonzero_niches::test_engine(engine.tcx);
        let prepared = preparation::prepare(&fresh, selected, 0).unwrap();
        let used = prepared.used();
        let mut held = prepared.revalidate(&fresh, selected, used).unwrap();
        let error = held.failed_probe(control).unwrap_err();
        match control {
            FailureProbe::Schema => assert_eq!(
                error,
                "allocation-size helper actual bound/division/result differs"
            ),
            FailureProbe::SolverProtocol => {
                assert!(error.starts_with("allocation-size helper size-one fact remains unknown:"));
                assert!(error.contains("(error "));
            }
            FailureProbe::SolverUnknown => assert_eq!(
                error.trim(),
                "allocation-size helper size-one fact remains unknown: \
                 solver did not decide the query: unknown"
            ),
        }
        assert_eq!(fresh.unknown_causes.borrow().get(&error), Some(&category));
        let stopped = held.used();
        assert_eq!(held.check_held().unwrap_err(), error);
        assert_eq!(held.size_one_helper_fact(stopped + 512).unwrap_err(), error);
        assert_eq!(held.used(), stopped); // No later work or replacement after the failed service.
        assert!(fresh.bodies.try_borrow_mut().is_err());
        assert!(fresh.call_signatures.try_borrow_mut().is_err());
        eprintln!(
            "ALLOCATION SIZE sticky-{control:?}-{category:?}-failure used={stopped} reason={error}"
        );
    }
    let capped = super::super::super::super::nonzero_niches::test_engine(engine.tcx);
    let prepared = preparation::prepare(&capped, selected, 0).unwrap();
    let used = prepared.used();
    let mut held = prepared.revalidate(&capped, selected, used).unwrap();
    let error = held.size_one_helper_fact(NICHE_GRAPH_WORK).unwrap_err();
    assert_eq!(
        capped.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    let stopped = held.used();
    assert!(stopped > NICHE_GRAPH_WORK);
    assert_eq!(held.check_held().unwrap_err(), error);
    assert_eq!(held.size_one_helper_fact(usize::MAX).unwrap_err(), error);
    assert_eq!(held.used(), stopped);
    assert!(capped.bodies.try_borrow_mut().is_err());
    drop(held);
    eprintln!("ALLOCATION SIZE sticky-cumulative-handoff-refusal used={stopped}");
    let mut expired = super::super::super::super::nonzero_niches::test_engine(engine.tcx);
    expired.started = std::time::Instant::now()
        .checked_sub(std::time::Duration::from_secs(
            expired.limits.root_timeout_secs + 1,
        ))
        .unwrap();
    let prepared = preparation::prepare(&expired, selected, 0).unwrap();
    let used = prepared.used();
    let mut held = prepared.revalidate(&expired, selected, used).unwrap();
    let error = held.size_one_helper_fact(held.used()).unwrap_err();
    assert_eq!(error, "allocation-size fact reached existing root deadline");
    assert_eq!(
        expired.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    let stopped = held.used();
    assert_eq!(held.check_held().unwrap_err(), error);
    assert_eq!(held.size_one_helper_fact(stopped + 512).unwrap_err(), error);
    assert_eq!(held.used(), stopped);
    assert!(expired.bodies.try_borrow_mut().is_err());
    assert!(expired.call_signatures.try_borrow_mut().is_err());
    drop(held);
    eprintln!("ALLOCATION SIZE sticky-actual-deadline-refusal used={stopped}");
    // Separate mathematical mutant: MAX remains admitted, but the result bound is lowered by1.
    // The cached Div->Mul control below is source authentication only (both agree at size1).
    let mutant = allocation_query(bits, (1u128 << (bits - 1)) - 2, engine.limits).unwrap();
    eprintln!(
        "ALLOCATION SIZE LOWERED BOUND QUERY START\n{}LOWERED BOUND QUERY END",
        mutant.text()
    );
    match Solver::with_limits(engine.limits).check_query(&mutant) {
        Answer::Sat(model) => {
            assert!(!model.trim().is_empty());
            eprintln!("ALLOCATION SIZE LOWERED BOUND SAT MODEL START\n{model}\nSAT MODEL END");
        }
        Answer::Unsat => panic!("lowered allocation bound incorrectly established the fact"),
        Answer::Unknown(reason) => {
            panic!("lowered allocation bound lacked a countermodel: {reason}")
        }
    }
    let borrowed = engine.bodies.borrow_mut();
    assert_eq!(
        preparation::prepare(engine, selected, 0).err().unwrap(),
        "byte source Body registry is borrowed"
    );
    drop(borrowed);
    let prepared = preparation::prepare(engine, selected, 0).unwrap();
    let other = super::super::super::super::nonzero_niches::test_engine(engine.tcx);
    let used = prepared.used();
    assert_eq!(
        prepared.revalidate(&other, selected, used).err().unwrap(),
        "byte preparation has a different root or lost prior work"
    );
    eprintln!("ALLOCATION SIZE foreign-engine-and-registry-conflict-refused");
    let original = engine.instantiated_body(selected).unwrap();
    let mut wrong = original.as_ref().clone();
    let StatementKind::Assign(value) =
        &mut wrong.basic_blocks.as_mut()[BasicBlock::from_usize(3)].statements[0].kind
    else {
        panic!("actual allocation division assignment disappeared")
    };
    let Rvalue::BinaryOp(operation, _) = &mut value.1 else {
        panic!("actual allocation division operation disappeared")
    };
    assert_eq!(*operation, BinOp::Div);
    *operation = BinOp::Mul;
    engine.bodies.borrow_mut().insert(selected, Rc::new(wrong));
    let error = preparation::prepare(engine, selected, 0).err().unwrap();
    assert_eq!(
        error,
        "byte source current statement differs from original compiler statement"
    );
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::Semantics)
    );
    engine.bodies.borrow_mut().insert(selected, original);
    let error = preparation::prepare(engine, selected, NICHE_GRAPH_WORK)
        .err()
        .unwrap();
    assert_eq!(
        engine.unknown_causes.borrow().get(&error),
        Some(&UnknownCategory::ResourceLimit)
    );
    eprintln!("ALLOCATION SIZE division-mutation-and-cumulative-budget-refused");
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) enum FailureProbe {
    Schema,
    SolverProtocol,
    SolverUnknown,
}

#[cfg(test)]
pub(super) fn failure_probe<'tcx>(
    source: &SourceObservation<'_, 'tcx>,
    work: &mut Work,
    control: FailureProbe,
) -> Result<(), Failure> {
    match control {
        FailureProbe::Schema => {
            work.charge(2)?;
            let body = source
                .bodies
                .get(&source.instance)
                .ok_or("allocation-size helper lost its guarded Body")?;
            let clone_work = inventory(
                source.engine,
                source.instance,
                body,
                SourcePhase::Normalized,
                work,
            )?;
            work.charge(3 * clone_work + 4)?;
            let mut mutant = body.as_ref().clone();
            let StatementKind::Assign(value) =
                &mut mutant.basic_blocks.as_mut()[BasicBlock::from_usize(3)].statements[0].kind
            else {
                return Err("actual allocation division assignment disappeared".into());
            };
            let Rvalue::BinaryOp(operation, _) = &mut value.1 else {
                return Err("actual allocation division operation disappeared".into());
            };
            *operation = BinOp::Add;
            // Standalone schema gate on an owned actual-Body mutant: never current-cache authority.
            shape_in_body(source, &mutant, work).map(|_| ())
        }
        FailureProbe::SolverUnknown => {
            shape(source, work)?;
            work.charge(128)?;
            let query = "(set-logic ALL)\n(set-option :timeout 1)\n\
                (declare-fun f (Int) Int)\n\
                (assert (forall ((x Int)) (= (f (f x)) (+ x 1))))\n(check-sat)\n";
            eprintln!("ALLOCATION SIZE LITERAL UNKNOWN QUERY START\n{query}QUERY END");
            // Independent diagnostic1ms fixture, not the allocation fact or production limit.
            // The ordinary solver API preserves actual literal solver output in Unknown.reason.
            let answer = Solver::with_limits(source.engine.limits).check(query);
            classify_answer(answer)
        }
        FailureProbe::SolverProtocol => {
            shape(source, work)?;
            work.charge(128 + 8 * usize::from(source.engine.tcx.sess.target.pointer_width))?;
            let query = Query::new(
                &["(declare-const v0 (_ BitVec 32))".into()],
                &[],
                "(= v0 undeclared_allocation_term)",
            );
            eprintln!(
                "ALLOCATION SIZE UNKNOWN QUERY START\n{}UNKNOWN QUERY END",
                query.text()
            );
            // Actual pinned solver rejects this diagnostic query; no fabricated Answer is used.
            check_query(source.engine, &query)
        }
    }
}
