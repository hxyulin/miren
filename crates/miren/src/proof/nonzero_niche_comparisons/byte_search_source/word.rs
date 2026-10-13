//! Body-derived zero-byte word fact. It grants no storage, pointer or search authority.
use super::*;

#[cfg(test)]
#[path = "word_probe.rs"]
mod probe;
use crate::solver::{Answer, Query, Solver};
use miren::smt::{Context, Op, Sort};

struct Shape<'tcx> {
    arithmetic: ty::Instance<'tcx>,
    low: u128,
    high: u128,
    bits: u32,
}

// Non-Clone, operation-local authority: both actual source registries remain borrowed.
struct WordCertificate<'a, 'tcx> {
    source: SourceObservation<'a, 'tcx>,
    arithmetic: Rc<Body<'tcx>>,
    query: Query,
}

fn plain(place: Place<'_>) -> Result<Local, Failure> {
    if !place.projection.is_empty() {
        return Err("word certificate requires a direct local place".into());
    }
    Ok(place.local)
}

fn operand_local(operand: &Operand<'_>) -> Result<Local, Failure> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => plain(*place),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => {
            Err("word certificate expected an actual local operand".into())
        }
    }
}

fn integer_constant<'tcx>(engine: &Engine<'tcx>, operand: &Operand<'tcx>) -> Result<u128, Failure> {
    let Operand::Constant(constant) = operand else {
        return Err("word certificate expected an original target-usize constant".into());
    };
    if constant.const_.ty() != engine.tcx.types.usize {
        return Err("word certificate constant has a different original Rust type".into());
    }
    constant
        .const_
        .try_eval_bits(engine.tcx, ty::TypingEnv::fully_monomorphized())
        .ok_or_else(|| "word certificate original constant is unavailable".into())
}

fn assignment<'a, 'tcx>(
    statement: &'a rustc_middle::mir::Statement<'tcx>,
) -> Result<(Local, &'a Rvalue<'tcx>), Failure> {
    let StatementKind::Assign(value) = &statement.kind else {
        return Err("word certificate requires every statement to be an assignment".into());
    };
    Ok((plain(value.0)?, &value.1))
}

fn binary<'a, 'tcx>(
    value: &'a Rvalue<'tcx>,
    operation: rustc_middle::mir::BinOp,
) -> Result<(&'a Operand<'tcx>, &'a Operand<'tcx>), Failure> {
    let Rvalue::BinaryOp(actual, operands) = value else {
        return Err("word certificate requires the exact original binary operation".into());
    };
    if *actual != operation {
        return Err("word certificate binary operation differs".into());
    }
    Ok((&operands.0, &operands.1))
}

fn shape<'tcx>(observation: &mut SourceObservation<'_, 'tcx>) -> Result<Shape<'tcx>, Failure> {
    // Six locals, two blocks, five operands/assignments, constant queries, identity comparisons.
    // This is separate work from source authentication and is paid before semantic traversal.
    observation.work.charge(192)?;
    let engine = observation.engine;
    let body = observation
        .bodies
        .get(&observation.instance)
        .ok_or("word source disappeared")?;
    let signature = observation
        .signatures
        .get(&observation.instance)
        .ok_or("word signature disappeared")?
        .skip_binder();
    if signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
    {
        return Err("word certificate requires an original safe Rust signature".into());
    }
    let bits = engine.tcx.data_layout.pointer_size().bits() as u32;
    if !observation.instance.args.is_empty()
        || !matches!(bits, 32 | 64)
        || body.arg_count != 1
        || body.local_decls.len() != 6
        || body.basic_blocks.len() != 2
        || body.return_ty() != engine.tcx.types.bool
        || body
            .local_decls
            .iter()
            .skip(1)
            .any(|local| local.ty != engine.tcx.types.usize)
    {
        return Err("word certificate original target/signature/local inventory differs".into());
    }
    let entry = &body.basic_blocks[START_BLOCK];
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        ..
    } = &entry.terminator().kind
    else {
        return Err("word certificate requires the actual arithmetic Call".into());
    };
    if !entry.statements.is_empty()
        || entry.is_cleanup
        || args.len() != 2
        || *target != Some(rustc_middle::mir::BasicBlock::from_usize(1))
        || *unwind != rustc_middle::mir::UnwindAction::Unreachable
        || operand_local(&args[0].node)? != Local::from_usize(1)
    {
        return Err("word certificate arithmetic Call transport differs".into());
    }
    let ty::FnDef(id, arguments) = func.ty(&body.local_decls, engine.tcx).kind() else {
        return Err("word certificate arithmetic is not an original function item".into());
    };
    if !arguments.skip_binder().is_empty() {
        return Err(
            "word certificate arithmetic has unsupported original generic arguments".into(),
        );
    }
    let arithmetic = engine.resolve_function_item(*id, arguments.skip_binder())?;
    if observation.helpers.len() != 1 || observation.helpers[0].selected != arithmetic {
        return Err("word certificate complete helper inventory differs".into());
    }
    let subtraction = plain(*destination)?;
    let low = integer_constant(engine, &args[1].node)?;
    let tail = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(1)];
    if tail.is_cleanup
        || tail.statements.len() != 4
        || !matches!(tail.terminator().kind, TerminatorKind::Return)
    {
        return Err("word certificate complete tail CFG differs".into());
    }
    let (not_local, value) = assignment(&tail.statements[0])?;
    let Rvalue::UnaryOp(rustc_middle::mir::UnOp::Not, input) = value else {
        return Err("word certificate requires original Not".into());
    };
    if operand_local(input)? != Local::from_usize(1) {
        return Err("word certificate Not input differs".into());
    }
    let (and_local, value) = assignment(&tail.statements[1])?;
    let (left, right) = binary(value, rustc_middle::mir::BinOp::BitAnd)?;
    if operand_local(left)? != subtraction || operand_local(right)? != not_local {
        return Err("word certificate first BitAnd operands differ".into());
    }
    let (mask_local, value) = assignment(&tail.statements[2])?;
    let (left, right) = binary(value, rustc_middle::mir::BinOp::BitAnd)?;
    if operand_local(left)? != and_local {
        return Err("word certificate mask input differs".into());
    }
    let high = integer_constant(engine, right)?;
    let (output, value) = assignment(&tail.statements[3])?;
    let (left, right) = binary(value, rustc_middle::mir::BinOp::Ne)?;
    if output != Local::from_usize(0)
        || operand_local(left)? != mask_local
        || integer_constant(engine, right)? != 0
    {
        return Err("word certificate result operands differ".into());
    }
    let locals = [subtraction, not_local, and_local, mask_local];
    for (index, local) in locals.iter().enumerate() {
        if local.as_usize() < 2 || locals[..index].contains(local) {
            return Err("word certificate temporary roles alias".into());
        }
    }
    let mut expected_low = 0;
    let mut expected_high = 0;
    for byte in 0..bits / 8 {
        expected_low |= 1_u128 << (8 * byte);
        expected_high |= 128_u128 << (8 * byte);
    }
    if low != expected_low || high != expected_high {
        return Err("word certificate compiler constants differ from exact byte masks".into());
    }
    Ok(Shape {
        arithmetic,
        low,
        high,
        bits,
    })
}

fn arithmetic(observation: &mut SourceObservation<'_, '_>) -> Result<(), Failure> {
    observation.work.charge(56)?;
    let signature = observation
        .signatures
        .get(&observation.instance)
        .ok_or("word arithmetic signature disappeared")?
        .skip_binder();
    if signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
    {
        return Err("word arithmetic requires an original safe Rust signature".into());
    }
    let body = observation
        .bodies
        .get(&observation.instance)
        .ok_or("word arithmetic disappeared")?;
    if body.arg_count != 2
        || body.local_decls.len() != 3
        || body.basic_blocks.len() != 1
        || body
            .local_decls
            .iter()
            .any(|local| local.ty != observation.engine.tcx.types.usize)
    {
        return Err("word arithmetic original signature/local inventory differs".into());
    }
    let block = &body.basic_blocks[START_BLOCK];
    if block.is_cleanup
        || block.statements.len() != 1
        || !matches!(block.terminator().kind, TerminatorKind::Return)
    {
        return Err("word arithmetic complete CFG differs".into());
    }
    let (output, value) = assignment(&block.statements[0])?;
    let (left, right) = binary(value, rustc_middle::mir::BinOp::Sub)?;
    if output != Local::from_usize(0)
        || operand_local(left)? != Local::from_usize(1)
        || operand_local(right)? != Local::from_usize(2)
        || !observation.helpers.is_empty()
    {
        return Err("word arithmetic original operand/helper inventory differs".into());
    }
    Ok(())
}

fn mathematical_query(shape: &Shape<'_>, limits: miren::AnalysisLimits) -> Result<Query, Failure> {
    let context = Context::default();
    let word = context.symbol(0, Sort::BitVec(shape.bits))?;
    let low = context.bit_vector(shape.low, shape.bits)?;
    let high = context.bit_vector(shape.high, shape.bits)?;
    let zero = context.bit_vector(0, shape.bits)?;
    let sub = context.apply(Op::BvSub, &[word.clone(), low])?;
    let inverse = context.apply(Op::BvNot, std::slice::from_ref(&word))?;
    let and = context.apply(Op::BvAnd, &[sub, inverse])?;
    let masked = context.apply(Op::BvAnd, &[and, high])?;
    let equal = context.apply(Op::Equal, &[masked, zero])?;
    let actual = context.apply(Op::Not, &[equal])?;
    let mut expected = context.boolean(false);
    for byte in 0..shape.bits / 8 {
        let part = context.apply(
            Op::Extract {
                high: 8 * byte + 7,
                low: 8 * byte,
            },
            std::slice::from_ref(&word),
        )?;
        let byte_zero = context.bit_vector(0, 8)?;
        let equal = context.apply(Op::Equal, &[part, byte_zero])?;
        expected = context.apply(Op::Or, &[expected, equal])?;
    }
    let same = context.apply(Op::Equal, &[actual, expected])?;
    let failure = context.apply(Op::Not, &[same])?;
    Query::from_terms_with_limits(&context, &[], &failure, &Default::default(), limits)
        .map_err(Into::into)
}

fn certify<'a, 'tcx>(
    mut source: SourceObservation<'a, 'tcx>,
) -> Result<WordCertificate<'a, 'tcx>, Failure> {
    let shape = shape(&mut source)?;
    let engine = source.engine;
    let root = source.instance;
    let depth = source.depth;
    let used = source.work.used;
    drop(source);
    // Paid preparation has no outstanding registry guards. No synchronous guest operation runs.
    let mut helper = observe_inner(engine, shape.arithmetic, depth + 1, used)?;
    arithmetic(&mut helper)?;
    helper.work.charge(4)?;
    let arithmetic = helper
        .bodies
        .get(&shape.arithmetic)
        .ok_or("word helper lost source")?
        .clone();
    let signature = *helper
        .signatures
        .get(&shape.arithmetic)
        .ok_or("word helper lost signature")?;
    let used = helper.work.used;
    drop(helper);
    // Fresh root authentication freezes both registries before consuming prepared helper evidence.
    let mut source = observe_inner(engine, root, depth, used)?;
    source.work.charge(8 + shape.arithmetic.args.len())?;
    if !source
        .bodies
        .get(&shape.arithmetic)
        .is_some_and(|body| Rc::ptr_eq(body, &arithmetic))
        || source.signatures.get(&shape.arithmetic) != Some(&signature)
    {
        return Err("word arithmetic current identity changed during preparation".into());
    }
    source.work.charge(256 + 32 * shape.bits as usize / 8)?;
    let query = mathematical_query(&shape, engine.limits)?;
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "word certificate reached existing root deadline".into(),
        });
    }
    let answer = Solver::with_limits(engine.limits).check_query(&query);
    if engine.started.elapsed().as_secs() >= engine.limits.root_timeout_secs {
        return Err(Failure {
            category: UnknownCategory::ResourceLimit,
            reason: "word certificate reached existing root deadline".into(),
        });
    }
    match answer {
        Answer::Unsat => Ok(WordCertificate {
            source,
            arithmetic,
            query,
        }),
        Answer::Sat(_) => Err("word helper equivalence is refuted".into()),
        Answer::Unknown(reason) => Err(Failure {
            category: UnknownCategory::Solver,
            reason: format!("word helper equivalence remains unknown: {reason}"),
        }),
    }
}

pub(super) fn reject(mut source: SourceObservation<'_, '_>) -> Result<(), String> {
    // Only actual usize -> Bool source candidates enter this semantic schema. Other source
    // observations preserve their original conservative consumption, including missing bodies.
    let engine = source.engine;
    source
        .work
        .charge(6)
        .map_err(|failure| engine.categorized_error(failure.category, failure.reason))?;
    let candidate = source
        .signatures
        .get(&source.instance)
        .is_some_and(|signature| {
            let signature = signature.skip_binder();
            signature.inputs() == [engine.tcx.types.usize]
                && signature.output() == engine.tcx.types.bool
        });
    if !candidate {
        return source.reject_without_word();
    }
    let certificate = certify(source)
        .map_err(|failure| engine.categorized_error(failure.category, failure.reason))?;
    // These guards remain live until the refusal. A word fact is never a full search result.
    let _source = certificate.source;
    let _arithmetic = certificate.arithmetic;
    let _query = certificate.query;
    Err(engine.categorized_error(
        UnknownCategory::Semantics,
        "authenticated word fact does not establish complete byte search".into(),
    ))
}
