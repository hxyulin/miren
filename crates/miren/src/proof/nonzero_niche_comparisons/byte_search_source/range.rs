//! Complete typed range-source binding. Conditional metadata grants no executable rights.
use super::*;

#[cfg(test)]
#[path = "range_probe.rs"]
pub(super) mod probe;
use rustc_middle::mir::{AggregateKind, AssertKind, BinOp, CastKind, UnOp, UnwindAction};

#[derive(Clone, Copy)]
enum Input {
    Copy(usize),
    Move(usize),
    MoveField(usize, usize),
    SomeField(usize),
    Deref(usize),
    Index(usize, usize),
    Number(u128),
    Word,
}

#[derive(Clone, Copy)]
enum Expression {
    Use(Input),
    Metadata(Input),
    Binary(BinOp, Input, Input),
    Discriminant(usize),
    Some(Input),
    None,
    Range(Input),
    Tuple(Input, Input),
    Cast(Input),
}

#[derive(Clone, Copy)]
struct Assignment(usize, Expression);

#[derive(Clone, Copy)]
enum End {
    Goto(usize),
    Return,
    Unreachable,
    Boolean(Input, usize, usize),
    Option(Input, usize, usize, usize),
    Overflow(usize, BinOp, Input, Input, usize),
    Bounds(Input, Input, Input, usize),
    Call(&'static str, &'static [Input], usize, usize),
}

struct Block {
    assignments: &'static [Assignment],
    end: End,
}

#[derive(Clone, Copy)]
enum LocalType {
    Option,
    Byte,
    Slice,
    Word,
    Bool,
    Signed,
    Overflow,
    BytePointer,
    WordPointer,
    Range,
    Arguments,
    Unit,
}

use Assignment as A;
use End::{Boolean, Bounds, Call, Goto, Option as OptionEnd, Overflow, Return, Unreachable};
use Expression::{
    Binary, Cast, Discriminant, Metadata, None as NoneValue, Range, Some as SomeValue,
};
use Expression::{Tuple, Use};
use Input::{Copy as C, Move as M, MoveField as MF, Number as N};

const NAIVE: &[Block] = &[
    Block {
        assignments: &[A(3, Use(N(0)))],
        end: Goto(1),
    },
    Block {
        assignments: &[
            A(5, Use(C(3))),
            A(6, Metadata(C(2))),
            A(4, Binary(BinOp::Lt, M(5), M(6))),
        ],
        end: Boolean(M(4), 7, 2),
    },
    Block {
        assignments: &[
            A(9, Use(C(3))),
            A(10, Metadata(C(2))),
            A(11, Binary(BinOp::Lt, C(9), C(10))),
        ],
        end: Bounds(M(11), M(10), C(9), 3),
    },
    Block {
        assignments: &[
            A(8, Use(Input::Index(2, 9))),
            A(7, Binary(BinOp::Eq, M(8), C(1))),
        ],
        end: Boolean(M(7), 5, 4),
    },
    Block {
        assignments: &[A(12, Use(C(3))), A(0, SomeValue(M(12)))],
        end: Goto(8),
    },
    Block {
        assignments: &[A(13, Binary(BinOp::AddWithOverflow, C(3), N(1)))],
        end: Overflow(13, BinOp::Add, C(3), N(1), 6),
    },
    Block {
        assignments: &[A(3, Use(MF(13, 0)))],
        end: Goto(1),
    },
    Block {
        assignments: &[A(0, NoneValue)],
        end: Goto(8),
    },
    Block {
        assignments: &[],
        end: Return,
    },
];

const NAIVE_KEY: &str = "DefId(core::slice::memchr::memchr_naive)";
const ALIGNED_KEY: &str = "DefId(core::slice::memchr::memchr_aligned)";
const RUNTIME_KEY: &str = "DefId(core::slice::memchr::memchr_aligned::runtime)";
const ROOT_KEY: &str = "DefId(core::slice::memchr::memchr)";
const POINTER_KEY: &str = "DefId(core::slice::{impl#0}::as_ptr)";
const ADD_KEY: &str = "DefId(core::ptr::const_ptr::{impl#0}::add)";
const ZERO_KEY: &str = "DefId(core::slice::memchr::contains_zero_byte)";

const RUNTIME: &[Block] = &[
    Block {
        assignments: &[A(3, Metadata(C(2)))],
        end: Call(POINTER_KEY, &[C(2)], 4, 1),
    },
    Block {
        assignments: &[],
        end: Call(
            "DefId(core::ptr::const_ptr::{impl#0}::align_offset)",
            &[C(4), Input::Word],
            5,
            2,
        ),
    },
    Block {
        assignments: &[A(7, Use(C(5))), A(6, Binary(BinOp::Gt, M(7), N(0)))],
        end: Boolean(M(6), 8, 3),
    },
    Block {
        assignments: &[A(9, Use(C(5)))],
        end: Call("DefId(core::cmp::Ord::min)", &[M(9), C(3)], 8, 4),
    },
    Block {
        assignments: &[A(5, Use(M(8))), A(12, Use(C(5))), A(11, Range(M(12)))],
        end: Call(
            "DefId(core::ops::index::Index::index)",
            &[C(2), M(11)],
            10,
            5,
        ),
    },
    Block {
        assignments: &[],
        end: Call(NAIVE_KEY, &[C(1), C(10)], 13, 6),
    },
    Block {
        assignments: &[A(14, Discriminant(13))],
        end: OptionEnd(M(14), 7, 8, 32),
    },
    Block {
        assignments: &[A(15, Use(Input::SomeField(13))), A(0, SomeValue(C(15)))],
        end: Goto(31),
    },
    Block {
        assignments: &[],
        end: Call("DefId(core::num::{impl#12}::repeat_u8)", &[C(1)], 16, 9),
    },
    Block {
        assignments: &[
            A(18, Use(C(5))),
            A(21, Binary(BinOp::MulWithOverflow, N(2), Input::Word)),
        ],
        end: Overflow(21, BinOp::Mul, N(2), Input::Word, 10),
    },
    Block {
        assignments: &[
            A(20, Use(MF(21, 0))),
            A(22, Binary(BinOp::SubWithOverflow, C(3), C(20))),
        ],
        end: Overflow(22, BinOp::Sub, C(3), M(20), 11),
    },
    Block {
        assignments: &[
            A(19, Use(MF(22, 0))),
            A(17, Binary(BinOp::Le, M(18), M(19))),
        ],
        end: Boolean(M(17), 22, 12),
    },
    Block {
        assignments: &[A(26, Use(C(5)))],
        end: Call(ADD_KEY, &[C(4), M(26)], 25, 13),
    },
    Block {
        assignments: &[
            A(24, Cast(M(25))),
            A(23, Use(Input::Deref(24))),
            A(31, Use(C(5))),
            A(32, Binary(BinOp::AddWithOverflow, C(31), Input::Word)),
        ],
        end: Overflow(32, BinOp::Add, M(31), Input::Word, 14),
    },
    Block {
        assignments: &[A(30, Use(MF(32, 0)))],
        end: Call(ADD_KEY, &[C(4), M(30)], 29, 15),
    },
    Block {
        assignments: &[
            A(28, Cast(M(29))),
            A(27, Use(Input::Deref(28))),
            A(34, Binary(BinOp::BitXor, C(23), C(16))),
        ],
        end: Call(ZERO_KEY, &[M(34)], 33, 16),
    },
    Block {
        assignments: &[A(36, Binary(BinOp::BitXor, C(27), C(16)))],
        end: Call(ZERO_KEY, &[M(36)], 35, 17),
    },
    Block {
        assignments: &[],
        end: Boolean(C(33), 18, 22),
    },
    Block {
        assignments: &[],
        end: Boolean(C(35), 19, 22),
    },
    Block {
        assignments: &[A(38, Binary(BinOp::MulWithOverflow, Input::Word, N(2)))],
        end: Overflow(38, BinOp::Mul, Input::Word, N(2), 20),
    },
    Block {
        assignments: &[
            A(37, Use(MF(38, 0))),
            A(39, Binary(BinOp::AddWithOverflow, C(5), C(37))),
        ],
        end: Overflow(39, BinOp::Add, C(5), M(37), 21),
    },
    Block {
        assignments: &[A(5, Use(MF(39, 0)))],
        end: Goto(9),
    },
    Block {
        assignments: &[],
        end: Call(POINTER_KEY, &[C(2)], 42, 23),
    },
    Block {
        assignments: &[A(43, Use(C(5)))],
        end: Call(ADD_KEY, &[M(42), M(43)], 41, 24),
    },
    Block {
        assignments: &[
            A(45, Metadata(C(2))),
            A(46, Use(C(5))),
            A(47, Binary(BinOp::SubWithOverflow, C(45), C(46))),
        ],
        end: Overflow(47, BinOp::Sub, M(45), M(46), 25),
    },
    Block {
        assignments: &[A(44, Use(MF(47, 0)))],
        end: Call(
            "DefId(core::slice::raw::from_raw_parts)",
            &[M(41), M(44)],
            40,
            26,
        ),
    },
    Block {
        assignments: &[],
        end: Call(NAIVE_KEY, &[C(1), C(40)], 48, 27),
    },
    Block {
        assignments: &[A(49, Discriminant(48))],
        end: OptionEnd(M(49), 28, 30, 32),
    },
    Block {
        assignments: &[
            A(50, Use(Input::SomeField(48))),
            A(52, Use(C(5))),
            A(53, Binary(BinOp::AddWithOverflow, C(52), C(50))),
        ],
        end: Overflow(53, BinOp::Add, M(52), C(50), 29),
    },
    Block {
        assignments: &[A(51, Use(MF(53, 0))), A(0, SomeValue(M(51)))],
        end: Goto(31),
    },
    Block {
        assignments: &[A(0, NoneValue)],
        end: Goto(31),
    },
    Block {
        assignments: &[],
        end: Return,
    },
    Block {
        assignments: &[],
        end: Unreachable,
    },
];

const ROOT: &[Block] = &[
    Block {
        assignments: &[
            A(5, Metadata(C(2))),
            A(7, Binary(BinOp::MulWithOverflow, N(2), Input::Word)),
        ],
        end: Overflow(7, BinOp::Mul, N(2), Input::Word, 1),
    },
    Block {
        assignments: &[A(6, Use(MF(7, 0))), A(4, Binary(BinOp::Lt, M(5), M(6)))],
        end: Boolean(M(4), 3, 2),
    },
    Block {
        assignments: &[],
        end: Call(NAIVE_KEY, &[C(1), C(2)], 3, 4),
    },
    Block {
        assignments: &[],
        end: Call(ALIGNED_KEY, &[C(1), C(2)], 3, 4),
    },
    Block {
        assignments: &[A(8, Discriminant(3))],
        end: OptionEnd(M(8), 5, 6, 7),
    },
    Block {
        assignments: &[
            A(9, Use(Input::SomeField(3))),
            A(12, Metadata(C(2))),
            A(11, Binary(BinOp::Lt, C(9), M(12))),
        ],
        end: Call("DefId(core::hint::assert_unchecked)", &[M(11)], 10, 6),
    },
    Block {
        assignments: &[A(0, Use(C(3)))],
        end: Return,
    },
    Block {
        assignments: &[],
        end: Unreachable,
    },
];

const FORWARDER: &[Block] = &[
    Block {
        assignments: &[A(3, Tuple(C(1), C(2)))],
        end: Call(RUNTIME_KEY, &[MF(3, 0), MF(3, 1)], 0, 1),
    },
    Block {
        assignments: &[],
        end: Return,
    },
];

use LocalType::{
    Arguments, Bool, Byte, BytePointer, Option as OptionType, Overflow as OverflowType,
};
use LocalType::{Range as RangeType, Signed, Slice, Unit, Word, WordPointer};
const NAIVE_LOCALS: &[LocalType] = &[
    OptionType,
    Byte,
    Slice,
    Word,
    Bool,
    Word,
    Word,
    Bool,
    Byte,
    Word,
    Word,
    Bool,
    Word,
    OverflowType,
];
const RUNTIME_LOCALS: &[LocalType] = &[
    OptionType,
    Byte,
    Slice,
    Word,
    BytePointer,
    Word,
    Bool,
    Word,
    Word,
    Word,
    Slice,
    RangeType,
    Word,
    OptionType,
    Signed,
    Word,
    Word,
    Bool,
    Word,
    Word,
    Word,
    OverflowType,
    OverflowType,
    Word,
    WordPointer,
    BytePointer,
    Word,
    Word,
    WordPointer,
    BytePointer,
    Word,
    Word,
    OverflowType,
    Bool,
    Word,
    Bool,
    Word,
    Word,
    OverflowType,
    OverflowType,
    Slice,
    BytePointer,
    BytePointer,
    Word,
    Word,
    Word,
    Word,
    OverflowType,
    OptionType,
    Signed,
    Word,
    Word,
    Word,
    OverflowType,
];
const ROOT_LOCALS: &[LocalType] = &[
    OptionType,
    Byte,
    Slice,
    OptionType,
    Bool,
    Word,
    Word,
    OverflowType,
    Signed,
    Word,
    Unit,
    Bool,
    Word,
];
const FORWARDER_LOCALS: &[LocalType] = &[OptionType, Byte, Slice, Arguments];

fn direct(place: Place<'_>, expected: usize) -> bool {
    place.local.as_usize() == expected && place.projection.is_empty()
}

pub(super) fn key(work: &mut Work, id: DefId) -> Result<String, Failure> {
    // Reuse the existing bounded key service, carrying the same cumulative work into and out of it.
    work.charge(4)?;
    let prior = work.used;
    work.charge(20 + 6 + NICHE_BODIES)?;
    let mut budget = GraphBudget::new(prior)?;
    let result = budget.key(id);
    work.used = budget.work;
    work.charge(0)?;
    result.map_err(Into::into)
}

fn constant<'tcx>(
    engine: &Engine<'tcx>,
    work: &mut Work,
    operand: &Operand<'tcx>,
    expected: Input,
) -> Result<bool, Failure> {
    work.charge(260)?; // Original constant type/identity and the independent compiler evaluation.
    let Operand::Constant(value) = operand else {
        return Ok(false);
    };
    if value.const_.ty() != engine.tcx.types.usize {
        return Ok(false);
    }
    let bits = value
        .const_
        .try_eval_bits(engine.tcx, ty::TypingEnv::fully_monomorphized());
    match expected {
        Input::Number(number) => Ok(bits == Some(number)),
        Input::Word => {
            let rustc_middle::mir::Const::Unevaluated(original, _) = value.const_ else {
                return Ok(false);
            };
            if original.promoted.is_some()
                || !original.args.is_empty()
                || engine.tcx.def_kind(original.def) != DefKind::Const
                || key(work, original.def)? != "DefId(core::slice::memchr::USIZE_BYTES)"
            {
                return Ok(false);
            }
            work.charge(260)?; // Independent original usize layout, not host or source-text width.
            let layout = engine
                .tcx
                .layout_of(
                    ty::TypingEnv::fully_monomorphized().as_query_input(engine.tcx.types.usize),
                )
                .map_err(|_| "range source original usize layout is unavailable")?;
            let size = layout.size.bytes();
            Ok(matches!(size, 4 | 8) && bits == Some(u128::from(size)))
        }
        Input::Copy(_)
        | Input::Move(_)
        | Input::MoveField(_, _)
        | Input::SomeField(_)
        | Input::Deref(_)
        | Input::Index(_, _) => Ok(false),
    }
}

fn field<'tcx>(place: Place<'tcx>, local: usize, field: usize, body: &Body<'tcx>) -> bool {
    let [ProjectionElem::Field(actual, original)] = place.projection.as_slice() else {
        return false;
    };
    let ty::Tuple(fields) = body.local_decls[Local::from_usize(local)].ty.kind() else {
        return false;
    };
    place.local.as_usize() == local
        && actual.as_usize() == field
        && fields
            .get(field)
            .is_some_and(|expected| expected == original)
}

fn input<'tcx>(
    engine: &Engine<'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    actual: &Operand<'tcx>,
    expected: Input,
) -> Result<bool, Failure> {
    work.charge(8)?;
    let valid = match expected {
        Input::Copy(local) => matches!(actual, Operand::Copy(place) if direct(*place, local)),
        Input::Move(local) => matches!(actual, Operand::Move(place) if direct(*place, local)),
        Input::MoveField(local, index) => {
            matches!(actual, Operand::Move(place) if field(*place, local, index, body))
        }
        Input::SomeField(local) => {
            let Operand::Copy(place) = actual else {
                return Ok(false);
            };
            matches!(place.projection.as_slice(),
                [ProjectionElem::Downcast(_, variant), ProjectionElem::Field(index, original)]
                if place.local.as_usize() == local && variant.as_usize() == 1
                    && index.as_usize() == 0 && *original == engine.tcx.types.usize)
        }
        Input::Deref(local) => matches!(actual, Operand::Copy(place)
            if place.local.as_usize() == local
                && matches!(place.projection.as_slice(), [ProjectionElem::Deref])),
        Input::Index(local, index) => {
            let Operand::Copy(place) = actual else {
                return Ok(false);
            };
            place.local.as_usize() == local
                && matches!(place.projection.as_slice(),
                    [ProjectionElem::Deref, ProjectionElem::Index(actual)]
                    if actual.as_usize() == index)
        }
        Input::Number(_) | Input::Word => return constant(engine, work, actual, expected),
    };
    Ok(valid)
}

fn aggregate<'tcx>(
    engine: &Engine<'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    value: &Rvalue<'tcx>,
    destination: usize,
    variant: usize,
    args: &[Input],
) -> Result<bool, Failure> {
    work.charge(12 + 8 * args.len())?;
    let Rvalue::Aggregate(kind, actual) = value else {
        return Ok(false);
    };
    let AggregateKind::Adt(id, tag, parameters, user, active) = kind.as_ref() else {
        return Ok(false);
    };
    if tag.as_usize() != variant
        || user.is_some()
        || active.is_some()
        || Ty::new_adt(engine.tcx, engine.tcx.adt_def(*id), parameters)
            != body.local_decls[Local::from_usize(destination)].ty
        || actual.len() != args.len()
    {
        return Ok(false);
    }
    for (actual, expected) in actual.iter().zip(args) {
        if !input(engine, work, body, actual, *expected)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn expression<'tcx>(
    engine: &Engine<'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    destination: usize,
    value: &Rvalue<'tcx>,
    expected: Expression,
) -> Result<bool, Failure> {
    work.charge(12)?;
    match expected {
        Expression::Use(expected) => {
            let Rvalue::Use(actual, rustc_middle::mir::WithRetag::Yes) = value else {
                return Ok(false);
            };
            input(engine, work, body, actual, expected)
        }
        Expression::Metadata(expected) => {
            let Rvalue::UnaryOp(UnOp::PtrMetadata, actual) = value else {
                return Ok(false);
            };
            input(engine, work, body, actual, expected)
        }
        Expression::Binary(expected, left, right) => {
            let Rvalue::BinaryOp(op, actual) = value else {
                return Ok(false);
            };
            Ok(*op == expected
                && input(engine, work, body, &actual.0, left)?
                && input(engine, work, body, &actual.1, right)?)
        }
        Expression::Discriminant(local) => {
            Ok(matches!(value, Rvalue::Discriminant(place) if direct(*place, local)))
        }
        Expression::Cast(expected) => {
            let Rvalue::Cast(CastKind::PtrToPtr, actual, original) = value else {
                return Ok(false);
            };
            Ok(
                *original == body.local_decls[Local::from_usize(destination)].ty
                    && input(engine, work, body, actual, expected)?,
            )
        }
        Expression::Some(expected) => {
            aggregate(engine, work, body, value, destination, 1, &[expected])
        }
        Expression::None => aggregate(engine, work, body, value, destination, 0, &[]),
        Expression::Range(expected) => {
            aggregate(engine, work, body, value, destination, 0, &[expected])
        }
        Expression::Tuple(first, second) => {
            let Rvalue::Aggregate(kind, actual) = value else {
                return Ok(false);
            };
            Ok(matches!(kind.as_ref(), AggregateKind::Tuple)
                && actual.len() == 2
                && input(
                    engine,
                    work,
                    body,
                    &actual[rustc_abi::FieldIdx::from_usize(0)],
                    first,
                )?
                && input(
                    engine,
                    work,
                    body,
                    &actual[rustc_abi::FieldIdx::from_usize(1)],
                    second,
                )?)
        }
    }
}

struct CallTarget<'a> {
    name: &'a str,
    inputs: &'a [Input],
    output: usize,
    next: usize,
}

fn call<'tcx>(
    observation: &GuardedRangeSource<'_, 'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    actual: &TerminatorKind<'tcx>,
    expected: CallTarget<'_>,
) -> Result<bool, Failure> {
    work.charge(24 + 16 * expected.inputs.len())?;
    let CallTarget {
        name,
        inputs: expected,
        output,
        next,
    } = expected;
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        ..
    } = actual
    else {
        return Ok(false);
    };
    let engine = observation.engine;
    if !direct(*destination, output)
        || target.map(|block| block.as_usize()) != Some(next)
        || *unwind != UnwindAction::Unreachable
        || args.len() != expected.len()
    {
        return Ok(false);
    }
    let ty::FnDef(id, parameters) = func.ty(&body.local_decls, engine.tcx).kind() else {
        return Ok(false);
    };
    if key(work, *id)? != name {
        return Ok(false);
    }
    work.charge(16 + 8 * parameters.skip_binder().len() + 4 * observation.helpers.len())?;
    let selected = engine.resolve_function_item(*id, parameters.skip_binder())?;
    let Some(helper) = observation
        .helpers
        .iter()
        .find(|helper| helper.selected == selected)
    else {
        return Ok(false);
    };
    if observation.signatures.get(&selected) != Some(&helper.signature) {
        return Ok(false);
    }
    work.charge(4 + helper.signature.bound_vars().len())?;
    let signature = engine
        .tcx
        .instantiate_bound_regions_with_erased(helper.signature);
    if signature.c_variadic()
        || signature.inputs().len() != args.len()
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || engine.tcx.erase_and_anonymize_regions(signature.output())
            != body.local_decls[destination.local].ty
    {
        return Ok(false);
    }
    for ((argument, expected), original) in args.iter().zip(expected).zip(signature.inputs()) {
        work.charge(16)?; // Actual operand type, formal erasure/equality and each transport visit.
        if argument.node.ty(&body.local_decls, engine.tcx)
            != engine.tcx.erase_and_anonymize_regions(*original)
            || !input(engine, work, body, &argument.node, *expected)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn terminator<'tcx>(
    source: &GuardedRangeSource<'_, 'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    actual: &TerminatorKind<'tcx>,
    expected: End,
) -> Result<bool, Failure> {
    work.charge(24)?;
    let engine = source.engine;
    match expected {
        End::Goto(expected) => Ok(matches!(actual, TerminatorKind::Goto { target }
            if target.as_usize() == expected)),
        End::Return => Ok(matches!(actual, TerminatorKind::Return)),
        End::Unreachable => Ok(matches!(actual, TerminatorKind::Unreachable)),
        End::Boolean(expected, zero, otherwise) => {
            let TerminatorKind::SwitchInt { discr, targets } = actual else {
                return Ok(false);
            };
            Ok(input(engine, work, body, discr, expected)?
                && targets
                    .iter()
                    .eq([(0, rustc_middle::mir::BasicBlock::from_usize(zero))])
                && targets.otherwise().as_usize() == otherwise)
        }
        End::Option(expected, some, none, otherwise) => {
            let TerminatorKind::SwitchInt { discr, targets } = actual else {
                return Ok(false);
            };
            Ok(input(engine, work, body, discr, expected)?
                && targets.iter().eq([
                    (1, rustc_middle::mir::BasicBlock::from_usize(some)),
                    (0, rustc_middle::mir::BasicBlock::from_usize(none)),
                ])
                && targets.otherwise().as_usize() == otherwise)
        }
        End::Overflow(local, op, left, right, next) => {
            let TerminatorKind::Assert {
                cond,
                expected: flag,
                msg,
                target,
                unwind,
            } = actual
            else {
                return Ok(false);
            };
            let AssertKind::Overflow(actual_op, actual_left, actual_right) = msg.as_ref() else {
                return Ok(false);
            };
            Ok(!flag
                && target.as_usize() == next
                && *unwind == UnwindAction::Unreachable
                && *actual_op == op
                && input(engine, work, body, cond, MF(local, 1))?
                && input(engine, work, body, actual_left, left)?
                && input(engine, work, body, actual_right, right)?)
        }
        End::Bounds(expected, length, index, next) => {
            let TerminatorKind::Assert {
                cond,
                expected: flag,
                msg,
                target,
                unwind,
            } = actual
            else {
                return Ok(false);
            };
            let AssertKind::BoundsCheck {
                len,
                index: actual_index,
            } = msg.as_ref()
            else {
                return Ok(false);
            };
            Ok(*flag
                && target.as_usize() == next
                && *unwind == UnwindAction::Unreachable
                && input(engine, work, body, cond, expected)?
                && input(engine, work, body, len, length)?
                && input(engine, work, body, actual_index, index)?)
        }
        End::Call(name, expected, output, next) => call(
            source,
            work,
            body,
            actual,
            CallTarget {
                name,
                inputs: expected,
                output,
                next,
            },
        ),
    }
}

fn local_type<'tcx>(
    engine: &Engine<'tcx>,
    work: &mut Work,
    original: Ty<'tcx>,
    expected: LocalType,
) -> Result<bool, Failure> {
    work.charge(16)?;
    let tcx = engine.tcx;
    let valid = match expected {
        LocalType::Byte => original == tcx.types.u8,
        LocalType::Word => original == tcx.types.usize,
        LocalType::Bool => original == tcx.types.bool,
        LocalType::Signed => original == tcx.types.isize,
        LocalType::Unit => original == tcx.types.unit,
        LocalType::Slice => matches!(original.kind(), ty::Ref(_, inner, rustc_hir::Mutability::Not)
            if matches!(inner.kind(), ty::Slice(item) if *item == tcx.types.u8)),
        LocalType::BytePointer => {
            matches!(original.kind(), ty::RawPtr(inner, rustc_hir::Mutability::Not)
                if *inner == tcx.types.u8)
        }
        LocalType::WordPointer => {
            matches!(original.kind(), ty::RawPtr(inner, rustc_hir::Mutability::Not)
                if *inner == tcx.types.usize)
        }
        LocalType::Overflow => {
            matches!(original.kind(), ty::Tuple(fields)
                if fields.as_slice() == [tcx.types.usize, tcx.types.bool])
        }
        LocalType::Arguments => matches!(original.kind(), ty::Tuple(fields) if fields.len() == 2
            && fields[0] == tcx.types.u8
            && matches!(fields[1].kind(), ty::Ref(_, inner, rustc_hir::Mutability::Not)
                if matches!(inner.kind(), ty::Slice(item) if *item == tcx.types.u8))),
        LocalType::Option => {
            matches!(original.kind(), ty::Adt(def, args)
                if tcx.lang_items().get(LangItem::Option) == Some(def.did())
                && args.len() == 1 && args[0].as_type() == Some(tcx.types.usize))
        }
        LocalType::Range => {
            if let ty::Adt(def, args) = original.kind() {
                args.len() == 1
                    && args[0].as_type() == Some(tcx.types.usize)
                    && key(work, def.did())? == "DefId(core::ops::range::RangeTo)"
            } else {
                false
            }
        }
    };
    Ok(valid)
}

fn shape<'tcx>(
    source: &GuardedRangeSource<'_, 'tcx>,
    work: &mut Work,
    body: &Body<'tcx>,
    expected_key: &str,
    locals: &[LocalType],
    blocks: &[Block],
) -> Result<(), Failure> {
    work.charge(16)?;
    if key(work, source.instance.def_id())? != expected_key
        || !source.instance.args.is_empty()
        || body.source.instance != source.instance.def
        || body.arg_count != 2
        || body.local_decls.len() != locals.len()
        || body.basic_blocks.len() != blocks.len()
    {
        return Err("range source complete original Instance/local/CFG inventory differs".into());
    }
    let signature = source
        .signatures
        .get(&source.instance)
        .ok_or("range source lost full signature")?;
    work.charge(20)?;
    if signature.skip_binder().safety() != rustc_hir::Safety::Safe
        || signature.skip_binder().abi() != rustc_abi::ExternAbi::Rust
        || signature.skip_binder().c_variadic()
        || signature.skip_binder().inputs().len() != 2
    {
        return Err("range source original safe Rust signature differs".into());
    }
    for (actual, expected) in body.local_decls.iter().zip(locals) {
        if !local_type(source.engine, work, actual.ty, *expected)? {
            return Err("range source exact original local type differs".into());
        }
    }
    for (actual, expected) in body.basic_blocks.iter().zip(blocks) {
        work.charge(8)?;
        if actual.is_cleanup || actual.statements.len() != expected.assignments.len() {
            return Err("range source complete block/statement inventory differs".into());
        }
        for (actual, A(local, expected)) in actual.statements.iter().zip(expected.assignments) {
            work.charge(8)?;
            let StatementKind::Assign(assignment) = &actual.kind else {
                return Err("range source requires original typed assignments".into());
            };
            if !direct(assignment.0, *local)
                || !expression(source.engine, work, body, *local, &assignment.1, *expected)?
            {
                return Err("range source typed assignment/dataflow differs".into());
            }
        }
        if !terminator(source, work, body, &actual.terminator().kind, expected.end)? {
            return Err("range source complete terminator/dataflow differs".into());
        }
    }
    Ok(())
}

// Non-Clone, operation-local prepared records carry original source authentication only.
// The owned Rc prevents in-place Body mutation; final guards additionally forbid replacement.
struct RangeRecord<'tcx> {
    instance: ty::Instance<'tcx>,
    current: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    helpers: Vec<Helper<'tcx>>,
}

struct GuardedRangeSource<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    helpers: &'a [Helper<'tcx>],
    signatures: &'a HashMap<ty::Instance<'tcx>, ty::PolyFnSig<'tcx>>,
}

// Both actual registries remain borrowed through every schema/constant/layout service.
// Slicing/load/lifetime operations remain unresolved premises, not application assumptions.
struct ConditionalRangeMetadata<'a, 'tcx> {
    records: Vec<RangeRecord<'tcx>>,
    minimum: minimum::MinimumRecord<'tcx>,
    bodies: Ref<'a, HashMap<ty::Instance<'tcx>, Rc<Body<'tcx>>>>,
    signatures: Ref<'a, HashMap<ty::Instance<'tcx>, ty::PolyFnSig<'tcx>>>,
    work: Work,
}

fn record<'tcx>(
    source: SourceObservation<'_, 'tcx>,
    work: &mut Work,
) -> Result<RangeRecord<'tcx>, Failure> {
    work.charge(12)?; // Actual current Rc clone, signature copy, helper Vec move and record fields.
    let current = source
        .bodies
        .get(&source.instance)
        .ok_or("range preparation lost authenticated current Body")?
        .clone();
    let signature = *source
        .signatures
        .get(&source.instance)
        .ok_or("range preparation lost authenticated original signature")?;
    let SourceObservation {
        instance,
        helpers,
        bodies,
        signatures,
        ..
    } = source;
    drop(bodies);
    drop(signatures);
    Ok(RangeRecord {
        instance,
        current,
        signature,
        helpers,
    })
}

fn selected<'tcx>(
    source: &RangeRecord<'tcx>,
    name: &str,
    work: &mut Work,
) -> Result<ty::Instance<'tcx>, Failure> {
    for helper in &source.helpers {
        work.charge(4)?;
        if key(work, helper.selected.def_id())? == name {
            return Ok(helper.selected);
        }
    }
    Err("range source actual helper Instance is absent".into())
}

fn conditional<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<ConditionalRangeMetadata<'a, 'tcx>, Failure> {
    let root_source = observe_inner(engine, root, 0, prior)?;
    let mut work = Work::new(root_source.work.used)?;
    let root_record = record(root_source, &mut work)?;
    let naive = selected(&root_record, NAIVE_KEY, &mut work)?;
    let aligned = selected(&root_record, ALIGNED_KEY, &mut work)?;
    let forwarder = observe_inner(engine, aligned, 1, work.used)?;
    work.used = forwarder.work.used;
    let forwarder_record = record(forwarder, &mut work)?;
    let runtime = selected(&forwarder_record, RUNTIME_KEY, &mut work)?;
    let naive_source = observe_inner(engine, naive, 1, work.used)?;
    work.used = naive_source.work.used;
    let naive_record = record(naive_source, &mut work)?;
    let runtime_source = observe_inner(engine, runtime, 2, work.used)?;
    work.used = runtime_source.work.used;
    let runtime_record = record(runtime_source, &mut work)?;
    let minimum = selected(
        &runtime_record,
        "DefId(core::cmp::impls::{impl#59}::min)",
        &mut work,
    )?;
    let minimum = minimum::prepare(engine, minimum, &mut work)?;
    work.charge(20)?; // Actual four-element record Vec allocation and four record moves.
    let records = vec![root_record, forwarder_record, naive_record, runtime_record];
    bind_records(engine, records, minimum, work)
}

fn bind_records<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    records: Vec<RangeRecord<'tcx>>,
    minimum: minimum::MinimumRecord<'tcx>,
    mut work: Work,
) -> Result<ConditionalRangeMetadata<'a, 'tcx>, Failure> {
    work.charge(4)?; // Actual consumed private prepared-record transition.
    if records.len() != 4 {
        return Err("range preparation requires all four original source records".into());
    }
    work.charge(8)?;
    let bodies = engine
        .bodies
        .try_borrow()
        .map_err(|_| "range source current Body registry is borrowed")?;
    let signatures = engine
        .call_signatures
        .try_borrow()
        .map_err(|_| "range source full signature registry is borrowed")?;
    // No preparation or cache publication occurs after this point. Pointer equality is only
    // revalidation of a private just-authenticated immutable record, never Memory authority.
    for (record, (name, locals, blocks)) in records.iter().zip([
        (ROOT_KEY, ROOT_LOCALS, ROOT),
        (ALIGNED_KEY, FORWARDER_LOCALS, FORWARDER),
        (NAIVE_KEY, NAIVE_LOCALS, NAIVE),
        (RUNTIME_KEY, RUNTIME_LOCALS, RUNTIME),
    ]) {
        work.charge(8 + 4 * record.helpers.len())?;
        if !bodies
            .get(&record.instance)
            .is_some_and(|current| Rc::ptr_eq(current, &record.current))
            || signatures.get(&record.instance) != Some(&record.signature)
        {
            return Err("range prepared original/current source identity changed".into());
        }
        for helper in &record.helpers {
            if signatures.get(&helper.selected) != Some(&helper.signature) {
                return Err("range prepared original helper signature changed".into());
            }
        }
        work.charge(4)?; // Actual operation-local borrowed checker view construction.
        let source = GuardedRangeSource {
            engine,
            instance: record.instance,
            helpers: &record.helpers,
            signatures: &signatures,
        };
        shape(&source, &mut work, &record.current, name, locals, blocks)?;
    }
    minimum::check(engine, &minimum, &bodies, &signatures, &mut work)?;
    work.charge(9)?; // Records plus minimum metadata, no external predicate exists.
    Ok(ConditionalRangeMetadata {
        records,
        minimum,
        bodies,
        signatures,
        work,
    })
}

pub(super) fn reject_pending_range<'tcx>(
    engine: &Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<usize, Failure> {
    let mut metadata = conditional(engine, root, prior)?;
    metadata.work.charge(16 + 4 * metadata.records.len())?;
    for record in &metadata.records {
        if !metadata
            .bodies
            .get(&record.instance)
            .is_some_and(|body| Rc::ptr_eq(body, &record.current))
            || metadata.signatures.get(&record.instance) != Some(&record.signature)
        {
            return Err("range held source guards lost prepared identity".into());
        }
    }
    minimum::check(
        engine,
        &metadata.minimum,
        &metadata.bodies,
        &metadata.signatures,
        &mut metadata.work,
    )?;
    // Consume conditional metadata. PendingSources still refuses its missing edge: raw-parts,
    // lifetime, slice and word-load premises remain undischarged.
    Ok(metadata.work.used)
}
