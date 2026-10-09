//! Typed, interned solver terms. SMT-LIB is emitted only by the printer.

mod fold;
pub mod horn;
mod printer;

use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::{Rc, Weak};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    BitVec(u32),
    Float { exponent: u32, significand: u32 },
    RoundingMode,
    Array(Box<Sort>, Box<Sort>),
}

impl Sort {
    fn uses_floating_point(&self) -> bool {
        match self {
            Self::Float { .. } | Self::RoundingMode => true,
            Self::Array(index, element) => {
                index.uses_floating_point() || element.uses_floating_point()
            }
            Self::Bool | Self::BitVec(_) => false,
        }
    }

    fn validate(&self) -> Result<(), String> {
        match self {
            Self::Bool | Self::RoundingMode => Ok(()),
            Self::BitVec(bits) => {
                if (1..=256).contains(bits) {
                    Ok(())
                } else {
                    Err("term bit-vector width must be between 1 and 256".to_owned())
                }
            }
            Self::Float {
                exponent,
                significand,
            } => {
                if matches!((*exponent, *significand), (8, 24) | (11, 53)) {
                    Ok(())
                } else {
                    Err("term floating-point format must be binary32 or binary64".to_owned())
                }
            }
            Self::Array(index, element) => {
                index.validate()?;
                element.validate()
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rounding {
    NearestEven,
    NearestAway,
    TowardPositive,
    TowardNegative,
    TowardZero,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Not,
    And,
    Or,
    Xor,
    Equal,
    Ite,
    BvNot,
    BvNeg,
    BvAdd,
    BvSub,
    BvMul,
    BvUnsignedDiv,
    BvSignedDiv,
    BvUnsignedRem,
    BvSignedRem,
    BvAnd,
    BvOr,
    BvXor,
    BvShiftLeft,
    BvLogicalShiftRight,
    BvArithmeticShiftRight,
    BvUnsignedLt,
    BvUnsignedLe,
    BvUnsignedGt,
    BvUnsignedGe,
    BvSignedLt,
    BvSignedLe,
    BvSignedGt,
    BvSignedGe,
    Extract { high: u32, low: u32 },
    ZeroExtend(u32),
    SignExtend(u32),
    Concat,
    Select,
    Store,
    ArrayOffset,
    ConstArray { index_bits: u32 },
    FpNeg,
    FpAbs,
    FpIsNaN,
    FpIsInfinite,
    FpEqual,
    FpLt,
    FpLe,
    FpGt,
    FpGe,
    FpAdd,
    FpSub,
    FpMul,
    FpDiv,
    FpRem,
    FpRoundToIntegral,
    FpSqrt,
    FpFma,
    FloatFromBits { exponent: u32, significand: u32 },
    SignedToFloat { exponent: u32, significand: u32 },
    UnsignedToFloat { exponent: u32, significand: u32 },
    FloatToFloat { exponent: u32, significand: u32 },
    FloatToSigned(u32),
    FloatToUnsigned(u32),
    PositiveZero { exponent: u32, significand: u32 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Constant {
    Bool(bool),
    BitVec(u128),
    Rounding(Rounding),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum KeyKind {
    Constant(Constant),
    Symbol(u32),
    Apply(Op, Vec<usize>),
    Quantified(Quantifier, usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Key {
    sort: Sort,
    kind: KeyKind,
}

enum Kind {
    Constant(Constant),
    Symbol(u32),
    Apply(Op, Vec<Term>),
    Quantified(Quantifier, Term, Term),
}

struct Node {
    id: usize,
    sort: Sort,
    kind: Kind,
    symbols: OnceCell<Option<BTreeSet<u32>>>,
    uses_floating_point: bool,
    has_quantifiers: bool,
}

#[derive(Default)]
struct Pool {
    nodes: HashMap<Key, Weak<Node>>,
    symbols: HashMap<u32, Sort>,
    next_id: usize,
}

/// One analysis owns a context. Clones share its interner, never another root's symbols.
#[derive(Clone, Default)]
pub struct Context(Rc<RefCell<Pool>>);

/// Cloning a term retains a node rather than copying its expression.
#[derive(Clone)]
pub struct Term {
    node: Rc<Node>,
    context: Context,
}

impl fmt::Debug for Term {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Term")
            .field("id", &self.node.id)
            .field("sort", &self.node.sort)
            .finish()
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.context.0, &other.context.0) && self.node.id == other.node.id
    }
}

impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.context.0).hash(state);
        self.node.id.hash(state);
    }
}

impl Term {
    pub fn id(&self) -> usize {
        self.node.id
    }

    pub fn sort(&self) -> &Sort {
        &self.node.sort
    }

    pub fn context(&self) -> &Context {
        &self.context
    }

    pub fn symbol_index(&self) -> Option<u32> {
        match self.node.kind {
            Kind::Symbol(index) => Some(index),
            Kind::Constant(_) | Kind::Apply(_, _) | Kind::Quantified(..) => None,
        }
    }

    pub fn symbols(&self) -> BTreeSet<u32> {
        if let Some(Some(symbols)) = self.node.symbols.get() {
            return symbols.clone();
        }
        if !self.has_quantifiers() {
            // Preserve the existing quantifier-free traversal and root-only retained cache.
            let mut visited = HashSet::new();
            let mut symbols = BTreeSet::new();
            let mut pending = vec![self];
            while let Some(term) = pending.pop() {
                if !visited.insert(term.id()) {
                    continue;
                }
                if let Some(Some(cached)) = term.node.symbols.get() {
                    symbols.extend(cached);
                    continue;
                }
                match &term.node.kind {
                    Kind::Symbol(index) => {
                        symbols.insert(*index);
                    }
                    Kind::Apply(_, children) => pending.extend(children),
                    Kind::Constant(_) => {}
                    Kind::Quantified(..) => unreachable!("quantifier-free metadata is retained"),
                }
            }
            let _ = self
                .node
                .symbols
                .set((symbols.len() <= 64).then(|| symbols.clone()));
            return symbols;
        }
        let mut computed = HashMap::<usize, BTreeSet<u32>>::new();
        let mut pending = vec![(self, false)];
        while let Some((term, expanded)) = pending.pop() {
            if computed.contains_key(&term.id()) {
                continue;
            }
            if let Some(Some(cached)) = term.node.symbols.get() {
                computed.insert(term.id(), cached.clone());
                continue;
            }
            if !term.has_quantifiers() {
                computed.insert(term.id(), term.symbols());
                continue;
            }
            if !expanded {
                pending.push((term, true));
                match &term.node.kind {
                    Kind::Apply(_, children) => {
                        pending.extend(children.iter().map(|child| (child, false)));
                    }
                    Kind::Quantified(_, _, body) => pending.push((body, false)),
                    Kind::Constant(_) | Kind::Symbol(_) => {}
                }
                continue;
            }
            let symbols = match &term.node.kind {
                Kind::Constant(_) => BTreeSet::new(),
                Kind::Symbol(index) => BTreeSet::from([*index]),
                Kind::Apply(_, children) => {
                    let mut symbols = BTreeSet::new();
                    for child in children {
                        symbols.extend(&computed[&child.id()]);
                    }
                    symbols
                }
                Kind::Quantified(_, binder, body) => {
                    let mut symbols = computed[&body.id()].clone();
                    symbols.remove(&binder.symbol_index().expect("certified symbol binder"));
                    symbols
                }
            };
            // Bound retained metadata even when an expression contains many free inputs.
            let _ = term
                .node
                .symbols
                .set((symbols.len() <= 64).then(|| symbols.clone()));
            computed.insert(term.id(), symbols);
        }
        computed.remove(&self.id()).expect("root symbols computed")
    }

    pub fn belongs_to(&self, context: &Context) -> bool {
        Rc::ptr_eq(&self.context.0, &context.0)
    }

    pub fn negated(&self) -> Option<&Term> {
        match &self.node.kind {
            Kind::Apply(Op::Not, arguments) => arguments.first(),
            Kind::Constant(_) | Kind::Symbol(_) | Kind::Apply(_, _) | Kind::Quantified(..) => None,
        }
    }

    pub fn conjuncts(&self) -> Vec<&Term> {
        let mut pending = vec![self];
        let mut terms = Vec::new();
        while let Some(term) = pending.pop() {
            match &term.node.kind {
                Kind::Apply(Op::And, arguments) => pending.extend(arguments.iter().rev()),
                Kind::Constant(_) | Kind::Symbol(_) | Kind::Apply(_, _) | Kind::Quantified(..) => {
                    terms.push(term)
                }
            }
        }
        terms
    }

    pub fn uses_floating_point(&self) -> bool {
        self.node.uses_floating_point
    }

    pub fn has_quantifiers(&self) -> bool {
        self.node.has_quantifiers
    }

    pub fn constant(&self) -> Option<Constant> {
        match self.node.kind {
            Kind::Constant(constant) => Some(constant),
            Kind::Symbol(_) | Kind::Apply(_, _) | Kind::Quantified(..) => None,
        }
    }

    /// Preserves DAG sharing with scoped lets; rejects output beyond the byte budget.
    pub fn smt(&self, max_bytes: usize) -> Result<String, String> {
        printer::print(self, max_bytes)
    }
}

impl Context {
    pub fn declarations(&self) -> Vec<String> {
        let pool = self.0.borrow();
        let mut symbols: Vec<_> = pool.symbols.iter().collect();
        symbols.sort_by_key(|(index, _)| **index);
        symbols
            .into_iter()
            .map(|(index, sort)| printer::declaration(*index, sort))
            .collect()
    }

    /// Prints only structurally reachable symbols, preserving numeric symbol order.
    pub fn declarations_for(&self, symbols: &BTreeSet<u32>) -> Result<Vec<String>, String> {
        let pool = self.0.borrow();
        symbols
            .iter()
            .map(|index| {
                pool.symbols
                    .get(index)
                    .map(|sort| printer::declaration(*index, sort))
                    .ok_or_else(|| format!("unknown term symbol v{index}"))
            })
            .collect()
    }

    /// Print a Boolean conjunction without folding its roots or adding global symbols.
    pub fn smt_conjunction(&self, roots: &[Term], max_bytes: usize) -> Result<String, String> {
        for root in roots {
            if root.sort() != &Sort::Bool || !root.belongs_to(self) {
                return Err("SMT conjunction requires Boolean terms from its context".into());
            }
        }
        printer::print_conjunction(roots, max_bytes)
    }

    fn intern(&self, sort: Sort, kind: Kind) -> Term {
        let key = Key {
            sort: sort.clone(),
            kind: match &kind {
                Kind::Constant(constant) => KeyKind::Constant(*constant),
                Kind::Symbol(index) => KeyKind::Symbol(*index),
                Kind::Apply(op, terms) => {
                    KeyKind::Apply(*op, terms.iter().map(|term| term.node.id).collect())
                }
                Kind::Quantified(kind, binder, body) => {
                    KeyKind::Quantified(*kind, binder.id(), body.id())
                }
            },
        };
        let mut pool = self.0.borrow_mut();
        if let Some(node) = pool.nodes.get(&key).and_then(Weak::upgrade) {
            return Term {
                node,
                context: self.clone(),
            };
        }
        let uses_floating_point = sort.uses_floating_point()
            || match &kind {
                Kind::Apply(_, children) => children.iter().any(Term::uses_floating_point),
                Kind::Quantified(_, binder, body) => {
                    binder.uses_floating_point() || body.uses_floating_point()
                }
                Kind::Constant(_) | Kind::Symbol(_) => false,
            };
        let has_quantifiers = match &kind {
            Kind::Quantified(..) => true,
            Kind::Apply(_, children) => children.iter().any(Term::has_quantifiers),
            Kind::Constant(_) | Kind::Symbol(_) => false,
        };
        let node = Rc::new(Node {
            id: pool.next_id,
            sort,
            kind,
            symbols: OnceCell::new(),
            uses_floating_point,
            has_quantifiers,
        });
        pool.next_id += 1;
        pool.nodes.insert(key, Rc::downgrade(&node));
        Term {
            node,
            context: self.clone(),
        }
    }

    pub fn boolean(&self, value: bool) -> Term {
        self.intern(Sort::Bool, Kind::Constant(Constant::Bool(value)))
    }

    pub fn bit_vector(&self, value: u128, bits: u32) -> Result<Term, String> {
        let sort = Sort::BitVec(bits);
        sort.validate()?;
        let value = if bits < 128 {
            value & (u128::MAX >> (128 - bits))
        } else {
            value
        };
        Ok(self.intern(sort, Kind::Constant(Constant::BitVec(value))))
    }

    pub fn rounding(&self, rounding: Rounding) -> Term {
        self.intern(
            Sort::RoundingMode,
            Kind::Constant(Constant::Rounding(rounding)),
        )
    }

    pub fn symbol(&self, index: u32, sort: Sort) -> Result<Term, String> {
        sort.validate()?;
        let mut pool = self.0.borrow_mut();
        if let Some(previous) = pool.symbols.get(&index)
            && previous != &sort
        {
            return Err("term symbol redeclared with a different sort".to_owned());
        }
        pool.symbols.insert(index, sort.clone());
        drop(pool);
        Ok(self.intern(sort, Kind::Symbol(index)))
    }

    pub fn apply(&self, op: Op, arguments: &[Term]) -> Result<Term, String> {
        if arguments
            .iter()
            .any(|term| !Rc::ptr_eq(&self.0, &term.context.0))
        {
            return Err("term operands belong to different analysis contexts".to_owned());
        }
        let sort = result_sort(op, arguments)?;
        sort.validate()?;
        if let Some(term) = fold::simplify(self, op, arguments, &sort) {
            return Ok(term);
        }
        Ok(self.intern(sort, Kind::Apply(op, arguments.to_vec())))
    }

    /// Lexically binds every occurrence of this Symbol within this Boolean body.
    /// The same symbol remains free outside this node; nested bindings may shadow it.
    /// Consumers should choose fresh logical indices, independently of application inputs.
    pub fn quantify(&self, kind: Quantifier, binder: &Term, body: &Term) -> Result<Term, String> {
        if !binder.belongs_to(self) || !body.belongs_to(self) {
            return Err("quantifier operands belong to different analysis contexts".into());
        }
        if binder.symbol_index().is_none() || body.sort() != &Sort::Bool {
            return Err("quantifier requires a Symbol binder and Boolean body".into());
        }
        binder.sort().validate()?;
        Ok(self.intern(
            Sort::Bool,
            Kind::Quantified(kind, binder.clone(), body.clone()),
        ))
    }
}

fn result_sort(op: Op, args: &[Term]) -> Result<Sort, String> {
    let sorts: Vec<_> = args.iter().map(Term::sort).collect();
    let boolean = |sort: &Sort| *sort == Sort::Bool;
    let bit_vector = |sort: &Sort| matches!(sort, Sort::BitVec(_));
    let float = |sort: &Sort| matches!(sort, Sort::Float { .. });
    let same_pair = |accept: fn(&Sort) -> bool| match sorts.as_slice() {
        [left, right] if left == right && accept(left) => Some((*left).clone()),
        _ => None,
    };
    let target_float = |exponent, significand| Sort::Float {
        exponent,
        significand,
    };
    let result = match op {
        Op::Not => match sorts.as_slice() {
            [Sort::Bool] => Some(Sort::Bool),
            _ => None,
        },
        Op::And | Op::Or => sorts.iter().all(|sort| boolean(sort)).then_some(Sort::Bool),
        Op::Xor => same_pair(boolean),
        Op::Equal => same_pair(|_| true).map(|_| Sort::Bool),
        Op::Ite => match sorts.as_slice() {
            [Sort::Bool, left, right] if left == right => Some((*left).clone()),
            _ => None,
        },
        Op::BvNot | Op::BvNeg => match sorts.as_slice() {
            [sort @ Sort::BitVec(_)] => Some((*sort).clone()),
            _ => None,
        },
        Op::BvAdd
        | Op::BvSub
        | Op::BvMul
        | Op::BvUnsignedDiv
        | Op::BvSignedDiv
        | Op::BvUnsignedRem
        | Op::BvSignedRem
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvShiftLeft
        | Op::BvLogicalShiftRight
        | Op::BvArithmeticShiftRight => same_pair(bit_vector),
        Op::BvUnsignedLt
        | Op::BvUnsignedLe
        | Op::BvUnsignedGt
        | Op::BvUnsignedGe
        | Op::BvSignedLt
        | Op::BvSignedLe
        | Op::BvSignedGt
        | Op::BvSignedGe => same_pair(bit_vector).map(|_| Sort::Bool),
        Op::Extract { high, low } => match sorts.as_slice() {
            [Sort::BitVec(bits)] if low <= high && high < *bits => {
                Some(Sort::BitVec(high - low + 1))
            }
            _ => None,
        },
        Op::ZeroExtend(extra) | Op::SignExtend(extra) => match sorts.as_slice() {
            [Sort::BitVec(bits)] => bits.checked_add(extra).map(Sort::BitVec),
            _ => None,
        },
        Op::Concat => match sorts.as_slice() {
            [Sort::BitVec(left), Sort::BitVec(right)] => left.checked_add(*right).map(Sort::BitVec),
            _ => None,
        },
        Op::Select => match sorts.as_slice() {
            [Sort::Array(index, element), actual] if index.as_ref() == *actual => {
                Some(element.as_ref().clone())
            }
            _ => None,
        },
        Op::Store => match sorts.as_slice() {
            [
                array @ Sort::Array(index, element),
                actual_index,
                actual_element,
            ] if index.as_ref() == *actual_index && element.as_ref() == *actual_element => {
                Some((*array).clone())
            }
            _ => None,
        },
        Op::ArrayOffset => match sorts.as_slice() {
            [array @ Sort::Array(index, _), actual]
                if matches!(index.as_ref(), Sort::BitVec(_)) && index.as_ref() == *actual =>
            {
                Some((*array).clone())
            }
            _ => None,
        },
        Op::ConstArray { index_bits } => match sorts.as_slice() {
            [element] => Some(Sort::Array(
                Box::new(Sort::BitVec(index_bits)),
                Box::new((*element).clone()),
            )),
            _ => None,
        },
        Op::FpNeg | Op::FpAbs => match sorts.as_slice() {
            [sort @ Sort::Float { .. }] => Some((*sort).clone()),
            _ => None,
        },
        Op::FpIsNaN | Op::FpIsInfinite => match sorts.as_slice() {
            [Sort::Float { .. }] => Some(Sort::Bool),
            _ => None,
        },
        Op::FpEqual | Op::FpLt | Op::FpLe | Op::FpGt | Op::FpGe => {
            same_pair(float).map(|_| Sort::Bool)
        }
        Op::FpRem => same_pair(float),
        Op::FpAdd | Op::FpSub | Op::FpMul | Op::FpDiv => match sorts.as_slice() {
            [Sort::RoundingMode, left, right] if left == right && float(left) => {
                Some((*left).clone())
            }
            _ => None,
        },
        Op::FpRoundToIntegral | Op::FpSqrt => match sorts.as_slice() {
            [Sort::RoundingMode, value] if float(value) => Some((*value).clone()),
            _ => None,
        },
        Op::FpFma => match sorts.as_slice() {
            [Sort::RoundingMode, first, second, third]
                if first == second && first == third && float(first) =>
            {
                Some((*first).clone())
            }
            _ => None,
        },
        Op::FloatFromBits {
            exponent,
            significand,
        } => match sorts.as_slice() {
            [Sort::BitVec(bits)] if exponent.checked_add(significand) == Some(*bits) => {
                Some(target_float(exponent, significand))
            }
            _ => None,
        },
        Op::SignedToFloat {
            exponent,
            significand,
        }
        | Op::UnsignedToFloat {
            exponent,
            significand,
        } => match sorts.as_slice() {
            [Sort::RoundingMode, Sort::BitVec(_)] => Some(target_float(exponent, significand)),
            _ => None,
        },
        Op::FloatToFloat {
            exponent,
            significand,
        } => match sorts.as_slice() {
            [Sort::RoundingMode, Sort::Float { .. }] => Some(target_float(exponent, significand)),
            _ => None,
        },
        Op::FloatToSigned(bits) | Op::FloatToUnsigned(bits) => match sorts.as_slice() {
            [Sort::RoundingMode, Sort::Float { .. }] => Some(Sort::BitVec(bits)),
            _ => None,
        },
        Op::PositiveZero {
            exponent,
            significand,
        } => sorts
            .is_empty()
            .then_some(target_float(exponent, significand)),
    };
    result.ok_or_else(|| format!("invalid sorts or arity for term operator {op:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wide_lexical_free_sets_keep_bounded_retained_caches() {
        let context = Context::default();
        let symbols: Vec<_> = (0..96)
            .map(|index| context.symbol(index, Sort::Bool).unwrap())
            .collect();
        let body = context.apply(Op::And, &symbols).unwrap();
        let expected: BTreeSet<_> = (0..96).collect();
        assert_eq!(body.symbols(), expected);
        assert!(matches!(body.node.symbols.get(), Some(None)));
        let quantified = context
            .quantify(Quantifier::Exists, &symbols[65], &body)
            .unwrap();
        let mut free = expected.clone();
        free.remove(&65);
        assert_eq!(quantified.symbols(), free);
        assert!(matches!(quantified.node.symbols.get(), Some(None)));
        assert_eq!(body.symbols(), expected);
        let mixed = context
            .apply(Op::Or, &[quantified, symbols[65].clone()])
            .unwrap();
        assert_eq!(mixed.symbols(), expected);
        assert_eq!(mixed.symbols(), expected);
    }
}
