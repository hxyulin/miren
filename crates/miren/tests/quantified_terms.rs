#![forbid(unsafe_code)]

use miren::smt::horn::{Atom, Clause, System};
use miren::smt::{Context, Op, Quantifier, Sort, Term};
use std::collections::BTreeSet;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

fn solve(assertions: &str) -> String {
    let executable = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.venv/bin/z3");
    let mut child = Command::new(executable)
        .args(["-in", "-smt2", "-T:6"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let query = format!("(set-logic ALL)\n(set-option :timeout 5000)\n{assertions}\n(check-sat)\n");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(query.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let result = String::from_utf8(output.stdout).unwrap().trim().to_owned();
    assert!(
        matches!(result.as_str(), "sat" | "unsat"),
        "{query}: {result}"
    );
    result
}

fn emitted(context: &Context, roots: &[Term], joint: bool) -> String {
    let symbols = roots.iter().flat_map(Term::symbols).collect();
    let mut text = context.declarations_for(&symbols).unwrap().join("\n");
    if joint {
        text.push_str(&format!(
            "\n(assert {})",
            context.smt_conjunction(roots, 200_000).unwrap()
        ));
    } else {
        for root in roots {
            text.push_str(&format!("\n(assert {})", root.smt(200_000).unwrap()));
        }
    }
    text
}

#[test]
fn explicit_binding_certifies_context_sorts_and_interned_identity() {
    let context = Context::default();
    let x = context.symbol(0, Sort::Bool).unwrap();
    let quantified = context.quantify(Quantifier::Exists, &x, &x).unwrap();
    assert_eq!(
        quantified,
        context.quantify(Quantifier::Exists, &x, &x).unwrap()
    );
    assert_ne!(
        quantified,
        context.quantify(Quantifier::Forall, &x, &x).unwrap()
    );
    assert!(quantified.has_quantifiers());
    let printed = quantified.smt(2000).unwrap();
    assert!(quantified.smt(printed.len()).is_ok());
    assert!(quantified.smt(printed.len() - 1).is_err());
    assert!(!x.has_quantifiers());
    assert!(quantified.symbols().is_empty());
    assert_eq!(x.symbols(), BTreeSet::from([0]));
    assert!(
        context
            .quantify(Quantifier::Exists, &context.boolean(true), &x)
            .is_err()
    );
    assert!(
        context
            .quantify(Quantifier::Exists, &x, &context.bit_vector(0, 8).unwrap())
            .is_err()
    );
    let other = Context::default();
    assert!(
        context
            .quantify(
                Quantifier::Exists,
                &other.symbol(0, Sort::Bool).unwrap(),
                &x
            )
            .is_err()
    );
    assert!(
        context
            .quantify(Quantifier::Exists, &x, &other.boolean(true))
            .is_err()
    );
    assert!(context.symbol(1, Sort::BitVec(0)).is_err());
    assert!(
        context
            .symbol(
                1,
                Sort::Float {
                    exponent: 5,
                    significand: 11
                }
            )
            .is_err()
    );
}

#[test]
fn the_same_symbol_is_bound_in_one_root_and_free_in_another() {
    let context = Context::default();
    let x = context.symbol(0, Sort::Bool).unwrap();
    let exists = context.quantify(Quantifier::Exists, &x, &x).unwrap();
    let negative = context.apply(Op::Not, &[x]).unwrap();
    let reference =
        "(declare-const free Bool)\n(assert (exists ((local Bool)) local))\n(assert (not free))";
    assert_eq!(solve(reference), "sat");
    for joint in [false, true] {
        let text = emitted(&context, &[exists.clone(), negative.clone()], joint);
        assert!(text.contains("(declare-const v0 Bool)"));
        assert_eq!(solve(&text), solve(reference));
    }
    // Binding globally instead of lexically would turn this into a contradiction.
    assert_eq!(
        solve("(declare-const x Bool)\n(assert x)\n(assert (not x))"),
        "unsat"
    );
}

#[test]
fn binder_dependent_shared_predicates_cannot_hoist_outside_their_scope() {
    let context = Context::default();
    let index = context.symbol(0, Sort::BitVec(8)).unwrap();
    let mut shifted = index.clone();
    for _ in 0..12 {
        shifted = context
            .apply(Op::BvAdd, &[shifted, context.bit_vector(1, 8).unwrap()])
            .unwrap();
    }
    let predicate = context
        .apply(
            Op::BvUnsignedLt,
            &[shifted, context.bit_vector(200, 8).unwrap()],
        )
        .unwrap();
    let all = context
        .quantify(Quantifier::Forall, &index, &predicate)
        .unwrap();
    let roots = [all, predicate.clone(), predicate.clone(), predicate];
    let reference = concat!(
        "(declare-const x (_ BitVec 8))\n(assert (forall ((i (_ BitVec 8))) ",
        "(bvult (bvadd i (_ bv12 8)) (_ bv200 8))))\n(assert (bvult (bvadd x ",
        "(_ bv12 8)) (_ bv200 8)))",
    );
    assert_eq!(solve(reference), "unsat");
    for joint in [false, true] {
        let text = emitted(&context, &roots, joint);
        assert_eq!(solve(&text), solve(reference));
        assert!(!text.contains("(let ((t"), "{text}");
    }
    let mut mutated = roots.clone();
    mutated[0] = context
        .quantify(Quantifier::Exists, &index, &roots[1])
        .unwrap();
    for joint in [false, true] {
        assert_eq!(solve(&emitted(&context, &mutated, joint)), "sat");
    }
    // Illegally replacing the scoped predicate with a free let makes this satisfiable.
    assert_eq!(
        solve(concat!(
            "(declare-const x (_ BitVec 8))\n(assert (let ((p (bvult (bvadd x (_ ",
            "bv12 8)) (_ bv200 8)))) (and (forall ((i (_ BitVec 8))) p) p)))",
        )),
        "sat"
    );
}

#[test]
fn nesting_and_same_symbol_shadowing_preserve_outer_dependencies() {
    let context = Context::default();
    let x = context.symbol(0, Sort::Bool).unwrap();
    let y = context.symbol(1, Sort::Bool).unwrap();
    let same = context.apply(Op::Equal, &[x.clone(), y.clone()]).unwrap();
    let inner = context.quantify(Quantifier::Exists, &y, &same).unwrap();
    assert_eq!(inner.symbols(), BTreeSet::from([0]));
    let outer = context.quantify(Quantifier::Forall, &x, &inner).unwrap();
    assert!(outer.symbols().is_empty());
    assert_eq!(
        solve(&emitted(&context, &[outer], true)),
        solve("(assert (forall ((x Bool)) (exists ((y Bool)) (= x y))))")
    );
    let shadow = context
        .quantify(
            Quantifier::Forall,
            &x,
            &context.quantify(Quantifier::Exists, &x, &x).unwrap(),
        )
        .unwrap();
    let roots = [
        shadow.clone(),
        shadow,
        context.apply(Op::Not, &[x]).unwrap(),
    ];
    for joint in [false, true] {
        assert_eq!(
            solve(&emitted(&context, &roots, joint)),
            solve(concat!(
                "(declare-const x Bool)\n(assert (forall ((x Bool)) (exists ((x Bool)) ",
                "x)))\n(assert (not x))",
            ))
        );
    }
}

#[test]
fn quantified_array_offset_selection_preserves_the_full_64_bit_index_domain() {
    let context = Context::default();
    let array = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(16))),
        )
        .unwrap();
    let index = context.symbol(1, Sort::BitVec(64)).unwrap();
    let offset = context.bit_vector(129, 64).unwrap();
    let shifted = context
        .apply(Op::ArrayOffset, &[array.clone(), offset.clone()])
        .unwrap();
    let selected = context
        .apply(Op::Select, &[shifted, index.clone()])
        .unwrap();
    let original = context
        .apply(
            Op::Select,
            &[
                array,
                context.apply(Op::BvAdd, &[index.clone(), offset]).unwrap(),
            ],
        )
        .unwrap();
    let equal = context.apply(Op::Equal, &[selected, original]).unwrap();
    let all = context
        .quantify(Quantifier::Forall, &index, &equal)
        .unwrap();
    let failure = context.apply(Op::Not, &[all]).unwrap();
    let reference = concat!(
        "(declare-const a (Array (_ BitVec 64) (_ BitVec 16)))\n(assert (not ",
        "(forall ((i (_ BitVec 64))) (= (select (lambda ((j (_ BitVec 64))) ",
        "(select a (bvadd (_ bv129 64) j))) i) (select a (bvadd i (_ bv129 ",
        "64)))))))",
    );
    assert_eq!(solve(reference), "unsat");
    assert_eq!(
        solve(&emitted(&context, &[failure], true)),
        solve(reference)
    );
}

#[test]
fn quantified_float_nan_and_signed_zero_keep_numeric_equality_and_float_metadata() {
    let context = Context::default();
    for (bits, exponent, significand, negative_zero) in
        [(32, 8, 24, 1_u128 << 31), (64, 11, 53, 1_u128 << 63)]
    {
        let raw = context.symbol(bits, Sort::BitVec(bits)).unwrap();
        let value = context
            .apply(
                Op::FloatFromBits {
                    exponent,
                    significand,
                },
                std::slice::from_ref(&raw),
            )
            .unwrap();
        let reflexive = context.apply(Op::FpEqual, &[value.clone(), value]).unwrap();
        let all = context
            .quantify(Quantifier::Forall, &raw, &reflexive)
            .unwrap();
        assert!(all.uses_floating_point());
        assert_eq!(
            solve(&emitted(&context, &[all], false)),
            solve(&format!(
                concat!(
                    "(assert (forall ((bits (_ BitVec {bits}))) (fp.eq ((_ to_fp ",
                    "{exponent} {significand}) bits) ((_ to_fp {exponent} {significand}) ",
                    "bits))))",
                ),
                bits = bits,
                exponent = exponent,
                significand = significand
            ))
        );
        let plus = context
            .apply(
                Op::PositiveZero {
                    exponent,
                    significand,
                },
                &[],
            )
            .unwrap();
        let minus = context
            .apply(
                Op::FloatFromBits {
                    exponent,
                    significand,
                },
                &[context.bit_vector(negative_zero, bits).unwrap()],
            )
            .unwrap();
        let equal = context.apply(Op::FpEqual, &[plus, minus]).unwrap();
        let exists = context.quantify(Quantifier::Exists, &raw, &equal).unwrap();
        assert!(exists.uses_floating_point());
        assert_eq!(solve(&emitted(&context, &[exists], true)), "sat");
    }
    let floating = context
        .symbol(
            100,
            Sort::Float {
                exponent: 8,
                significand: 24,
            },
        )
        .unwrap();
    let vacuous = context
        .quantify(Quantifier::Forall, &floating, &context.boolean(true))
        .unwrap();
    assert!(
        vacuous.uses_floating_point(),
        "binder sort must remain in floating metadata"
    );
}

#[test]
fn decoded_char_gap_is_preserved_under_quantified_logical_seeds() {
    let context = Context::default();
    let seed = context.symbol(0, Sort::BitVec(32)).unwrap();
    let valid_seed = context
        .apply(
            Op::BvUnsignedLt,
            &[seed.clone(), context.bit_vector(0x10_f800, 32).unwrap()],
        )
        .unwrap();
    let below = context
        .apply(
            Op::BvUnsignedLt,
            &[seed.clone(), context.bit_vector(0xd800, 32).unwrap()],
        )
        .unwrap();
    let decoded = context
        .apply(
            Op::Ite,
            &[
                below,
                seed.clone(),
                context
                    .apply(
                        Op::BvAdd,
                        &[seed.clone(), context.bit_vector(0x800, 32).unwrap()],
                    )
                    .unwrap(),
            ],
        )
        .unwrap();
    let surrogate = context
        .apply(
            Op::And,
            &[
                context
                    .apply(
                        Op::BvUnsignedGe,
                        &[decoded.clone(), context.bit_vector(0xd800, 32).unwrap()],
                    )
                    .unwrap(),
                context
                    .apply(
                        Op::BvUnsignedLe,
                        &[decoded, context.bit_vector(0xdfff, 32).unwrap()],
                    )
                    .unwrap(),
            ],
        )
        .unwrap();
    let counterexample = context.apply(Op::And, &[valid_seed, surrogate]).unwrap();
    let exists = context
        .quantify(Quantifier::Exists, &seed, &counterexample)
        .unwrap();
    let reference = concat!(
        "(assert (exists ((s (_ BitVec 32))) (and (bvult s (_ bv1112064 32)) ",
        "(let ((c (ite (bvult s (_ bv55296 32)) s (bvadd s (_ bv2048 32))))) ",
        "(and (bvuge c (_ bv55296 32)) (bvule c (_ bv57343 32)))))))",
    );
    assert_eq!(solve(reference), "unsat");
    assert_eq!(solve(&emitted(&context, &[exists], true)), solve(reference));
}

#[test]
fn deep_lexical_metadata_and_printing_stay_iterative_and_byte_bounded() {
    let context = Context::default();
    let symbol = context.symbol(0, Sort::Bool).unwrap();
    let other = context.symbol(1, Sort::Bool).unwrap();
    let mut terms = vec![symbol.clone()];
    for _ in 0..10_000 {
        let body = context
            .apply(Op::Xor, &[terms.last().unwrap().clone(), other.clone()])
            .unwrap();
        terms.push(
            context
                .quantify(Quantifier::Forall, &symbol, &body)
                .unwrap(),
        );
    }
    let root = terms.last().unwrap();
    assert_eq!(root.symbols(), BTreeSet::from([1]));
    assert!(root.smt(1024).unwrap_err().contains("byte budget"));
    while terms.pop().is_some() {}
}

#[test]
fn horn_explicitly_refuses_quantifiers_in_conditions_and_relation_arguments() {
    let context = Context::default();
    let x = context.symbol(0, Sort::Bool).unwrap();
    let quantified = context.quantify(Quantifier::Exists, &x, &x).unwrap();
    let mut system = System {
        relations: vec![vec![Sort::Bool]],
        clauses: vec![Clause {
            premise: None,
            conditions: vec![quantified.clone()],
            conclusion: None,
        }],
    };
    assert!(
        system
            .smt(&context, 2000)
            .unwrap_err()
            .contains("quantified terms")
    );
    system.clauses[0].conditions.clear();
    system.clauses[0].conclusion = Some(Atom {
        relation: 0,
        arguments: vec![quantified],
    });
    assert!(
        system
            .smt(&context, 2000)
            .unwrap_err()
            .contains("quantified terms")
    );
}
