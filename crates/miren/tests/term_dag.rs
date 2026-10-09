use miren::smt::{Constant, Context, Op, Rounding, Sort, Term};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn solve(queries: &[String]) -> Vec<String> {
    let solver = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../.venv/bin/z3");
    let mut child = Command::new(solver)
        .args(["-in", "-smt2"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("term differential tests require Z3");
    let mut input = String::from("(set-logic ALL)\n(set-option :timeout 5000)\n");
    for query in queries {
        input.push_str("(push 1)\n");
        input.push_str(query);
        input.push_str("\n(check-sat)\n(pop 1)\n");
    }
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let answers: Vec<_> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(str::to_owned)
        .collect();
    assert_eq!(answers.len(), queries.len());
    answers
}

fn equivalent(term: &Term, expected: &str) -> String {
    format!(
        "(assert (not (= {} {expected})))",
        term.smt(200_000).unwrap()
    )
}

#[test]
fn equal_terms_share_nodes_and_roots_keep_distinct_namespaces() {
    let context = Context::default();
    let x = context.symbol(0, Sort::BitVec(32)).unwrap();
    let y = context.symbol(1, Sort::BitVec(32)).unwrap();
    let left = context.apply(Op::BvAdd, &[x.clone(), y.clone()]).unwrap();
    let right = context.apply(Op::BvAdd, &[x.clone(), y]).unwrap();
    assert_eq!(left, right);
    assert_eq!(left.smt(100).unwrap(), "(bvadd v0 v1)");
    let other = Context::default().symbol(0, Sort::BitVec(32)).unwrap();
    assert_ne!(x, other);
    assert!(context.apply(Op::BvAdd, &[x, other]).is_err());
    assert!(context.symbol(0, Sort::Bool).is_err());
}

#[test]
fn invalid_sorts_and_arity_are_rejected_before_simplification() {
    let context = Context::default();
    let false_value = context.boolean(false);
    let word = context.bit_vector(1, 8).unwrap();
    for op in [Op::BvAdd, Op::Equal, Op::And, Op::FpEqual, Op::Select] {
        assert!(
            context
                .apply(op, &[false_value.clone(), word.clone()])
                .is_err()
        );
    }
    assert!(context.apply(Op::Not, &[]).is_err());
    assert!(
        context
            .apply(Op::Ite, &[false_value.clone(), word])
            .is_err()
    );
    assert!(context.bit_vector(0, 0).is_err());
    assert!(context.bit_vector(0, 257).is_err());
    assert!(context.symbol(4, Sort::BitVec(0)).is_err());
    assert!(
        context
            .apply(
                Op::Extract { high: 8, low: 0 },
                &[context.bit_vector(0, 8).unwrap()]
            )
            .is_err()
    );
    assert!(
        context
            .apply(Op::ConstArray { index_bits: 0 }, &[false_value])
            .is_err()
    );
}

#[test]
fn structural_boolean_folding_preserves_symbolic_obligations() {
    let context = Context::default();
    let x = context.symbol(0, Sort::Bool).unwrap();
    let negated = context.apply(Op::Not, std::slice::from_ref(&x)).unwrap();
    assert_eq!(context.apply(Op::Not, &[negated]).unwrap(), x);
    assert_eq!(context.apply(Op::And, &[]).unwrap(), context.boolean(true));
    assert_eq!(context.apply(Op::Or, &[]).unwrap(), context.boolean(false));
    assert_eq!(
        context
            .apply(Op::And, &[x.clone(), context.boolean(true)])
            .unwrap(),
        x
    );
    assert_eq!(
        context
            .apply(
                Op::Ite,
                &[context.boolean(false), context.boolean(true), x.clone()]
            )
            .unwrap(),
        x
    );
    let queries = [
        "(declare-const v0 Bool)\n(assert (not v0))".to_owned(),
        "(declare-const v0 Bool)\n(assert v0)\n(assert (not v0))".to_owned(),
    ];
    assert_eq!(solve(&queries), ["sat", "unsat"]);
}

#[test]
fn integer_guard_normalization_matches_z3_for_every_supported_symbolic_width() {
    let mut queries = Vec::new();
    for bits in [1, 8, 16, 32, 64, 128, 256] {
        let context = Context::default();
        let left = context.symbol(0, Sort::BitVec(bits)).unwrap();
        let right = context.symbol(1, Sort::BitVec(bits)).unwrap();
        for (op, name) in [
            (Op::BvUnsignedLt, "bvult"),
            (Op::BvUnsignedLe, "bvule"),
            (Op::BvUnsignedGt, "bvugt"),
            (Op::BvUnsignedGe, "bvuge"),
            (Op::BvSignedLt, "bvslt"),
            (Op::BvSignedLe, "bvsle"),
            (Op::BvSignedGt, "bvsgt"),
            (Op::BvSignedGe, "bvsge"),
        ] {
            let term = context.apply(op, &[left.clone(), right.clone()]).unwrap();
            queries.push(format!(
                "(declare-const v0 (_ BitVec {bits}))\n\
                 (declare-const v1 (_ BitVec {bits}))\n{}",
                equivalent(&term, &format!("({name} v0 v1)")),
            ));
        }
        for (less, greater_equal) in [
            (Op::BvUnsignedLt, Op::BvUnsignedGe),
            (Op::BvSignedLt, Op::BvSignedGe),
        ] {
            let less = context.apply(less, &[left.clone(), right.clone()]).unwrap();
            let greater_equal = context
                .apply(greater_equal, &[left.clone(), right.clone()])
                .unwrap();
            assert_eq!(greater_equal.negated(), Some(&less));
            assert_eq!(
                context
                    .apply(Op::And, &[less, greater_equal])
                    .unwrap()
                    .constant(),
                Some(Constant::Bool(false))
            );
        }
    }
    assert!(solve(&queries).iter().all(|answer| answer == "unsat"));
}

#[test]
fn boolean_groups_flatten_deduplicate_and_fold_only_exact_complements() {
    let context = Context::default();
    let p = context.symbol(0, Sort::Bool).unwrap();
    let q = context.symbol(1, Sort::Bool).unwrap();
    let not_p = context.apply(Op::Not, std::slice::from_ref(&p)).unwrap();
    for (op, opposite_result) in [(Op::And, false), (Op::Or, true)] {
        let group = context.apply(op, &[p.clone(), q.clone()]).unwrap();
        assert_eq!(
            context.apply(op, &[group.clone(), p.clone()]).unwrap(),
            group
        );
        assert_eq!(
            context
                .apply(op, &[group, not_p.clone()])
                .unwrap()
                .constant(),
            Some(Constant::Bool(opposite_result))
        );
        assert!(
            context
                .apply(op, &[p.clone(), q.clone()])
                .unwrap()
                .constant()
                .is_none()
        );
        let foreign = Context::default().symbol(0, Sort::Bool).unwrap();
        assert!(
            context
                .apply(op, &[p.clone(), not_p.clone(), foreign])
                .is_err()
        );
    }
    let decode = Op::FloatFromBits {
        exponent: 8,
        significand: 24,
    };
    let nan = context
        .apply(decode, &[context.bit_vector(0x7fc0_0001, 32).unwrap()])
        .unwrap();
    let zero = context
        .apply(decode, &[context.bit_vector(0, 32).unwrap()])
        .unwrap();
    let less = context
        .apply(Op::FpLt, &[nan.clone(), zero.clone()])
        .unwrap();
    let greater_equal = context.apply(Op::FpGe, &[nan, zero]).unwrap();
    assert!(greater_equal.negated().is_none());
    let both = context.apply(Op::Or, &[less, greater_equal]).unwrap();
    assert_eq!(solve(&[equivalent(&both, "false")]), ["unsat"]);
}

#[test]
fn widened_unsigned_index_guards_match_z3_without_casting_away_out_of_range_bounds() {
    let mut queries = Vec::new();
    for (bits, widened) in [
        (1, 32),
        (8, 32),
        (8, 64),
        (16, 64),
        (32, 64),
        (64, 128),
        (128, 256),
    ] {
        let context = Context::default();
        let value = context.symbol(0, Sort::BitVec(bits)).unwrap();
        let extended = context
            .apply(Op::ZeroExtend(widened - bits), std::slice::from_ref(&value))
            .unwrap();
        let mut bounds = vec![0, 1, u128::MAX];
        if bits < 128 {
            bounds.extend([(1_u128 << bits) - 1, 1_u128 << bits]);
        }
        for bound in bounds {
            let constant = context.bit_vector(bound, widened).unwrap();
            let Constant::BitVec(actual) = constant.constant().unwrap() else {
                unreachable!()
            };
            for (operands, expected) in [
                (
                    [extended.clone(), constant.clone()],
                    format!(
                        "(bvult ((_ zero_extend {}) v0) (_ bv{actual} {widened}))",
                        widened - bits
                    ),
                ),
                (
                    [constant, extended.clone()],
                    format!(
                        "(bvult (_ bv{actual} {widened}) ((_ zero_extend {}) v0))",
                        widened - bits
                    ),
                ),
            ] {
                let term = context.apply(Op::BvUnsignedLt, &operands).unwrap();
                queries.push(format!(
                    "(declare-const v0 (_ BitVec {bits}))\n{}",
                    equivalent(&term, &expected)
                ));
            }
        }
        let bound = context.bit_vector(1, widened).unwrap();
        let wide_guard = context.apply(Op::BvUnsignedLt, &[extended, bound]).unwrap();
        let narrow_guard = context
            .apply(
                Op::BvUnsignedLt,
                &[value, context.bit_vector(1, bits).unwrap()],
            )
            .unwrap();
        assert_eq!(wide_guard, narrow_guard);
    }
    assert!(solve(&queries).iter().all(|answer| answer == "unsat"));
}

#[test]
fn boolean_switch_equalities_keep_their_exact_guard_identity() {
    let context = Context::default();
    let p = context.symbol(0, Sort::Bool).unwrap();
    let q = context.symbol(1, Sort::Bool).unwrap();
    let not_p = context.apply(Op::Not, std::slice::from_ref(&p)).unwrap();
    assert_eq!(
        context
            .apply(Op::Equal, &[p.clone(), context.boolean(true)])
            .unwrap(),
        p
    );
    assert_eq!(
        context
            .apply(Op::Equal, &[context.boolean(false), p.clone()])
            .unwrap(),
        not_p
    );
    assert_eq!(
        context.apply(Op::Equal, &[p.clone(), q.clone()]).unwrap(),
        context.apply(Op::Equal, &[q, p]).unwrap()
    );
}

#[test]
fn closed_bit_vector_operations_match_z3_at_signed_and_width_boundaries() {
    let context = Context::default();
    let operations = [
        (Op::BvAdd, "bvadd"),
        (Op::BvSub, "bvsub"),
        (Op::BvMul, "bvmul"),
        (Op::BvUnsignedDiv, "bvudiv"),
        (Op::BvSignedDiv, "bvsdiv"),
        (Op::BvUnsignedRem, "bvurem"),
        (Op::BvSignedRem, "bvsrem"),
        (Op::BvAnd, "bvand"),
        (Op::BvOr, "bvor"),
        (Op::BvXor, "bvxor"),
        (Op::BvShiftLeft, "bvshl"),
        (Op::BvLogicalShiftRight, "bvlshr"),
        (Op::BvArithmeticShiftRight, "bvashr"),
        (Op::BvUnsignedLt, "bvult"),
        (Op::BvUnsignedLe, "bvule"),
        (Op::BvUnsignedGt, "bvugt"),
        (Op::BvUnsignedGe, "bvuge"),
        (Op::BvSignedLt, "bvslt"),
        (Op::BvSignedLe, "bvsle"),
        (Op::BvSignedGt, "bvsgt"),
        (Op::BvSignedGe, "bvsge"),
    ];
    let mut queries = Vec::new();
    for bits in [1, 8, 16, 32, 64, 128] {
        let maximum = u128::MAX >> (128 - bits);
        let sign = 1_u128 << (bits - 1);
        for left in [0, 1, maximum, sign, sign - 1] {
            for right in [0, 1, maximum, sign, sign - 1] {
                let a = context.bit_vector(left, bits).unwrap();
                let b = context.bit_vector(right, bits).unwrap();
                for (op, name) in operations {
                    let term = context.apply(op, &[a.clone(), b.clone()]).unwrap();
                    assert!(term.constant().is_some());
                    queries.push(equivalent(
                        &term,
                        &format!("({name} (_ bv{left} {bits}) (_ bv{right} {bits}))"),
                    ));
                }
            }
        }
    }
    let answers = solve(&queries);
    assert_eq!(answers.len(), queries.len());
    for (answer, query) in answers.iter().zip(queries) {
        assert_eq!(answer, "unsat", "{query}");
    }
}

#[test]
fn widened_arithmetic_keeps_exact_terms_when_native_folding_cannot_represent_them() {
    let context = Context::default();
    let max = context.bit_vector(u128::MAX, 128).unwrap();
    let wide = context.apply(Op::ZeroExtend(128), &[max]).unwrap();
    let product = context.apply(Op::BvMul, &[wide.clone(), wide]).unwrap();
    assert_eq!(product.sort(), &Sort::BitVec(256));
    assert_eq!(product.constant(), None);
    let expected = concat!(
        "(bvmul ((_ zero_extend 128) (_ bv340282366920938463463374607431768211455 128)) ",
        "((_ zero_extend 128) (_ bv340282366920938463463374607431768211455 128)))"
    );
    assert_eq!(solve(&[equivalent(&product, expected)]), ["unsat"]);
}

#[test]
fn floating_point_equality_preserves_nan_and_signed_zero_semantics() {
    let context = Context::default();
    let decode = Op::FloatFromBits {
        exponent: 8,
        significand: 24,
    };
    let nan = context
        .apply(decode, &[context.bit_vector(0x7fc0_0001, 32).unwrap()])
        .unwrap();
    let positive = context
        .apply(decode, &[context.bit_vector(0, 32).unwrap()])
        .unwrap();
    let negative = context
        .apply(decode, &[context.bit_vector(0x8000_0000, 32).unwrap()])
        .unwrap();
    let nan_equal = context.apply(Op::FpEqual, &[nan.clone(), nan]).unwrap();
    assert_eq!(nan_equal.constant(), None);
    let numeric_zero_equal = context
        .apply(Op::FpEqual, &[positive.clone(), negative.clone()])
        .unwrap();
    let structural_zero_equal = context.apply(Op::Equal, &[positive, negative]).unwrap();
    let queries = [
        equivalent(&nan_equal, "false"),
        equivalent(&numeric_zero_equal, "true"),
        equivalent(&structural_zero_equal, "false"),
    ];
    assert_eq!(solve(&queries), ["unsat", "unsat", "unsat"]);
}

#[test]
fn byte_array_updates_and_float_conversions_print_well_typed_terms() {
    let context = Context::default();
    let array = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
        )
        .unwrap();
    let index = context.bit_vector(2, 32).unwrap();
    let byte = context.bit_vector(91, 8).unwrap();
    let stored = context
        .apply(Op::Store, &[array, index.clone(), byte.clone()])
        .unwrap();
    let read = context.apply(Op::Select, &[stored, index]).unwrap();
    assert_eq!(read, byte);
    let constant = context
        .apply(Op::ConstArray { index_bits: 32 }, &[byte])
        .unwrap();
    let word = context.symbol(1, Sort::BitVec(32)).unwrap();
    let converted = context
        .apply(
            Op::UnsignedToFloat {
                exponent: 8,
                significand: 24,
            },
            &[context.rounding(Rounding::NearestEven), word],
        )
        .unwrap();
    let integer = context
        .apply(
            Op::FloatToUnsigned(32),
            &[context.rounding(Rounding::TowardZero), converted],
        )
        .unwrap();
    let queries = [
        equivalent(
            &constant,
            "((as const (Array (_ BitVec 32) (_ BitVec 8))) (_ bv91 8))",
        ),
        format!(
            "(declare-const v1 (_ BitVec 32))\n{}",
            equivalent(
                &integer,
                "((_ fp.to_ubv 32) RTZ ((_ to_fp_unsigned 8 24) RNE v1))"
            )
        ),
    ];
    assert_eq!(solve(&queries), ["unsat", "unsat"]);
}

#[test]
fn the_printer_shares_repeated_terms_without_capturing_symbols_or_growing_exponentially() {
    let context = Context::default();
    let mut term = context.symbol(0, Sort::BitVec(32)).unwrap();
    let mut expanded = "v0".to_owned();
    for _ in 0..12 {
        term = context.apply(Op::BvAdd, &[term.clone(), term]).unwrap();
        expanded = format!("(bvadd {expanded} {expanded})");
        assert!(term.smt(200_000).unwrap().len() <= expanded.len());
    }
    let text = term.smt(200_000).unwrap();
    assert!(text.contains("(let ((t"));
    assert!(text.len() < 600, "{text}");
    assert_eq!(
        solve(&[format!(
            "(declare-const v0 (_ BitVec 32))\n{}",
            equivalent(&term, &expanded)
        )]),
        ["unsat"]
    );
    let changed = format!("(bvadd {expanded} (_ bv1 32))");
    assert_eq!(
        solve(&[format!(
            "(declare-const v0 (_ BitVec 32))\n{}",
            equivalent(&term, &changed)
        )]),
        ["sat"]
    );
    for _ in 0..244 {
        term = context.apply(Op::BvAdd, &[term.clone(), term]).unwrap();
    }
    let text = term.smt(20_000).unwrap();
    assert!(text.len() < 12_000);
    assert!(term.smt(100).is_err());
    assert_eq!(
        context.bit_vector(256, 8).unwrap().constant(),
        Some(Constant::BitVec(0))
    );
}

#[test]
fn modular_add_sub_cancellation_retains_the_exact_other_term_at_every_width() {
    let mut queries = Vec::new();
    for bits in 1..=256 {
        let context = Context::default();
        let offset = context.symbol(0, Sort::BitVec(bits)).unwrap();
        let variable = context.symbol(1, Sort::BitVec(bits)).unwrap();
        let one = context.bit_vector(1, bits).unwrap();
        for retained in [one, variable] {
            for operands in [
                [offset.clone(), retained.clone()],
                [retained.clone(), offset.clone()],
            ] {
                let sum = context.apply(Op::BvAdd, &operands).unwrap();
                let result = context.apply(Op::BvSub, &[sum, offset.clone()]).unwrap();
                assert_eq!(result, retained);
                if [1, 8, 32, 64, 128, 256].contains(&bits) {
                    queries.push(format!(
                        "(declare-const v0 (_ BitVec {bits}))\n\
                         (declare-const v1 (_ BitVec {bits}))\n\
                         (assert (not (= {} (bvsub (bvadd {} {}) v0))))",
                        result.smt(100).unwrap(),
                        operands[0].smt(100).unwrap(),
                        operands[1].smt(100).unwrap(),
                    ));
                }
            }
        }
        let doubled = context
            .apply(Op::BvAdd, &[offset.clone(), offset.clone()])
            .unwrap();
        assert_eq!(
            context
                .apply(Op::BvSub, &[doubled, offset.clone()])
                .unwrap(),
            offset
        );
    }
    assert!(solve(&queries).iter().all(|answer| answer == "unsat"));
}

#[test]
fn add_sub_cancellation_does_not_identify_distinct_terms_or_cross_extensions() {
    let context = Context::default();
    let offset = context.symbol(0, Sort::BitVec(8)).unwrap();
    let other = context.symbol(1, Sort::BitVec(8)).unwrap();
    let one = context.bit_vector(1, 8).unwrap();
    let sum = context.apply(Op::BvAdd, &[offset.clone(), one]).unwrap();
    let unrelated = context.apply(Op::BvSub, &[sum.clone(), other]).unwrap();
    assert_eq!(
        unrelated.smt(100).unwrap(),
        "(bvsub (bvadd v0 (_ bv1 8)) v1)"
    );
    let extended_sum = context.apply(Op::ZeroExtend(8), &[sum]).unwrap();
    let extended_offset = context
        .apply(Op::ZeroExtend(8), std::slice::from_ref(&offset))
        .unwrap();
    let result = context
        .apply(Op::BvSub, &[extended_sum, extended_offset])
        .unwrap();
    assert!(result.constant().is_none());
    let sign_extended = context
        .apply(Op::SignExtend(8), std::slice::from_ref(&offset))
        .unwrap();
    let zero_extended = context
        .apply(Op::ZeroExtend(8), std::slice::from_ref(&offset))
        .unwrap();
    let wide_one = context.bit_vector(1, 16).unwrap();
    let wide_sum = context
        .apply(Op::BvAdd, &[sign_extended, wide_one])
        .unwrap();
    assert!(
        context
            .apply(Op::BvSub, &[wide_sum, zero_extended])
            .unwrap()
            .constant()
            .is_none()
    );
    assert!(
        context
            .apply(
                Op::BvSub,
                &[context.bit_vector(1, 16).unwrap(), offset.clone()]
            )
            .is_err()
    );
    let foreign = Context::default().symbol(0, Sort::BitVec(8)).unwrap();
    let local_sum = context.apply(Op::BvAdd, &[offset.clone(), offset]).unwrap();
    assert!(context.apply(Op::BvSub, &[local_sum, foreign]).is_err());
}

#[test]
fn literal_array_reads_skip_only_unequal_keys_and_preserve_latest_writes() {
    let mut queries = Vec::new();
    for bits in [8, 16, 32, 64, 128] {
        let context = Context::default();
        let array = context
            .symbol(
                0,
                Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8))),
            )
            .unwrap();
        let mut stored = array.clone();
        let mut expected = "v0".to_owned();
        for (key, byte) in [(3, 7), (9, 11), (3, 17), (255, 19)] {
            stored = context
                .apply(
                    Op::Store,
                    &[
                        stored,
                        context.bit_vector(key, bits).unwrap(),
                        context.bit_vector(byte, 8).unwrap(),
                    ],
                )
                .unwrap();
            expected = format!("(store {expected} (_ bv{key} {bits}) (_ bv{byte} 8))");
        }
        for key in [0, 3, 9, 255] {
            let read = context
                .apply(
                    Op::Select,
                    &[stored.clone(), context.bit_vector(key, bits).unwrap()],
                )
                .unwrap();
            queries.push(format!(
                "{}\n{}",
                context.declarations().join("\n"),
                equivalent(&read, &format!("(select {expected} (_ bv{key} {bits}))"))
            ));
            if key == 3 {
                assert_eq!(read.constant(), Some(Constant::BitVec(17)));
            }
        }
    }
    assert!(solve(&queries).iter().all(|answer| answer == "unsat"));
}

#[test]
fn read_over_write_stops_at_symbolic_keys_and_keeps_conditional_payloads() {
    let context = Context::default();
    let array = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
        )
        .unwrap();
    let key = context.symbol(1, Sort::BitVec(32)).unwrap();
    let condition = context.symbol(2, Sort::Bool).unwrap();
    let conditional = context
        .apply(
            Op::Ite,
            &[
                condition,
                context.bit_vector(9, 8).unwrap(),
                context.bit_vector(13, 8).unwrap(),
            ],
        )
        .unwrap();
    let initial = context
        .apply(
            Op::Store,
            &[
                array,
                context.bit_vector(3, 32).unwrap(),
                context.bit_vector(7, 8).unwrap(),
            ],
        )
        .unwrap();
    let barrier = context
        .apply(Op::Store, &[initial, key.clone(), conditional])
        .unwrap();
    let stored = context
        .apply(
            Op::Store,
            &[
                barrier.clone(),
                context.bit_vector(4, 32).unwrap(),
                context.bit_vector(11, 8).unwrap(),
            ],
        )
        .unwrap();
    let read = context
        .apply(
            Op::Select,
            &[stored.clone(), context.bit_vector(3, 32).unwrap()],
        )
        .unwrap();
    let shortened = context
        .apply(Op::Select, &[barrier, context.bit_vector(3, 32).unwrap()])
        .unwrap();
    assert_eq!(read, shortened);
    assert!(read.smt(200_000).unwrap().contains("v1"));
    let original = "(select (store (store (store v0 (_ bv3 32) (_ bv7 8)) v1 (ite v2 (_ bv9 8) (_ bv13 8))) (_ bv4 32) (_ bv11 8)) (_ bv3 32))";
    let declarations = context.declarations().join("\n");
    let query = format!("{declarations}\n{}", equivalent(&read, original));
    let symbolic_read = context.apply(Op::Select, &[stored, key]).unwrap();
    let query2 = format!(
        "{declarations}\n{}",
        equivalent(
            &symbolic_read,
            "(select (store (store (store v0 (_ bv3 32) (_ bv7 8)) v1 (ite v2 (_ bv9 8) (_ bv13 8))) (_ bv4 32) (_ bv11 8)) v1)"
        )
    );
    assert_eq!(solve(&[query, query2]), ["unsat", "unsat"]);
}

#[test]
fn long_literal_store_chains_are_walked_without_recursive_select_rewriting() {
    let context = Context::default();
    let base = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
        )
        .unwrap();
    let mut array = base.clone();
    for key in 1..=512 {
        array = context
            .apply(
                Op::Store,
                &[
                    array,
                    context.bit_vector(key, 32).unwrap(),
                    context.bit_vector(key % 256, 8).unwrap(),
                ],
            )
            .unwrap();
    }
    let zero = context.bit_vector(0, 32).unwrap();
    let read = context.apply(Op::Select, &[array, zero.clone()]).unwrap();
    let expected = context.apply(Op::Select, &[base, zero]).unwrap();
    assert_eq!(read, expected);
    let backing = context
        .symbol(
            1,
            Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
        )
        .unwrap();
    let foreign_key = Context::default().bit_vector(0, 32).unwrap();
    assert!(
        context
            .apply(Op::Select, &[backing.clone(), foreign_key])
            .is_err()
    );
    let wrong_key = context.bit_vector(0, 16).unwrap();
    assert!(context.apply(Op::Select, &[backing, wrong_key]).is_err());
}
