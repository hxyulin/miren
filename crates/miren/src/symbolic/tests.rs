use super::{Constant, Context, Op, Sort, Value, binary, constant, integer};

#[test]
fn arithmetic_folding_preserves_wrapping_signedness_and_declared_width() {
    let context = Context::default();
    for (operation, left, right, bits, signed, expected) in [
        ("add", 255, 1, 8, false, 0_u128),
        ("sub", 0, 1, 8, true, 255),
        (
            "mul",
            u64::MAX as u128,
            3,
            64,
            false,
            18_446_744_073_709_551_613,
        ),
        ("add", u128::MAX, 1, 128, false, 0),
    ] {
        let Value::Int {
            expression,
            bits: actual,
            signed: actual_signed,
        } = binary(
            &context,
            operation,
            integer(&context, left, bits, signed),
            integer(&context, right, bits, signed),
        )
        .unwrap()
        else {
            panic!("arithmetic must preserve the integer shape");
        };
        assert_eq!(
            constant(&expression),
            Some(Constant::BitVec {
                value: expected,
                bits
            })
        );
        assert_eq!((actual, actual_signed), (bits, signed));
    }
    assert!(
        binary(
            &context,
            "add",
            integer(&context, 1, 8, false),
            integer(&context, 2, 16, false)
        )
        .is_err()
    );
}

#[test]
fn checked_results_fold_the_wrapped_value_and_overflow_independently() {
    let context = Context::default();
    for (left, right, bits, signed) in [
        (255, 1, 8, false),
        (127, 1, 8, true),
        (0, 1, 8, true),
        (i64::MAX as u128, 1, 64, true),
        (u64::MAX as u128, 1, 64, false),
    ] {
        let Value::Tuple(fields) = binary(
            &context,
            "checked_add",
            integer(&context, left, bits, signed),
            integer(&context, right, bits, signed),
        )
        .unwrap() else {
            panic!("checked arithmetic must return a tuple");
        };
        let overflow = if signed {
            (left + right) > (1_u128 << (bits - 1)) - 1
        } else {
            left + right >= 1_u128 << bits
        };
        assert_eq!(
            constant(&fields[1].boolean().unwrap()),
            Some(Constant::Bool(overflow))
        );
        let expected = (left + right) & (u128::MAX >> (128 - bits));
        assert_eq!(
            constant(&fields[0].integer().unwrap().0),
            Some(Constant::BitVec {
                value: expected,
                bits
            })
        );
    }
}

#[test]
fn checked_integer_folding_matches_native_arithmetic_at_signed_boundaries() {
    let context = Context::default();
    for bits in [1, 8, 16, 32, 64] {
        let mask = u128::MAX >> (128 - bits);
        let sign = 1_u128 << (bits - 1);
        for left in [0, 1, sign - 1, sign, mask] {
            for right in [0, 1, sign - 1, sign, mask] {
                for signed in [false, true] {
                    let a = ((left << (128 - bits)) as i128) >> (128 - bits);
                    let b = ((right << (128 - bits)) as i128) >> (128 - bits);
                    for operation in ["checked_add", "checked_sub", "checked_mul"] {
                        let (expected, overflow) = if signed {
                            let wide = match operation {
                                "checked_add" => a + b,
                                "checked_sub" => a - b,
                                "checked_mul" => a * b,
                                _ => unreachable!("listed checked arithmetic operations"),
                            };
                            (
                                (wide as u128) & mask,
                                !(-(sign as i128)..=(sign - 1) as i128).contains(&wide),
                            )
                        } else {
                            let (wide, overflow) = match operation {
                                "checked_add" => left.overflowing_add(right),
                                "checked_sub" => left.overflowing_sub(right),
                                "checked_mul" => left.overflowing_mul(right),
                                _ => unreachable!("listed checked arithmetic operations"),
                            };
                            (wide & mask, overflow || wide > mask)
                        };
                        let Value::Tuple(fields) = binary(
                            &context,
                            operation,
                            integer(&context, left, bits, signed),
                            integer(&context, right, bits, signed),
                        )
                        .unwrap() else {
                            panic!("checked arithmetic must return a tuple");
                        };
                        assert_eq!(
                            constant(&fields[0].integer().unwrap().0),
                            Some(Constant::BitVec {
                                value: expected,
                                bits
                            }),
                            "{operation} {left}, {right}, width {bits}, signed {signed}"
                        );
                        assert_eq!(
                            constant(&fields[1].boolean().unwrap()),
                            Some(Constant::Bool(overflow)),
                            "{operation} {left}, {right}, width {bits}, signed {signed}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn symbolic_and_wide_arithmetic_remain_terms_and_unsupported_operations_fail() {
    let context = Context::default();
    let input = Value::Int {
        expression: context.symbol(0, Sort::BitVec(8)).unwrap(),
        bits: 8,
        signed: false,
    };
    let result = binary(
        &context,
        "add",
        input.clone(),
        integer(&context, 1, 8, false),
    )
    .unwrap();
    assert_eq!(constant(&result.integer().unwrap().0), None);
    assert!(
        binary(
            &context,
            "unsupported",
            input,
            integer(&context, 1, 8, false)
        )
        .is_err()
    );
    let wide = context
        .apply(Op::ZeroExtend(1), &[context.bit_vector(1, 128).unwrap()])
        .unwrap();
    assert_eq!(constant(&wide), None);
    assert!(
        context
            .apply(
                Op::BvAdd,
                &[
                    context.bit_vector(1, 8).unwrap(),
                    context.bit_vector(1, 16).unwrap()
                ]
            )
            .is_err()
    );
}

#[test]
fn moving_references_through_owned_iterators_does_not_enable_identity_repeats() {
    for mutable in [false, true] {
        let reference = Value::Reference {
            allocation: 0,
            projection: Vec::new(),
            mutable,
        };
        let values = Value::Elements(vec![Value::Tuple(vec![reference])].into());
        assert_eq!(values.owned_iterator_size(), Some(3));
        assert_eq!(values.owned_repeat_size(), None);
    }
    let cells = Value::Elements(vec![Value::Cell { allocation: 0 }].into());
    assert_eq!(cells.owned_iterator_size(), None);
}

fn legacy_integer_choice(context: &Context, elements: &[Value], index: &Value) -> Value {
    let (index, index_bits, _) = index.integer().unwrap();
    let mut result = elements.last().unwrap().clone();
    for (position, value) in elements.iter().enumerate().rev().skip(1) {
        let Value::Int {
            expression,
            bits,
            signed,
        } = value
        else {
            panic!("integer fixture")
        };
        let (otherwise, _, _) = result.integer().unwrap();
        let condition = context
            .apply(
                Op::Equal,
                &[
                    index.clone(),
                    context.bit_vector(position as u128, index_bits).unwrap(),
                ],
            )
            .unwrap();
        result = Value::Int {
            expression: context
                .apply(Op::Ite, &[condition, expression.clone(), otherwise])
                .unwrap(),
            bits: *bits,
            signed: *signed,
        };
    }
    result
}

#[test]
fn constant_integer_choices_match_legacy_for_all_indices_and_declared_widths() {
    use crate::solver::{Answer, Query, Solver};
    let mut solver = Solver::default();
    for (length, index_bits, bits, signed) in [
        (1, 8, 8, false),
        (3, 8, 16, true),
        (256, 8, 16, false),
        (256, 32, 16, false),
        (5, 64, 128, true),
    ] {
        let context = Context::default();
        let index = Value::Int {
            expression: context.symbol(0, Sort::BitVec(index_bits)).unwrap(),
            bits: index_bits,
            signed: false,
        };
        let elements: Vec<_> = (0..length)
            .map(|value| integer(&context, (value as u128).wrapping_mul(7919), bits, signed))
            .collect();
        let actual = super::select_element(&context, &elements, &index).unwrap();
        let legacy = legacy_integer_choice(&context, &elements, &index);
        let equal = binary(&context, "eq", actual.clone(), legacy)
            .unwrap()
            .boolean()
            .unwrap();
        let failure = context.apply(Op::Not, &[equal]).unwrap();
        let query = Query::new(&context.declarations(), &[], &failure.smt(200_000).unwrap());
        assert!(
            matches!(solver.check_query(&query), Answer::Unsat),
            "length={length} index_bits={index_bits} bits={bits} signed={signed}"
        );
        let (_, actual_bits, actual_signed) = actual.integer().unwrap();
        assert_eq!((actual_bits, actual_signed), (bits, signed));
    }
}

#[test]
fn constant_integer_choice_keeps_last_default_and_rejects_forged_metadata() {
    let context = Context::default();
    let elements = [
        integer(&context, 3, 16, true),
        integer(&context, 4, 16, true),
    ];
    for index in [0, 1, 2, 255] {
        let index = integer(&context, index, 8, false);
        let (actual, _, _) = super::select_element(&context, &elements, &index)
            .unwrap()
            .integer()
            .unwrap();
        let expected =
            if index.integer().unwrap().0.constant() == Some(miren::smt::Constant::BitVec(0)) {
                3
            } else {
                4
            };
        use crate::solver::{Answer, Query, Solver};
        let equal = context
            .apply(
                Op::Equal,
                &[actual, context.bit_vector(expected, 16).unwrap()],
            )
            .unwrap();
        let failure = context.apply(Op::Not, &[equal]).unwrap();
        assert!(matches!(
            Solver::default().check_query(&Query::new(&[], &[], &failure.smt(200_000).unwrap())),
            Answer::Unsat
        ));
    }
    let foreign = Context::default();
    let foreign_index = Value::Int {
        expression: foreign.symbol(0, Sort::BitVec(8)).unwrap(),
        bits: 8,
        signed: false,
    };
    assert!(super::select_element(&context, &elements, &foreign_index).is_err());
    let wrong_width = Value::Int {
        expression: context.symbol(0, Sort::BitVec(16)).unwrap(),
        bits: 8,
        signed: false,
    };
    assert!(super::select_element(&context, &elements, &wrong_width).is_err());
    let wrong_element = Value::Int {
        expression: context.bit_vector(3, 8).unwrap(),
        bits: 16,
        signed: true,
    };
    assert!(
        super::select_element(&context, &[wrong_element], &integer(&context, 0, 8, false)).is_err()
    );
    let foreign_element = integer(&foreign, 3, 16, true);
    assert!(
        super::select_element(
            &context,
            &[foreign_element],
            &integer(&context, 0, 8, false)
        )
        .is_err()
    );
}

#[test]
fn compact_integer_choice_leaves_symbolic_mixed_and_narrow_index_choices_unchanged() {
    let context = Context::default();
    let index = Value::Int {
        expression: context.symbol(0, Sort::BitVec(1)).unwrap(),
        bits: 1,
        signed: false,
    };
    let over_capacity = [
        integer(&context, 3, 8, false),
        integer(&context, 4, 8, false),
        integer(&context, 5, 8, false),
    ];
    let actual = super::select_element(&context, &over_capacity, &index)
        .unwrap()
        .integer()
        .unwrap()
        .0;
    let legacy = legacy_integer_choice(&context, &over_capacity, &index)
        .integer()
        .unwrap()
        .0;
    assert_eq!(actual, legacy);
    let symbolic = Value::Int {
        expression: context.symbol(1, Sort::BitVec(8)).unwrap(),
        bits: 8,
        signed: false,
    };
    let elements = [integer(&context, 3, 8, false), symbolic];
    let actual = super::select_element(&context, &elements, &index)
        .unwrap()
        .integer()
        .unwrap()
        .0;
    let legacy = legacy_integer_choice(&context, &elements, &index)
        .integer()
        .unwrap()
        .0;
    assert_eq!(actual, legacy);
    let mixed = [
        integer(&context, 3, 8, false),
        integer(&context, 4, 8, true),
    ];
    assert!(super::select_element(&context, &mixed, &index).is_err());
    assert!(super::select_element(&context, &[], &index).is_err());
    let booleans = [
        Value::Bool(context.boolean(false)),
        Value::Bool(context.boolean(true)),
    ];
    assert!(
        super::select_element(&context, &booleans, &index)
            .unwrap()
            .boolean()
            .unwrap()
            .smt(200_000)
            .unwrap()
            .contains("ite")
    );
}
