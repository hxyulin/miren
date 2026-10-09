#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[inline(never)]
fn selected_field(values: &[(u16, u16)], index: usize) -> u16 {
    values[index].0
}

#[inline(never)]
fn copied_pair(values: &[(u16, u16)], index: usize) -> (u16, u16) {
    values[index]
}

#[inline(never)]
fn selected_pair(values: &[(u16, u16)], index: usize) -> &(u16, u16) {
    &values[index]
}

#[inline(never)]
fn selected_second(values: &[(u16, u16)], index: usize) -> &u16 {
    &values[index].1
}

pub fn pair_correlation(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.0 == values[index].0);
        assert!(copied.1 == values[index].1);
    }
}

pub fn owned_helper_copy(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let copied = copied_pair(values, index);
        assert!(copied.0 == values[index].0);
        assert!(copied.1 == values[index].1);
    }
}

pub fn caller_backed_borrows(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let borrowed = selected_pair(values, index);
        assert!(borrowed.0 == values[index].0);
        assert!(*selected_second(values, index) == values[index].1);
    }
}

pub fn owned_copy_mutation(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let original = values[index].0;
        let mut copied = values[index];
        copied.0 = copied.0.wrapping_add(1);
        assert!(copied.0 == original.wrapping_add(1));
        assert!(values[index].0 == original);
        assert!(copied.1 == values[index].1);
    }
}

pub fn same_index_relation(values: &[(u16, u16)], left: usize, right: usize) {
    if left < values.len() && left == right {
        assert!(values[left].0 == values[right].0);
        assert!(values[left].1 == values[right].1);
    }
}

pub fn nested_mixed(values: &[((bool, char), [i16; 2])], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.0.0 == values[index].0.0);
        assert!(copied.0.1 == values[index].0.1);
        assert!(copied.1[0] == values[index].1[0]);
        assert!(copied.1[1] == values[index].1[1]);
        let unicode = copied.0.1 as u32;
        assert!(unicode <= 0x10ffff);
        assert!(unicode < 0xd800 || unicode > 0xdfff);
    }
}

pub fn nested_arrays(values: &[[[u16; 2]; 2]], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied[0][0] == values[index][0][0]);
        assert!(copied[0][1] == values[index][0][1]);
        assert!(copied[1][0] == values[index][1][0]);
        assert!(copied[1][1] == values[index][1][1]);
    }
}

pub fn pure_empty_fields(values: &[((), [u16; 0], u16)], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.1.len() == 0);
        assert!(copied.2 == values[index].2);
    }
}

pub fn float_field_bits(values: &[(f32, f64)], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.0.to_bits() == values[index].0.to_bits());
        assert!(copied.1.to_bits() == values[index].1.to_bits());
        if copied.0.is_nan() {
            assert!(values[index].0.is_nan());
        }
        if copied.1.is_nan() {
            assert!(values[index].1.is_nan());
        }
        if copied.0.to_bits() == 0x80000000 {
            assert!(values[index].0 == 0.0);
        }
        if copied.1.to_bits() == 0x8000000000000000 {
            assert!(values[index].1 == 0.0);
        }
    }
}

pub fn subview_correlation(values: &[(u16, u16)], offset: usize, index: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        if index < suffix.len() {
            assert!(suffix[index].0 == values[offset + index].0);
            assert!(suffix[index].1 == values[offset + index].1);
        }
    }
    let end = values.len();
    assert!(values[end..end].len() == 0);
}

pub fn long_field_mutation_claim(values: &[(u16, u16)]) {
    if values.len() > 128 {
        assert!(selected_field(values, 128) == values[128].0);
    }
}

// Preserve the exact existing capability root, including its false assertion.
pub fn open_aggregate_slice(values: &[(u16, u16)]) {
    if !values.is_empty() {
        assert!(values[0].0 == 0);
    }
}

pub fn wrong_field_correlation(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        assert!(values[index].0 == values[index].1);
    }
}

pub fn wrong_nested_position(values: &[[u16; 2]], index: usize) {
    if index < values.len() {
        assert!(values[index][0] == values[index][1]);
    }
}

pub fn bounds_at_end(values: &[(u16, u16)]) -> u16 {
    values[values.len()].0
}

pub fn float_numeric_reflexivity(values: &[(f32, f64)], index: usize) {
    if index < values.len() {
        assert!(values[index].0 == values[index].0);
    }
}

pub fn mutable_root(values: &mut [(u16, u16)]) -> usize {
    values.len()
}

pub fn competing_roots(left: &[(u16, u16)], right: &[(u16, u16)]) -> bool {
    left.len() == right.len()
}

pub fn nested_references(values: &[(u16, &u16)]) -> usize {
    values.len()
}

pub struct Wrapper(u16);

pub fn adt_leaf(values: &[(u16, Wrapper)]) -> usize {
    values.len()
}

pub fn nonzero_leaf(values: &[(u16, core::num::NonZeroU16)]) -> usize {
    values.len()
}

pub struct Dropped(u16);

impl Drop for Dropped {
    fn drop(&mut self) {
        let _ = self.0;
    }
}

pub fn drop_leaf(values: &[(u16, Dropped)]) -> usize {
    values.len()
}

pub fn empty_reference_array(values: &[(u16, [&u16; 0])]) -> usize {
    values.len()
}

type Positive = core::pattern_type!(u16 is 1..);

pub fn empty_refined_array(values: &[(u16, [Positive; 0])]) -> usize {
    values.len()
}

pub fn wholly_zero_sized(values: &[((), [u16; 0])]) -> usize {
    values.len()
}

pub fn full_composite_contains(values: &[(u16, u16)], needle: (u16, u16)) -> bool {
    values.contains(&needle)
}

pub fn full_composite_equality(values: &[(u16, u16)]) -> bool {
    values == values
}

pub fn deferred_iteration(values: &[(u16, u16)], index: usize) -> Option<&(u16, u16)> {
    values.iter().nth(index)
}

pub fn oversized_type_array(values: &[[u16; 129]]) -> usize {
    values.len()
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    unsafe extern "Rust" {
        fn opaque_field(value: u16) -> u16;
    }

    pub fn missing_body(values: &[(u16, u16)]) {
        if !values.is_empty() {
            let result = unsafe { opaque_field(values[0].0) };
            assert!(result == values[0].0);
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn readonly_cannot_restore_mutation(values: &[(u16, u16)]) {
        mir! {
            let mutable: &mut [(u16, u16)];
            {
                mutable = &mut *values;
                Return()
            }
        }
    }

    fn inspect(values: &[(u16, u16); 1]) -> u16 {
        values[0].0
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_original_backing() -> u16 {
        mir! {
            let pair: (u16, u16);
            let backing: [(u16, u16); 1];
            let source: &[(u16, u16); 1];
            {
                pair = (3_u16, 7_u16);
                backing = [pair];
                source = &backing;
                StorageDead(backing);
                Call(RET = inspect(source), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positives() {
        let long = [(3, 7); 129];
        for values in [&[][..], &[(3, 7)][..], &long[..]] {
            long_field_mutation_claim(values);
            for index in [0, 128, values.len()] {
                pair_correlation(values, index);
                owned_helper_copy(values, index);
                owned_copy_mutation(values, index);
                caller_backed_borrows(values, index);
                same_index_relation(values, index, index);
                subview_correlation(values, 0, index);
                subview_correlation(values, 1, index);
            }
        }
        for unicode in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            let values = [((false, unicode), [i16::MIN, i16::MAX]); 129];
            nested_mixed(&values, 128);
        }
        nested_mixed(&[], 0);
        nested_arrays(&[[[1, 2], [3, 4]]; 129], 128);
        nested_arrays(&[], 0);
        pure_empty_fields(&[((), [], 7); 129], 128);
        pure_empty_fields(&[], 0);
        float_field_bits(&[], 0);
        for value in [
            (
                f32::from_bits(0x7fc00015),
                f64::from_bits(0x7ff8000000000015),
            ),
            (-0.0, -0.0),
            (0.0, 0.0),
            (f32::MIN_POSITIVE, f64::MAX),
        ] {
            float_field_bits(&[value; 129], 128);
        }
    }

    #[test]
    fn mutation_guard() {
        long_field_mutation_claim(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn original_false_zero_failure() {
        open_aggregate_slice(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn field_failure() {
        wrong_field_correlation(&[(3, 7); 129], 128);
    }

    #[test]
    #[should_panic]
    fn nested_position_failure() {
        wrong_nested_position(&[[3, 7]; 129], 128);
    }

    #[test]
    #[should_panic]
    fn bounds_failure() {
        let _ = bounds_at_end(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn nan_failure() {
        float_numeric_reflexivity(&[(f32::NAN, 0.0); 129], 128);
    }
}
