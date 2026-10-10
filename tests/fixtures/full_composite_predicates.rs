#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[inline(never)]
pub fn selected_needle(values: &[(u16, u16)], index: usize) -> (u16, u16) {
    values[index]
}
pub fn tuple_selected(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        assert!(values.contains(&selected_needle(values, index)));
    }
}
pub fn tuple_self(values: &[(u16, u16)]) {
    assert!(values == values);
}
pub fn tuple_absent(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&selected_needle(values, index)));
    }
}
pub fn array_selected(values: &[[u16; 2]], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(values.contains(&selected));
    }
}

pub fn nested_selected(values: &[((bool, u16), [i32; 2])], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(values.contains(&selected));
    }
}
pub fn char_selected(values: &[(char, u16)], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(values.contains(&selected));
    }
}
pub fn long_selected(values: &[(u16, u16)]) {
    if values.len() > 128 {
        assert!(values.contains(&selected_needle(values, values.len() - 1)));
    }
}
pub fn same_views(values: &[(u16, u16)], start: usize, end: usize) {
    if start <= end && end <= values.len() {
        assert!(values[start..end] == values[start..end]);
    }
}
pub fn distinct_views(values: &[(u16, u16)]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] != values[1..]);
    }
}
pub fn falsely_equal_views(values: &[(u16, u16)]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}
pub fn falsely_equal_lengths(values: &[(u16, u16)]) {
    if !values.is_empty() {
        assert!(values == &values[..values.len() - 1]);
    }
}
pub fn nan_absent(values: &[(f32, f64)]) {
    assert!(!values.contains(&(f32::NAN, 0.0)));
}
pub fn signed_zero(values: &[(f32, f64)]) {
    if !values.is_empty() {
        let first = values[0];
        if first.0 == 0.0 && first.1 == 0.0 {
            assert!(values.contains(&(-0.0, -0.0)));
        }
    }
}
pub fn non_nan_selected(values: &[(f32, f64)], index: usize) {
    if index < values.len() {
        let selected = values[index];
        if selected.0 == selected.0 && selected.1 == selected.1 {
            assert!(values.contains(&selected));
        }
    }
}
pub fn falsely_float_self(values: &[(f32, f64)]) {
    assert!(values == values);
}
pub fn zero_contains(values: &[((), [u16; 0])]) {
    assert!(values.contains(&((), [])) == !values.is_empty());
}
pub fn zero_self(values: &[((), [u16; 0])]) {
    assert!(values == values);
}
pub fn maximum_contains(values: &[((), [u16; 0])]) {
    if values.len() == usize::MAX {
        assert!(values.contains(&((), [])));
    }
}
pub fn maximum_reachable(values: &[((), [u16; 0])]) {
    assert!(values.len() != usize::MAX);
}
pub fn mutable_root(values: &mut [(u16, u16)]) {
    assert!(values == values);
}
pub fn competing_roots(left: &[(u16, u16)], right: &[(u16, u16)]) {
    assert!(left == right);
}
pub fn reference_zero(values: &[([&'static u16; 0], u16)]) {
    assert!(values == values);
}
pub fn refined_zero(values: &[([core::pattern_type!(u16 is 1..); 0], u16)]) {
    assert!(values.len() == values.len());
}
pub struct Dropped;
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn drop_zero(values: &[([Dropped; 0], u16)]) {
    assert!(values.len() == values.len());
}
#[derive(Clone, Copy)]
pub struct FalseEquality {
    pub value: u16,
}
impl PartialEq for FalseEquality {
    #[inline(never)]
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
pub fn nominal_equality(values: &[FalseEquality]) {
    assert!(values == values);
}
pub fn nominal_contains(values: &[FalseEquality], needle: FalseEquality) {
    assert!(values.contains(&needle));
}
pub fn finite_custom_false(value: u16) {
    let values = [FalseEquality { value }; 2];
    assert!(values.contains(&values[0]));
}
#[derive(Clone, Copy)]
pub struct PanickingEquality {
    pub value: u16,
}
impl PartialEq for PanickingEquality {
    #[inline(never)]
    fn eq(&self, _other: &Self) -> bool {
        panic!("actual custom comparison");
    }
}
pub fn nominal_panicking(values: &[PanickingEquality], needle: PanickingEquality) {
    assert!(values.contains(&needle));
}
#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn unavailable() -> (u16, u16);
    }
    pub fn missing_body(values: &[(u16, u16)]) {
        let needle = unsafe { unavailable() };
        assert!(values.contains(&needle));
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for values in [&[][..], &[(3, 7)][..], &[(3, 7); 129][..]] {
            tuple_self(values);
            same_views(values, 0, values.len());
            for index in [0, 128] {
                tuple_selected(values, index);
            }
            long_selected(values);
        }
        distinct_views(&[(3, 7), (5, 11)]);
        array_selected(&[[3, 7]; 129], 128);
        nested_selected(&[((true, 7), [-1, i32::MIN]); 129], 128);
        char_selected(
            &[
                ('\0', 3),
                ('\u{d7ff}', 7),
                ('\u{e000}', 11),
                ('\u{10ffff}', 13),
            ],
            3,
        );
        nan_absent(&[(f32::NAN, f64::NAN), (-0.0, 0.0)]);
        signed_zero(&[(0.0, -0.0)]);
        non_nan_selected(&[(-0.0, 1.0); 129], 128);
        zero_contains(&[]);
        zero_contains(&[((), []); 129]);
        zero_self(&[((), []); 129]);
        let maximum = [((), [0u16; 0]); usize::MAX];
        maximum_contains(&maximum);
    }
    #[test]
    fn mutation_guard() {
        tuple_selected(&[(3, 7); 129], 128);
    }
    #[test]
    #[should_panic]
    fn negative_absent() {
        tuple_absent(&[(3, 7); 129], 128);
    }
    #[test]
    #[should_panic]
    fn negative_views() {
        falsely_equal_views(&[(3, 7), (5, 11)]);
    }
    #[test]
    #[should_panic]
    fn negative_lengths() {
        falsely_equal_lengths(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn negative_nan() {
        falsely_float_self(&[(f32::NAN, 1.0)]);
    }
    #[test]
    #[should_panic]
    fn negative_maximum() {
        let maximum = [((), [0u16; 0]); usize::MAX];
        maximum_reachable(&maximum);
    }
    #[test]
    #[should_panic]
    fn negative_custom() {
        finite_custom_false(3);
    }
}

#[cfg(not(test))]
mod lifecycle {
    use core::intrinsics::mir::*;
    #[inline(never)]
    fn empty_contains(values: &[(u16, u16); 0]) -> bool {
        values.contains(&(3, 7))
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> bool {
        mir! {
            let backing: [(u16,u16);0]; let borrowed: &[(u16,u16);0];
            { backing = []; borrowed = &backing; StorageDead(backing);
              Call(RET = empty_contains(borrowed), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
}

pub fn one_byte_membership(values: &[[u8; 1]]) {
    if !values.is_empty() {
        assert!(values.contains(&values[0]));
    }
}

pub fn mixed_finite_equality(values: &[(u16, u16)]) {
    if values.len() == 1 {
        assert!(values == &[values[0]]);
    }
}
