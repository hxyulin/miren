#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Reading {
    Missing = 3,
    Word(u16) = 7,
    Pair(u16, u16) = 11,
}
#[inline(never)]
pub fn selected_pair(value: Reading) -> Option<u16> {
    match value {
        Reading::Pair(left, _) => Some(left),
        Reading::Missing | Reading::Word(_) => None,
    }
}
pub fn guarded_pair(values: &[Reading], index: usize) {
    if index < values.len() {
        let selected = values[index];
        if let Reading::Pair(left, _) = selected {
            assert!(selected_pair(selected) == Some(left));
        }
    }
}
pub fn false_pair(values: &[Reading], index: usize) {
    if index < values.len() {
        if let Reading::Pair(left, _) = values[index] {
            assert!(left == 0);
        }
    }
}
pub fn arbitrary_tag(values: &[Reading], index: usize) {
    if index < values.len() {
        assert!(matches!(values[index], Reading::Missing));
    }
}
pub fn option_selected(values: &[Option<u16>], index: usize) {
    if index < values.len() {
        let selected = values[index];
        if let Some(value) = selected {
            assert!(values[index] == Some(value));
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn option_unwrap(values: &[Option<u16>], index: usize) {
    if index < values.len() {
        let _ = values[index].unwrap();
    }
}
pub fn long_selected(values: &[Reading]) {
    if values.len() > 128 {
        if let Reading::Pair(left, _) = values[values.len() - 1] {
            assert!(selected_pair(values[values.len() - 1]) == Some(left));
        }
    }
}
pub fn checked_cursor(values: &[Reading], index: usize) {
    match values.iter().nth(index) {
        Some(value) => {
            assert!(index < values.len());
            if let Reading::Pair(left, _) = *value {
                assert!(selected_pair(values[index]) == Some(left));
            }
        }
        None => assert!(index >= values.len()),
    }
}
pub fn selected_view(values: &[Reading], start: usize, index: usize) {
    if start <= values.len() && index < values.len() - start {
        if let Reading::Pair(left, _) = values[start..][index] {
            assert!(selected_pair(values[start + index]) == Some(left));
        }
    }
}
#[derive(Clone, Copy)]
#[repr(i16)]
pub enum Sparse {
    Negative = -7,
    Present(bool, u32) = 19,
}
pub fn signed_tags(values: &[Sparse], index: usize) {
    if index < values.len() {
        match values[index] {
            Sparse::Negative => assert!(matches!(values[index], Sparse::Negative)),
            Sparse::Present(flag, value) => {
                if flag { assert!(value == value); }
            }
        }
    }
}
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Numerical {
    Empty,
    Values(char, f32, f64),
}
pub fn numerical_bits(values: &[Numerical], index: usize) {
    if index < values.len() {
        if let Numerical::Values(character, single, double) = values[index] {
            if let Numerical::Values(other_char, other_single, other_double) = values[index] {
                assert!(character == other_char);
                assert!(single.to_bits() == other_single.to_bits());
                assert!(double.to_bits() == other_double.to_bits());
            } else {
                panic!();
            }
        }
    }
}
pub fn payload_tuple(values: &[(Reading, [u16; 2])], index: usize) {
    if index < values.len() {
        let (value, sibling) = values[index];
        if let Reading::Pair(left, _) = value {
            assert!(selected_pair(values[index].0) == Some(left));
        }
        assert!(sibling[0] == values[index].1[0]);
    }
}
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Nested {
    Empty,
    Values(Reading, [u16; 2]),
}
pub fn nested_sum(values: &[Nested], index: usize) {
    if index < values.len() {
        if let Nested::Values(Reading::Pair(left, _), sibling) = values[index] {
            if let Nested::Values(reading, other) = values[index] {
                assert!(selected_pair(reading) == Some(left));
                assert!(sibling[1] == other[1]);
            } else { panic!(); }
        }
    }
}
#[derive(Clone, Copy)]
pub struct Nominal;
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum NominalPayload {
    Empty,
    Value([Nominal; 0]),
}
pub fn nominal_payload_zero(values: &[NominalPayload]) {
    let _ = values.len();
}
pub fn zero_payload(values: &[([Reading; 0], u16)], index: usize) {
    if index < values.len() {
        assert!(values[index].0.len() == 0);
    }
}
pub fn cursor_metadata(values: &[Reading]) {
    let mut cursor = values.iter();
    assert!(cursor.len() == values.len());
    let cloned = cursor.clone();
    assert!(cloned.count() == values.len());
    let _ = cursor.next_back();
    assert!(cursor.len() == values.len().saturating_sub(1));
}
pub fn dynamic_layout(values: &[Reading]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<Reading>());
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<Reading>());
}
pub fn unsupported_contains(values: &[Reading]) {
    let _ = values.contains(&Reading::Missing);
}
pub fn unsupported_equality(values: &[Reading]) {
    assert!(values == values);
}
pub fn niche_bool(values: &[Option<bool>]) {
    let _ = values.len();
}
pub fn niche_char(values: &[Option<char>]) {
    let _ = values.len();
}
pub fn niche_nonzero(values: &[Option<core::num::NonZeroU16>]) {
    let _ = values.len();
}
pub fn mutable_root(values: &mut [Reading]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub enum Borrowed {
    Empty,
    Reference(&'static u16),
}
pub fn reference_zero(values: &[([Borrowed; 0], u16)]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub enum Refined {
    Empty,
    Value(core::pattern_type!(u16 is 1..)),
}
pub fn refined_zero(values: &[([Refined; 0], u16)]) {
    let _ = values.len();
}
pub enum Dropped {
    Empty,
    Value(u16),
}
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn dropped_zero(values: &[([Dropped; 0], u16)]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub enum TooLarge {
    Empty,
    Value([u16; 129]),
}
pub fn type_budget(values: &[TooLarge]) {
    let _ = values.len();
}
pub fn out_of_bounds(values: &[Reading], index: usize) {
    let _ = values[index];
}
#[cfg(not(test))]
pub mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn unavailable(value: Reading) -> u16;
    }
    pub fn missing_body(values: &[Reading], index: usize) {
        if index < values.len() {
            assert!(unsafe { unavailable(values[index]) } == 0);
        }
    }

    fn iterator_len(iterator: &core::slice::Iter<'_, Reading>) -> usize { iterator.len() }
    fn empty_iterator(values: &[Reading; 0]) -> core::slice::Iter<'_, Reading> { values.iter() }
    fn slice_iterator(values: &[Reading]) -> core::slice::Iter<'_, Reading> { values.iter() }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_handle_live(values: &[Reading]) -> usize {
        mir! {
            let iterator: core::slice::Iter<'_, Reading>;
            let borrow: &core::slice::Iter<'_, Reading>;
            { Call(iterator = slice_iterator(values), ReturnTo(retire), UnwindUnreachable()) }
            retire = {
                StorageDead(values);
                borrow = &iterator;
                Call(RET = iterator_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty_metadata() -> usize {
        mir! {
            let backing: [Reading; 0];
            let source: &[Reading; 0];
            let iterator: core::slice::Iter<'_, Reading>;
            let borrow: &core::slice::Iter<'_, Reading>;
            {
                backing = [];
                source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                borrow = &iterator;
                Call(RET = iterator_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    pub fn raw_source(pointer: *const Reading, length: usize) -> usize {
        unsafe { core::slice::from_raw_parts(pointer, length) }.len()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn unchecked_payload(value: Reading) -> u16 {
        mir! { { RET = Field(Variant(value, 2), 0); Return() } }
    }
    pub fn inactive_payload(values: &[Reading], index: usize) -> u16 {
        if index < values.len() { unchecked_payload(values[index]) } else { 0 }
    }

}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        guarded_pair(&[], usize::MAX);
        option_selected(&[None, Some(37)], 1);
        let values = [Reading::Pair(3, 7); 129];
        guarded_pair(&values, 128);
        long_selected(&values);
        checked_cursor(&values, 128);
        checked_cursor(&values, usize::MAX);
        selected_view(&values, 128, 0);
        payload_tuple(&[(Reading::Pair(3, 7), [17, 19])], 0);
        numerical_bits(&[Numerical::Values('🦀', f32::NAN, -0.0)], 0);
        nested_sum(&[Nested::Values(Reading::Pair(3, 7), [17, 19])], 0);
        cursor_metadata(&values);
        dynamic_layout(&values);
        zero_payload(&[([], 1)], 0);
        signed_tags(&[Sparse::Negative, Sparse::Present(true, 9)], 1);
    }
    #[test]
    fn mutation_guard() {
        let values = [Reading::Pair(3, 7); 129];
        guarded_pair(&values, 128);
    }
    #[test]
    #[should_panic]
    fn false_tag() { arbitrary_tag(&[Reading::Word(3)], 0); }
    #[test]
    #[should_panic]
    fn false_payload() { false_pair(&[Reading::Pair(3, 7)], 0); }
    #[test]
    #[should_panic]
    fn false_unwrap() { option_unwrap(&[None], 0); }
}
