#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

#[inline(never)]
pub fn first(values: &[u16]) -> u16 {
    values[0]
}

#[inline(never)]
fn identity(values: &[u16]) -> &[u16] {
    values
}

pub fn repeated_integer(values: &[u16], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(selected == identity(values)[index]);
    }
}

pub fn signed_integer(values: &[i32], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(selected >= i32::MIN);
        assert!(selected <= i32::MAX);
        assert!(selected as u32 == values[index] as u32);
    }
}

pub fn wide_integer(values: &[u128], index: usize) {
    assert!(values.len() <= isize::MAX as usize / 16);
    if index < values.len() {
        assert!(values[index] == values[index]);
    }
}

pub fn bool_values(values: &[bool], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(selected || !selected);
        assert!(selected == values[index]);
    }
}

pub fn float32_bits(values: &[f32], index: usize) {
    if index < values.len() {
        let selected = values[index].to_bits();
        assert!(selected == values[index].to_bits());
        if selected == 0x80000000 {
            assert!(values[index] == 0.0);
        }
        if selected == 0x7fc00015 {
            assert!(values[index].is_nan());
        }
    }
}

pub fn float64_bits(values: &[f64], index: usize) {
    if index < values.len() {
        let selected = values[index].to_bits();
        assert!(selected == values[index].to_bits());
        if selected == 0x8000000000000000 {
            assert!(values[index] == 0.0);
        }
        if selected == 0x7ff8000000000015 {
            assert!(values[index].is_nan());
        }
    }
}

pub fn char_values(values: &[char], index: usize) {
    if index < values.len() {
        let selected = values[index] as u32;
        assert!(selected <= 0x10ffff);
        assert!(selected < 0xd800 || selected > 0xdfff);
        assert!(selected == values[index] as u32);
    }
}

pub fn extent(values: &[u16]) {
    assert!(values.len() <= isize::MAX as usize / 2);
    assert!(core::mem::size_of_val(values) == values.len() * 2);
}

pub fn retained_return(values: &[u16]) {
    let copy = identity(values);
    assert!(copy.len() == values.len());
    if !copy.is_empty() {
        assert!(first(copy) == values[0]);
    }
}

pub fn mutation_claim(values: &[u16]) {
    if values.len() >= 2 {
        assert!(first(values) == values[0]);
    }
}

#[inline(never)]
fn range(values: &[u16], start: usize, end: usize) -> &[u16] {
    &values[start..end]
}

pub fn nested_subviews(values: &[u16]) {
    if values.len() >= 4 {
        let outer = range(values, 1, 4);
        let inner = range(outer, 1, 2);
        assert!(inner.len() == 1);
        assert!(first(inner) == values[2]);
        assert!(identity(inner)[0] == values[2]);
    }
}

pub fn empty_at_end(values: &[u16]) {
    let end = values.len();
    let empty = range(values, end, end);
    assert!(empty.is_empty());
}

pub fn invalid_range(values: &[u16]) -> &[u16] {
    range(values, 2, 1)
}

pub fn char_reinterpret(values: &[char]) -> &[u32] {
    unsafe { core::mem::transmute(values) }
}

pub fn first_word_zero(values: &[u16]) {
    if !values.is_empty() {
        assert!(values[0] == 0);
    }
}

pub fn large_slice_wrong_claim(values: &[u16]) {
    if values.len() > 128 {
        assert!(values[128] == 0);
    }
}

pub fn unguarded_index(values: &[u16], index: usize) -> u16 {
    values[index]
}

pub fn float_reflexivity(values: &[f32]) {
    if !values.is_empty() {
        assert!(values[0] == values[0]);
    }
}

pub fn mutable_input(values: &mut [u16]) {
    let _ = values.len();
}

pub fn raw_elements(values: &[*const u16]) {
    let _ = values.len();
}

pub fn zero_sized_elements(values: &[()]) {
    let _ = values.len();
}

type Positive = core::pattern_type!(u16 is 1..);
pub fn pattern_elements(values: &[Positive]) {
    let _ = values.len();
}

pub fn competing_inputs(left: &[u16], right: &[u16]) {
    let _ = (left.len(), right.len());
}

#[inline(never)]
fn length(values: &[u16]) -> usize {
    values.len()
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_handle(values: &[u16]) -> usize {
    mir! {
        {
            StorageDead(values);
            Call(RET = length(values), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[cfg(test)]
#[test]
fn native_valid_controls() {
    let large = [7_u16; 129];
    for values in [&[][..], &[0, 3, u16::MAX][..], &large[..]] {
        extent(values);
        retained_return(values);
        nested_subviews(values);
        empty_at_end(values);
        mutation_claim(values);
        for index in [0, 1, 128, values.len()] {
            repeated_integer(values, index);
        }
    }
    for index in [0, 1, 2, 3] {
        signed_integer(&[i32::MIN, 0, i32::MAX], index);
        wide_integer(&[0, u128::MAX], index);
        bool_values(&[false, true], index);
        float32_bits(&[0.0, -0.0, f32::from_bits(0x7fc00015)], index);
        float64_bits(&[0.0, -0.0, f64::from_bits(0x7ff8000000000015)], index);
        char_values(&['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'], index);
    }
    mutation_claim(&[3, 7]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_first_word_counterexample() {
    first_word_zero(&[1]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_large_slice_counterexample() {
    large_slice_wrong_claim(&[1; 129]);
}

#[cfg(test)]
#[test]
fn native_mutation_guard() {
    mutation_claim(&[3, 7]);
}
