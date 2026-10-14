//! Genuine nested helpers retain the actual whole Product owner and returned storage effects.
use crate::mutable_product_child_survey as original;

pub fn nested_float(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        let untouched = values[index][1].to_bits();
        original::nested_child(values, index);
        assert!(values[index][0].to_bits() == 0x7fc0_1234);
        assert!(values[index][1].to_bits() == untouched);
    }
}

pub fn wrong_nested_float(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        original::nested_child(values, index);
        assert!(values[index][0].to_bits() == 0x7fc0_1235);
    }
}

#[inline(never)]
pub fn nested_wide(values: &mut [[f64; 2]], index: usize) -> u64 {
    original::wide_return(values, index)
}

pub fn wide_effect(values: &mut [[f64; 2]], index: usize) {
    if index < values.len() {
        let bits = nested_wide(values, index);
        assert!(bits == 0x8000_0000_0000_0000);
        assert!(values[index][0].to_bits() == bits);
        assert!(values[index][1].to_bits() == 0x7ff8_0000_0000_1234);
    }
}

#[inline(never)]
pub fn nested_tuple(values: &mut [(bool, char)], index: usize) {
    original::write_tuple(values, index);
}

pub fn tuple_effect(values: &mut [(bool, char)], index: usize) {
    if index < values.len() {
        nested_tuple(values, index);
        assert!(values[index].0 && values[index].1 as u32 == 0x1f980);
    }
}

#[inline(never)]
pub fn nested_record(values: &mut [original::Record], index: usize) {
    original::write_record(values, index);
}

pub fn record_retention(values: &mut [original::Record], index: usize) {
    if index < values.len() {
        let word = values[index].word;
        nested_record(values, index);
        assert!(values[index].ready && values[index].word == word);
    }
}

#[inline(never)]
pub fn nested_zero(values: &mut [()], index: usize) {
    original::zero_child(values, index);
}

pub fn zero_metadata(values: &mut [()], index: usize) {
    let length = values.len();
    nested_zero(values, index);
    assert!(values.len() == length);
}

pub fn sequential_nested(values: &mut [[f32; 2]]) {
    if values.len() >= 2 {
        let untouched = values[1][1].to_bits();
        original::nested_child(values, 0);
        original::nested_child(values, 1);
        assert!(values[0][0].to_bits() == 0x7fc0_1234);
        assert!(values[1][0].to_bits() == 0x7fc0_1234);
        assert!(values[1][1].to_bits() == untouched);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn actual_nested_effects_and_retention() {
        super::nested_float(&mut [[1.0, -0.0], [2.0, 3.0]], 1);
        super::wide_effect(&mut [[1.0, 2.0]], 0);
        super::tuple_effect(&mut [(false, 'x')], 0);
        super::record_retention(&mut [super::original::Record { word: 19, ready: false }], 0);
        super::zero_metadata(&mut [(); 3], 1);
        super::integer_effect(&mut [(0, false)], 0, u32::MAX);
        super::sequential_nested(&mut [[1.0, -0.0], [2.0, 3.0]]);
    }
}

#[inline(never)]
pub fn integer_leaf(values: &mut [(u32, bool)], index: usize, value: u32) -> u32 {
    let result = value.wrapping_add(7);
    values[index] = (result, true);
    result
}

#[inline(never)]
pub fn integer_child(values: &mut [(u32, bool)], index: usize, value: u32) -> u32 {
    integer_leaf(values, index, value)
}

pub fn integer_effect(values: &mut [(u32, bool)], index: usize, value: u32) {
    if index < values.len() {
        let result = integer_child(values, index, value);
        assert!(values[index].0 == result && values[index].1);
        assert!(result == value.wrapping_add(7));
    }
}

pub fn wrong_integer_effect(values: &mut [(u32, bool)], index: usize, value: u32) {
    if index < values.len() {
        let result = integer_child(values, index, value);
        assert!(values[index].0 == result && values[index].1);
        assert!(result == value.wrapping_add(8));
    }
}

unsafe extern "Rust" {
    fn unavailable_product_word(value: u32) -> u32;
}

pub fn unavailable_integer_effect(values: &mut [(u32, bool)], index: usize, value: u32) {
    if index < values.len() {
        integer_child(values, index, value);
        let _ = unsafe { unavailable_product_word(value) };
    }
}
