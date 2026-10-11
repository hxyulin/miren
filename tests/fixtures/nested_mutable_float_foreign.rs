#![no_std]
#![forbid(unsafe_code)]
extern crate nested_float_dependency;
#[inline(never)]
fn leaf(values: &mut [f32], value: f32) -> f32 {
    let result = nested_float_dependency::copied(value);
    if values.len() > 0 { values[0] = result; }
    result
}
#[inline(never)]
fn outer(values: &mut [f32], value: f32) -> f32 { leaf(&mut *(&mut *values), value) }
pub fn retained_or_omitted(values: &mut [f32], value: f32) {
    let result = outer(values, value);
    assert!(result.to_bits() == value.to_bits());
}
pub fn empty_selected(values: &mut [f32], value: f32) {
    if values.len() == 0 {
        let result = outer(values, value);
        assert!(result.to_bits() == value.to_bits());
    }
}
