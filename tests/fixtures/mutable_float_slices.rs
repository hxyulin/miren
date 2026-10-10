#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn replacement(value: f32) -> f32 {
    if value == 1.0 { 2.0 } else { 1.0 }
}
#[inline(never)]
pub fn child(values: &mut [f32], index: usize, value: f32) {
    values[index] = replacement(value);
}
pub fn selected(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        child(values, index, value);
        assert!(values[index] == if value == 1.0 { 2.0 } else { 1.0 });
    }
}
pub fn direct_bits(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        values[index] = value;
        assert!(values[index].to_bits() == value.to_bits());
    }
}
pub fn negate_bits(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        values[index] = -value;
        assert!(values[index].to_bits() == value.to_bits() ^ 0x80000000);
    }
}
pub fn abs_bits(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        values[index] = value.abs();
        assert!(values[index].to_bits() == value.to_bits() & 0x7fffffff);
    }
}
pub fn direct64(values: &mut [f64], index: usize, value: f64) {
    if index < values.len() {
        values[index] = value;
        assert!(values[index].to_bits() == value.to_bits());
    }
}
pub fn negate64(values: &mut [f64], index: usize, value: f64) {
    if index < values.len() {
        values[index] = -value;
        assert!(values[index].to_bits() == value.to_bits() ^ 0x8000000000000000);
    }
}
pub fn untouched(values: &mut [f32], index: usize, other: usize, value: f32) {
    if index < values.len() && other < values.len() && index != other {
        let old = values[other].to_bits();
        child(values, index, value);
        assert!(values[other].to_bits() == old);
    }
}
pub fn arithmetic(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() && value == 1.0 {
        values[index] = value + 1.0;
        assert!(values[index] == 2.0);
    }
}
pub fn arithmetic64(values: &mut [f64], index: usize, value: f64) {
    if index < values.len() && value == 1.0 {
        values[index] = value + 1.0;
        assert!(values[index] == 2.0);
    }
}
pub fn branches(values: &mut [f32], index: usize, value: f32, flag: bool) {
    if index < values.len() {
        let next = if flag { value } else { -value };
        values[index] = next;
        assert!(values[index].to_bits() == next.to_bits());
    }
}
pub fn signed_zero(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = -0.0;
        assert!(values[0] == 0.0 && values[0].to_bits() == 0x80000000);
    }
}
pub fn nan_payload(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = f32::from_bits(0x7fc00017);
        assert!(values[0].to_bits() == 0x7fc00017);
    }
}
#[inline(never)]
pub fn returning(values: &mut [f32], index: usize, value: f32) -> f32 {
    values[index] = replacement(value);
    values[index]
}
pub fn returned(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        let result = returning(values, index, value);
        assert!(result == if value == 1.0 { 2.0 } else { 1.0 });
    }
}
pub fn empty(values: &mut [f32]) {
    if values.len() == 0 {
        assert!(values.len() == 0);
    }
}
pub fn ghost_length(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = 1.0;
    }
}
pub fn wrong(values: &mut [f32], index: usize) {
    if index < values.len() {
        values[index] = 1.0;
        assert!(values[index] == 2.0);
    }
}
pub fn bounds(values: &mut [f32], index: usize) {
    values[index] = 1.0;
}
pub fn nan_self(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = f32::from_bits(0x7fc00017);
        assert!(values[0] == values[0]);
    }
}
pub fn wrong_zero_bits(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = -0.0;
        assert!(values[0].to_bits() == 0);
    }
}
pub fn arithmetic_nan_is_nan(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = f32::INFINITY - f32::INFINITY;
        assert!(values[0].is_nan());
    }
}
pub fn arithmetic_nan_fixed_payload(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = f32::INFINITY - f32::INFINITY;
        assert!(values[0].to_bits() == 0x7fc00000);
    }
}
pub fn retained(values: &mut [f32], index: usize) {
    if index < values.len() {
        let item = &values[index];
        assert!(*item == *item);
    }
}
pub fn raw(values: &mut [f32]) {
    let _ = values.as_mut_ptr();
}
pub fn competing(first: &mut [f32], second: &mut [f32]) {
    let _ = first.len() + second.len();
}
#[inline(never)]
pub fn grandchild(values: &mut [f32], index: usize) {
    values[index] = 1.0;
}
#[inline(never)]
pub fn nested_child(values: &mut [f32], index: usize) {
    grandchild(values, index);
}
pub fn nested(values: &mut [f32], index: usize) {
    if index < values.len() {
        nested_child(values, index);
        assert!(values[index] == 1.0);
    }
}
pub fn escape(values: &mut [f32]) -> &mut [f32] {
    values
}
#[cfg(external_control)]
pub fn external_float(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() {
        values[index] = stage195_dependency::selected(value);
        assert!(values[index] == if value == 1.0 { 2.0 } else { 1.0 });
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn mutation_guard() {
        let mut values = [0.0; 129];
        selected(&mut values, 128, 0.0);
    }
    #[test]
    fn storage_encodings() {
        for bits in [
            0, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00017, 0xffc00018,
        ] {
            let mut values = [0.0; 129];
            let value = f32::from_bits(bits);
            direct_bits(&mut values, 128, value);
            negate_bits(&mut values, 128, value);
            abs_bits(&mut values, 128, value);
            branches(&mut values, 128, value, false);
            untouched(&mut values, 128, 0, value);
            returned(&mut values, 128, value);
        }
        let mut values = [0.0; 129];
        arithmetic(&mut values, 128, 1.0);
        signed_zero(&mut values);
        nan_payload(&mut values);
    }
    #[test]
    fn wide_encodings() {
        for bits in [0, 0x8000000000000000, 0x7ff8000000000017] {
            let mut values = [0.0; 129];
            let value = f64::from_bits(bits);
            direct64(&mut values, 128, value);
            negate64(&mut values, 128, value);
        }
        let mut values = [0.0; 129];
        arithmetic64(&mut values, 128, 1.0);
    }
}
