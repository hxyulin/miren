#![no_std]

#[inline(never)]
pub fn helper(value: f32) -> f32 {
    value % 3.0
}

#[inline(never)]
fn rem32(left: f32, right: f32) -> f32 {
    left % right
}

#[inline(never)]
fn rem64(left: f64, right: f64) -> f64 {
    left % right
}

pub fn correction_and_signs() {
    assert!(rem32(5.0, 3.0) == 2.0);
    assert!(rem32(-5.0, 3.0) == -2.0);
    assert!(rem32(5.0, -3.0) == 2.0);
    assert!(rem32(-5.0, -3.0) == -2.0);
    assert!(rem64(5.0, 3.0) == 2.0);
    assert!(rem64(-5.0, -3.0) == -2.0);
}

pub fn uncorrected_and_ties() {
    assert!(rem32(4.0, 3.0) == 1.0);
    assert!(rem32(-4.0, 3.0) == -1.0);
    assert!(rem32(3.0, 2.0) == 1.0);
    assert!(rem32(5.0, 2.0) == 1.0);
    assert!(rem32(7.0, 2.0) == 1.0);
    assert!(rem64(4.0, 3.0) == 1.0);
    assert!(rem64(-3.0, -2.0) == -1.0);
    assert!(rem64(5.0, 2.0) == 1.0);
    assert!(rem64(7.0, 2.0) == 1.0);
}

pub fn zero_signs() {
    assert!(rem32(-0.0, 3.0).to_bits() == (-0.0_f32).to_bits());
    assert!(rem32(0.0, -3.0).to_bits() == 0);
    assert!(rem32(-6.0, 3.0).to_bits() == (-0.0_f32).to_bits());
    assert!(rem64(-0.0, -3.0).to_bits() == (-0.0_f64).to_bits());
    assert!(rem64(6.0, -3.0).to_bits() == 0);
    assert!(rem64(-6.0, -3.0).to_bits() == (-0.0_f64).to_bits());
}

pub fn subnormal_and_extreme_values() {
    let small32 = f32::from_bits(1);
    let small64 = f64::from_bits(1);
    assert!(rem32(f32::from_bits(5), f32::from_bits(3)).to_bits() == 2);
    assert!(rem32(-f32::from_bits(5), f32::from_bits(3)).to_bits() == 0x80000002);
    assert!(rem64(f64::from_bits(5), f64::from_bits(3)).to_bits() == 2);
    assert!(rem64(-f64::from_bits(5), -f64::from_bits(3)).to_bits() == 0x8000000000000002);
    assert!(rem32(f32::MIN_POSITIVE, small32).to_bits() == 0);
    assert!(rem64(f64::MIN_POSITIVE, small64).to_bits() == 0);
    assert!(rem32(f32::MAX, small32).to_bits() == 0);
    assert!(rem64(f64::MAX, small64).to_bits() == 0);
    assert!(rem32(small32, f32::MAX).to_bits() == 1);
    assert!(rem64(small64, f64::MAX).to_bits() == 1);
}

pub fn exceptional_values() {
    assert!(rem32(7.0, f32::INFINITY) == 7.0);
    assert!(rem64(-7.0, f64::NEG_INFINITY) == -7.0);
    assert!(rem32(f32::INFINITY, 3.0).is_nan());
    assert!(rem64(f64::NEG_INFINITY, 3.0).is_nan());
    assert!(rem32(7.0, 0.0).is_nan());
    assert!(rem64(7.0, -0.0).is_nan());
    assert!(rem32(f32::NAN, 3.0).is_nan());
    assert!(rem64(3.0, f64::NAN).is_nan());
}

pub fn assignment_and_symbolic_call(value: f32, wide: f64) {
    if value == 5.0 {
        let mut result = value;
        result %= 3.0;
        assert!(result == 2.0);
        assert!(helper(value) == result);
    }
    if wide == -5.0 {
        let mut result = wide;
        result %= -3.0;
        assert!(result == -2.0);
    }
}

pub fn mutation_claim() {
    assert!(helper(5.0) == 2.0);
}

pub fn nearest_remainder_is_wrong() {
    assert!(rem32(5.0, 3.0) == -1.0);
}

pub fn divisor_sign_is_wrong() {
    assert!(rem64(-5.0, 3.0) == 2.0);
}

pub fn positive_zero_is_wrong() {
    assert!(rem32(-6.0, 3.0).to_bits() == 0);
}

pub fn arbitrary_claim(value: f32) {
    assert!(helper(value) == 2.0);
}

unsafe extern "Rust" {
    fn external_remainder(left: f64, right: f64) -> f64;
}

pub fn missing_external_body(value: f64) -> f64 {
    unsafe { external_remainder(value, 3.0) }
}

#[cfg(test)]
#[test]
fn native_valid_controls() {
    correction_and_signs();
    uncorrected_and_ties();
    zero_signs();
    subnormal_and_extreme_values();
    exceptional_values();
    assignment_and_symbolic_call(5.0, -5.0);
    assignment_and_symbolic_call(0.0, 0.0);
    mutation_claim();
}
