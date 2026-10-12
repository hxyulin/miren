#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn actual_float() -> f32 {
    f32::from_bits(0x7fc0_1234)
}
