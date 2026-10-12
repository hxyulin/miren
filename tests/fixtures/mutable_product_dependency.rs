#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn observe_bits(value: f32) -> u32 {
    value.to_bits()
}
