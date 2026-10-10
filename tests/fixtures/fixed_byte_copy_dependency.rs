#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn apply(values: &mut [u8]) {
    values[..2].copy_from_slice(&[17, 19]);
}
