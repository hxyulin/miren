#![no_std]
#![forbid(unsafe_code)]
#[derive(Clone, Copy)]
pub struct External;

#[inline(never)]
pub fn missing_tag() -> u16 {
    17
}
