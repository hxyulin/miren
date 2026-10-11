#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn selected(value: core::num::NonZeroU16) -> u16 {
    value.get()
}
