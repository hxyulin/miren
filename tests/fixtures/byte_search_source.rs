#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn word(left: u32, right: u32) -> u32 {
    left.wrapping_sub(right)
}

#[inline(never)]
pub fn source_unknown(values: &[Option<core::num::NonZeroU8>]) -> bool {
    values.contains(&None)
}

#[inline(never)]
pub fn duplicate_words(left: u32, right: u32, _wrong: bool) -> u32 {
    let first = left.wrapping_sub(right);
    first.wrapping_sub(left)
}

pub trait ForeignProjection {
    type Output;
}

pub fn foreign_projection<I: ForeignProjection>(_: I::Output) {}
