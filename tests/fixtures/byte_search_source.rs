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

#[inline(never)]
pub fn population_word(value: usize) -> u32 {
    value.count_ones()
}

#[inline(never)]
pub fn leading_word(value: usize) -> u32 {
    value.leading_zeros()
}

pub fn population_claims() {
    assert_eq!(population_word(0), 0);
    assert_eq!(population_word(1), 1);
    assert_eq!(population_word(core::mem::size_of::<usize>()), 1);
    assert_eq!(population_word(usize::MAX), usize::BITS);
}

#[cfg(test)]
mod population_native {
    #[test]
    fn original_claims() {
        super::population_claims();
    }
}

#[inline(never)]
pub fn trailing_word(value: usize) -> u32 {
    value.trailing_zeros()
}
