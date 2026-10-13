#![no_std]
#![forbid(unsafe_code)]
extern crate local_niche_dependency;
#[derive(Clone, Copy)]
pub enum Word {
    Empty,
    Word(core::num::NonZeroU32),
}
pub fn claim(values: &[Word], index: usize) {
    if index < values.len()
        && let Word::Word(value) = values[index]
    {
        assert!(local_niche_dependency::observe(value.get()) == value.get());
    }
}
