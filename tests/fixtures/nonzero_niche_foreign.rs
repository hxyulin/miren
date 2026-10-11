#![no_std]
#![forbid(unsafe_code)]
use core::num::NonZeroU16;

pub fn foreign_selected(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(nonzero_niche_dependency::selected(value) == value.get());
        }
    }
}

#[cfg(test)]
#[test]
fn native_foreign() {
    let values = [None, NonZeroU16::new(1), NonZeroU16::new(u16::MAX)];
    for index in 0..values.len() {
        foreign_selected(&values, index);
    }
}
