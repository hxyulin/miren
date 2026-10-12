#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]

use core::num::{NonZeroI8, NonZeroU8};

#[inline(never)]
pub fn selected_observer(value: Option<NonZeroU8>) -> u8 {
    match value {
        None => 0,
        Some(word) => word.get(),
    }
}

#[inline(never)]
pub fn selected_equal8(left: Option<NonZeroU8>, right: Option<NonZeroU8>) -> bool {
    left == right
}

#[inline(never)]
pub fn selected_not_equal8(left: Option<NonZeroU8>, right: Option<NonZeroU8>) -> bool {
    left != right
}

pub fn same_observation_ne8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(!selected_not_equal8(value, value));
    }
}

pub fn observe_correlated8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        match value {
            None => assert!(selected_observer(value) == 0),
            Some(word) => assert!(selected_observer(value) == word.get() && word.get() != 0),
        }
    }
}

pub fn wrong_some_zero8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len()
        && let Some(word) = values[index]
    {
        assert!(word.get() == 0);
    }
}

pub fn same_observation_eq8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(selected_equal8(value, value));
    }
}

pub fn wrong_ne8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(selected_not_equal8(value, value));
    }
}

#[inline(never)]
pub fn selected_member8(values: &[Option<NonZeroU8>], needle: Option<NonZeroU8>) -> bool {
    values.contains(&needle)
}

pub fn asserted_contains8(values: &[Option<NonZeroU8>]) {
    if !values.is_empty() && values[0].is_none() {
        assert!(selected_member8(values, None));
    }
}

#[derive(Clone, Copy)]
pub enum Local8 {
    Empty,
    Word(NonZeroU8),
}

pub fn local_enum_unknown(values: &[Local8], index: usize) {
    if index < values.len()
        && let Local8::Word(word) = values[index]
    {
        assert!(word.get() != 0);
    }
}

pub fn mutable_unknown(values: &mut [Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}

pub fn signed_unknown(values: &[Option<NonZeroI8>], index: usize) {
    if index < values.len()
        && let Some(word) = values[index]
    {
        assert!(word.get() != 0);
    }
}

pub fn pointer_unknown(values: &[Option<&u8>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}

#[cfg(test)]
mod native {
    use super::*;

    fn values() -> [Option<NonZeroU8>; 129] {
        let mut values = [None; 129];
        for (index, value) in values.iter_mut().enumerate() {
            if index % 3 != 0 {
                *value = NonZeroU8::new(index as u8);
            }
        }
        values[1] = NonZeroU8::new(1);
        values[128] = NonZeroU8::new(u8::MAX);
        values
    }

    #[test]
    fn observer_claims() {
        let values = values();
        for index in 0..values.len() {
            observe_correlated8(&values, index);
        }
        observe_correlated8(&[], 0);
    }

    #[test]
    fn equality_claims() {
        let values = values();
        for index in 0..values.len() {
            same_observation_eq8(&values, index);
        }
        same_observation_eq8(&[], 0);
    }
}
