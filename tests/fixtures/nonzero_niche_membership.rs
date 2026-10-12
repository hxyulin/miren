#![no_std]
#![forbid(unsafe_code)]
use core::num::{NonZeroU16, NonZeroU32};

#[inline(never)]
pub fn member(values: &[Option<NonZeroU16>], needle: Option<NonZeroU16>) -> bool {
    values.contains(&needle)
}

pub fn selected_none(values: &[Option<NonZeroU16>]) {
    if !values.is_empty() && values[0].is_none() {
        assert!(member(values, None));
    }
}

pub fn selected_some(values: &[Option<NonZeroU16>], needle: NonZeroU16) {
    if !values.is_empty()
        && let Some(first) = values[0]
        && first.get() == needle.get()
    {
        assert!(member(values, Some(needle)));
    }
}

pub fn empty(values: &[Option<NonZeroU16>]) {
    if values.is_empty() {
        assert!(!member(values, None));
    }
}

pub fn wrong_empty(values: &[Option<NonZeroU16>]) {
    if values.is_empty() {
        assert!(member(values, None));
    }
}

pub fn unsupported_width(values: &[Option<NonZeroU32>], needle: Option<NonZeroU32>) {
    assert!(values.contains(&needle));
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        let first = core::num::NonZeroU16::new(1).unwrap();
        let second = core::num::NonZeroU16::new(2).unwrap();
        super::selected_none(&[None, Some(first), None]);
        super::selected_some(&[Some(first), Some(second)], first);
        super::empty(&[]);
    }
}
