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

#[inline(never)]
pub fn member_u32(values: &[Option<NonZeroU32>], needle: Option<NonZeroU32>) -> bool {
    values.contains(&needle)
}

pub fn selected_none_u32(values: &[Option<NonZeroU32>]) {
    if !values.is_empty() && values[0].is_none() { assert!(member_u32(values,None)); }
}

pub fn selected_some_u32(values: &[Option<NonZeroU32>], needle: NonZeroU32) {
    if !values.is_empty() && let Some(first)=values[0] && first.get()==needle.get() {
        assert!(member_u32(values,Some(needle)));
    }
}

pub fn empty_u32(values: &[Option<NonZeroU32>]) {
    if values.is_empty() { assert!(!member_u32(values,None)); }
}

pub fn wrong_empty_u32(values: &[Option<NonZeroU32>]) {
    if values.is_empty() { assert!(member_u32(values,None)); }
}

pub fn unsupported_byte_niche(values: &[Option<core::num::NonZeroU8>]) {
    let _ = values.contains(&None);
}

#[cfg(test)]
mod native_u32 {
    #[test]
    fn genuine_claims() {
        let high=super::NonZeroU32::new(0x8000_0000).unwrap();
        let maximum=super::NonZeroU32::new(u32::MAX).unwrap();
        super::selected_none_u32(&[Some(high),None]);
        super::selected_some_u32(&[Some(maximum),Some(high)],maximum);
        super::empty_u32(&[]);
    }
}
