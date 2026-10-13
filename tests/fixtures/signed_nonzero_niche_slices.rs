#![no_std]
#![forbid(unsafe_code)]
use core::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroIsize};

#[inline(never)]
pub fn actual_get8(value: NonZeroI8) -> i8 {
    value.get()
}
#[inline(never)]
pub fn actual_get16(value: NonZeroI16) -> i16 {
    value.get()
}
#[inline(never)]
pub fn actual_get32(value: NonZeroI32) -> i32 {
    value.get()
}
#[inline(never)]
pub fn actual_equal16(left: Option<NonZeroI16>, right: Option<NonZeroI16>) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member16(values: &[Option<NonZeroI16>], needle: Option<NonZeroI16>) -> bool {
    values.contains(&needle)
}

pub fn correlated8(values: &[Option<NonZeroI8>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get8(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn correlated16(values: &[Option<NonZeroI16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(actual_get16(value) != 0);
            if value.get() < 0 {
                assert!(value.get() <= -1);
            } else {
                assert!(value.get() >= 1);
            }
        }
    }
}
pub fn correlated32(values: &[Option<NonZeroI32>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(actual_get32(value) != 0);
            if value.get() < 0 {
                assert!(value.get() <= -1);
            }
        }
    }
}
pub fn same16(values: &[Option<NonZeroI16>], index: usize) {
    if index < values.len() {
        assert!(actual_equal16(values[index], values[index]));
    }
}
pub fn minimums() {
    let values = [NonZeroI8::new(i8::MIN), NonZeroI8::new(-1), None];
    assert!(actual_get8(values[0].unwrap()) == i8::MIN);
    assert!(actual_get8(values[1].unwrap()) == -1);
    assert!(values[2].is_none());
    assert!(actual_get16(NonZeroI16::new(i16::MIN).unwrap()) == i16::MIN);
    assert!(actual_get32(NonZeroI32::new(i32::MIN).unwrap()) == i32::MIN);
}
pub fn fixed_array(values: &[Option<NonZeroI32>; 2]) {
    if let Some(value) = values[1] {
        assert!(actual_get32(value) != 0);
    }
}
pub fn contains_selected(values: &[Option<NonZeroI16>], index: usize) {
    if index < values.len() {
        assert!(actual_member16(values, values[index]));
    }
}
pub fn wrong_nonnegative(values: &[Option<NonZeroI16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(actual_get16(value) > 0);
        }
    }
}
pub fn wrong_zero(values: &[Option<NonZeroI8>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(actual_get8(value) == 0);
        }
    }
}
pub fn wrong_minimum() {
    assert!(actual_get32(NonZeroI32::new(i32::MIN).unwrap()) == i32::MAX);
}

#[derive(Clone, Copy)]
pub enum SignedLocal {
    Empty,
    Value(NonZeroI16),
}
pub fn local_enum_unknown(values: &[SignedLocal], index: usize) {
    if index < values.len() {
        if let SignedLocal::Value(value) = values[index] {
            assert!(value.get() != 0);
        }
    }
}
pub fn mutable_unknown(values: &mut [Option<NonZeroI16>]) {
    if !values.is_empty() {
        values[0] = None;
    }
}
pub fn pointer_unknown(values: &[Option<NonZeroIsize>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_none() || values[index].is_some());
    }
}
pub fn width64_unknown(values: &[Option<NonZeroI64>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_none() || values[index].is_some());
    }
}
pub fn signed_byte_unknown(values: &[Option<NonZeroI8>], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn actual_signed_helpers_preserve_negative_claims() {
        let a = [
            None,
            NonZeroI8::new(i8::MIN),
            NonZeroI8::new(-1),
            NonZeroI8::new(1),
        ];
        let b = [
            None,
            NonZeroI16::new(i16::MIN),
            NonZeroI16::new(-1),
            NonZeroI16::new(1),
        ];
        let c = [
            None,
            NonZeroI32::new(i32::MIN),
            NonZeroI32::new(-1),
            NonZeroI32::new(1),
        ];
        for i in 0..4 {
            super::correlated8(&a, i);
            super::correlated16(&b, i);
            super::correlated32(&c, i);
            super::same16(&b, i);
            super::contains_selected(&b, i);
        }
        super::fixed_array(&[NonZeroI32::new(-1), NonZeroI32::new(i32::MIN)]);
        super::minimums();
    }
    use core::num::{NonZeroI8, NonZeroI16, NonZeroI32};
}
