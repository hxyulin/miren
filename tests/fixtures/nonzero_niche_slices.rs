#![no_std]
#![forbid(unsafe_code)]
use core::num::NonZeroU16;

#[derive(Clone, Copy)]
pub enum Word {
    Empty,
    Present(NonZeroU16),
}

#[derive(Clone, Copy)]
pub enum Reversed {
    Present(NonZeroU16),
    Empty,
}

#[inline(never)]
pub fn selected(value: Option<NonZeroU16>) -> u16 {
    match value {
        None => 0,
        Some(value) => value.get(),
    }
}

pub fn repeated(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        let value = values[index];
        match value {
            None => assert!(selected(value) == 0),
            Some(word) => assert!(selected(value) == word.get()),
        }
    }
}

pub fn wrong(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(word) = values[index] {
            assert!(word.get() == 0);
        }
    }
}

pub fn local_sum(values: &[Word], index: usize) {
    if index < values.len() {
        if let Word::Present(word) = values[index] {
            assert!(word.get() != 0);
        }
    }
}

pub fn reversed(values: &[Reversed], index: usize) {
    if index < values.len() {
        if let Reversed::Present(word) = values[index] {
            assert!(word.get() != 0);
        }
    }
}

pub fn nonzero(values: &[NonZeroU16], index: usize) {
    if index < values.len() {
        assert!(values[index].get() != 0);
    }
}

pub fn zero_array(values: &[[Option<NonZeroU16>; 0]], index: usize) {
    if index < values.len() {
        assert!(values[index].len() == 0);
    }
}

pub fn pointer_niche(values: &[Option<&u16>], index: usize) {
    if index < values.len() {
        if let Some(word) = values[index] {
            let _ = *word;
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn mutation_guard() {
        let mut values = [None; 129];
        for (index, value) in values.iter_mut().enumerate() {
            if index % 3 != 0 {
                *value = NonZeroU16::new(index as u16 + 1);
            }
        }
        values[128] = NonZeroU16::new(u16::MAX);
        for index in 0..values.len() {
            repeated(&values, index);
        }
    }
}

#[inline(never)]
fn identity(value: NonZeroU16) -> NonZeroU16 {
    value
}

pub fn copied_payload(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            let copied = value;
            assert!(copied.get() == value.get());
        }
    }
}

pub fn helper_payload(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(identity(value).get() == value.get());
        }
    }
}

pub fn shared_payload(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(value) = &values[index] {
            assert!(value.get() != 0);
        }
    }
}

pub fn fixed_array(values: &[[Option<NonZeroU16>; 2]], index: usize) {
    if index < values.len() {
        let row = values[index];
        if let Some(value) = row[1] {
            assert!(selected(row[1]) == value.get());
        }
    }
}

pub fn tuple_child(values: &[(Option<NonZeroU16>, u16)], index: usize) {
    if index < values.len() {
        let row = values[index];
        if let Some(value) = row.0 {
            assert!(selected(row.0) == value.get());
        }
    }
}

pub fn independent_roots(left: &[Option<NonZeroU16>], right: &[Option<NonZeroU16>], index: usize) {
    if index < left.len() && index < right.len() {
        if let (Some(left), Some(right)) = (left[index], right[index]) {
            assert!(left.get() != 0 && right.get() != 0);
        }
    }
}

pub fn wrong_independent(left: &[Option<NonZeroU16>], right: &[Option<NonZeroU16>], index: usize) {
    if index < left.len() && index < right.len() {
        if let (Some(left), Some(right)) = (left[index], right[index]) {
            assert!(left.get() == right.get());
        }
    }
}

pub fn none_branch(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() && values[index].is_none() {
        assert!(selected(values[index]) == 0);
    }
}

pub fn wrong_none(values: &[Option<NonZeroU16>], index: usize) {
    if index < values.len() && values[index].is_none() {
        assert!(selected(values[index]) != 0);
    }
}

pub fn wrong_bounds(values: &[Option<NonZeroU16>], index: usize) {
    let _ = selected(values[index]);
}

pub fn zero_max(values: &[[Option<NonZeroU16>; 0]]) {
    if values.len() == usize::MAX {
        assert!(values[0].is_empty());
    }
}

pub fn unsupported_zero(values: &[[Option<core::num::NonZeroU32>; 0]], index: usize) {
    if index < values.len() {
        assert!(values[index].is_empty());
    }
}

pub fn signed_niche(values: &[Option<core::num::NonZeroI16>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(value.get() != 0);
        }
    }
}

pub fn over_budget(values: &[[Option<NonZeroU16>; 129]], index: usize) {
    if index < values.len() {
        let _ = values[index];
    }
}

pub fn expanded_budget(values: &[[Option<NonZeroU16>; 86]], index: usize) {
    if index < values.len() {
        let _ = values[index];
    }
}

pub fn whole_membership(values: &[Option<NonZeroU16>], needle: Option<NonZeroU16>) {
    let _ = values.contains(&needle);
}

pub fn mutable_niche(values: &mut [Option<NonZeroU16>], index: usize) {
    if index < values.len() {
        values[index] = None;
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum ExplicitTag {
    Empty,
    Present(NonZeroU16),
}

pub fn explicit_tag(values: &[ExplicitTag], index: usize) {
    if index < values.len() {
        if let ExplicitTag::Present(value) = values[index] {
            assert!(value.get() != 0);
        }
    }
}

#[cfg(test)]
#[test]
fn native_safe_domains() {
    let values = [None, NonZeroU16::new(1), NonZeroU16::new(u16::MAX)];
    let words = [Word::Empty, Word::Present(NonZeroU16::new(1).unwrap())];
    let reversed_values = [
        Reversed::Empty,
        Reversed::Present(NonZeroU16::new(u16::MAX).unwrap()),
    ];
    for index in 0..values.len() {
        copied_payload(&values, index);
        helper_payload(&values, index);
        shared_payload(&values, index);
        none_branch(&values, index);
        tuple_child(&[(values[index], 17)], 0);
        fixed_array(&[[None, values[index]]], 0);
        independent_roots(&values, &values, index);
    }
    for index in 0..words.len() {
        local_sum(&words, index);
        reversed(&reversed_values, index);
    }
}

pub fn paired_columns(values: &[(Option<NonZeroU16>, Option<NonZeroU16>)], index: usize) {
    if index < values.len() {
        if let (Some(left), Some(right)) = values[index] {
            assert!(left.get() != 0 && right.get() != 0);
        }
    }
}

pub fn wrong_paired_columns(values: &[(Option<NonZeroU16>, Option<NonZeroU16>)], index: usize) {
    if index < values.len() {
        if let (Some(left), Some(right)) = values[index] {
            assert!(left.get() == right.get());
        }
    }
}
