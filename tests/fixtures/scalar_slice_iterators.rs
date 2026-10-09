#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

pub fn metadata(values: &[u16]) {
    let mut iterator = values.iter();
    assert!(iterator.len() == values.len());
    assert!(iterator.size_hint() == (values.len(), Some(values.len())));
    assert!(iterator.clone().count() == values.len());
    assert!(iterator.by_ref().count() == values.len());
    assert!(iterator.len() == 0);
    assert!(iterator.next().is_none());
}

pub fn symbolic_nth(values: &[i32], index: usize) {
    let mut iterator = values.iter();
    let next = iterator.nth(index);
    if index < values.len() {
        assert!(*next.unwrap() == values[index]);
        assert!(iterator.len() == values.len() - index - 1);
    } else {
        assert!(next.is_none());
        assert!(iterator.len() == 0);
    }
}

pub fn reverse_and_mixed(values: &[u16], index: usize) {
    let mut iterator = values.iter();
    if values.len() >= 2 {
        assert!(*iterator.next().unwrap() == values[0]);
        assert!(*iterator.next_back().unwrap() == values[values.len() - 1]);
        assert!(iterator.len() == values.len() - 2);
        if index < iterator.len() {
            assert!(*iterator.nth_back(index).unwrap() == values[values.len() - 2 - index]);
        }
    }
}

pub fn cloned_cursors(values: &[u16]) {
    let mut original = values.iter();
    let mut cloned = original.clone();
    if !values.is_empty() {
        assert!(*cloned.next().unwrap() == values[0]);
        assert!(original.len() == values.len());
        assert!(*original.next().unwrap() == values[0]);
        assert!(original.len() == cloned.len());
    }
}

#[inline(never)]
fn scalar_iterator(values: &[u16]) -> core::slice::Iter<'_, u16> {
    values.iter()
}

pub fn retained_iterator(values: &[u16], index: usize) {
    if index < values.len() {
        let mut iterator = scalar_iterator(values);
        assert!(*iterator.nth(index).unwrap() == values[index]);
    }
}

struct MixedStorage<'a> {
    borrowed: &'a [u16],
    finite: [u16; 2],
}

pub fn unrelated_finite_source(values: &[u16]) {
    let storage = MixedStorage {
        borrowed: values,
        finite: [3, 7],
    };
    assert!(storage.borrowed.len() == values.len());
    let mut iterator = storage.finite.iter();
    assert!(*iterator.next().unwrap() == 3);
    assert!(*iterator.next_back().unwrap() == 7);
    assert!(iterator.len() == 0);
}

pub fn oversized_skip(values: &[u128]) {
    let mut iterator = values.iter();
    assert!(iterator.nth(usize::MAX).is_none());
    assert!(iterator.next().is_none());
    assert!(iterator.next_back().is_none());
    assert!(iterator.size_hint() == (0, Some(0)));
}

pub fn float32_storage(values: &[f32], index: usize) {
    if index < values.len() {
        let selected = *values.iter().nth(index).unwrap();
        assert!(selected.to_bits() == values[index].to_bits());
    }
}

pub fn float64_storage(values: &[f64], index: usize) {
    if index < values.len() {
        let selected = *values.iter().nth_back(values.len() - index - 1).unwrap();
        assert!(selected.to_bits() == values[index].to_bits());
    }
}

pub fn character_domain(values: &[char], index: usize) {
    if index < values.len() {
        let selected = *values.iter().nth(index).unwrap() as u32;
        assert!(selected == values[index] as u32);
        assert!(selected <= 0x10ffff);
        assert!(selected < 0xd800 || selected > 0xdfff);
    }
}

pub fn boolean_domain(values: &[bool], index: usize) {
    if index < values.len() {
        let selected = *values.iter().nth(index).unwrap();
        assert!(selected == values[index]);
        assert!(selected || !selected);
    }
}

pub fn large_view(values: &[u16]) {
    if values.len() > 128 {
        assert!(*values.iter().nth(128).unwrap() == values[128]);
    }
}

pub fn mutation_claim(values: &[u16]) {
    if values.len() >= 2 {
        let mut iterator = values.iter();
        let selected = iterator.nth(0).unwrap();
        assert!(*selected == values[0]);
    }
}

pub fn wrong_first(values: &[u16]) {
    if !values.is_empty() {
        assert!(*values.iter().next().unwrap() == 0);
    }
}

pub fn wrong_large(values: &[u16]) {
    if values.len() > 128 {
        assert!(*values.iter().nth(128).unwrap() == 0);
    }
}

pub fn wrong_clone(values: &[u16]) {
    if !values.is_empty() {
        let original = values.iter();
        let mut cloned = original.clone();
        let _ = cloned.next();
        assert!(original.len() == cloned.len());
    }
}

pub fn float_reflexivity(values: &[f32]) {
    if !values.is_empty() {
        let selected = *values.iter().next().unwrap();
        assert!(selected == selected);
    }
}

pub fn aggregate_input(values: &[(u16, bool)]) {
    let _ = values.iter().next();
}

pub fn mutable_input(values: &mut [u16]) {
    let _ = values.iter_mut().next();
}

pub fn unbounded_scan(values: &[u16]) -> u64 {
    values
        .iter()
        .fold(0_u64, |sum, value| sum.wrapping_add(u64::from(*value)))
}

pub fn borrowed_into_iterator(values: &[u16], index: usize) {
    if index < values.len() {
        assert!(*values.into_iter().nth(index).unwrap() == values[index]);
    }
}

#[inline(never)]
fn make_iterator(values: &[u16; 2]) -> core::slice::Iter<'_, u16> {
    values.iter()
}

#[inline(never)]
fn make_exhausted_iterator(values: &[u16; 2]) -> core::slice::Iter<'_, u16> {
    let mut iterator = values.iter();
    let _ = iterator.nth(usize::MAX);
    iterator
}

#[inline(never)]
fn iterator_len(iterator: core::slice::Iter<'_, u16>) -> usize {
    iterator.len()
}

#[inline(never)]
fn iterator_hint(iterator: core::slice::Iter<'_, u16>) -> usize {
    iterator.size_hint().0
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_metadata() -> usize {
    mir! {
        let backing: [u16; 2];
        let source: &[u16; 2];
        let iterator: core::slice::Iter<'_, u16>;
        {
            backing = [3_u16, 7_u16];
            source = &backing;
            Call(iterator = make_iterator(source), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(backing);
            Call(RET = iterator_len(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_exhausted_hint() -> usize {
    mir! {
        let backing: [u16; 2];
        let source: &[u16; 2];
        let iterator: core::slice::Iter<'_, u16>;
        {
            backing = [3_u16, 7_u16];
            source = &backing;
            Call(iterator = make_exhausted_iterator(source), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(backing);
            Call(RET = iterator_hint(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn live_metadata() -> usize {
    mir! {
        let backing: [u16; 2];
        let source: &[u16; 2];
        let iterator: core::slice::Iter<'_, u16>;
        {
            backing = [3_u16, 7_u16];
            source = &backing;
            Call(iterator = make_iterator(source), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(source);
            Call(RET = iterator_len(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[inline(never)]
fn iterator_count(iterator: core::slice::Iter<'_, u16>) -> usize {
    iterator.count()
}

#[inline(never)]
fn iterator_clone(iterator: core::slice::Iter<'_, u16>) -> usize {
    iterator.clone().len()
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_count() -> usize {
    mir! {
        let backing: [u16; 2];
        let source: &[u16; 2];
        let iterator: core::slice::Iter<'_, u16>;
        {
            backing = [3_u16, 7_u16];
            source = &backing;
            Call(iterator = make_iterator(source), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(backing);
            Call(RET = iterator_count(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_clone() -> usize {
    mir! {
        let backing: [u16; 2];
        let source: &[u16; 2];
        let iterator: core::slice::Iter<'_, u16>;
        {
            backing = [3_u16, 7_u16];
            source = &backing;
            Call(iterator = make_iterator(source), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(backing);
            Call(RET = iterator_clone(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[cfg(test)]
#[test]
fn native_valid_controls() {
    let large = [7_u16; 129];
    for values in [&[][..], &[3, 7, u16::MAX][..], &large[..]] {
        metadata(values);
        unrelated_finite_source(values);
        cloned_cursors(values);
        large_view(values);
        mutation_claim(values);
        for index in [0, 1, 128, values.len(), usize::MAX] {
            reverse_and_mixed(values, index);
            retained_iterator(values, index);
            borrowed_into_iterator(values, index);
        }
    }
    for index in [0, 1, 2, 3, usize::MAX] {
        symbolic_nth(&[i32::MIN, 0, i32::MAX], index);
        float32_storage(&[0.0, -0.0, f32::from_bits(0x7fc00015)], index);
        float64_storage(&[0.0, -0.0, f64::from_bits(0x7ff8000000000015)], index);
        character_domain(&['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'], index);
        boolean_domain(&[false, true], index);
    }
    oversized_skip(&[]);
    oversized_skip(&[0, u128::MAX]);
}

#[cfg(test)]
#[test]
fn native_mutation_guard() {
    mutation_claim(&[3, 7]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_first_counterexample() {
    wrong_first(&[1]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_large_counterexample() {
    wrong_large(&[1; 129]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_clone_counterexample() {
    wrong_clone(&[3]);
}

#[cfg(test)]
#[test]
#[should_panic]
fn native_nan_counterexample() {
    float_reflexivity(&[f32::from_bits(0x7fc00015)]);
}
