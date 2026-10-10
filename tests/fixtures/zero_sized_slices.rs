#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[inline(never)]
fn remaining(values: &[()], index: usize) -> usize {
    let mut iterator = values.iter();
    let _ = iterator.nth(index);
    iterator.len()
}

pub fn unsupported_size_of_val(values: &[()]) {
    assert!(core::mem::size_of_val(values) == 0);
}

pub fn metadata(values: &[()]) {
    let mut iterator = values.iter();
    assert!(iterator.len() == values.len());
    assert!(iterator.size_hint() == (values.len(), Some(values.len())));
    assert!(iterator.clone().count() == values.len());
    assert!(iterator.by_ref().count() == values.len());
    assert!(iterator.next().is_none());
}

pub fn checked_index(values: &[()], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied == ());
        assert!(*values.iter().nth(index).unwrap() == ());
    }
}

pub fn nested_copies(values: &[((), [u16; 0], ((), [char; 0]))], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.0 == ());
        assert!(copied.1.len() == 0);
        assert!(copied.2.0 == ());
        assert!(copied.2.1.len() == 0);
        let selected = values.iter().nth(index).unwrap();
        assert!(selected.1.len() == 0);
    }
}

pub fn empty_array_elements(values: &[[bool; 0]], index: usize) {
    if index < values.len() {
        assert!(values[index].len() == 0);
        assert!(values.iter().nth(index).unwrap().len() == 0);
    }
}

pub fn views(values: &[()], offset: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(suffix.len() == values.len() - offset);
        assert!(suffix.iter().count() == suffix.len());
    }
    let end = values.len();
    assert!(values[end..end].iter().count() == 0);
}

pub fn mixed_cursor(values: &[()], index: usize) {
    let mut iterator = values.iter();
    if values.len() >= 2 {
        assert!(iterator.next().is_some());
        assert!(iterator.next_back().is_some());
        assert!(iterator.len() == values.len() - 2);
        if index < iterator.len() {
            assert!(iterator.nth_back(index).is_some());
            assert!(iterator.len() == values.len() - 3 - index);
        }
    }
}

pub fn maximum_length(values: &[()]) {
    if values.len() == usize::MAX {
        let mut iterator = values.iter();
        assert!(iterator.nth(usize::MAX - 1).is_some());
        assert!(iterator.len() == 0);
        assert!(iterator.next().is_none());
        assert!(values[usize::MAX - 1] == ());
    }
}

pub fn maximum_skip(values: &[()]) {
    let mut iterator = values.iter();
    assert!(iterator.nth(usize::MAX).is_none());
    assert!(iterator.len() == 0);
}

pub fn mutation_claim(values: &[()]) {
    if values.len() > 128 {
        assert!(remaining(values, 128) == values.len() - 129);
    }
}

pub fn maximum_length_reachable(values: &[()]) {
    assert!(values.len() != usize::MAX);
}

pub fn falsely_isize_bounded(values: &[()]) {
    assert!(values.len() <= isize::MAX as usize);
}

pub fn bounds_at_end(values: &[()]) -> () {
    values[values.len()]
}

pub fn wrong_remaining(values: &[()]) {
    if !values.is_empty() {
        assert!(remaining(values, 0) == values.len());
    }
}

pub fn mutable_root(values: &mut [()]) -> usize {
    values.len()
}
pub fn competing_roots(left: &[()], right: &[()]) -> bool {
    left.len() == right.len()
}
pub fn empty_reference(values: &[[&u16; 0]]) -> usize {
    values.len()
}
pub struct Wrapper;
pub fn empty_adt(values: &[[Wrapper; 0]]) -> usize {
    values.len()
}
pub struct Dropped;
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn empty_drop(values: &[[Dropped; 0]]) -> usize {
    values.len()
}
type Positive = core::pattern_type!(u32 is 1..);
pub fn empty_refined(values: &[[Positive; 0]]) -> usize {
    values.len()
}
pub fn oversized_shape(values: &[[(); 129]]) -> usize {
    values.len()
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_unit(value: ()) -> ();
    }
    pub fn missing_body(values: &[()]) {
        if !values.is_empty() {
            unsafe { opaque_unit(values[0]) };
        }
    }
    pub fn raw_source(pointer: *const (), length: usize) -> usize {
        unsafe { core::slice::from_raw_parts(pointer, length) }
            .iter()
            .count()
    }
    fn iterator_len(iterator: &core::slice::Iter<'_, ()>) -> usize {
        iterator.len()
    }
    fn iterator_next(mut iterator: core::slice::Iter<'_, ()>) -> bool {
        iterator.next().is_none()
    }
    fn empty_iterator(values: &[(); 0]) -> core::slice::Iter<'_, ()> {
        values.iter()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty_metadata() -> usize {
        mir! {
            let backing: [(); 0];
            let source: &[(); 0];
            let iterator: core::slice::Iter<'_, ()>;
            let borrow: &core::slice::Iter<'_, ()>;
            {
                backing = [];
                source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                borrow = &iterator;
                Call(RET = iterator_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_exhausted_next() -> bool {
        mir! {
            let backing: [(); 0];
            let source: &[(); 0];
            let iterator: core::slice::Iter<'_, ()>;
            {
                backing = [];
                source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                Call(RET = iterator_next(iterator), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let maximum = [(); usize::MAX];
        maximum_length(&maximum);
        maximum_skip(&maximum);
        checked_index(&maximum, usize::MAX - 1);
        let long = [(); 129];
        for values in [&[][..], &[(), ()][..], &long[..]] {
            metadata(values);
            views(values, values.len());
            maximum_length(values);
            maximum_skip(values);
            for index in [0, 1, 128, values.len(), usize::MAX] {
                checked_index(values, index);
                mixed_cursor(values, index);
            }
        }
        nested_copies(&[((), [], ((), [])); 129], 128);
        empty_array_elements(&[[]; 129], 128);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(&[(); 129]);
    }
    #[test]
    #[should_panic]
    fn bounds_negative() {
        bounds_at_end(&[(); 129]);
    }
    #[test]
    #[should_panic]
    fn remaining_negative() {
        wrong_remaining(&[(); 129]);
    }
}
