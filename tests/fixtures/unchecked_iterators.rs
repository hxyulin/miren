#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, trusted_random_access)]

use core::intrinsics::mir::*;
use core::slice::{Iter, IterMut};

pub fn zipped_floats(values: &mut [f32; 3]) {
    let mut replacements = [1.0f32, 2.0, 3.0];
    for (value, replacement) in values.iter_mut().zip(replacements.iter_mut()) {
        *value = *replacement;
    }
    assert!(values[0] == 1.0 && values[1] == 2.0 && values[2] == 3.0);
}

pub fn zipped_shared(values: [u16; 3]) {
    let mut expected = [1u16, 2, 3];
    for (left, right) in values.iter().zip(expected.iter_mut()) {
        assert!(*right <= 3);
        let _ = left;
    }
}

pub fn wrong_zip_claim(values: &mut [f32; 3]) {
    zipped_floats(values);
    assert!(values[2] == 2.0);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn get_mut<'a>(iterator: &mut IterMut<'a, u8>, index: usize) -> &'a mut u8 {
    mir! {
        {
            Call(RET = <IterMut<'a, u8> as Iterator>::__iterator_get_unchecked(iterator, index),
                ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn get_shared<'a, T>(iterator: &mut Iter<'a, T>, index: usize) -> &'a T {
    mir! {
        {
            Call(RET = <Iter<'a, T> as Iterator>::__iterator_get_unchecked(iterator, index),
                ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

pub fn distinct_mutable_indices(values: &mut [u8; 3]) {
    let mut iterator = values.iter_mut();
    let first = get_mut(&mut iterator, 0);
    let last = get_mut(&mut iterator, 2);
    *first = 7;
    *last = 9;
    assert!(values[0] == 7 && values[2] == 9);
}

pub fn cursor_before_unchecked(values: &mut [u8; 3]) {
    let mut iterator = values.iter_mut();
    *iterator.next().unwrap() = 3;
    *get_mut(&mut iterator, 0) = 7;
    assert!(values[0] == 3 && values[1] == 7);
}

pub fn shared_duplicate_indices(values: [u16; 3]) {
    let mut iterator = values.iter();
    let first = get_shared(&mut iterator, 1);
    let repeated = get_shared(&mut iterator, 1);
    assert!(*first == *repeated);
}

pub fn unchecked_bounds_unknown(values: &mut [u8; 3], index: usize) {
    let mut iterator = values.iter_mut();
    *get_mut(&mut iterator, index) = 7;
}

pub fn duplicate_mutable_unknown(values: &mut [u8; 3]) {
    let mut iterator = values.iter_mut();
    let first = get_mut(&mut iterator, 0);
    let repeated = get_mut(&mut iterator, 0);
    *first = 7;
    *repeated = 9;
}

pub fn possible_duplicate_unknown(values: &mut [u8; 3], index: usize) {
    if index < 3 {
        let mut iterator = values.iter_mut();
        let first = get_mut(&mut iterator, 0);
        let second = get_mut(&mut iterator, index);
        *first = 7;
        *second = 9;
    }
}

pub fn ordinary_next_after_unchecked_unknown(values: &mut [u8; 3]) {
    let mut iterator = values.iter_mut();
    *get_mut(&mut iterator, 0) = 7;
    *iterator.next().unwrap() = 9;
}

pub fn guarded_symbolic_unchecked(values: &mut [u8; 3], index: usize) {
    if index < 3 {
        let mut iterator = values.iter_mut();
        *get_mut(&mut iterator, index) = 7;
        assert!(values[index] == 7);
    }
}

pub fn unknown_source(mut iterator: IterMut<'_, u8>) {
    *get_mut(&mut iterator, 0) = 7;
}

pub fn empty_iterator_unknown(values: &mut [u8; 0]) {
    let mut iterator = values.iter_mut();
    *get_mut(&mut iterator, 0) = 7;
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_backing_unknown(values: [u16; 3]) -> u16 {
    mir! {
        let array: &[u16; 3];
        let slice: &[u16];
        let iterator: Iter<'_, u16>;
        let receiver: &mut Iter<'_, u16>;
        let item: &u16;
        {
            array = &values;
            slice = CastUnsize(array);
            Call(iterator = <[u16]>::iter(slice), ReturnTo(dead), UnwindUnreachable())
        }
        dead = {
            receiver = &mut iterator;
            StorageDead(values);
            Call(item = get_shared(receiver, 0), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            RET = *item;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_bytes_snapshot_unknown(values: [u8; 3]) -> u8 {
    mir! {
        let array: &[u8; 3];
        let slice: &[u8];
        let iterator: Iter<'_, u8>;
        let receiver: &mut Iter<'_, u8>;
        let item: &u8;
        {
            array = &values;
            slice = CastUnsize(array);
            Call(iterator = <[u8]>::iter(slice), ReturnTo(dead), UnwindUnreachable())
        }
        dead = {
            receiver = &mut iterator;
            StorageDead(values);
            Call(item = get_shared(receiver, 0), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            RET = *item;
            Return()
        }
    }
}

struct Spoof;
impl Spoof {
    fn __iterator_get_unchecked(&mut self, index: usize) {
        assert!(index < 3);
    }
}
pub fn similarly_named_method_executes_body(index: usize) {
    Spoof.__iterator_get_unchecked(index);
}

#[cfg(test)]
mod tests {
    #[test]
    fn safe_zip_writes_replay() {
        let mut values = [0.0; 3];
        super::zipped_floats(&mut values);
        super::zipped_shared([3, 5, 7]);
    }
}
