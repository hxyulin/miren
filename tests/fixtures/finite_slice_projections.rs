#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

fn add(value: &mut u16) {
    *value += 1;
}

pub fn indexed_update() {
    let mut values = [10_u16, 20, 30, 40];
    let slice = &mut values[1..3];
    add(&mut slice[0]);
    assert!(values == [10, 21, 30, 40]);
}

pub fn nested_tuple_update() {
    let mut values = [(1_u16, 10_u32), (2, 20), (3, 30), (4, 40)];
    let outer = &mut values[1..4];
    let inner = &mut outer[1..2];
    inner[0].1 += 7;
    assert!(values == [(1, 10), (2, 20), (3, 37), (4, 40)]);
}

pub fn shared_reborrow() {
    let mut values = [10_u16, 20, 30, 40];
    let slice = &mut values[1..3];
    let shared = &*slice;
    assert!(shared[0] == 20 && shared[1] == 30);
    add(&mut slice[1]);
    assert!(values[2] == 31 && values[3] == 40);
}

pub fn empty_at_end() {
    let mut values = [1_u16, 2, 3];
    let empty = &mut values[3..3];
    assert!(empty.is_empty());
}

pub fn constrained_symbolic_length(length: usize) {
    if length == 2 {
        let mut values = [10_u16, 20, 30];
        let slice = &mut values[..length];
        assert!(slice.len() == length);
        add(&mut slice[1]);
        assert!(values == [10, 21, 30]);
    }
}

pub fn symbolic_scalar_offset(start: usize) {
    if start < 3 {
        let mut values = [10_u16, 20, 30, 40];
        let slice = &mut values[start..start + 1];
        assert!(slice[0] >= 10 && slice[0] <= 30);
    }
}

pub fn callback_order() {
    let mut values = [1_u16, 2, 3, 4];
    let slice = &mut values[1..3];
    add(&mut slice[0]);
    slice.iter_mut().for_each(|value| *value *= 2);
    assert!(values == [1, 6, 6, 4]);
}

pub fn wrong_callback_order() {
    let mut values = [1_u16, 2, 3, 4];
    let slice = &mut values[1..3];
    add(&mut slice[0]);
    slice.iter_mut().for_each(|value| *value *= 2);
    assert!(values[1] == 5);
}

pub fn invalid_range(end: usize) {
    let mut values = [1_u16, 2, 3];
    let slice = &mut values[..end];
    assert!(slice.len() == end);
}

pub fn invalid_index(index: usize) {
    let mut values = [1_u16, 2, 3];
    let slice = &mut values[1..3];
    let _ = slice[index];
}

pub fn variable_length(length: usize) {
    if length <= 3 {
        let mut values = [1_u16, 2, 3];
        let slice = &mut values[..length];
        assert!(slice.len() == length);
    }
}

pub fn ambiguous_tuple_offset(start: usize) {
    if start < 2 {
        let mut values = [(1_u16, 2_u32), (3, 4), (5, 6)];
        let slice = &mut values[start..start + 1];
        assert!(slice[0].0 <= 3);
    }
}

pub fn ambiguous_write(index: usize) {
    if index < 2 {
        let mut values = [1_u16, 2, 3];
        let slice = &mut values[..2];
        slice[index] = 7;
    }
}

pub fn bounded_large_backing(values: &mut [u16; 129]) {
    let slice = &mut values[..1];
    slice[0] = 7;
    assert!(values[0] == 7);
}

pub fn oversized(values: &mut [u16; 129]) {
    let slice = &mut values[..129];
    assert!(slice.len() == 129);
}

pub fn floating_shape() {
    let mut values = [1.0_f32, 2.0];
    let slice = &mut values[..1];
    assert!(slice[0] == 1.0);
}

fn initial() -> [u16; 4] {
    [10, 20, 30, 40]
}

fn middle(values: &mut [u16; 4]) -> &mut [u16] {
    &mut values[1..3]
}

pub fn returned_view() {
    let mut values = [10_u16, 20, 30, 40];
    let slice = middle(&mut values);
    add(&mut slice[1]);
    assert!(values == [10, 20, 31, 40]);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn escaped_frame<'a>() -> &'a mut [u16] {
    mir! {
        let values: [u16; 4];
        let reference: &mut [u16; 4];
        {
            StorageLive(values);
            Call(values = initial(), ReturnTo(borrow), UnwindUnreachable())
        }
        borrow = {
            reference = &mut values;
            Call(RET = middle(reference), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

fn empty(values: &mut [u16; 4]) -> &mut [u16] {
    &mut values[4..4]
}

fn length(values: &mut [u16]) -> usize {
    values.len()
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_empty() -> usize {
    mir! {
        let values: [u16; 4];
        let reference: &mut [u16; 4];
        let slice: &mut [u16];
        {
            StorageLive(values);
            Call(values = initial(), ReturnTo(borrow), UnwindUnreachable())
        }
        borrow = {
            reference = &mut values;
            Call(slice = empty(reference), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(values);
            Call(RET = length(slice), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn forbidden_write(input: &&mut [u16]) {
    mir! {
        let extracted: &mut [u16];
        let index: usize;
        { extracted = *input; index = 0_usize; (*extracted)[index] = 99_u16; Return() }
    }
}

pub fn shared_write() {
    let mut values = [10_u16, 20];
    let slice = &mut values[..1];
    forbidden_write(&slice);
}

pub fn opaque_effect(effect: fn(&mut [u16])) {
    let mut values = [10_u16, 20];
    let slice = &mut values[..1];
    effect(slice);
    assert!(slice[0] == 10);
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positive() {
        indexed_update();
        nested_tuple_update();
        shared_reborrow();
        returned_view();
        empty_at_end();
        constrained_symbolic_length(2);
        symbolic_scalar_offset(1);
        callback_order();
        bounded_large_backing(&mut [0; 129]);
    }

    #[test]
    #[should_panic]
    fn negative() {
        wrong_callback_order();
    }
}
