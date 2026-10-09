#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]
use core::intrinsics::mir::*;
static mut BYTES: [u8; 3] = [0, 1, 2];
static mut EMPTY: [u8; 0] = [];
static mut LARGE: [u8; 129] = [0; 129];
static mut WORDS: [u16; 3] = [0, 1, 2];
#[inline(never)] pub fn boundary() -> u8 { 7 }
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn mutable_array<T>(pointer: *mut T) -> &'static mut T {
    mir! {{ RET = &mut *pointer; Return() }}
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn drop_array<T>(pointer: *mut T) {
    mir! {{ Drop(*pointer, ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }}
}
pub fn selected_element_is_valid() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let value = *slice.get_mut(1).unwrap();
    valid_byte(value);
}
pub fn selected_element_can_overflow() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    *slice.get_mut(1).unwrap() += 1;
}
pub fn zero_is_not_restored() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    assert!(*slice.get_mut(0).unwrap() == 0);
}
pub fn outside_returns_none() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    assert!(slice.get_mut(3).is_none());
}
pub fn outside_unwrap_panics() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let _ = slice.get_mut(3).unwrap();
}
pub fn empty_returns_none() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 0]>(&raw mut EMPTY);
    assert!(slice.get_mut(0).is_none());
}
pub fn uniquely_guarded_index(index: usize) {
    if index == 1 {
        let _ = boundary();
        let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
        let value = *slice.get_mut(index).unwrap();
        valid_byte(value);
    }
}
pub fn ambiguous_index(index: usize) {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    if let Some(value) = slice.get_mut(index) { let _ = *value; }
}
pub fn retired_parent_before_none_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    drop_array(&raw mut BYTES);
    let _ = slice.get_mut(3);
}
pub fn retired_empty_before_none_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 0]>(&raw mut EMPTY);
    drop_array(&raw mut EMPTY);
    let _ = slice.get_mut(0);
}
pub fn oversized_array_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 129]>(&raw mut LARGE);
    let _ = slice.get_mut(0);
}
pub fn wrong_element_is_unknown() {
    let _ = boundary();
    let slice: &mut [u16] = mutable_array::<[u16; 3]>(&raw mut WORDS);
    let _ = slice.get_mut(0);
}
pub fn mutable_iterator_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let _ = slice.iter_mut().next();
}
pub fn shared_reborrow_reads() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let shared: &[u8] = &*slice;
    let value = shared[1];
    valid_byte(value);
}
pub fn shared_iterator_reads() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let value = *slice.iter().next().unwrap();
    valid_byte(value);
}
pub fn static_store_does_not_restore_history() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    *slice.get_mut(0).unwrap() = 7;
    assert!(*slice.get_mut(0).unwrap() == 7);
}

pub fn valid_byte(value: u8) { assert!(u16::from(value) + 1 <= 256); }
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn shared_copy_write(pointer: &mut u8) {
    mir! {
        let outer: &&mut u8; let extracted: &mut u8;
        { outer = &pointer; extracted = *outer; *extracted = 7; Return() }
    }
}
pub fn forged_shared_element_write_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    shared_copy_write(slice.get_mut(1).unwrap());
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn shared_copy_return(pointer: &mut u8) -> &'static mut u8 {
    mir! {
        let outer: &&mut u8;
        { outer = &pointer; RET = *outer; Return() }
    }
}
pub fn forged_shared_element_escape_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let _ = shared_copy_return(slice.get_mut(1).unwrap());
}
fn read_nested(pointer: &&mut u8) -> u8 { **pointer }
pub fn legitimate_nested_shared_read() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let element = slice.get_mut(1).unwrap();
    valid_byte(read_nested(&element));
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn shared_slice_write(slice: &mut [u8]) {
    mir! {
        let outer: &&mut [u8]; let extracted: &mut [u8]; let index: usize;
        { index = 1; outer = &slice; extracted = *outer;
            (*extracted)[index] = 7; Return() }
    }
}
pub fn forged_shared_slice_write_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    shared_slice_write(slice);
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn forge_mutable_element(pointer: &u8) -> &'static mut u8 {
    mir! {{ RET = &mut *pointer; Return() }}
}
pub fn shared_reborrow_cannot_restore_mutation() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let shared: &[u8] = &*slice;
    let _ = forge_mutable_element(&shared[1]);
}
pub fn shared_iterator_cannot_restore_mutation() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let shared = slice.iter().next().unwrap();
    let _ = forge_mutable_element(shared);
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn readonly_array(pointer: *const [u8; 3]) -> &'static mut [u8; 3] {
    mir! {{ RET = &mut *pointer; Return() }}
}
pub fn readonly_array_cannot_unsize_mutable() {
    let _ = boundary();
    const POINTER: *const [u8; 3] = &raw const BYTES;
    let slice: &mut [u8] = readonly_array(POINTER);
    let _ = slice.get_mut(1);
}
pub fn numeric_array_cannot_unsize_mutable() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(0x20000000usize as *mut [u8; 3]);
    let _ = slice.get_mut(1);
}
#[cfg(test)]
mod native {
    use super::*;
    #[test] fn only_pure_byte_arithmetic() {
        for value in [0, 1, 127, 254, 255] { valid_byte(value); }
    }
}

#[inline(never)] pub fn opaque_boundary() -> u8 { 7 }
pub fn dead_epoch_before_none_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let _ = opaque_boundary();
    let _ = slice.get_mut(3);
}
pub fn dead_empty_epoch_before_none_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 0]>(&raw mut EMPTY);
    let _ = opaque_boundary();
    let _ = slice.get_mut(0);
}
pub fn retired_parent_before_escape_is_unknown() -> &'static mut [u8] {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    drop_array(&raw mut BYTES);
    slice
}
pub fn retired_parent_before_exhausted_next_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    let mut iter = slice.iter();
    assert!(iter.nth(3).is_none());
    drop_array(&raw mut BYTES);
    let _ = iter.next();
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn shared_tuple_write(tuple: (&mut u8,)) {
    mir! {
        let outer: &(&mut u8,); let extracted: (&mut u8,); let pointer: &mut u8;
        { outer = &tuple; extracted = *outer; pointer = extracted.0;
            *pointer = 7; Return() }
    }
}
pub fn forged_shared_tuple_write_is_unknown() {
    let _ = boundary();
    let slice: &mut [u8] = mutable_array::<[u8; 3]>(&raw mut BYTES);
    shared_tuple_write((slice.get_mut(1).unwrap(),));
}
