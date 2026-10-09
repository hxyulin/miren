#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicU8, Ordering};

#[derive(Clone, Copy)]
#[repr(C)]
struct Pair {
    left: u32,
    right: u32,
}

#[derive(Clone, Copy)]
#[repr(C)]
struct Nested {
    padding: u8,
    pair: Pair,
    tuple: (u16, i32),
}

static PAIR: SyncUnsafeCell<Pair> = SyncUnsafeCell::new(Pair { left: 1, right: 2 });
static NESTED: SyncUnsafeCell<Nested> = SyncUnsafeCell::new(Nested {
    padding: 1,
    pair: Pair { left: 1, right: 2 },
    tuple: (3, 4),
});
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Single {
    value: u32,
}
static SINGLE: SyncUnsafeCell<Single> = SyncUnsafeCell::new(Single { value: 1 });
static CHOICE: AtomicU8 = AtomicU8::new(0);
static REFERENCES: SyncUnsafeCell<(&AtomicU8, u32)> = SyncUnsafeCell::new((&CHOICE, 0));
static POINTERS: SyncUnsafeCell<(usize, u32)> = SyncUnsafeCell::new((0, 0));
static ARRAY: SyncUnsafeCell<[u32; 2]> = SyncUnsafeCell::new([1, 2]);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write<T>(pointer: *mut T, value: T) {
    mir! {{ *pointer = Move(value); Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read<T: Copy>(pointer: *const T) -> T {
    mir! {{ RET = *pointer; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn left(pointer: *mut Pair) -> *mut u32 {
    mir! {{ RET = &raw mut (*pointer).left; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn right(pointer: *mut Pair) -> *mut u32 {
    mir! {{ RET = &raw mut (*pointer).right; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn nested_pair(pointer: *mut Nested) -> *mut Pair {
    mir! {{ RET = &raw mut (*pointer).pair; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn nested_tuple(pointer: *mut Nested) -> *mut (u16, i32) {
    mir! {{ RET = &raw mut (*pointer).tuple; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn tuple_second(pointer: *mut (u16, i32)) -> *mut i32 {
    mir! {{ RET = &raw mut (*pointer).1; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn single_value(pointer: *mut Single) -> *mut u32 {
    mir! {{ RET = &raw mut (*pointer).value; Return() }}
}

pub fn identical_parent_child_footprints_are_typed_projections() {
    write(SINGLE.get(), Single { value: 7 });
    assert!(read(single_value(SINGLE.get())) == 7);
    write(single_value(SINGLE.get()), 8);
    assert!(read(SINGLE.get()).value == 8);
}

fn store_pair() {
    write(PAIR.get(), Pair { left: 3, right: 4 });
}

pub fn stored_child() {
    store_pair();
    assert!(read(right(PAIR.get())) == 4);
}

pub fn child_update_preserves_sibling() {
    store_pair();
    write(left(PAIR.get()), 5);
    assert!(read(left(PAIR.get())) == 5);
    assert!(read(right(PAIR.get())) == 4);
    let pair = read(PAIR.get());
    assert!(pair.left == 5 && pair.right == 4);
}

pub fn old_initializer_is_refuted() {
    store_pair();
    write(left(PAIR.get()), 5);
    assert!(read(right(PAIR.get())) == 2);
}

pub fn nested_fields_and_tuples() {
    write(
        NESTED.get(),
        Nested {
            padding: 8,
            pair: Pair { left: 9, right: 10 },
            tuple: (11, -12),
        },
    );
    write(right(nested_pair(NESTED.get())), 13);
    write(tuple_second(nested_tuple(NESTED.get())), -14);
    let value = read(NESTED.get());
    assert!(value.padding == 8 && value.pair.left == 9 && value.pair.right == 13);
    assert!(value.tuple.0 == 11 && value.tuple.1 == -14);
}

pub fn whole_write_replaces_children() {
    write(left(PAIR.get()), 9);
    store_pair();
    assert!(read(left(PAIR.get())) == 3);
    assert!(read(right(PAIR.get())) == 4);
}

pub fn branch_isolation() {
    store_pair();
    if CHOICE
        .compare_exchange_weak(0, 1, Ordering::Relaxed, Ordering::Relaxed)
        .is_ok()
    {
        write(left(PAIR.get()), 5);
        assert!(read(left(PAIR.get())) == 5);
    } else {
        assert!(read(left(PAIR.get())) == 3);
    }
    assert!(read(right(PAIR.get())) == 4);
}

pub fn wrong_field_type() {
    store_pair();
    assert!(read(right(PAIR.get()).cast::<i32>()) == 4);
}

pub fn numeric_pointee_remains_unknown() {
    write(POINTERS.get(), (0x2000_0000_usize, 7));
    let tuple = read(POINTERS.get());
    assert!(read(tuple.0 as *const u32) == 0);
}

pub fn array_element_history_remains_unknown() {
    write(ARRAY.get(), [3, 4]);
    assert!(read(ARRAY.get().cast::<u32>()) == 3);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn retire<T>(pointer: *mut T) {
    mir! {{ Drop(*pointer, ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

pub fn retired_child_is_unknown() {
    store_pair();
    retire(right(PAIR.get()));
    assert!(read(right(PAIR.get())) == 4);
}

pub fn retirement_does_not_resurrect_sibling() {
    store_pair();
    retire(left(PAIR.get()));
    write(left(PAIR.get()), 5);
    assert!(read(right(PAIR.get())) == 2);
}

pub fn whole_reinitialization_after_retirement() {
    store_pair();
    retire(left(PAIR.get()));
    store_pair();
    assert!(read(right(PAIR.get())) == 4);
}

pub fn matching_child_reinitialization_then_parent_store() {
    store_pair();
    let pointer = PAIR.get();
    let child = left(pointer);
    retire(child);
    write(child, 5);
    write(pointer, Pair { left: 6, right: 7 });
    assert!(read(right(pointer)) == 7);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn first_reference(pointer: *mut (&'static AtomicU8, u32)) -> *mut &'static AtomicU8 {
    mir! {{ RET = &raw mut (*pointer).0; Return() }}
}

pub fn retired_reference_in_parent_is_unknown() {
    write(REFERENCES.get(), (&CHOICE, 7));
    retire(CHOICE.as_ptr());
    let atomic = read(first_reference(REFERENCES.get()));
    assert!(atomic.load(Ordering::Relaxed) == 0);
}

pub fn boundary() {}

pub fn opaque_boundary_discards_parent() {
    store_pair();
    boundary();
    assert!(read(right(PAIR.get())) == 4);
}

pub fn opaque_boundary_child_write_does_not_restore_parent() {
    store_pair();
    boundary();
    write(left(PAIR.get()), 5);
    assert!(read(right(PAIR.get())) == 4);
}

#[cfg(test)]
#[test]
fn native_child_updates() {
    stored_child();
    child_update_preserves_sibling();
    nested_fields_and_tuples();
    whole_write_replaces_children();
}
