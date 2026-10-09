#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicPtr, Ordering};

static OPTIONAL: SyncUnsafeCell<Option<u32>> = SyncUnsafeCell::new(None);
static POINTER: AtomicPtr<u32> = AtomicPtr::new(core::ptr::null_mut());
type Callback = Option<fn(u32) -> u32>;
static CALLBACK: SyncUnsafeCell<Callback> = SyncUnsafeCell::new(None);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn optional(pointer: *mut Option<u32>) -> &'static Option<u32> {
    mir! { { RET = &*pointer; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn set_callback(pointer: *mut Callback, callback: Callback) {
    mir! { { *pointer = callback; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn callback(pointer: *mut Callback) -> &'static Callback {
    mir! { { RET = &*pointer; Return() } }
}

fn add_two(value: u32) -> u32 {
    value + 2
}

pub fn isolated_publication_keeps_disjoint_initializers() {
    POINTER.store(0x2000_0000_usize as *mut u32, Ordering::Release);
    assert!(optional(OPTIONAL.get()).is_none());
    assert!(POINTER.load(Ordering::Acquire) as usize == 0x2000_0000);
}

pub fn isolated_callback_store_executes_the_actual_function() {
    set_callback(CALLBACK.get(), Some(add_two));
    let function = callback(CALLBACK.get()).unwrap();
    assert!(function(3) == 5);
    assert!(optional(OPTIONAL.get()).is_none());
}

#[repr(C)]
struct Pair {
    left: u32,
    right: u32,
}
static PAIR: SyncUnsafeCell<Pair> = SyncUnsafeCell::new(Pair { left: 1, right: 2 });

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write_pair(pointer: *mut Pair) {
    mir! { { *pointer = Pair { left: 3, right: 4 }; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write_left(pointer: *mut Pair) {
    mir! { { (*pointer).left = 5; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn right(pointer: *mut Pair) -> u32 {
    mir! { { RET = (*pointer).right; Return() } }
}

pub fn overwritten_parent_cannot_resurrect_a_child_initializer() {
    write_pair(PAIR.get());
    write_left(PAIR.get());
    assert!(right(PAIR.get()) == 2);
}

pub fn boundary() {}

pub fn isolated_opaque_calls_discard_unseen_initializers() {
    boundary();
    assert!(optional(OPTIONAL.get()).is_none());
}

pub fn isolated_opaque_calls_discard_written_callbacks() {
    set_callback(CALLBACK.get(), Some(add_two));
    boundary();
    assert!(callback(CALLBACK.get()).is_some());
}

pub async fn async_factory() {}

pub fn root_with_argument(value: u32) {
    assert!(value == 0);
}

#[cfg(test)]
#[test]
fn native_callback_store() {
    isolated_callback_store_executes_the_actual_function();
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn retire_optional(pointer: *mut Option<u32>) {
    mir! {
        { Drop(*pointer, ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write_optional(pointer: *mut Option<u32>) {
    mir! { { *pointer = Some(7); Return() } }
}

pub fn isolated_retirement_preserves_disjoint_history_and_requires_reinitialization() {
    let pointer = OPTIONAL.get();
    retire_optional(pointer);
    assert!(POINTER.load(Ordering::Relaxed).is_null());
    write_optional(pointer);
    assert!(optional(pointer).is_some());
}

pub fn isolated_retired_payload_reads_are_unknown() {
    retire_optional(OPTIONAL.get());
    assert!(optional(OPTIONAL.get()).is_none());
}
