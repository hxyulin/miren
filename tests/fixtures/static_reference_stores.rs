#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;

pub struct Snapshot {
    byte: u8,
    words: (u16, bool),
    bytes: [u8; 4],
}

static SHARED: SyncUnsafeCell<Option<&'static Snapshot>> = SyncUnsafeCell::new(None);
static MUTABLE: SyncUnsafeCell<Option<&'static mut Snapshot>> = SyncUnsafeCell::new(None);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn store<T>(pointer: *mut T, value: T) {
    mir! {
        {
            *pointer = Move(value);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(value: S) -> T {
    mir! {
        {
            RET = CastTransmute(value);
            Return()
        }
    }
}

pub fn stores_shared_snapshot(value: &'static Snapshot) {
    if value.byte < 8 {
        store(SHARED.get(), Some(value));
        assert!(value.byte < 8);
    }
}

pub fn store_then_wrong_claim(value: &'static Snapshot) {
    store(SHARED.get(), Some(value));
    assert!(value.byte < 8);
}

pub fn frame_borrow_cannot_escape(byte: u8) {
    let local = Snapshot { byte, words: (3, true), bytes: [1; 4] };
    let reference: &'static Snapshot = cast(&local);
    store(SHARED.get(), Some(reference));
}

pub fn mutable_snapshot_is_unknown(value: &'static Snapshot) {
    let mutable: &'static mut Snapshot = cast(value);
    store(MUTABLE.get(), Some(mutable));
}

pub fn mismatched_snapshot_is_unknown(value: &'static u16) {
    let mismatched: &'static Snapshot = cast(value);
    store(SHARED.get(), Some(mismatched));
}

static BYTE_REFERENCE: SyncUnsafeCell<Option<&'static u8>> = SyncUnsafeCell::new(None);
static CELL_REFERENCE: SyncUnsafeCell<Option<&'static SyncUnsafeCell<u8>>> =
    SyncUnsafeCell::new(None);

pub fn stores_nonfreeze_root_reference(value: &'static SyncUnsafeCell<u8>) {
    store(CELL_REFERENCE.get(), Some(value));
}

pub fn mismatched_retained_reference_is_unknown(byte: u8) {
    let local = byte;
    let mismatched: &'static Snapshot = cast(&local);
    store(SHARED.get(), Some(mismatched));
}

pub fn shared_interior_write_is_unknown(value: &'static SyncUnsafeCell<u8>) {
    store(value.get(), 7);
}

pub fn two_interior_roots_are_unknown(
    first: &'static SyncUnsafeCell<u8>, second: &'static SyncUnsafeCell<u8>,
) {
    store(CELL_REFERENCE.get(), Some(first));
    store(CELL_REFERENCE.get(), Some(second));
}

pub fn nonfreeze_frame_borrow_cannot_escape(byte: u8) {
    let local = SyncUnsafeCell::new(byte);
    let reference: &'static SyncUnsafeCell<u8> = cast(&local);
    store(CELL_REFERENCE.get(), Some(reference));
}

pub struct SpawnerLike {
    executor: &'static SyncUnsafeCell<u8>,
}

pub fn stores_nested_shared_root(value: SpawnerLike) {
    store(CELL_REFERENCE.get(), Some(value.executor));
}

pub fn nested_shared_root_does_not_hide_panics(value: SpawnerLike, byte: u8) {
    stores_nested_shared_root(value);
    assert!(byte < 8);
}

pub fn nested_and_direct_roots_are_unknown(
    value: SpawnerLike, other: &'static SyncUnsafeCell<u8>,
) {
    store(CELL_REFERENCE.get(), Some(value.executor));
    store(CELL_REFERENCE.get(), Some(other));
}

fn boundary() {}

pub fn unknown_effects_keep_incoming_reference_evidence(value: SpawnerLike) {
    stores_nested_shared_root(value);
    boundary();
}

fn byte_destination() -> *mut Option<&'static u8> {
    BYTE_REFERENCE.get()
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_reference_is_unknown(byte: u8) {
    mir! {
        let local: u8;
        let reference: &'static u8;
        let payload: Option<&'static u8>;
        let destination: *mut Option<&'static u8>;
        {
            StorageLive(local);
            local = byte;
            reference = &local;
            StorageDead(local);
            payload = Option::Some(reference);
            Call(destination = byte_destination(), ReturnTo(write), UnwindUnreachable())
        }
        write = {
            Call(RET = store(destination, payload), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn guards_remain_real_code() {
        static VALUE: super::Snapshot = super::Snapshot {
            byte: 8, words: (3, true), bytes: [1; 4],
        };
        super::stores_shared_snapshot(&VALUE);
    }
}
