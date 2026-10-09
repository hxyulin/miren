#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;

use core::task::{RawWaker, Waker};

pub struct Callbacks {
    pub callback: fn(u8) -> u8,
    pub flag: bool,
    pub byte: u8,
}

pub struct UnsafeCallbacks {
    pub callback: unsafe extern "C" fn(*const ()) -> *const (),
    pub clone: unsafe fn(*const ()) -> RawWaker,
    pub flag: bool,
}

pub fn ignore_callback(callback: fn(u8) -> u8, value: u8) {
    let _ = callback;
    if value < 16 {
        assert!(value <= 15);
    }
}

pub fn unused_fields(callbacks: Callbacks) {
    if callbacks.flag {
        assert!(callbacks.byte <= 255);
    }
}

pub fn unsafe_signature_unused(callbacks: UnsafeCallbacks) {
    let _ = callbacks.callback;
    let _ = callbacks.clone;
    assert!(callbacks.flag || !callbacks.flag);
}

pub fn raw_waker_unused(waker: RawWaker) {
    let _ = waker;
}

pub fn shared_waker_unused(waker: &Waker) {
    let _ = waker;
}

pub fn unused_callback_does_not_hide_panic(callbacks: Callbacks) {
    let _ = callbacks.callback;
    assert!(callbacks.byte < 16);
}

pub fn waker_does_not_hide_panic(waker: &Waker, byte: u8) {
    let _ = waker;
    assert!(byte < 16);
}

pub fn invoked_callback_unknown(callback: fn(u8) -> u8, value: u8) {
    assert!(callback(value) < 16);
}

pub fn field_invocation_unknown(callbacks: Callbacks) {
    assert!((callbacks.callback)(callbacks.byte) < 16);
}

pub fn waker_effects_unknown(waker: &Waker) {
    waker.wake_by_ref();
}

pub fn waker_drop_unknown(waker: Waker) {
    core::mem::drop(waker);
}

pub fn contract_identity(first: fn(u8) -> u8, second: fn(u8) -> u8) {
    let _ = (first, second);
}

pub fn equality_unknown(first: fn(u8) -> u8, second: fn(u8) -> u8) {
    assert!(core::ptr::fn_addr_eq(first, second));
}

pub fn address_unknown(callback: fn(u8) -> u8) {
    assert!((callback as usize) != 0);
}

#[derive(Clone, Copy)]
pub struct Record {
    pub callback: fn(u8) -> u8,
    pub byte: u8,
}

pub fn large_lazy_unused(records: [Record; 256], value: u8) {
    let _ = records;
    if value < 16 {
        assert!(value <= 15);
    }
}

pub fn large_lazy_panic(records: [Record; 256]) {
    assert!(records[255].byte < 16);
}

pub fn large_lazy_invocation_unknown(records: [Record; 256]) {
    assert!((records[255].callback)(records[255].byte) < 16);
}

pub fn replaced_with_known_target(callback: fn(u8) -> u8, value: u8) {
    let _ = callback;
    let callback: fn(u8) -> u8 = low_bits;
    assert!(callback(value) < 16);
}

fn low_bits(value: u8) -> u8 {
    value & 15
}

static STORED: SyncUnsafeCell<Option<fn(u8) -> u8>> = SyncUnsafeCell::new(None);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn store<T>(pointer: *mut T, value: T) {
    mir! {
        {
            *pointer = Move(value);
            Return()
        }
    }
}

pub fn store_opaque_callback(callback: fn(u8) -> u8) {
    store(STORED.get(), Some(callback));
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsafe_invocation_unknown(
    callback: unsafe extern "C" fn(*const ()) -> *const (),
    data: *const (),
) -> *const () {
    mir! {
        {
            Call(RET = callback(data), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(source: S) -> T {
    mir! {
        {
            RET = CastTransmute(source);
            Return()
        }
    }
}

pub fn wrong_stored_signature_unknown(callback: fn(u16) -> u16) {
    let changed: fn(u8) -> u8 = cast(callback);
    store(STORED.get(), Some(changed));
}

pub fn unsafe_signature_change_unknown(callback: unsafe fn(u8) -> u8) {
    let changed: fn(u8) -> u8 = cast(callback);
    store(STORED.get(), Some(changed));
}

pub fn abi_signature_change_unknown(callback: extern "C" fn(u8) -> u8) {
    let changed: fn(u8) -> u8 = cast(callback);
    store(STORED.get(), Some(changed));
}

pub fn binders_unused(callback: for<'a> fn(&'a u8) -> &'a u8) {
    let _ = callback;
}

pub fn binders_invocation_unknown(callback: for<'a> fn(&'a u8) -> &'a u8, value: &u8) {
    let _ = callback(value);
}

#[cfg(test)]
mod tests {
    #[test]
    fn unused_inputs_replay_without_callback_execution() {
        super::ignore_callback(super::low_bits, 15);
        super::unused_fields(super::Callbacks {
            callback: super::low_bits,
            flag: true,
            byte: 255,
        });
        super::shared_waker_unused(core::task::Waker::noop());
        super::replaced_with_known_target(super::low_bits, 255);
        let records = [super::Record { callback: super::low_bits, byte: 15 }; 256];
        super::large_lazy_unused(records, 15);
    }
}
