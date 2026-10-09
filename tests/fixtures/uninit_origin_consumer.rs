#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::intrinsics::mir::*;
use core::mem::MaybeUninit;

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn share<T: 'static>(pointer: *mut T) -> &'static T {
    mir! { { RET = &*pointer; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn store<T>(pointer: *mut T, value: T) {
    mir! { { *pointer = Move(value); Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn load(pointer: *const [u8; 256]) -> [u8; 256] {
    mir! { { RET = *pointer; Return() } }
}

fn address() -> *mut [u8; 256] {
    // Keep the original UnsafeCell raw capability; a shared Freeze reborrow would forbid writes.
    dependency_uninit::BUFFER.get().cast::<[u8; 256]>()
}

fn readonly_address() -> *mut [u8; 256] {
    let container: &MaybeUninit<[u8; 256]> = share(dependency_uninit::BUFFER.get());
    container.as_ptr().cast_mut()
}

pub fn shared_uninit_pointer_cannot_write() {
    store(readonly_address(), [7; 256]);
}

static mut INTERIOR: MaybeUninit<core::cell::UnsafeCell<[u8; 256]>> = MaybeUninit::uninit();

pub fn shared_uninit_interior_cell_can_write() {
    let container: &MaybeUninit<core::cell::UnsafeCell<[u8; 256]>> = share(&raw mut INTERIOR);
    store(core::cell::UnsafeCell::raw_get(container.as_ptr()), [7; 256]);
}

pub fn dependency_uninit_store() {
    store(address(), [7; 256]);
}

pub fn dependency_uninit_read() {
    let bytes = load(address());
    assert!(bytes[0] == 7);
}

pub fn dependency_initialized_union() {
    let container: &MaybeUninit<[u8; 256]> = share(dependency_uninit::INITIALIZED.get());
    store(container.as_ptr().cast_mut(), [7; 256]);
}

pub fn dependency_spoof_union() {
    store(dependency_uninit::SPOOF.get().cast::<[u8; 256]>(), [7; 256]);
}

pub fn dependency_wrong_payload_type() {
    let container = share(dependency_uninit::SHORT.get());
    store(container.as_ptr().cast_mut().cast::<[u8; 256]>(), [7; 256]);
}

pub fn dependency_uninit_store_real_guard(byte: u8) {
    store(address(), [byte; 256]);
    if byte < 8 {
        assert!(byte < 8);
    }
}

pub fn dependency_uninit_store_wrong_guard(byte: u8) {
    store(address(), [byte; 256]);
    assert!(byte < 8);
}

pub fn dependency_uninit_read_after_store() {
    store(address(), [7; 256]);
    assert!(load(address())[0] == 7);
}

#[cfg(test)]
mod tests {
    #[test]
    fn stores_keep_runtime_guards() {
        for byte in 0..=u8::MAX {
            super::dependency_uninit_store_real_guard(byte);
        }
    }
}

pub fn dependency_boolean_storage() {
    store(dependency_uninit::BOOL_BYTE.get(), 7);
}

pub fn shared_uninit_payload_reference_is_unknown() {
    let container: &MaybeUninit<core::cell::UnsafeCell<[u8; 256]>> = share(&raw mut INTERIOR);
    let cell: &core::cell::UnsafeCell<[u8; 256]> = share(container.as_ptr().cast_mut());
    store(cell.get(), [7; 256]);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn direct_shared_as_ptr_store(container: &MaybeUninit<[u8; 256]>) {
    mir! {
        let pointer: *const [u8; 256]; let mutable: *mut [u8; 256];
        let value: [u8; 256]; let ignored: ();
        { Call(pointer = MaybeUninit::<[u8; 256]>::as_ptr(container),
            ReturnTo(convert), UnwindUnreachable()) }
        convert = { mutable = CastPtrToPtr(pointer); value = [7; 256];
            Call(ignored = store(mutable, Move(value)), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
pub fn directly_forwarded_shared_uninit_pointer_cannot_write() {
    let container = share(dependency_uninit::BUFFER.get());
    direct_shared_as_ptr_store(container);
}
