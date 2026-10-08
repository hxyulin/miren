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
    let container: &MaybeUninit<[u8; 256]> = share(dependency_uninit::BUFFER.get());
    container.as_ptr().cast_mut()
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
