#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

#[repr(C)]
pub struct Wire {
    first: [u8; 2],
    second: [u8; 2],
}

#[repr(C)]
pub struct Padded {
    first: u8,
    second: u32,
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn shared(pointer: *const [u8]) -> &'static [u8] {
    mir! { { RET = &*pointer; Return() } }
}

pub fn wire_bytes(first: u8, second: u8) {
    let wire = Wire {
        first: [first, 7],
        second: [second, 9],
    };
    let pointer = (&raw const wire).cast::<u8>();
    let bytes = shared(core::ptr::slice_from_raw_parts(pointer, 4));
    let mut copied = [0u8; 4];
    copied.copy_from_slice(bytes);
    assert!(copied == [first, 7, second, 9]);
}

pub fn wrong_wire_byte(first: u8) {
    let wire = Wire {
        first: [first, 7],
        second: [8, 9],
    };
    let bytes = shared(core::ptr::slice_from_raw_parts(
        (&raw const wire).cast::<u8>(),
        4,
    ));
    assert!(bytes[3] == 8);
}

pub fn integer_bytes(value: u32) {
    let bytes = shared(core::ptr::slice_from_raw_parts(
        (&raw const value).cast::<u8>(),
        4,
    ));
    assert!(bytes == value.to_ne_bytes());
}

pub fn wrong_integer_endian(value: u32) {
    let bytes = shared(core::ptr::slice_from_raw_parts(
        (&raw const value).cast::<u8>(),
        4,
    ));
    assert!(bytes == value.to_be_bytes());
}

pub fn updates_are_visible() {
    let mut storage = [1u8; 4];
    let pointer = core::ptr::slice_from_raw_parts((&raw const storage).cast::<u8>(), 4);
    storage[2] = 7;
    let bytes = shared(pointer);
    assert!(bytes[2] == 7);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn offset(pointer: *const u8, count: isize) -> *const u8 {
    mir! { { RET = Offset(pointer, count); Return() } }
}

pub fn partial_slice() {
    let storage = [3u8, 5, 7, 9];
    let pointer = offset((&raw const storage).cast::<u8>(), 1);
    let bytes = shared(core::ptr::slice_from_raw_parts(pointer, 2));
    assert!(bytes == [5, 7]);
}

pub fn wrong_partial_slice() {
    let storage = [3u8, 5, 7, 9];
    let pointer = offset((&raw const storage).cast::<u8>(), 1);
    let bytes = shared(core::ptr::slice_from_raw_parts(pointer, 2));
    assert!(bytes == [3, 5]);
}

pub fn mutable_slice() {
    let mut storage = [0u8; 4];
    let pointer = core::ptr::slice_from_raw_parts_mut((&raw mut storage).cast::<u8>(), 4);
    assert!(pointer.len() == 4);
}

pub fn raw_subobject_slice() {
    let wire = Wire {
        first: [1, 2],
        second: [3, 4],
    };
    let pointer = (&raw const wire.second).cast::<u8>();
    let bytes = shared(core::ptr::slice_from_raw_parts(pointer, 2));
    assert!(bytes == [3, 4]);
}

pub fn numeric_slice(address: usize) {
    let bytes = shared(core::ptr::slice_from_raw_parts(address as *const u8, 4));
    assert!(bytes.len() == 4);
}

pub fn padded_storage() {
    let storage = Padded {
        first: 1,
        second: 2,
    };
    let bytes = shared(core::ptr::slice_from_raw_parts(
        (&raw const storage).cast::<u8>(),
        core::mem::size_of::<Padded>(),
    ));
    assert!(bytes[0] == 1);
}

pub fn outside_storage() {
    let storage = [1u8; 4];
    let bytes = shared(core::ptr::slice_from_raw_parts(
        (&raw const storage).cast::<u8>(),
        5,
    ));
    assert!(bytes.len() == 5);
}

pub fn escaping_slice() -> &'static [u8] {
    let storage = [1u8; 4];
    shared(core::ptr::slice_from_raw_parts(
        (&raw const storage).cast::<u8>(),
        4,
    ))
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_slice() {
    mir! {
        let storage: [u8; 4];
        let pointer: *const [u8; 4];
        let thin: *const u8;
        let fat: *const [u8];
        {
            storage = [1_u8; 4];
            pointer = &raw const storage;
            thin = CastPtrToPtr(pointer);
            Call(
                fat = core::ptr::slice_from_raw_parts(thin, 4_usize),
                ReturnTo(next),
                UnwindUnreachable()
            )
        }
        next = {
            StorageDead(storage);
            RET = ();
            Call(RET = inspect(fat), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

pub fn inspect(pointer: *const [u8]) {
    assert!(shared(pointer).len() == 4);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_bytes_match_native_layout() {
        for first in [0, 17, 255] {
            for second in [0, 73, 255] {
                wire_bytes(first, second);
            }
        }
        for value in [0, 0x12345678, u32::MAX] {
            integer_bytes(value);
        }
        partial_slice();
        updates_are_visible();
    }
}
