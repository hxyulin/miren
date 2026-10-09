#![no_std]

#[inline(never)]
fn touch(value: &mut u32) {
    *value = 2;
}

pub fn shared_pointer_after_store() {
    let mut value = 1_u32;
    let pointer = &value as *const u32;
    value = 2;
    let read = unsafe { pointer.read_volatile() };
    assert!(read == 2);
}

pub fn mutable_pointer_after_reborrow() {
    let mut value = 1_u32;
    let pointer = &mut value as *mut u32;
    touch(&mut value);
    let read = unsafe { pointer.read_volatile() };
    assert!(read == 2);
}

pub fn raw_slice_after_original_store() {
    let mut value = 1_u32;
    let pointer = &value as *const u32 as *const u8;
    let bytes = unsafe { core::slice::from_raw_parts(pointer, 4) };
    value = 2;
    assert!(bytes[0] == 2);
}

pub fn raw_slice_after_reborrow_before_construction() {
    let mut value = 1_u32;
    let pointer = &mut value as *mut u32 as *const u8;
    touch(&mut value);
    let bytes = unsafe { core::slice::from_raw_parts(pointer, 4) };
    assert!(bytes[0] == 2);
}

pub fn nonempty_raw_reference_array() {
    let mut value = 1_u32;
    let pointer = &mut value as *mut u32;
    touch(&mut value);
    let references: [&mut u32; 1] = unsafe { core::mem::transmute([pointer]) };
    assert!(*references[0] == 2);
}

pub fn empty_raw_reference_array() {
    let pointers: [*mut u32; 0] = [];
    let references: [&mut u32; 0] = unsafe { core::mem::transmute(pointers) };
    assert!(references.len() == 0);
}

pub fn raw_pointer_metadata(length: usize) {
    let pointer = core::ptr::slice_from_raw_parts(core::ptr::null::<u8>(), length);
    assert!(pointer.len() == length);
}

pub fn excessive_raw_pointer_metadata() {
    let value = 1_u8;
    let pointer = core::ptr::slice_from_raw_parts(&raw const value, usize::MAX);
    assert!(pointer.len() == usize::MAX);
}

pub fn wrong_raw_pointer_metadata(length: usize) {
    let pointer = core::ptr::slice_from_raw_parts(core::ptr::null::<u8>(), length);
    assert!(pointer.len() != length);
}

pub fn ordinary_reference_access() {
    let mut value = 1_u32;
    touch(&mut value);
    assert!(value == 2);
}

pub fn wrong_ordinary_reference_claim() {
    let mut value = 1_u32;
    touch(&mut value);
    assert!(value == 3);
}

pub fn address_only() {
    let mut value = 1_u32;
    let pointer = &raw const value;
    let address = pointer as usize;
    touch(&mut value);
    assert!(pointer as usize == address);
}

#[cfg(test)]
#[test]
fn native_defined_controls() {
    // Do not execute the old-pointer access or nonempty transmute probes.
    empty_raw_reference_array();
    excessive_raw_pointer_metadata();
    ordinary_reference_access();
    address_only();
    for length in [0, 1, 128, usize::MAX] {
        raw_pointer_metadata(length);
    }
}
