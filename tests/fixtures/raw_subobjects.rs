#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub fn array_mutations(mut values: [u16; 3]) {
    let [first, second, third] = values.each_mut();
    *first = 7;
    *second = 11;
    *third = 19;
    assert!(values == [7, 11, 19]);
}

pub fn guarded_element_address(values: &mut [u32; 3], index: usize) {
    if index < 3 {
        let parent = values as *mut [u32; 3] as usize;
        let child = &raw mut values[index] as usize;
        assert!(child == parent + index * core::mem::size_of::<u32>());
    }
}

pub fn unguarded_element_address(values: &mut [u32; 3], index: usize) -> *mut u32 {
    &raw mut values[index]
}

pub fn field_address(mut value: (u8, u32)) {
    let parent = &raw const value as usize;
    let field = &raw const value.1 as usize;
    assert!(field == parent + core::mem::offset_of!((u8, u32), 1));
    let mutable = &raw mut value.1;
    assert!(mutable as usize == field);
}

pub fn frame_element_escape() -> *const u32 {
    let values = [3, 5];
    &raw const values[1]
}

pub fn snapshots_have_no_raw_subobject_provenance(values: &[u32; 2]) -> *const u32 {
    &raw const values[0]
}

pub fn symbolic_mutation(mut values: [u32; 3], index: usize) {
    if index < 3 {
        let refs = values.each_mut();
        *refs[index] = 23;
        assert!(values[index] == 23);
    }
}

pub fn nested_array_mutations(mut values: [[u16; 2]; 2]) {
    let [first, second] = values[1].each_mut();
    *first = 17;
    *second = 29;
    assert!(values[1] == [17, 29]);
}

pub fn zero_sized_subobjects() {
    let mut values = [(); 3];
    let [first, second, third] = values.each_mut();
    *first = ();
    *second = ();
    *third = ();
}

pub fn subobject_one_past(mut values: [u32; 2]) {
    let start = &raw mut values[0];
    let end = synthetic::offset(start, 1);
    assert!(end as usize == start as usize + 4);
}

pub fn subobject_extent_is_not_the_parent(mut values: [u32; 2]) -> *mut u32 {
    synthetic::offset(&raw mut values[0], 2)
}

pub fn raw_subobject_reads_remain_unknown(values: [u32; 2]) -> u32 {
    synthetic::read(&raw const values[1])
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_subobject_origin() -> *mut u32 {
    mir! {
        let storage: [u32; 2];
        let pointer: *mut u32;
        let index: usize;
        {
            index = 1_usize;
            storage = [3_u32, 5_u32];
            pointer = &raw mut storage[index];
            StorageDead(storage);
            RET = Offset(pointer, 0_isize);
            Return()
        }
    }
}

pub fn duplicate_mutable_subobjects(mut value: u32) {
    let pointer = &raw mut value;
    let _ = synthetic::references([pointer, pointer]);
}

pub fn numeric_addresses_cannot_become_references() {
    let _ = synthetic::references([0x58024400usize as *mut u32; 2]);
}

pub fn shared_subobjects_cannot_gain_write_permission(value: u32) {
    let pointer = (&raw const value).cast_mut();
    let _ = synthetic::references([pointer, pointer]);
}

pub mod synthetic {
    use super::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn offset(pointer: *mut u32, count: isize) -> *mut u32 {
        mir! { { RET = Offset(pointer, count); Return() } }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn read(pointer: *const u32) -> u32 {
        mir! { { RET = *pointer; Return() } }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn references(pointers: [*mut u32; 2]) -> [&'static mut u32; 2] {
        mir! { { RET = CastTransmute(Move(pointers)); Return() } }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_subobject_storage_and_addresses() {
        array_mutations([1, 2, 3]);
        field_address((1, 7));
        nested_array_mutations([[1, 2], [3, 4]]);
        zero_sized_subobjects();
        subobject_one_past([3, 5]);
        for index in 0..3 {
            guarded_element_address(&mut [3, 5, 7], index);
            symbolic_mutation([3, 5, 7], index);
        }
    }
}
