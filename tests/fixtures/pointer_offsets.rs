#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub fn array_cursor(index: u8) {
    if index <= 4 {
        let array = [0u32; 4];
        let start = (&raw const array).cast::<u32>();
        let cursor = synthetic::offset(start, isize::from(index));
        assert!(cursor as usize == start as usize + usize::from(index) * 4);
        let back = synthetic::offset(cursor, -isize::from(index));
        assert!(back == start);
    }
}

pub fn stride_relationship() {
    let array = [0u32; 4];
    let start = (&raw const array).cast::<u32>();
    let next = synthetic::offset(start, 1);
    assert!(next as usize == start as usize + 4);
}

pub fn scalar_one_past(value: u32) {
    let start = &raw const value;
    let end = synthetic::offset(start, 1);
    assert!(end as usize == start as usize + 4);
    assert!(synthetic::offset(end, -1) == start);
}

pub fn offset_keeps_later_panic(index: u8) -> u8 {
    stride_relationship();
    [0u8; 2][usize::from(index)]
}

pub fn negative_out_of_bounds(value: u32) -> usize {
    synthetic::offset(&raw const value, -1) as usize
}

pub fn scaled_offset_overflow(value: u32) -> usize {
    synthetic::offset(&raw const value, isize::MAX) as usize
}

pub fn numeric_origin(pointer: usize) -> usize {
    synthetic::offset(pointer as *const u32, 0) as usize
}

pub fn unknown_reference(value: &u32) -> usize {
    synthetic::offset(&raw const *value, 0) as usize
}

pub fn zero_sized_stride() -> usize {
    let value = ();
    synthetic::offset_unit(&raw const value, 1) as usize
}

pub fn one_past_read(value: u32) -> u32 {
    synthetic::read(synthetic::offset(&raw const value, 1))
}

pub fn offset_frame_escape() -> *const u32 {
    let value = 0u32;
    synthetic::offset(&raw const value, 1)
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_origin() -> *const u32 {
    mir! {
        let storage: u32;
        let pointer: *const u32;
        {
            storage = 4;
            pointer = &raw const storage;
            StorageDead(storage);
            RET = Offset(pointer, 0_isize);
            Return()
        }
    }
}

pub mod synthetic {
    use super::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn offset(pointer: *const u32, count: isize) -> *const u32 {
        mir! { { RET = Offset(pointer, count); Return() } }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn offset_unit(pointer: *const (), count: isize) -> *const () {
        mir! { { RET = Offset(pointer, count); Return() } }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn read(pointer: *const u32) -> u32 {
        mir! { { RET = *pointer; Return() } }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_offsets_match_native_address_relationships() {
        for index in 0..=4 {
            array_cursor(index);
        }
        stride_relationship();
        for value in [0, 1, u32::MAX] {
            scalar_one_past(value);
        }
    }
}
