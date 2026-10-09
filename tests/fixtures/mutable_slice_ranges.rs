#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub fn guarded_region(start: usize, end: usize) {
    let mut bytes = [1_u8, 2, 3, 4];
    if start <= end && end <= bytes.len() {
        let region = &mut bytes[start..end];
        assert!(region.len() == end - start);
        if start < end {
            region[0] = 9;
            assert!(bytes[start] == 9);
        }
    }
}

pub fn nested_ranges_keep_storage() {
    let mut bytes = [0_u8; 8];
    let region = &mut bytes[2..7];
    let nested = &mut region[1..3];
    nested[1] = 17;
    assert!(bytes[4] == 17);
    assert!(bytes[3] == 0);
}

pub fn empty_range_at_end() {
    let mut bytes = [1_u8; 4];
    let region = &mut bytes[4..4];
    assert!(region.is_empty());
}

pub fn out_of_bounds() {
    let mut bytes = [1_u8; 4];
    let _ = &mut bytes[0..5];
}

pub fn reversed_bounds(start: usize, end: usize) {
    if end < start {
        let mut bytes = [1_u8; 4];
        let _ = &mut bytes[start..end];
    }
}

pub fn wrong_write_claim() {
    let mut bytes = [0_u8; 4];
    bytes[1..3][0] = 7;
    assert!(bytes[1] == 8);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(value: S) -> T {
    mir! {{ RET = CastTransmute(value); Return() }}
}

pub fn readonly_storage_is_unknown() {
    let bytes = [0_u8; 4];
    let source: &[u8] = &bytes;
    let mutable: &mut [u8] = cast(source);
    let _ = &mut mutable[1..3];
}

pub fn arbitrary_raw_slice_is_unknown(pointer: *mut [u8]) {
    let mutable: &mut [u8] = cast(pointer);
    let _ = &mut mutable[1..3];
}

pub fn nonbyte_region_is_unknown() {
    let mut values = [1.0_f32; 4];
    let _ = &mut values[1..3];
}

pub struct FakeRange { start: usize, end: usize }
pub struct Wrapper { bytes: [u8; 4] }

impl core::ops::Index<FakeRange> for Wrapper {
    type Output = [u8];
    fn index(&self, range: FakeRange) -> &[u8] {
        let _ = (range.start, range.end);
        &self.bytes
    }
}

impl core::ops::IndexMut<FakeRange> for Wrapper {
    fn index_mut(&mut self, range: FakeRange) -> &mut [u8] {
        let _ = (range.start, range.end);
        &mut self.bytes
    }
}

pub fn lookalike_index_uses_its_actual_body() {
    let mut wrapper = Wrapper { bytes: [0; 4] };
    wrapper[FakeRange { start: 5, end: 4 }][0] = 7;
    assert!(wrapper.bytes[0] == 7);
}

#[cfg(test)]
mod native {
    #[test]
    fn positive() {
        for start in 0..=4 {
            for end in start..=4 { super::guarded_region(start, end); }
        }
        super::nested_ranges_keep_storage();
        super::empty_range_at_end();
        super::lookalike_index_uses_its_actual_body();
    }

    #[test]
    fn bounds_panic() { super::out_of_bounds(); }

    #[test]
    fn reversed_panic() { super::reversed_bounds(3, 1); }

    #[test]
    fn wrong_claim_panic() { super::wrong_write_claim(); }
}

fn takes_range(bytes: &mut [u8; 4]) {
    let _ = &mut bytes[1..3];
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_range_backing_is_unknown() {
    mir! {
        let bytes: [u8; 4];
        let reference: &mut [u8; 4];
        {
            StorageLive(bytes);
            bytes = [0_u8; 4];
            reference = &mut bytes;
            StorageDead(bytes);
            Call(RET = takes_range(reference), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

mod foreign_lookalike {
    pub extern "C" fn index_mut(start: usize, end: usize) -> u8 {
        if end < start { 7 } else { 0 }
    }
}

pub fn different_abi_uses_its_actual_body() {
    assert!(foreign_lookalike::index_mut(5, 4) == 7);
}

pub fn guarded_borrowed_region(bytes: &mut [u8], start: usize, end: usize) {
    if start <= end && end <= bytes.len() {
        let region = &mut bytes[start..end];
        assert!(region.len() == end - start);
        if start < end {
            region[0] = 19;
            assert!(bytes[start] == 19);
        }
    }
}
