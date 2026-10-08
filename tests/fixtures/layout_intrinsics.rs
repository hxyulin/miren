#![no_std]
#![forbid(unsafe_code)]
#![feature(core_intrinsics, custom_mir, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

pub fn slice_size(bytes: &[u8]) {
    assert_eq!(core::mem::size_of_val(bytes), bytes.len());
}

pub fn array_size(bytes: &[u16; 3]) {
    assert_eq!(core::mem::size_of_val(bytes), 6);
}

pub fn bad_array_size(bytes: &[u16; 3]) {
    assert!(core::mem::size_of_val(bytes) == 3);
}

pub fn zero_guard() {
    core::intrinsics::assert_zero_valid::<(u32, bool)>();
}

pub fn bad_zero_guard() {
    core::intrinsics::assert_zero_valid::<core::num::NonZeroU16>();
}

pub fn byte_float(bytes: [u8; 4]) {
    let sample = f32::from_ne_bytes(bytes);
    assert!(sample.to_bits() == u32::from_ne_bytes(bytes));
}

pub fn byte_wide_float(bytes: [u8; 8]) {
    let sample = f64::from_ne_bytes(bytes);
    assert!(sample.to_bits() == u64::from_ne_bytes(bytes));
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_byte_bool(byte: [u8; 1]) -> bool {
    mir! { { RET = CastTransmute(Move(byte)); Return() } }
}

pub fn same_name_guard() {
    fn assert_zero_valid<T>() { let _ = core::mem::size_of::<T>(); panic!(); }
    assert_zero_valid::<u32>();
}

pub fn special_byte_floats() {
    assert!(f32::from_le_bytes([0, 0, 0, 128]).to_bits() == 0x8000_0000);
    assert!(f32::from_be_bytes([127, 128, 0, 1]).to_bits() == 0x7f80_0001);
    assert!(f64::from_be_bytes([127, 240, 0, 0, 0, 0, 0, 1]).to_bits()
        == 0x7ff0_0000_0000_0001);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_byte_reference(bytes: [u8; core::mem::size_of::<usize>()]) -> &'static u8 {
    mir! { { RET = CastTransmute(Move(bytes)); Return() } }
}

#[cfg(test)]
#[test]
fn native_layout_and_encoding_cases() {
    slice_size(&[1, 2, 3]);
    array_size(&[10, 20, 30]);
    zero_guard();
    special_byte_floats();
    for bits in [0_u32, 0x8000_0000, 0x7f80_0001, 0x7fc0_1234, u32::MAX] {
        byte_float(bits.to_ne_bytes());
    }
    for bits in [0_u64, 0x8000_0000_0000_0000, 0x7ff0_0000_0000_0001, u64::MAX] {
        byte_wide_float(bits.to_ne_bytes());
    }
}

pub fn wide_slice_size(bytes: &[u16; 3]) {
    let slice: &[u16] = bytes;
    assert!(core::mem::size_of_val(slice) == 6);
}

pub fn valid_zero_guard_then_panic() {
    core::intrinsics::assert_zero_valid::<u16>();
    panic!();
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_byte_char(bytes: [u8; 4]) -> char {
    mir! { { RET = CastTransmute(Move(bytes)); Return() } }
}

type Positive = core::pattern_type!(u32 is 1..);

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_byte_range(bytes: [u8; 4]) -> Positive {
    mir! { { RET = CastTransmute(Move(bytes)); Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn byte_word(bytes: [u8; 4]) -> u32 {
    mir! { { RET = CastTransmute(Move(bytes)); Return() } }
}
