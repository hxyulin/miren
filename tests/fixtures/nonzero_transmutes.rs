#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;
use core::num::NonZero;

macro_rules! exact_primitive {
    ($cast:ident, $check:ident, $integer:ty) => {
        #[custom_mir(dialect = "runtime", phase = "optimized")]
        pub fn $cast(value: NonZero<$integer>) -> $integer {
            mir! { { RET = CastTransmute(value); Return() } }
        }
        pub fn $check(value: NonZero<$integer>) {
            assert!($cast(value) == value.get());
            assert!($cast(value) != 0);
        }
    };
}
exact_primitive!(cast_u8, exact_u8, u8);
exact_primitive!(cast_u16, exact_u16, u16);
exact_primitive!(cast_u32, exact_u32, u32);
exact_primitive!(cast_u64, exact_u64, u64);
exact_primitive!(cast_u128, exact_u128, u128);
exact_primitive!(cast_usize, exact_usize, usize);
exact_primitive!(cast_i8, exact_i8, i8);
exact_primitive!(cast_i16, exact_i16, i16);
exact_primitive!(cast_i32, exact_i32, i32);
exact_primitive!(cast_i64, exact_i64, i64);
exact_primitive!(cast_i128, exact_i128, i128);
exact_primitive!(cast_isize, exact_isize, isize);

pub fn guarded_power(value: u8) {
    if value <= 15 { assert!(value.pow(2) >= value); }
}
pub fn unchecked_power(value: u8) { let _ = value.pow(2); }
pub fn negative_value() { assert!(cast_i16(NonZero::new(-1).unwrap()) == -1); }
pub fn zero_unwrap() { let _ = cast_u8(NonZero::new(0).unwrap()); }
pub fn mutation_claim(value: NonZero<u32>) { assert!(cast_u32(value) == value.get()); }
pub fn wrong_value(value: NonZero<u32>) { assert!(cast_u32(value) == 0); }

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn signedness_mismatch(value: NonZero<i16>) -> u16 {
    mir! { { RET = CastTransmute(value); Return() } }
}
#[repr(transparent)]
pub struct Wrapper(NonZero<u32>);
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn noncore_wrapper(value: Wrapper) -> u32 {
    mir! { { RET = CastTransmute(value); Return() } }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn wrong_primitive(value: NonZero<u32>) -> f32 {
    mir! { { RET = CastTransmute(value); Return() } }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn raw_integer_is_not_nonzero(value: u32) -> NonZero<u32> {
    mir! { { RET = CastTransmute(value); Return() } }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unchecked_payload(value: u32) -> u32 {
    mir! {
        let option: Option<NonZero<u32>>;
        let payload: NonZero<u32>;
        { Call(option = NonZero::<u32>::new(value), ReturnTo(read), UnwindUnreachable()) }
        read = { payload = Field::<NonZero<u32>>(Variant(option, 1), 0);
                 RET = CastTransmute(payload); Return() }
    }
}

#[cfg(test)]
extern crate std;
#[cfg(test)]
#[test]
fn native_exact_values_and_powers() {
    for value in 0..=15 { guarded_power(value); }
    for value in [1, 17, u32::MAX] { exact_u32(NonZero::new(value).unwrap()); }
    for value in [i16::MIN, -1, 1, i16::MAX] { exact_i16(NonZero::new(value).unwrap()); }
    for value in [i128::MIN, -1, 1, i128::MAX] { exact_i128(NonZero::new(value).unwrap()); }
    for value in [1, usize::MAX] { exact_usize(NonZero::new(value).unwrap()); }
    mutation_claim(NonZero::new(17).unwrap());
    negative_value();
    assert!(std::panic::catch_unwind(zero_unwrap).is_err());
    assert!(std::panic::catch_unwind(|| unchecked_power(16)).is_err());
}

macro_rules! nonzero_scan {
    ($scan:ident, $check:ident, $integer:ty) => {
        #[custom_mir(dialect = "runtime", phase = "optimized")]
        pub fn $scan(value: $integer) -> u32 {
            mir! { { Call(RET = core::intrinsics::ctlz_nonzero(value),
                           ReturnTo(done), UnwindUnreachable()) }
                   done = { Return() } }
        }
        pub fn $check(value: $integer) {
            if value != 0 {
                assert!($scan(value) == value.leading_zeros());
                assert!($scan(value) < <$integer>::BITS);
            }
        }
    };
}
nonzero_scan!(scan_u8, check_u8_scan, u8);
nonzero_scan!(scan_u16, check_u16_scan, u16);
nonzero_scan!(scan_u32, check_u32_scan, u32);
nonzero_scan!(scan_u64, check_u64_scan, u64);
nonzero_scan!(scan_u128, check_u128_scan, u128);
nonzero_scan!(scan_usize, check_usize_scan, usize);
nonzero_scan!(scan_i8, check_i8_scan, i8);
nonzero_scan!(scan_i16, check_i16_scan, i16);
nonzero_scan!(scan_i32, check_i32_scan, i32);
nonzero_scan!(scan_i64, check_i64_scan, i64);
nonzero_scan!(scan_i128, check_i128_scan, i128);
nonzero_scan!(scan_isize, check_isize_scan, isize);

pub fn zero_scan() -> u32 { scan_u8(0) }
pub fn wrong_count(value: u8) { if value != 0 { assert!(scan_u8(value) == 8); } }

mod lookalike {
    pub fn ctlz_nonzero(_: u8) -> u32 { 42 }
}
pub fn lookalike_body(value: u8) { assert!(lookalike::ctlz_nonzero(value) == 42); }
pub fn lookalike_wrong_claim(value: u8) { assert!(lookalike::ctlz_nonzero(value) == 0); }

#[cfg(test)]
#[test]
fn native_nonzero_scan_bit_positions() {
    for bit in 0..128 {
        let value = 1_u128 << bit;
        assert!(scan_u128(value) == 127 - bit);
        assert!(scan_i128(value as i128) == 127 - bit);
        check_u128_scan(value);
        check_i128_scan(value as i128);
    }
    for bit in 0..usize::BITS {
        let value = 1_usize << bit;
        assert!(scan_usize(value) == usize::BITS - bit - 1);
    }
    for value in 1..=u8::MAX {
        assert!(scan_u8(value) == value.leading_zeros());
    }
    lookalike_body(0);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unchecked_shift(value: u32, count: u32) -> u32 {
    mir! { { Call(RET = u32::unchecked_shl(value, count), ReturnTo(done), UnwindUnreachable()) }
           done = { Return() } }
}
pub fn guarded_shift(value: u32, count: u32) {
    if count < 32 { assert!(unchecked_shift(value, count) == value << count); }
}
pub fn zero_shift() { assert!(unchecked_shift(0, 0) == 0); }
pub fn largest_shift() { assert!(unchecked_shift(1, 31) == 0x8000_0000); }
pub fn invalid_shift() -> u32 { unchecked_shift(1, 32) }
pub fn negative_shift(count: i32) -> u32 {
    if count < 0 { unchecked_shift(1, count as u32) } else { 0 }
}
pub fn wrong_shift(value: u32) { assert!(unchecked_shift(value, 0) == 0); }

#[cfg(test)]
#[test]
fn native_valid_unchecked_shifts() {
    zero_shift();
    largest_shift();
    mixed_width_valid();
    signed_count_valid();
    for count in 0..32 {
        guarded_shift(0, count);
        guarded_shift(u32::MAX, count);
        assert!(unchecked_shift(1, count) == 1 << count);
    }
}

#[custom_mir(dialect = "runtime", phase = "initial")]
pub fn mixed_width_shift(value: u32, count: u64) -> u32 {
    mir! { { Call(RET = core::intrinsics::unchecked_shl(value, count),
                   ReturnTo(done), UnwindUnreachable()) }
           done = { Return() } }
}
#[custom_mir(dialect = "runtime", phase = "initial")]
pub fn signed_count_shift(value: u32, count: i64) -> u32 {
    mir! { { Call(RET = core::intrinsics::unchecked_shl(value, count),
                   ReturnTo(done), UnwindUnreachable()) }
           done = { Return() } }
}
pub fn mixed_width_valid() { assert!(mixed_width_shift(1, 31) == 0x8000_0000); }
pub fn mixed_width_overflow() -> u32 { mixed_width_shift(1, 32) }
pub fn mixed_width_narrowing() -> u32 { mixed_width_shift(1, 1_u64 << 32) }
pub fn signed_count_negative() -> u32 { signed_count_shift(1, -1) }
pub fn signed_count_valid() { assert!(signed_count_shift(1, 31) == 0x8000_0000); }
