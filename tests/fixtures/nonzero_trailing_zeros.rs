#![no_std]
#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

macro_rules! nonzero_scan {
    ($scan:ident, $check:ident, $integer:ty) => {
        #[custom_mir(dialect = "runtime", phase = "optimized")]
        pub fn $scan(value: $integer) -> u32 {
            mir! { { Call(RET = core::intrinsics::cttz_nonzero(value),
                           ReturnTo(done), UnwindUnreachable()) }
                   done = { Return() } }
        }
        pub fn $check(value: $integer) {
            if value != 0 {
                assert!($scan(value) == value.trailing_zeros());
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
    pub fn cttz_nonzero(_: u8) -> u32 { 42 }
}
pub fn lookalike_body(value: u8) { assert!(lookalike::cttz_nonzero(value) == 42); }
pub fn lookalike_wrong_claim(value: u8) { assert!(lookalike::cttz_nonzero(value) == 0); }

#[cfg(test)]
#[test]
fn native_nonzero_scan_bit_positions() {
    for bit in 0..128 {
        let value = 1_u128 << bit;
        assert!(scan_u128(value) == bit);
        assert!(scan_i128(value as i128) == bit);
        check_u128_scan(value);
        check_i128_scan(value as i128);
    }
    for bit in 0..usize::BITS {
        let value = 1_usize << bit;
        assert!(scan_usize(value) == bit);
    }
    for value in 1..=u8::MAX {
        assert!(scan_u8(value) == value.trailing_zeros());
    }
    lookalike_body(0);
}


macro_rules! safe_scan {
    ($name:ident, $integer:ty) => {
        pub fn $name(value: $integer) {
            if let Some(nonzero) = core::num::NonZero::new(value) {
                assert!(nonzero.trailing_zeros() == value.trailing_zeros());
                assert!(nonzero.trailing_zeros() < <$integer>::BITS);
            }
        }
    };
}
safe_scan!(safe_u8, u8);
safe_scan!(safe_u16, u16);
safe_scan!(safe_u32, u32);
safe_scan!(safe_u64, u64);
safe_scan!(safe_u128, u128);
safe_scan!(safe_usize, usize);
safe_scan!(safe_i32, i32);
pub fn negative_value() { assert!(scan_i32(-8) == 3); }
pub fn mutation_claim() { assert!(scan_u8(8) == 3); }
#[cfg(test)]
#[test]
fn native_safe_and_mutation_control() {
    mutation_claim();
    negative_value();
    for value in 0..=u8::MAX { safe_u8(value); }
    safe_i32(-8);
}

#[cfg(test)]
#[test]
fn native_every_primitive_bit_position() {
    macro_rules! bits {
        ($scan:ident, $integer:ty) => {
            for bit in 0..<$integer>::BITS {
                let value = (1_u128 << bit) as $integer;
                assert!($scan(value) == bit);
            }
        };
    }
    bits!(scan_u8, u8);
    bits!(scan_u16, u16);
    bits!(scan_u32, u32);
    bits!(scan_u64, u64);
    bits!(scan_u128, u128);
    bits!(scan_usize, usize);
    bits!(scan_i8, i8);
    bits!(scan_i16, i16);
    bits!(scan_i32, i32);
    bits!(scan_i64, i64);
    bits!(scan_i128, i128);
    bits!(scan_isize, isize);
}
