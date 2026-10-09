#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;
use core::num::{NonZeroI16, NonZeroI128, NonZeroU32, NonZeroUsize};

pub fn correlated_unsigned(raw: u32) {
    match NonZeroU32::new(raw) {
        Some(value) => assert!(value.get() == raw && raw != 0),
        None => assert!(raw == 0),
    }
}

pub fn correlated_signed(raw: i16) {
    match NonZeroI16::new(raw) {
        Some(value) => assert!(value.get() == raw && raw != 0),
        None => assert!(raw == 0),
    }
}

pub fn correlated_wide_signed(raw: i128) {
    match NonZeroI128::new(raw) {
        Some(value) => assert!(value.get() == raw && raw != 0),
        None => assert!(raw == 0),
    }
}

pub fn correlated_pointer_width(raw: usize) {
    match NonZeroUsize::new(raw) {
        Some(value) => assert!(value.get() == raw && raw != 0),
        None => assert!(raw == 0),
    }
}

pub fn zero_is_none() { assert!(NonZeroU32::new(0).is_none()); }
pub fn negative_is_some() { assert!(NonZeroI16::new(-1).unwrap().get() == -1); }
pub fn unguarded_unwrap(raw: u32) { let _ = NonZeroU32::new(raw).unwrap(); }
pub fn zero_unwrap() { let _ = NonZeroU32::new(0).unwrap(); }
pub fn wrong_none_claim(raw: u32) { assert!(NonZeroU32::new(raw).is_some()); }

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn signedness_mismatch(raw: u16) -> Option<NonZeroI16> {
    mir! { { RET = CastTransmute(raw); Return() } }
}

#[repr(transparent)]
pub struct Wrapper(NonZeroU32);

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn wrapper_is_not_core_nonzero(raw: u32) -> Option<Wrapper> {
    mir! { { RET = CastTransmute(raw); Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn pointer_niche_is_not_integer(raw: usize) -> Option<core::ptr::NonNull<u8>> {
    mir! { { RET = CastTransmute(raw); Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn different_niche(raw: u8) -> Option<bool> {
    mir! { { RET = CastTransmute(raw); Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unguarded_some_payload(raw: u32) -> u32 {
    mir! {
        let option: Option<NonZeroU32>;
        let payload: NonZeroU32;
        {
            Call(option = NonZeroU32::new(raw), ReturnTo(read), UnwindUnreachable())
        }
        read = {
            payload = Field::<NonZeroU32>(Variant(option, 1), 0);
            Call(RET = NonZeroU32::get(payload), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[cfg(test)]
extern crate std;
#[cfg(test)]
#[test]
fn native_nonzero_branches_and_unwrap_failures() {
    for raw in [0, 1, 17, u32::MAX] { correlated_unsigned(raw); }
    for raw in [0, i16::MIN, -1, 1, i16::MAX] { correlated_signed(raw); }
    for raw in [0, i128::MIN, -1, 1, i128::MAX] { correlated_wide_signed(raw); }
    for raw in [0, 1, usize::MAX] { correlated_pointer_width(raw); }
    zero_is_none();
    negative_is_some();
    assert!(std::panic::catch_unwind(|| zero_unwrap()).is_err());
    assert!(std::panic::catch_unwind(|| unguarded_unwrap(0)).is_err());
}


mod unrelated {
    pub fn new(_: u32) -> Option<super::NonZeroU32> { None }
}

pub fn same_name_constructor_body_runs(raw: u32) {
    assert!(unrelated::new(raw).is_none());
}


macro_rules! correlated_primitive {
    ($name:ident, $raw:ty) => {
        pub fn $name(raw: $raw) {
            match core::num::NonZero::<$raw>::new(raw) {
                Some(value) => { assert!(value.get() == raw); assert!(raw != 0); }
                None => { assert!(raw == 0); }
            }
        }
    };
}
correlated_primitive!(unsigned_byte, u8);
correlated_primitive!(unsigned_short, u16);
correlated_primitive!(unsigned_long, u64);
correlated_primitive!(unsigned_wide, u128);
correlated_primitive!(signed_byte, i8);
correlated_primitive!(signed_word, i32);
correlated_primitive!(signed_long, i64);
correlated_primitive!(signed_pointer_width, isize);
