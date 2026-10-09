#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn load<T: Copy>(pointer: *const T) -> T {
    mir! {
        { Call(RET = core::intrinsics::volatile_load(pointer), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(value: S) -> T {
    mir! {{ RET = CastTransmute(value); Return() }}
}

pub fn retains_f32_bits(value: f32) {
    assert!(load(&raw const value).to_bits() == value.to_bits());
}

pub fn retains_f64_bits(value: f64) {
    assert!(load(&raw const value).to_bits() == value.to_bits());
}

pub fn retains_boolean_and_integer(value: bool, number: i32) {
    assert!(load(&raw const value) == value);
    assert!(load(&raw const number) == number);
}

pub fn special_float_bits() {
    let nan = f32::from_bits(0x7fc0_1234);
    let negative_zero = f64::from_bits(0x8000_0000_0000_0000);
    assert!(load(&raw const nan).to_bits() == 0x7fc0_1234);
    assert!(load(&raw const negative_zero).to_bits() == 0x8000_0000_0000_0000);
}

pub fn wrong_float_claim() {
    let value = 1.0_f32;
    assert!(load(&raw const value) == 2.0);
}

pub fn numeric_mmio_is_unknown() {
    let pointer: *const f32 = cast(0x4000_0000_usize);
    let _ = load(pointer);
}

pub fn arbitrary_pointer_is_unknown(pointer: *const f32) {
    let _ = load(pointer);
}

pub fn punned_type_is_unknown() {
    let value = 1.0_f32;
    let pointer: *const u32 = cast(&raw const value);
    let _ = load(pointer);
}

struct Pair { first: f32, second: u32 }

pub fn projected_scalar_is_unknown() {
    let pair = Pair { first: 1.0, second: 2 };
    let _ = load(&raw const pair.first);
}

static mut SHARED: f32 = 1.0;

pub fn static_storage_is_unknown() {
    let _ = load(&raw const SHARED);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn cursor_is_unknown() {
    mir! {
        let value: f32;
        let pointer: *const f32;
        let displaced: *const f32;
        let result: f32;
        {
            value = 1.0_f32;
            pointer = &raw const value;
            displaced = Offset(pointer, 1_isize);
            Call(result = load(displaced), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_storage_is_unknown() {
    mir! {
        let value: f32;
        let pointer: *const f32;
        let result: f32;
        {
            StorageLive(value);
            value = 1.0_f32;
            pointer = &raw const value;
            StorageDead(value);
            Call(result = load(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (); Return() }
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn floats() {
        super::special_float_bits();
        for bits in [0, 0x8000_0000, 0x7fc0_1234, 0x7fa0_0001, 0x3f80_0000] {
            super::retains_f32_bits(f32::from_bits(bits));
        }
        for bits in [0, 0x8000_0000_0000_0000, 0x7ff8_0000_0000_1234] {
            super::retains_f64_bits(f64::from_bits(bits));
        }
        super::retains_boolean_and_integer(false, -37);
    }

    #[test]
    fn wrong_claim() {
        super::wrong_float_claim();
    }
}

pub fn opaque_effect() {}

pub fn effects_invalidate_backing() {
    let value = 1.0_f32;
    let pointer = &raw const value;
    opaque_effect();
    let _ = load(pointer);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn uninitialized_storage_is_unknown() {
    mir! {
        let value: f32;
        let pointer: *const f32;
        let result: f32;
        {
            StorageLive(value);
            pointer = &raw const value;
            Call(result = load(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (); Return() }
    }
}
