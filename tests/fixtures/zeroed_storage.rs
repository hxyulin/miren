#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

use core::intrinsics::mir::*;
use core::mem::MaybeUninit;

// Synthetic MIR calls the unsafe core API without adding an unsafe Rust implementation.
// The analyzer must check the compiler validity guard before reconstructing actual zero bits.
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn zero<T>() -> T {
    mir! {
        { Call(RET = core::mem::zeroed::<T>(), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

pub struct Record {
    flag: bool,
    count: u32,
    character: char,
    samples: [i16; 3],
    nested: (u64, f32, f64),
}

pub fn scalar_fields() {
    let value = zero::<Record>();
    assert!(!value.flag);
    assert!(value.count == 0);
    assert_eq!(value.character, '\0');
    assert_eq!(value.samples[2], 0);
    assert_eq!(value.nested.0, 0);
    assert_eq!(value.nested.1.to_bits(), 0);
    assert_eq!(value.nested.2.to_bits(), 0);
}

pub fn large_bytes(index: usize) {
    let mut bytes = zero::<[u8; 1024]>();
    if index < bytes.len() {
        assert_eq!(bytes[index], 0);
        bytes[index] = 3;
        assert_eq!(bytes[index], 3);
    }
}

pub fn wrong_zero() {
    assert!(zero::<u32>() == 1);
}

pub fn zero_then_panic() {
    let _: (u32, bool) = zero();
    panic!();
}

pub fn invalid_reference() -> &'static u32 {
    zero()
}

pub fn invalid_nonzero() -> core::num::NonZeroU32 {
    zero()
}

pub fn unknown_pointer() -> *const u32 {
    zero()
}

pub fn unknown_uninit() -> MaybeUninit<u32> {
    zero()
}

pub fn unknown_maybe_uninit_constructor() -> MaybeUninit<u32> {
    MaybeUninit::zeroed()
}

pub union Choice {
    word: u32,
    bytes: [u8; 4],
}

pub fn unknown_union() -> Choice {
    zero()
}

#[repr(u8)]
pub enum Mode {
    First = 3,
    Second = 0,
}

pub fn direct_tag_enum() {
    assert!(matches!(zero::<Mode>(), Mode::Second));
}

pub enum PayloadMode {
    Empty,
    Data(u32),
}

pub fn unknown_payload_enum() -> PayloadMode {
    zero()
}

pub enum NicheMode {
    Empty,
    Data(core::num::NonZeroU32),
}

pub fn unknown_niche_enum() -> NicheMode {
    zero()
}

#[repr(u8)]
pub enum InvalidMode {
    First = 1,
    Second = 2,
}

pub fn invalid_enum() -> InvalidMode {
    zero()
}

type Positive = core::pattern_type!(u32 is 1..);
type Inclusive = core::pattern_type!(u32 is 0..);

pub fn invalid_pattern() -> Positive {
    zero()
}

pub fn unknown_pattern() -> Inclusive {
    zero()
}

pub fn unknown_elements_budget() -> [[u32; 128]; 2] {
    zero()
}

pub fn unknown_array_budget() -> [u16; 129] {
    zero()
}

pub fn same_name() {
    fn zeroed() -> u32 { panic!(); }
    let _ = zeroed();
}

pub struct Empty;

pub fn empty_types() {
    let _: Empty = zero();
    let _: () = zero();
    let _: [u16; 0] = zero();
}

#[cfg(test)]
#[test]
fn native_initialized_zero_bits() {
    scalar_fields();
    large_bytes(1023);
    direct_tag_enum();
    empty_types();
}
