#![no_std]
#![feature(
    custom_mir,
    core_intrinsics,
    sync_unsafe_cell,
    pattern_types,
    pattern_type_macro
)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;

fn scalar(value: u32) -> bool {
    value <= 0x10ffff && !(0xd800..=0xdfff).contains(&value)
}

pub fn incoming(value: char) {
    assert!(scalar(value as u32));
}

pub fn checked(value: u32) {
    match char::from_u32(value) {
        Some(character) => {
            assert!(character as u32 == value);
            assert!(scalar(character as u32));
        }
        None => assert!(!scalar(value)),
    }
}

pub fn mutation_claim(value: u32) {
    if let Some(character) = char::from_u32(value) {
        assert!(character as u32 == value);
    }
}

pub fn wrong_claim(value: u32) {
    if let Some(character) = char::from_u32(value) {
        assert!(character as u32 != value);
    }
}

pub fn checked_unchecked(value: u32) {
    if scalar(value) {
        let character = unsafe { char::from_u32_unchecked(value) };
        assert!(character as u32 == value);
    }
}

pub fn exact_bits(value: u32) {
    if scalar(value) {
        let character = unsafe { core::mem::transmute::<u32, char>(value) };
        assert!(character as u32 == value);
    }
}

pub fn exact_signed(value: i32) {
    if value >= 0 && scalar(value as u32) {
        let character = unsafe { core::mem::transmute::<i32, char>(value) };
        assert!(character as u32 == value as u32);
    }
}

pub fn output_bits(value: char) {
    let unsigned = unsafe { core::mem::transmute::<char, u32>(value) };
    let signed = unsafe { core::mem::transmute::<char, i32>(value) };
    let same = unsafe { core::mem::transmute::<char, char>(value) };
    assert!(unsigned == value as u32);
    assert!(signed as u32 == unsigned);
    assert!(same == value);
}

pub fn byte_character(value: u8) {
    assert!(value as char as u32 == value as u32);
    assert!(char::from(value) as u32 == value as u32);
}

pub fn valid_float_bits() {
    for value in [0, 0xd7ff, 0xe000, 0x10ffff] {
        let character = unsafe { core::mem::transmute::<f32, char>(f32::from_bits(value)) };
        assert!(character as u32 == value);
    }
}

pub fn float_roundtrip(value: char) {
    let float = unsafe { core::mem::transmute::<char, f32>(value) };
    assert!(float.to_bits() == value as u32);
}

pub fn zeroed() {
    let character = unsafe { core::mem::zeroed::<char>() };
    assert!(character == '\0');
}

#[cfg(not(test))]
pub fn surrogate() -> char {
    unsafe { core::mem::transmute::<u32, char>(0xd800) }
}

#[cfg(not(test))]
pub fn out_of_range() -> char {
    unsafe { core::mem::transmute::<u32, char>(0x110000) }
}

#[cfg(not(test))]
pub fn unconstrained(value: u32) -> char {
    unsafe { core::mem::transmute::<u32, char>(value) }
}

#[cfg(not(test))]
pub fn invalid_float_bits() -> char {
    unsafe { core::mem::transmute::<f32, char>(f32::from_bits(0xd800)) }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[cfg(not(test))]
fn expose(pointer: *const u8) -> char {
    mir! {{ RET = Cast(pointer, CastKind::PointerExposeProvenance); Return() }}
}

#[cfg(not(test))]
pub fn expose_invalid() -> char {
    expose(0xd800usize as *const u8)
}

#[cfg(not(test))]
pub fn expose_valid() {
    assert!(expose(0xe000usize as *const u8) as u32 == 0xe000);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[cfg(not(test))]
fn integer_cast(value: u32) -> char {
    mir! {{ RET = Cast(value, CastKind::IntToInt); Return() }}
}

#[cfg(not(test))]
pub fn integer_cast_invalid() -> char {
    integer_cast(0xdfff)
}

#[cfg(not(test))]
pub fn integer_cast_valid(value: u32) {
    if scalar(value) {
        assert!(integer_cast(value) as u32 == value);
    }
}

#[cfg(target_pointer_width = "32")]
#[cfg(not(test))]
pub fn pointer_invalid() -> char {
    unsafe { core::mem::transmute::<*const u8, char>(0xd800usize as *const u8) }
}

#[cfg(target_pointer_width = "32")]
#[cfg(not(test))]
pub fn pointer_valid() {
    let character = unsafe { core::mem::transmute::<*const u8, char>(0xe000usize as *const u8) };
    assert!(character as u32 == 0xe000);
}

static mut LETTER: char = 'a';
static CELL: SyncUnsafeCell<char> = SyncUnsafeCell::new('a');
static UNINIT: SyncUnsafeCell<core::mem::MaybeUninit<char>> =
    SyncUnsafeCell::new(core::mem::MaybeUninit::uninit());
static mut BYTE: u8 = 0;

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[cfg(not(test))]
fn read<T: Copy>(pointer: *const T) -> T {
    mir! {{ RET = *pointer; Return() }}
}

#[cfg(not(test))]
pub fn static_domain() {
    assert!(scalar(read(&raw const LETTER) as u32));
}

#[cfg(not(test))]
pub fn cell_domain() {
    assert!(scalar(read(CELL.get()) as u32));
}

#[cfg(not(test))]
pub fn no_initializer() {
    assert!(read(&raw const LETTER) == 'a');
}

#[cfg(not(test))]
pub fn uninitialized() -> char {
    read(UNINIT.get() as *const char)
}

#[cfg(not(test))]
pub fn static_address() -> char {
    expose(&raw const BYTE)
}

#[cfg(not(test))]
pub fn unsupported_wrapper() {
    let _ = unsafe { core::mem::MaybeUninit::new('a').assume_init() };
}

#[test]
fn native_valid_characters_and_checked_invalid_inputs() {
    for value in [
        0,
        1,
        65,
        0xff,
        0xd7ff,
        0xe000,
        0x10ffff,
        0xd800,
        0xdfff,
        0x110000,
        u32::MAX,
    ] {
        checked(value);
        mutation_claim(value);
        checked_unchecked(value);
        exact_bits(value);
        if value <= i32::MAX as u32 {
            exact_signed(value as i32);
        }
        if let Some(character) = char::from_u32(value) {
            incoming(character);
            output_bits(character);
            float_roundtrip(character);
        }
    }
    for value in [0, 1, 65, 255] {
        byte_character(value);
    }
    valid_float_bits();
    zeroed();
}

// Source-level forged restricted scalar formations are analysis-only negative controls.
type Positive = core::pattern_type!(u32 is 1..);
type RestrictedChar = core::pattern_type!(char is '\u{1}'..);
#[cfg(not(test))]
pub fn float_pattern_integer() -> Positive {
    unsafe { core::mem::transmute::<f32, Positive>(f32::from_bits(0)) }
}
#[cfg(not(test))]
pub fn float_pattern_char() -> RestrictedChar {
    unsafe { core::mem::transmute::<f32, RestrictedChar>(f32::from_bits(0xd800)) }
}
#[cfg(target_pointer_width = "32")]
#[cfg(not(test))]
pub fn pointer_pattern() -> Positive {
    unsafe { core::mem::transmute::<*const u8, Positive>(core::ptr::null()) }
}

#[cfg(not(test))]
pub fn float_pattern_integer_valid() -> Positive {
    unsafe { core::mem::transmute::<f32, Positive>(f32::from_bits(1)) }
}

#[cfg(not(test))]
pub fn float_pattern_char_valid() -> RestrictedChar {
    unsafe { core::mem::transmute::<f32, RestrictedChar>(f32::from_bits(0xe000)) }
}

#[cfg(not(test))]
pub fn float_pattern_char_zero() -> RestrictedChar {
    unsafe { core::mem::transmute::<f32, RestrictedChar>(f32::from_bits(0)) }
}

#[cfg(all(not(test), target_pointer_width = "32"))]
pub fn pointer_pattern_valid() -> Positive {
    unsafe { core::mem::transmute::<*const u8, Positive>(1usize as *const u8) }
}

#[cfg(not(test))]
pub fn startup_initializer() {
    assert!(read(&raw const LETTER) == 'a');
}

#[cfg(not(test))]
pub fn startup_store() {
    unsafe { LETTER = '\u{e000}' };
    assert!(read(&raw const LETTER) == '\u{e000}');
}
