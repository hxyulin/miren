#![no_std]
#![feature(core_intrinsics, pattern_types, pattern_type_macro)]

use core::mem::MaybeUninit;

fn initialized(value: char) -> MaybeUninit<char> {
    MaybeUninit::new(value)
}

pub fn symbolic(value: char) {
    let result = unsafe { initialized(value).assume_init() };
    assert!(result == value);
    let bits = result as u32;
    assert!(bits <= 0x10ffff && (bits < 0xd800 || bits > 0xdfff));
}

pub fn scalar_edges() {
    let result =
        unsafe { MaybeUninit::new(['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}']).assume_init() };
    assert!(result[0] == '\0');
    assert!(result[1] == '\u{d7ff}');
    assert!(result[2] == '\u{e000}');
    assert!(result[3] == '\u{10ffff}');
}

pub fn checked(value: u32) {
    if let Some(character) = char::from_u32(value) {
        assert!(unsafe { initialized(character).assume_init() } as u32 == value);
    }
}

pub fn copied(value: char, replacement: char, pick: bool) {
    let mut cell = initialized(value);
    let copy = cell;
    if pick {
        cell = initialized(replacement);
    }
    assert!(unsafe { copy.assume_init() } == value);
    let result = unsafe { cell.assume_init() };
    if pick {
        assert!(result == replacement);
    } else {
        assert!(result == value);
    }
}

pub fn nested_tuple(left: char, right: char, flag: bool) {
    let value = (left, (right, flag), [left, right]);
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result.0 == left);
    assert!(result.1.0 == right);
    assert!(result.1.1 == flag);
    assert!(result.2[0] == left && result.2[1] == right);
}

pub fn wrapper_carrier(value: char) {
    let tuple = (initialized(value), 1u8);
    assert!(unsafe { tuple.0.assume_init() } == value);
    let array = [initialized(value), initialized('\u{e000}')];
    assert!(unsafe { array[0].assume_init() } == value);
}

pub fn array(values: [char; 3], index: usize) {
    let result = unsafe { MaybeUninit::new(values).assume_init() };
    if index < 3 {
        assert!(result[index] == values[index]);
    }
}

pub fn selected_tuple(values: [(char, bool); 2], index: usize) {
    if index < 2 {
        let result = unsafe { MaybeUninit::new(values[index]).assume_init() };
        assert!(result.0 == values[index].0);
        assert!(result.1 == values[index].1);
    }
}

pub fn boundary(value: char) {
    let result = unsafe { MaybeUninit::new([value; 128]).assume_init() };
    assert!(result[127] == value);
}

pub fn empty_initialized() {
    let result = unsafe { MaybeUninit::new([] as [char; 0]).assume_init() };
    assert!(result.len() == 0);
}

pub fn empty_uninitialized() {
    let result = unsafe { MaybeUninit::<[char; 0]>::uninit().assume_init() };
    assert!(result.len() == 0);
}

fn mutation_initializer() -> MaybeUninit<char> {
    MaybeUninit::new('\u{e000}')
}

pub fn mutation_claim() {
    assert!(unsafe { mutation_initializer().assume_init() } == '\u{e000}');
}

pub fn wrong_claim(value: char) {
    assert!(unsafe { initialized(value).assume_init() } != value);
}

pub fn wrong_element(value: char) {
    let result = unsafe { MaybeUninit::new([value, '\0']).assume_init() };
    assert!(result[1] == '\u{e000}');
}

pub fn uninitialized() -> char {
    unsafe { MaybeUninit::<char>::uninit().assume_init() }
}

pub fn uninitialized_array() -> [char; 1] {
    unsafe { MaybeUninit::<[char; 1]>::uninit().assume_init() }
}

pub fn conditional(value: char, pick: bool) -> char {
    let mut cell = MaybeUninit::uninit();
    if pick {
        cell = initialized(value);
    }
    unsafe { cell.assume_init() }
}

pub fn invalid_surrogate() -> char {
    let character = unsafe { core::mem::transmute::<u32, char>(0xd800) };
    unsafe { initialized(character).assume_init() }
}

pub fn invalid_float() -> char {
    let character = unsafe { core::mem::transmute::<f32, char>(f32::from_bits(0xdfff)) };
    unsafe { initialized(character).assume_init() }
}

#[cfg(target_pointer_width = "32")]
pub fn invalid_pointer() -> char {
    let character = unsafe { core::mem::transmute::<*const u8, char>(0xd800usize as *const u8) };
    unsafe { initialized(character).assume_init() }
}

pub fn incoming(value: MaybeUninit<char>) -> char {
    unsafe { value.assume_init() }
}

pub fn wrong_type(value: char) -> u32 {
    unsafe { core::mem::transmute::<MaybeUninit<char>, u32>(initialized(value)) }
}

pub fn initialized_ref(value: char) -> char {
    let cell = initialized(value);
    unsafe { *cell.assume_init_ref() }
}

pub fn partial_write(value: char) -> char {
    let mut cell = MaybeUninit::<char>::uninit();
    cell.write(value);
    unsafe { cell.assume_init() }
}

pub fn pointer_payload(value: *const char) -> *const char {
    unsafe { MaybeUninit::new(value).assume_init() }
}

pub fn oversized() {
    let _ = MaybeUninit::<[char; 129]>::uninit();
}

pub fn node_exhaustion() {
    let _ = MaybeUninit::<[(char, bool); 86]>::uninit();
}

type RestrictedChar = core::pattern_type!(char is '\u{1}'..);
pub fn pattern(value: RestrictedChar) {
    let _ = MaybeUninit::new(value);
}

pub fn empty_pattern() {
    let _ = unsafe { MaybeUninit::<[RestrictedChar; 0]>::uninit().assume_init() };
}

#[test]
fn native_complete_char_payloads_preserve_values() {
    for value in ['\0', 'a', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
        symbolic(value);
        copied(value, '\u{e000}', false);
        copied(value, '\u{e000}', true);
        nested_tuple(value, '\u{10ffff}', true);
        wrapper_carrier(value);
        boundary(value);
        for index in 0..3 {
            array([value, 'a', '\u{10ffff}'], index);
        }
        selected_tuple([(value, true), ('a', false)], 0);
        selected_tuple([(value, true), ('a', false)], 1);
    }
    for bits in [
        0,
        0xd7ff,
        0xe000,
        0x10ffff,
        0xd800,
        0xdfff,
        0x110000,
        u32::MAX,
    ] {
        checked(bits);
    }
    scalar_edges();
    empty_initialized();
    empty_uninitialized();
    mutation_claim();
}
