#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn boolean(value: bool) -> bool {
    value ^ false
}

#[inline(never)]
pub fn character(value: char) -> char {
    value
}

#[inline(never)]
pub fn generic<T: Copy>(value: T) -> T {
    value
}

pub extern "C" fn foreign(value: bool) -> bool {
    value
}

pub fn selected_bool(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 16] = [boolean; 16];
    if index < 16 {
        assert!(table[index](value) == value);
    }
}

pub fn wrong_bool(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 16] = [boolean; 16];
    if index < 16 {
        assert!(table[index](value) != value);
    }
}

pub fn selected_char(index: usize, value: char) {
    let table: [fn(char) -> char; 16] = [character; 16];
    if index < 16 {
        assert!(table[index](value) == value);
    }
}

#[inline(never)]
pub fn branch_character(value: char) -> char {
    if value == 'A' { 'A' } else { value }
}

pub fn body_dispatch_budget(index: usize, value: char) {
    let table: [fn(char) -> char; 16] = [branch_character; 16];
    if index < 16 {
        assert!(table[index](value) == value);
    }
}

pub fn wrong_char(index: usize, value: char) {
    let table: [fn(char) -> char; 16] = [character; 16];
    if index < 16 {
        assert!(table[index](value) != value);
    }
}

pub fn opaque_bool(value: bool, callback: fn(bool) -> bool) {
    let table = [callback; 2];
    assert!(table[0](value) == value);
}

pub fn opaque_char(value: char, callback: fn(char) -> char) {
    let table = [callback; 2];
    assert!(table[0](value) == value);
}

pub fn generic_bool(value: bool) {
    let table: [fn(bool) -> bool; 2] = [generic::<bool>; 2];
    assert!(table[0](value) == value);
}

pub fn foreign_bool(value: bool) {
    let table: [extern "C" fn(bool) -> bool; 2] = [foreign; 2];
    assert!(table[0](value) == value);
}

pub fn last_char(value: char) {
    let table: [fn(char) -> char; 128] = [character; 128];
    assert!(table[127](value) == value);
}

pub fn count_budget(value: bool) {
    let table: [fn(bool) -> bool; 129] = [boolean; 129];
    assert!(table[0](value) == value);
}

pub fn dispatch_budget(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 128] = [boolean; 128];
    if index < 128 {
        assert!(table[index](value) == value);
    }
}

pub fn zero() {
    let booleans: [fn(bool) -> bool; 0] = [boolean; 0];
    let characters: [fn(char) -> char; 0] = [character; 0];
    assert!(booleans.len() == 0 && characters.len() == 0);
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        for index in 0..16 {
            for value in [false, true] {
                super::selected_bool(index, value);
            }
            for value in ['\0', 'A', 'B', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
                super::selected_char(index, value);
                super::last_char(value);
            }
        }
        super::zero();
    }
}
