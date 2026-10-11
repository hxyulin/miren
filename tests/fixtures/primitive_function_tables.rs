#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn bool_first(value: bool) -> bool {
    value ^ false
}

#[inline(never)]
pub fn bool_second(value: bool) -> bool {
    !value
}

#[inline(never)]
pub fn char_first(value: char) -> char {
    value
}

#[inline(never)]
pub fn char_second(value: char) -> char {
    if value == 'A' { 'B' } else { 'A' }
}

pub fn selected_bool(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 2] = [bool_first, bool_second];
    if index < 2 {
        let actual = table[index](value);
        assert!(actual == if index == 0 { value } else { !value });
    }
}

pub fn wrong_bool(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 2] = [bool_first, bool_second];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

pub fn opaque_bool(index: usize, value: bool, callback: fn(bool) -> bool) {
    let table: [fn(bool) -> bool; 2] = [bool_first, callback];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

pub fn selected_char(index: usize, value: char) {
    let table: [fn(char) -> char; 2] = [char_first, char_second];
    if index < 2 {
        let actual = table[index](value);
        let expected = if index == 0 { value } else if value == 'A' { 'B' } else { 'A' };
        assert!(actual == expected);
    }
}

pub fn wrong_char(index: usize, value: char) {
    let table: [fn(char) -> char; 2] = [char_first, char_second];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

pub fn opaque_char(index: usize, value: char, callback: fn(char) -> char) {
    let table: [fn(char) -> char; 2] = [char_first, callback];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        for index in 0..2 {
            for value in [false, true] {
                super::selected_bool(index, value);
            }
            for value in ['\0', 'A', 'B', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
                super::selected_char(index, value);
            }
        }
    }
}
