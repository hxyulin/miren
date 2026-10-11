#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn word(value: char) -> char {
    if value == '\0' { '\0' } else { value }
}

#[inline(never)]
pub fn leaf(values: &mut [char]) {
    if values.len() > 0 {
        values[0] = word(values[0]);
    }
}
