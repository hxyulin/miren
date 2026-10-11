#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn scalar(word: u16) -> u16 {
    word ^ 0
}
#[inline(never)]
pub fn leaf(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        values[0] = scalar(word);
    }
}
