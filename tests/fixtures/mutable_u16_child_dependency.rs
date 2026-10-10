#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn selected(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = word;
    }
}
