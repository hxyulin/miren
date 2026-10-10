#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn selected(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        values[index] = word;
    }
}
