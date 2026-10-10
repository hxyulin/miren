#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn selected(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        values[index] = if value == 'A' { 'B' } else { 'A' };
    }
}
