#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn selected(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        values[index] = !value;
    }
}
