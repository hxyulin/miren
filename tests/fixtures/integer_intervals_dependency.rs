#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn selected_i32(values: &mut [i32], word: i32) {
    values[0] = word;
}
#[inline(never)]
pub fn selected_usize(values: &mut [usize], word: usize) {
    values[0] = word;
}
#[inline(never)]
pub fn empty_i32(values: &mut [i32]) {
    assert!(values.len() == 0);
}
#[inline(never)]
pub fn empty_usize(values: &mut [usize]) {
    assert!(values.len() == 0);
}
