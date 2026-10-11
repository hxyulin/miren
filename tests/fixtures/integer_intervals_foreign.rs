#![no_std]
#![forbid(unsafe_code)]
extern crate stage205_dependency;

pub fn selected_i32(values: &mut [i32], start: usize, end: usize, word: i32) {
    if start < end && end <= values.len() {
        stage205_dependency::selected_i32(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn selected_usize(values: &mut [usize], start: usize, end: usize, word: usize) {
    if start < end && end <= values.len() {
        stage205_dependency::selected_usize(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn empty_i32(values: &mut [i32], at: usize) {
    if at <= values.len() {
        stage205_dependency::empty_i32(&mut values[at..at]);
    }
}
pub fn empty_usize(values: &mut [usize], at: usize) {
    if at <= values.len() {
        stage205_dependency::empty_usize(&mut values[at..at]);
    }
}
