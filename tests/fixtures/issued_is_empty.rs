#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn word(value: u16) -> u16 {
    value ^ 0
}
#[inline(never)]
pub fn child(values: &mut [u16], value: u16) {
    if !values.is_empty() {
        values[0] = word(value);
    }
}
#[inline(never)]
pub fn empty_child(values: &mut [u16]) {
    assert!(values.is_empty());
}
#[inline(never)]
pub fn len_child(values: &mut [u16], value: u16) {
    if values.len() > 0 {
        values[0] = word(value);
    }
}
pub fn root(values: &mut [u16]) {
    assert!(values.is_empty() == (values.len() == 0));
}
pub fn wrong_bool(values: &mut [u16]) {
    assert!(values.is_empty() != (values.len() == 0));
}
pub fn whole(values: &mut [u16], value: u16) {
    if values.len() > 0 {
        child(values, value);
        assert!(values[0] == value);
    }
}
pub fn proper(values: &mut [u16], start: usize, end: usize, value: u16) {
    if start < end && end <= values.len() {
        child(&mut values[start..end], value);
        assert!(values[start] == value);
    }
}
pub fn proper_empty(values: &mut [u16], at: usize) {
    if at <= values.len() {
        empty_child(&mut values[at..at]);
    }
}
pub fn len_anchor(values: &mut [u16], value: u16) {
    if values.len() > 0 {
        len_child(values, value);
        assert!(values[0] == value);
    }
}
pub fn len_wrong(values: &mut [u16], value: u16) {
    if values.len() > 0 {
        len_child(values, value);
        assert!(values[0] != value);
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn safe_guard() {
        root(&mut []);
        root(&mut [0; 129]);
        for value in [0, 1, u16::MAX] {
            whole(&mut [0; 129], value);
            proper(&mut [0; 129], 1, 129, value);
            len_anchor(&mut [0; 129], value);
        }
        for at in [0, 64, 129] {
            proper_empty(&mut [0; 129], at);
        }
    }
}
