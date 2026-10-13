#![no_std]
#![forbid(unsafe_code)]
extern crate deeper_scope_dependency;
#[inline(never)]
pub fn leaf(values: &mut [u16], word: u16) {
    values[0] = deeper_scope_dependency::payload(word);
}
#[inline(never)]
pub fn inner(values: &mut [u16], word: u16) {
    leaf(values, word);
}
#[inline(never)]
pub fn outer(values: &mut [u16], word: u16) {
    inner(values, word);
}
pub fn missing_payload(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        outer(values, word);
        assert!(values[0] == word);
    }
}
