#![no_std]
#![forbid(unsafe_code)]
extern crate retained_scalar_helper_dependency;
pub fn missing(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = retained_scalar_helper_dependency::opaque(word);
        assert!(child[0] == word);
    }
}
