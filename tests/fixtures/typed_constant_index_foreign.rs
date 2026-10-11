#![no_std]
#![forbid(unsafe_code)]
extern crate typed_constant_index_dependency;

pub fn selected(values: &mut [char]) {
    typed_constant_index_dependency::leaf(values);
}

pub fn empty() {
    typed_constant_index_dependency::leaf(&mut []);
}

pub fn guarded_empty(values: &mut [char]) {
    if values.len() == 0 {
        typed_constant_index_dependency::leaf(values);
    }
}
