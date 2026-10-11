#![no_std]
#![forbid(unsafe_code)]
extern crate scalar_metadata_dependency;

pub fn foreign_bool(values: &mut [bool]) {
    assert!(scalar_metadata_dependency::metadata_result(values.is_empty()) == (values.len() == 0));
}

pub fn foreign_char(values: &mut [char]) {
    assert!(scalar_metadata_dependency::metadata_result(values.is_empty()) == (values.len() == 0));
}

pub fn foreign_empty(values: &mut [i32]) {
    if values.len() == 0 {
        assert!(scalar_metadata_dependency::metadata_result(values.is_empty()));
    }
}
