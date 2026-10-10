#![no_std]
#![forbid(unsafe_code)]
extern crate fixed_byte_copy_dependency;

pub fn selected(values: &mut [u8]) {
    if values.len() >= 2 {
        fixed_byte_copy_dependency::apply(values);
        assert!(values[0] == 17 && values[1] == 19);
    }
}
