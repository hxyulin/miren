#![no_std]
#![forbid(unsafe_code)]

pub fn returned_value() {
    let value = critical_section::with(|_| 42u32);
    assert!(value == 42);
}

pub fn wrong_value() {
    let value = critical_section::with(|_| 42u32);
    assert!(value == 43);
}
