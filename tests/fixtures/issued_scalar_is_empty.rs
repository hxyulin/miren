#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn metadata_boolean(value: bool) -> bool {
    value
}

pub fn bool_empty(values: &mut [bool]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn char_empty(values: &mut [char]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn i32_empty(values: &mut [i32]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn usize_empty(values: &mut [usize]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn u16_anchor(values: &mut [u16]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn float_excluded(values: &mut [f32]) {
    assert!(values.is_empty() == (values.len() == 0));
}

pub fn boolean_helper(value: bool) {
    assert!(metadata_boolean(value) == value);
}

pub fn boolean_wrong(value: bool) {
    assert!(metadata_boolean(value) != value);
}

pub fn bool_wrong(values: &mut [bool]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn bool_partition(values: &mut [bool]) {
    if values.is_empty() {
        assert!(values.len() == 0);
    } else {
        assert!(values.len() > 0);
    }
}

pub fn char_wrong(values: &mut [char]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn char_partition(values: &mut [char]) {
    if values.is_empty() {
        assert!(values.len() == 0);
    } else {
        assert!(values.len() > 0);
    }
}

pub fn i32_wrong(values: &mut [i32]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn i32_partition(values: &mut [i32]) {
    if values.is_empty() {
        assert!(values.len() == 0);
    } else {
        assert!(values.len() > 0);
    }
}

pub fn usize_wrong(values: &mut [usize]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn usize_partition(values: &mut [usize]) {
    if values.is_empty() {
        assert!(values.len() == 0);
    } else {
        assert!(values.len() > 0);
    }
}

pub fn i8_empty(values: &mut [i8]) {
    assert!(values.is_empty() == (values.len() == 0));
}

pub fn u128_empty(values: &mut [u128]) {
    assert!(values.is_empty() == (values.len() == 0));
}

#[cfg(test)]
mod tests {
    #[test]
    fn metadata_native_guard() {
        super::bool_empty(&mut []);
        super::bool_empty(&mut [false; 129]);
        super::char_empty(&mut ['\u{10ffff}'; 129]);
        super::i32_empty(&mut [i32::MIN; 129]);
        super::usize_empty(&mut [usize::MAX; 129]);
        super::u16_anchor(&mut [u16::MAX; 129]);
        super::bool_partition(&mut []);
        super::bool_partition(&mut [true; 129]);
        super::char_partition(&mut []);
        super::char_partition(&mut ['\u{d7ff}'; 129]);
        super::i32_partition(&mut []);
        super::i32_partition(&mut [i32::MAX; 129]);
        super::usize_partition(&mut []);
        super::usize_partition(&mut [0; 129]);
        super::i8_empty(&mut [i8::MIN; 129]);
        super::u128_empty(&mut [u128::MAX; 129]);
        super::boolean_helper(false);
        super::boolean_helper(true);
    }
}


pub fn float32_metadata(values: &mut [f32]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn float64_metadata(values: &mut [f64]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn float32_wrong(values: &mut [f32]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn float64_wrong(values: &mut [f64]) {
    assert!(metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn float_nested_metadata(values: &mut [[f32; 2]]) {
    assert!(metadata_boolean(values.is_empty()) == (values.len() == 0));
}

#[cfg(test)]
mod float_native {
    extern crate std;
    #[test]
    fn metadata_bits_and_lengths() {
        for bits in [0, 0x8000_0000, 0x7f80_0000, 0x7fc0_1234, 0x7f80_0100] {
            for length in [0, 1, 2, 129] {
                super::float32_metadata(&mut std::vec![f32::from_bits(bits); length]);
            }
        }
        for bits in [0, 0x8000_0000_0000_0000, 0x7ff0_0000_0000_0000,
            0x7ff8_0000_0000_1234, 0x7ff0_0000_0000_0100] {
            for length in [0, 1, 2, 129] {
                super::float64_metadata(&mut std::vec![f64::from_bits(bits); length]);
            }
        }
    }
}
