#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn first32(value: f32) -> f32 { value }
#[inline(never)]
pub fn second32(value: f32) -> f32 { -value }
#[inline(never)]
pub fn first64(value: f64) -> f64 { value }
#[inline(never)]
pub fn second64(value: f64) -> f64 { -value }

pub fn selected32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [first32, second32];
    if index < 2 {
        let actual = table[index](value);
        let expected = value.to_bits() ^ if index == 0 { 0 } else { 0x8000_0000 };
        assert!(actual.to_bits() == expected);
    }
}
pub fn wrong32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [first32, second32];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn opaque32(index: usize, value: f32, callback: fn(f32) -> f32) {
    let table: [fn(f32) -> f32; 2] = [first32, callback];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn repeat32(index: usize, value: f32) {
    let callback: fn(f32) -> f32 = first32;
    let table = [callback; 2];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn selected64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [first64, second64];
    if index < 2 {
        let actual = table[index](value);
        let expected = value.to_bits() ^ if index == 0 { 0 } else { 0x8000_0000_0000_0000 };
        assert!(actual.to_bits() == expected);
    }
}
pub fn wrong64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [first64, second64];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn opaque64(index: usize, value: f64, callback: fn(f64) -> f64) {
    let table: [fn(f64) -> f64; 2] = [first64, callback];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn repeat64(index: usize, value: f64) {
    let callback: fn(f64) -> f64 = first64;
    let table = [callback; 2];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}

#[cfg(test)]
mod native {
    #[test]
    fn copied_bits_and_signs() {
        for index in 0..2 {
            for bits in [0, 0x8000_0000, 1, 0x7f7f_ffff, 0x7f80_0000, 0xff80_0000,
                0x7fc0_0001, 0xffc1_2345] {
                super::selected32(index, f32::from_bits(bits));
            }
            for bits in [0, 0x8000_0000_0000_0000, 1, 0x7fef_ffff_ffff_ffff,
                0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000, 0x7ff8_0000_0000_0001,
                0xfff8_1234_5678_9abc] {
                super::selected64(index, f64::from_bits(bits));
            }
        }
    }
}
