#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn identity_bool(value: bool) -> bool {
    value
}
#[inline(never)]
pub fn flip_bool(value: bool) -> bool {
    !value
}

pub fn nested_bool(i: usize, j: usize, value: bool) {
    let inner: [fn(bool) -> bool; 2] = [identity_bool, flip_bool];
    if i < 2 && j < 2 {
        let selected = inner[i];
        let outer: [fn(bool) -> bool; 2] = [selected, identity_bool];
        assert!(outer[j](value) == if j == 0 && i == 1 { !value } else { value });
    }
}
pub fn repeat_bool(i: usize, j: usize, value: bool) {
    let inner: [fn(bool) -> bool; 2] = [identity_bool, flip_bool];
    if i < 2 && j < 2 {
        let selected = inner[i];
        let outer = [selected; 2];
        assert!(outer[j](value) == if i == 1 { !value } else { value });
        assert!(outer[1 - j](value) == if i == 1 { !value } else { value });
    }
}
pub fn wrong_correlation(i: usize, j: usize, value: bool) {
    let inner: [fn(bool) -> bool; 2] = [identity_bool, flip_bool];
    if i < 2 && j < 2 {
        let outer = [inner[i], identity_bool as fn(bool) -> bool];
        assert!(outer[j](value) == value);
    }
}
pub fn opaque_bool(i: usize, j: usize, value: bool, opaque: fn(bool) -> bool) {
    let inner = [identity_bool as fn(bool) -> bool, opaque];
    if i < 2 && j < 2 {
        let outer = [inner[i]; 2];
        assert!(outer[j](value) == value);
    }
}
#[inline(never)]
fn char_first(value: char) -> char {
    value
}
#[inline(never)]
fn char_second(value: char) -> char {
    if value == 'a' { 'b' } else { value }
}
pub fn nested_char(i: usize, j: usize, value: char) {
    let inner: [fn(char) -> char; 2] = [char_first, char_second];
    if i < 2 && j < 2 {
        let outer = [inner[i], char_first as fn(char) -> char];
        let expected = if i == 1 && j == 0 && value == 'a' {
            'b'
        } else {
            value
        };
        assert!(outer[j](value) == expected);
    }
}

#[inline(never)]
fn first_u8(value: u8) -> u8 {
    value
}
#[inline(never)]
fn second_u8(value: u8) -> u8 {
    value ^ 1
}
pub fn nested_u8(i: usize, j: usize, value: u8) {
    let inner: [fn(u8) -> u8; 2] = [first_u8, second_u8];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_u8 as fn(u8) -> u8];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_u16(value: u16) -> u16 {
    value
}
#[inline(never)]
fn second_u16(value: u16) -> u16 {
    value ^ 1
}
pub fn nested_u16(i: usize, j: usize, value: u16) {
    let inner: [fn(u16) -> u16; 2] = [first_u16, second_u16];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_u16 as fn(u16) -> u16];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_u32(value: u32) -> u32 {
    value
}
#[inline(never)]
fn second_u32(value: u32) -> u32 {
    value ^ 1
}
pub fn nested_u32(i: usize, j: usize, value: u32) {
    let inner: [fn(u32) -> u32; 2] = [first_u32, second_u32];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_u32 as fn(u32) -> u32];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_u64(value: u64) -> u64 {
    value
}
#[inline(never)]
fn second_u64(value: u64) -> u64 {
    value ^ 1
}
pub fn nested_u64(i: usize, j: usize, value: u64) {
    let inner: [fn(u64) -> u64; 2] = [first_u64, second_u64];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_u64 as fn(u64) -> u64];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_u128(value: u128) -> u128 {
    value
}
#[inline(never)]
fn second_u128(value: u128) -> u128 {
    value ^ 1
}
pub fn nested_u128(i: usize, j: usize, value: u128) {
    let inner: [fn(u128) -> u128; 2] = [first_u128, second_u128];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_u128 as fn(u128) -> u128];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_usize(value: usize) -> usize {
    value
}
#[inline(never)]
fn second_usize(value: usize) -> usize {
    value ^ 1
}
pub fn nested_usize(i: usize, j: usize, value: usize) {
    let inner: [fn(usize) -> usize; 2] = [first_usize, second_usize];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_usize as fn(usize) -> usize];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_i8(value: i8) -> i8 {
    value
}
#[inline(never)]
fn second_i8(value: i8) -> i8 {
    value ^ 1
}
pub fn nested_i8(i: usize, j: usize, value: i8) {
    let inner: [fn(i8) -> i8; 2] = [first_i8, second_i8];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_i8 as fn(i8) -> i8];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_i16(value: i16) -> i16 {
    value
}
#[inline(never)]
fn second_i16(value: i16) -> i16 {
    value ^ 1
}
pub fn nested_i16(i: usize, j: usize, value: i16) {
    let inner: [fn(i16) -> i16; 2] = [first_i16, second_i16];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_i16 as fn(i16) -> i16];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_i32(value: i32) -> i32 {
    value
}
#[inline(never)]
fn second_i32(value: i32) -> i32 {
    value ^ 1
}
pub fn nested_i32(i: usize, j: usize, value: i32) {
    let inner: [fn(i32) -> i32; 2] = [first_i32, second_i32];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_i32 as fn(i32) -> i32];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_i64(value: i64) -> i64 {
    value
}
#[inline(never)]
fn second_i64(value: i64) -> i64 {
    value ^ 1
}
pub fn nested_i64(i: usize, j: usize, value: i64) {
    let inner: [fn(i64) -> i64; 2] = [first_i64, second_i64];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_i64 as fn(i64) -> i64];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_i128(value: i128) -> i128 {
    value
}
#[inline(never)]
fn second_i128(value: i128) -> i128 {
    value ^ 1
}
pub fn nested_i128(i: usize, j: usize, value: i128) {
    let inner: [fn(i128) -> i128; 2] = [first_i128, second_i128];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_i128 as fn(i128) -> i128];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_isize(value: isize) -> isize {
    value
}
#[inline(never)]
fn second_isize(value: isize) -> isize {
    value ^ 1
}
pub fn nested_isize(i: usize, j: usize, value: isize) {
    let inner: [fn(isize) -> isize; 2] = [first_isize, second_isize];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_isize as fn(isize) -> isize];
        assert!(outer[j](value) == value ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}

#[inline(never)]
fn first_f32(value: f32) -> f32 {
    value
}
#[inline(never)]
fn second_f32(value: f32) -> f32 {
    -value
}
pub fn nested_f32(i: usize, j: usize, value: f32) {
    let inner: [fn(f32) -> f32; 2] = [first_f32, second_f32];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_f32 as fn(f32) -> f32];
        assert!(
            outer[j](value).to_bits()
                == value.to_bits() ^ if i == 1 && j == 0 { 0x8000_0000_u32 } else { 0 }
        );
    }
}

#[inline(never)]
fn first_f64(value: f64) -> f64 {
    value
}
#[inline(never)]
fn second_f64(value: f64) -> f64 {
    -value
}
pub fn nested_f64(i: usize, j: usize, value: f64) {
    let inner: [fn(f64) -> f64; 2] = [first_f64, second_f64];
    if i < 2 && j < 2 {
        let outer = [inner[i], first_f64 as fn(f64) -> f64];
        assert!(
            outer[j](value).to_bits()
                == value.to_bits()
                    ^ if i == 1 && j == 0 {
                        0x8000_0000_0000_0000_u64
                    } else {
                        0
                    }
        );
    }
}

#[inline(never)]
fn pair_first(a: i128, b: u8) -> u16 {
    (a as u16) ^ (b as u16)
}
#[inline(never)]
fn pair_second(a: i128, b: u8) -> u16 {
    pair_first(a, b) ^ 1
}
pub fn nested_pair(i: usize, j: usize, a: i128, b: u8) {
    let inner: [fn(i128, u8) -> u16; 2] = [pair_first, pair_second];
    if i < 2 && j < 2 {
        let outer = [inner[i], pair_first as fn(i128, u8) -> u16];
        assert!(outer[j](a, b) == ((a as u16) ^ (b as u16)) ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}
pub fn repeat_bool_once(i: usize, j: usize, value: bool) {
    let inner: [fn(bool) -> bool; 2] = [identity_bool, flip_bool];
    if i < 2 && j < 2 {
        let outer = [inner[i]; 2];
        assert!(outer[j](value) == if i == 1 { !value } else { value });
    }
}
#[inline(never)]
fn pair_direct(a: i128, b: u8) -> u16 {
    ((a as u16) ^ (b as u16)) ^ 1
}
pub fn nested_pair_direct(i: usize, j: usize, a: i128, b: u8) {
    let inner: [fn(i128, u8) -> u16; 2] = [pair_first, pair_direct];
    if i < 2 && j < 2 {
        let outer = [inner[i], pair_first as fn(i128, u8) -> u16];
        assert!(outer[j](a, b) == ((a as u16) ^ (b as u16)) ^ if i == 1 && j == 0 { 1 } else { 0 });
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn original_correlation() {
        for i in 0..3 {
            for j in 0..3 {
                super::nested_bool(i, j, false);
                super::repeat_bool(i, j, true);
                super::repeat_bool_once(i, j, false);
                super::nested_char(i, j, 'a');
                super::nested_i128(i, j, -17);
                super::nested_u128(i, j, 129);
                super::nested_pair(i, j, -13, 11);
                super::nested_pair_direct(i, j, -13, 11);
                super::nested_f32(i, j, f32::from_bits(0x7fc0_1234));
                super::nested_f64(i, j, f64::from_bits(0x8000_0000_0000_0000));
            }
        }
    }
}
