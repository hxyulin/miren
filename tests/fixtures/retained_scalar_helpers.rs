#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn flip(word: u16) -> u16 {
    let mask = 1;
    let first = word ^ mask;
    let second = first ^ 0;
    let third = second ^ 0;
    let fourth = third ^ 0;
    let result = fourth ^ 0;
    result
}

pub fn scalar(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}

pub fn product(values: &mut [[f32; 2]], word: u16) {
    if values.len() >= 2 {
        let old = values[1][0].to_bits();
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let mapped = flip(word);
            assert!(mapped == word ^ 1);
            child[0][0] = 1.0;
        }
        assert!(values[0][0] == 1.0);
        assert!(values[1][0].to_bits() == old);
    }
}

pub fn wrong(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = flip(word);
        assert!(child[0] == word);
    }
}

#[inline(never)]
fn nested_flip(word: u16) -> u16 {
    flip(word)
}
pub fn nested_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = nested_flip(word);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn helper_results_and_parent_sibling_storage() {
        let mut scalars = [0, 7];
        super::scalar(&mut scalars, 14);
        assert!(scalars == [15, 7]);
        let mut products = [[3.0, 4.0], [5.0, 6.0]];
        super::product(&mut products, 14);
        assert!(products == [[1.0, 4.0], [5.0, 6.0]]);
        for value in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            super::character(&mut scalars, value);
        }
        super::boolean(&mut scalars, false);
        super::boolean(&mut scalars, true);
        for raw in [0, 0x8000_0000, 0x7fc0_0042] {
            let value = f32::from_bits(raw);
            super::float32(&mut scalars, value);
            assert!(super::id_f32(value).to_bits() == raw);
        }
        for raw in [0, 0x8000_0000_0000_0000, 0x7ff8_0000_0000_0042] {
            let value = f64::from_bits(raw);
            super::float64(&mut scalars, value);
            assert!(super::id_f64(value).to_bits() == raw);
        }
        super::unit(&mut scalars);
        super::associated(&mut scalars, 14);
        super::mixed(&mut scalars, false, i32::MIN, i32::MAX);
        super::mixed(&mut scalars, true, i32::MIN, i32::MAX);
        super::integer_i8(&mut scalars, i8::MIN);
        super::integer_i16(&mut scalars, i16::MIN);
        super::integer_i32(&mut scalars, i32::MIN);
        super::integer_i64(&mut scalars, i64::MIN);
        super::integer_i128(&mut scalars, i128::MIN);
        super::integer_isize(&mut scalars, isize::MIN);
        super::integer_u8(&mut scalars, u8::MAX);
        super::integer_u16(&mut scalars, u16::MAX);
        super::integer_u32(&mut scalars, u32::MAX);
        super::integer_u64(&mut scalars, u64::MAX);
        super::integer_u128(&mut scalars, u128::MAX);
        super::integer_usize(&mut scalars, usize::MAX);
    }
}

macro_rules! identity_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        #[inline(never)]
        pub fn $helper(value: $ty) -> $ty { value }
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
identity_case!(id_u8, integer_u8, u8);
identity_case!(id_u16, integer_u16, u16);
identity_case!(id_u32, integer_u32, u32);
identity_case!(id_u64, integer_u64, u64);
identity_case!(id_u128, integer_u128, u128);
identity_case!(id_usize, integer_usize, usize);
identity_case!(id_i8, integer_i8, i8);
identity_case!(id_i16, integer_i16, i16);
identity_case!(id_i32, integer_i32, i32);
identity_case!(id_i64, integer_i64, i64);
identity_case!(id_i128, integer_i128, i128);
identity_case!(id_isize, integer_isize, isize);
identity_case!(id_bool, boolean, bool);
identity_case!(id_char, character, char);

#[inline(never)]
pub fn id_f32(value: f32) -> f32 { value }
#[inline(never)]
pub fn id_f64(value: f64) -> f64 { value }
macro_rules! float_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value || value != value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
float_case!(id_f32, float32, f32);
float_case!(id_f64, float64, f64);
#[inline(never)]
pub fn id_unit(value: ()) { value }
pub fn unit(values: &mut [u16]) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            id_unit(());
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}

#[inline(never)]
pub fn guarded(word: u16) -> u16 { word ^ 1 }
pub fn contract_positive(values: &mut [u16], word: u16) {
    if !values.is_empty() && word < 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
        assert!(child[0] == word ^ 1);
    }
}
pub fn contract_negative(values: &mut [u16], word: u16) {
    if !values.is_empty() && word >= 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
    }
}


pub struct Associated;
impl Associated {
    #[inline(never)]
    pub fn flip(value: u16) -> u16 { value ^ 1 }
}
pub fn associated(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = Associated::flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}
#[inline(never)]
pub fn choose(flag: bool, left: i32, right: i32) -> i32 {
    if flag { left } else { right }
}
pub fn mixed(values: &mut [u16], flag: bool, left: i32, right: i32) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let value = choose(flag, left, right);
            assert!(if flag { value == left } else { value == right });
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}
