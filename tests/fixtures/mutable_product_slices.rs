#![no_std]
#![forbid(unsafe_code)]

pub fn metadata32(values: &mut [[f32; 2]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

pub fn metadata64(values: &mut [[f64; 2]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

pub fn wrong_metadata(values: &mut [[f32; 2]]) {
    let length = values.len();
    assert!(values.is_empty() != (length == 0));
}

#[inline(never)]
pub fn observe_bits(value: f32) -> u32 {
    value.to_bits()
}

pub fn copied_helper(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        let value = values[index][0];
        assert!(observe_bits(value) == value.to_bits());
    }
}

#[inline(never)]
pub fn stored_word() -> f32 {
    f32::from_bits(0x7fc0_1234)
}

pub fn store_nan(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        let untouched = values[index][1].to_bits();
        values[index][0] = stored_word();
        assert!(values[index][0].to_bits() == 0x7fc0_1234);
        assert!(values[index][1].to_bits() == untouched);
    }
}

pub fn wrong_stored_bits(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        values[index][0] = stored_word();
        assert!(values[index][0].to_bits() == 0x7fc0_1235);
    }
}

pub fn wrong_untouched_leaf(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        let untouched = values[index][1].to_bits();
        values[index][0] = stored_word();
        assert!(values[index][1].to_bits() != untouched);
    }
}

pub fn whole64(values: &mut [[f64; 2]], index: usize) {
    if index < values.len() {
        values[index] = [-0.0, f64::from_bits(0x7ff8_0000_0000_1234)];
        assert!(values[index][0].to_bits() == 0x8000_0000_0000_0000);
        assert!(values[index][1].to_bits() == 0x7ff8_0000_0000_1234);
    }
}

pub fn outer_retention(values: &mut [[f32; 2]]) {
    if values.len() >= 2 {
        let untouched = values[1][0].to_bits();
        values[0][0] = stored_word();
        assert!(values[0][0].to_bits() == 0x7fc0_1234);
        assert!(values[1][0].to_bits() == untouched);
    }
}

pub fn unguarded(values: &mut [[f32; 2]], index: usize) {
    let _ = values[index][0].to_bits();
}

pub fn integer_pair(values: &mut [[u16; 2]], index: usize) {
    if index < values.len() {
        let untouched = values[index][1];
        values[index][0] = 42;
        assert!(values[index][0] == 42 && values[index][1] == untouched);
    }
}

pub fn tuple_pair(values: &mut [(bool, char)], index: usize) {
    if index < values.len() {
        values[index] = (true, '\u{10ffff}');
        assert!(values[index].0 && values[index].1 as u32 == 0x10ffff);
    }
}

#[derive(Clone, Copy)]
pub struct Reading {
    pub number: u16,
    pub ready: bool,
    pub character: char,
    pub temperature: f64,
}

pub fn struct_fields(values: &mut [Reading], index: usize, word: f64) {
    if index < values.len() {
        let number = values[index].number;
        values[index].temperature = -word;
        values[index].ready = true;
        values[index].character = '\u{1f980}';
        assert!(values[index].temperature.to_bits() == (-word).to_bits());
        assert!(values[index].ready && values[index].character as u32 == 0x1f980);
        assert!(values[index].number == number);
    }
}

pub fn zero_inner(values: &mut [[f32; 0]], index: usize) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
    if index < values.len() {
        values[index] = [];
    }
}

pub fn proper_reborrow(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
    }
}

#[inline(never)]
pub fn owner_child(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        values[0][0] = stored_word();
    }
}

pub fn unsupported_child(values: &mut [[f32; 2]]) {
    owner_child(values);
}

pub fn symbolic_suffix(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        values[outer][inner] = stored_word();
    }
}

pub fn pointer_product(values: &mut [[*const u8; 2]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

pub fn reference_product(values: &mut [[&u16; 2]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

pub fn niche_product(values: &mut [[Option<core::num::NonZeroU8>; 2]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

pub fn oversized(values: &mut [[f32; 129]]) {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
}

#[cfg(test)]
mod native {
    #[test]
    fn copied_helper_claims() {
        for bits in [0, 0x8000_0000, 0x7fc0_4567, 0x7f80_0000, 0xff80_0000] {
            let mut values = [[f32::from_bits(bits), 3.0], [4.0, -0.0]];
            super::copied_helper(&mut values, 0);
            super::copied_helper(&mut values, 1);
        }
    }

    #[test]
    fn actual_store_claims() {
        let mut values = [[1.0_f32, -0.0], [f32::from_bits(0x7fc0_4567), 3.0]];
        super::store_nan(&mut values, 0);
        super::store_nan(&mut values, 1);
        super::outer_retention(&mut values);
        let mut wide = [[1.0_f64, 2.0]];
        super::whole64(&mut wide, 0);
        assert_eq!(wide[0][0].to_bits(), 0x8000_0000_0000_0000);
        let mut pair = [(false, 'a')];
        super::tuple_pair(&mut pair, 0);
        let mut readings = [super::Reading {
            number: 7,
            ready: false,
            character: 'a',
            temperature: 1.0,
        }];
        super::struct_fields(&mut readings, 0, -0.0);
        assert_eq!(readings[0].number, 7);
        let mut zero = [[]; 2];
        super::zero_inner(&mut zero, 1);
        super::metadata32(&mut []);
        super::metadata64(&mut wide);
    }
}
