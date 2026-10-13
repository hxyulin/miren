#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn payload_u16(word: u16) -> u16 {
    word
}
#[inline(never)]
pub fn leaf_u16(values: &mut [u16], index: usize, word: u16) {
    values[index] = payload_u16(word);
}
#[inline(never)]
pub fn level1_u16(values: &mut [u16], index: usize, word: u16) {
    leaf_u16(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_u16(values: &mut [u16], index: usize, word: u16) {
    level1_u16(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_u16(values: &mut [u16], index: usize, word: u16) {
    level2_u16(&mut *(&mut *values), index, word);
}
pub fn claim_u16(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        let old_length = values.len();
        level3_u16(values, index, word);
        assert!(values[index] == word);
        assert!(values.len() == old_length);
    }
}
pub fn wrong_u16(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        level3_u16(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn payload_i32(word: i32) -> i32 {
    word
}
#[inline(never)]
pub fn leaf_i32(values: &mut [i32], index: usize, word: i32) {
    values[index] = payload_i32(word);
}
#[inline(never)]
pub fn level1_i32(values: &mut [i32], index: usize, word: i32) {
    leaf_i32(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_i32(values: &mut [i32], index: usize, word: i32) {
    level1_i32(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_i32(values: &mut [i32], index: usize, word: i32) {
    level2_i32(&mut *(&mut *values), index, word);
}
pub fn claim_i32(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        let old_length = values.len();
        level3_i32(values, index, word);
        assert!(values[index] == word);
        assert!(values.len() == old_length);
    }
}
pub fn wrong_i32(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        level3_i32(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn payload_bool(word: bool) -> bool {
    word
}
#[inline(never)]
pub fn leaf_bool(values: &mut [bool], index: usize, word: bool) {
    values[index] = payload_bool(word);
}
#[inline(never)]
pub fn level1_bool(values: &mut [bool], index: usize, word: bool) {
    leaf_bool(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_bool(values: &mut [bool], index: usize, word: bool) {
    level1_bool(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_bool(values: &mut [bool], index: usize, word: bool) {
    level2_bool(&mut *(&mut *values), index, word);
}
pub fn claim_bool(values: &mut [bool], index: usize, word: bool) {
    if index < values.len() {
        let old_length = values.len();
        level3_bool(values, index, word);
        assert!(values[index] == word);
        assert!(values.len() == old_length);
    }
}
pub fn wrong_bool(values: &mut [bool], index: usize, word: bool) {
    if index < values.len() {
        level3_bool(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn payload_char(word: char) -> char {
    word
}
#[inline(never)]
pub fn leaf_char(values: &mut [char], index: usize, word: char) {
    values[index] = payload_char(word);
}
#[inline(never)]
pub fn level1_char(values: &mut [char], index: usize, word: char) {
    leaf_char(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_char(values: &mut [char], index: usize, word: char) {
    level1_char(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_char(values: &mut [char], index: usize, word: char) {
    level2_char(&mut *(&mut *values), index, word);
}
pub fn claim_char(values: &mut [char], index: usize, word: char) {
    if index < values.len() {
        let old_length = values.len();
        level3_char(values, index, word);
        assert!(values[index] == word);
        assert!(values.len() == old_length);
    }
}
pub fn wrong_char(values: &mut [char], index: usize, word: char) {
    if index < values.len() {
        level3_char(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn payload_f32(word: f32) -> f32 {
    word
}
#[inline(never)]
pub fn leaf_f32(values: &mut [f32], index: usize, word: f32) {
    values[index] = payload_f32(word);
}
#[inline(never)]
pub fn level1_f32(values: &mut [f32], index: usize, word: f32) {
    leaf_f32(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_f32(values: &mut [f32], index: usize, word: f32) {
    level1_f32(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_f32(values: &mut [f32], index: usize, word: f32) {
    level2_f32(&mut *(&mut *values), index, word);
}
pub fn claim_f32(values: &mut [f32], index: usize, word: f32) {
    if index < values.len() {
        let old_length = values.len();
        level3_f32(values, index, word);
        assert!(values[index].to_bits() == word.to_bits());
        assert!(values.len() == old_length);
    }
}
pub fn wrong_f32(values: &mut [f32], index: usize, word: f32) {
    if index < values.len() {
        level3_f32(values, index, word);
        assert!(values[index].to_bits() != word.to_bits());
    }
}

#[inline(never)]
pub fn payload_f64(word: f64) -> f64 {
    word
}
#[inline(never)]
pub fn leaf_f64(values: &mut [f64], index: usize, word: f64) {
    values[index] = payload_f64(word);
}
#[inline(never)]
pub fn level1_f64(values: &mut [f64], index: usize, word: f64) {
    leaf_f64(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level2_f64(values: &mut [f64], index: usize, word: f64) {
    level1_f64(&mut *(&mut *values), index, word);
}
#[inline(never)]
pub fn level3_f64(values: &mut [f64], index: usize, word: f64) {
    level2_f64(&mut *(&mut *values), index, word);
}
pub fn claim_f64(values: &mut [f64], index: usize, word: f64) {
    if index < values.len() {
        let old_length = values.len();
        level3_f64(values, index, word);
        assert!(values[index].to_bits() == word.to_bits());
        assert!(values.len() == old_length);
    }
}
pub fn wrong_f64(values: &mut [f64], index: usize, word: f64) {
    if index < values.len() {
        level3_f64(values, index, word);
        assert!(values[index].to_bits() != word.to_bits());
    }
}

pub struct Associated;
impl Associated {
    #[inline(never)]
    pub fn payload(word: u16) -> u16 {
        word
    }
    #[inline(never)]
    pub fn leaf(values: &mut [u16], index: usize, word: u16) {
        values[index] = Self::payload(word);
    }
    #[inline(never)]
    pub fn level1(values: &mut [u16], index: usize, word: u16) {
        Self::leaf(&mut *values, index, word);
    }
    #[inline(never)]
    pub fn level2(values: &mut [u16], index: usize, word: u16) {
        Self::level1(&mut *values, index, word);
    }
    #[inline(never)]
    pub fn level3(values: &mut [u16], index: usize, word: u16) {
        Self::level2(&mut *values, index, word);
    }
}
pub fn claim_associated(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        Associated::level3(values, index, word);
        assert!(values[index] == word);
    }
}
pub fn wrong_associated(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        Associated::level3(values, index, word);
        assert!(values[index] != word);
    }
}
pub fn sibling_retention(values: &mut [i32], word: i32) {
    if values.len() > 1 {
        let sibling = values[1];
        level3_i32(values, 0, word);
        assert!(values[0] == word);
        assert!(values[1] == sibling);
    }
}
pub fn unchecked_bounds(values: &mut [u16], index: usize, word: u16) {
    level3_u16(values, index, word);
}
pub fn interval_unknown(values: &mut [u16], start: usize, end: usize, word: u16) {
    if start <= end && end <= values.len() && start < end {
        level3_u16(&mut values[start..end], 0, word);
    }
}
#[inline(never)]
pub fn product_leaf(values: &mut [[u16; 2]], word: u16) {
    values[0][0] = word;
}
#[inline(never)]
pub fn product_outer(values: &mut [[u16; 2]], word: u16) {
    product_leaf(values, word);
}
pub fn product_unknown(values: &mut [[u16; 2]], word: u16) {
    if !values.is_empty() {
        product_outer(values, word);
    }
}
// A compiler probe enters this actual call and follows all normal Frames/Returns.
pub fn probe_root(values: &mut [u16]) {
    probe_level3(values);
}
#[inline(never)]
pub fn probe_level3(values: &mut [u16]) {
    probe_level2(values);
}
#[inline(never)]
pub fn probe_level2(values: &mut [u16]) {
    probe_level1(values);
}
#[inline(never)]
pub fn probe_level1(values: &mut [u16]) {
    probe_leaf(values);
}
#[inline(never)]
pub fn probe_leaf(values: &mut [u16]) {
    if !values.is_empty() {
        values[0] = 37;
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn actual_deep_helpers_preserve_original_claims() {
        for index in [0, 1, 2, usize::MAX] {
            super::claim_u16(&mut [0; 2], index, 37);
        }
        for index in [0, 1, 2, usize::MAX] {
            super::claim_i32(&mut [0; 2], index, -19);
        }
        for index in [0, 1, 2, usize::MAX] {
            super::claim_bool(&mut [false; 2], index, true);
        }
        for index in [0, 1, 2, usize::MAX] {
            super::claim_char(&mut ['\0'; 2], index, 'λ');
        }
        for index in [0, 1, 2, usize::MAX] {
            super::claim_f32(&mut [0.0_f32; 2], index, f32::from_bits(0x7fc0_1234));
        }
        for index in [0, 1, 2, usize::MAX] {
            super::claim_f64(
                &mut [0.0_f64; 2],
                index,
                f64::from_bits(0x7ff8_0000_0000_1234),
            );
        }
        super::claim_associated(&mut [0; 2], 1, 37);
        super::sibling_retention(&mut [1, 2, 3], -19);
    }
}
