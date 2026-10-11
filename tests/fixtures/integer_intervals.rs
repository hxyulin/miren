#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn replacement_i32(word: i32) -> i32 { word ^ 0 }
#[inline(never)]
pub fn replacement_usize(word: usize) -> usize { word ^ 0 }
#[inline(never)]
pub fn child_i32(values: &mut [i32], word: i32) { values[0] = replacement_i32(word); }
#[inline(never)]
pub fn child_usize(values: &mut [usize], word: usize) {
    values[0] = replacement_usize(word);
}
#[inline(never)]
pub fn child_u16(values: &mut [u16], word: u16) { values[0] = word; }
#[inline(never)]
pub fn empty_i32(values: &mut [i32]) { assert!(values.len() == 0); }
#[inline(never)]
pub fn empty_usize(values: &mut [usize]) { assert!(values.len() == 0); }
#[inline(never)]
pub fn empty_u16(values: &mut [u16]) { assert!(values.len() == 0); }

pub fn i32_range(values: &mut [i32], start: usize, end: usize, word: i32) {
    if start < end && end <= values.len() {
        child_i32(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn i32_sibling(values: &mut [i32], start: usize, end: usize, other: usize, word: i32) {
    if start < end && end <= values.len() && other < values.len() && other < start {
        let old = values[other];
        child_i32(&mut values[start..end], word);
        assert!(values[start] == word && values[other] == old);
    }
}
pub fn i32_empty(values: &mut [i32], at: usize) {
    if at <= values.len() { empty_i32(&mut values[at..at]); }
}
pub fn i32_wrong(values: &mut [i32], start: usize, end: usize, word: i32) {
    if start < end && end <= values.len() {
        child_i32(&mut values[start..end], word);
        assert!(values[start] != word);
    }
}
pub fn i32_bounds(values: &mut [i32], start: usize, end: usize, word: i32) {
    child_i32(&mut values[start..end], word);
}
pub fn usize_range(values: &mut [usize], start: usize, end: usize, word: usize) {
    if start < end && end <= values.len() {
        child_usize(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn usize_sibling(
    values: &mut [usize], start: usize, end: usize, other: usize, word: usize,
) {
    if start < end && end <= values.len() && other < values.len() && other < start {
        let old = values[other];
        child_usize(&mut values[start..end], word);
        assert!(values[start] == word && values[other] == old);
    }
}
pub fn usize_empty(values: &mut [usize], at: usize) {
    if at <= values.len() { empty_usize(&mut values[at..at]); }
}
pub fn usize_wrong(values: &mut [usize], start: usize, end: usize, word: usize) {
    if start < end && end <= values.len() {
        child_usize(&mut values[start..end], word);
        assert!(values[start] != word);
    }
}
pub fn u16_range(values: &mut [u16], start: usize, end: usize, word: u16) {
    if start < end && end <= values.len() {
        child_u16(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn u16_sibling(values: &mut [u16], start: usize, end: usize, other: usize, word: u16) {
    if start < end && end <= values.len() && other < values.len() && other < start {
        let old = values[other];
        child_u16(&mut values[start..end], word);
        assert!(values[start] == word && values[other] == old);
    }
}
pub fn u16_empty(values: &mut [u16], at: usize) {
    if at <= values.len() { empty_u16(&mut values[at..at]); }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn proper_ranges() {
        for start in 1..129 {
            for word in [i32::MIN, -1, 0, 1, i32::MAX] {
                i32_range(&mut [0; 129], start, 129, word);
                i32_sibling(&mut [7; 129], start, 129, 0, word);
            }
            for word in [0, 1, usize::MAX] {
                usize_range(&mut [0; 129], start, 129, word);
                usize_sibling(&mut [7; 129], start, 129, 0, word);
            }
            u16_range(&mut [0; 129], start, 129, u16::MAX);
            u16_sibling(&mut [7; 129], start, 129, 0, u16::MAX);
        }
        for at in [0, 64, 129] {
            i32_empty(&mut [0; 129], at);
            usize_empty(&mut [0; 129], at);
            u16_empty(&mut [0; 129], at);
        }
        i32_empty(&mut [], 0);
        usize_empty(&mut [], 0);
        u16_empty(&mut [], 0);
    }
}
