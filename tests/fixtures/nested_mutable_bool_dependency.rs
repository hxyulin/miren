#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn scalar(word: bool) -> bool { word ^ false }
#[inline(never)]
pub fn leaf(values: &mut [bool], word: bool) {
    if values.len() > 0 { values[0] = scalar(word); }
}
#[inline(never)]
pub fn outer(values: &mut [bool], word: bool) -> bool {
    leaf(&mut *(&mut *values), word);
    scalar(word)
}
