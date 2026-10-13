#![no_std]
#![forbid(unsafe_code)]

pub struct Record {
    pub word: u16,
    pub guard: u16,
}
#[inline(never)]
pub fn release_guard(value: u16) -> u16 {
    value
}
impl Drop for Record {
    fn drop(&mut self) {
        assert!(release_guard(self.guard) == self.guard);
    }
}
#[inline(never)]
pub fn word(value: &u16) -> u16 {
    *value
}
#[inline(never)]
pub fn observe(value: &Record) -> u16 {
    word(&value.word)
}
pub fn claim(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(observe(&values[index]) == values[index].word);
    }
}
pub fn wrong(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(observe(&values[index]) == (values[index].word ^ 1));
    }
}
pub fn unguarded(values: [Record; 2], index: usize) {
    assert!(observe(&values[index]) == values[index].word);
}
#[inline(never)]
pub fn forward(value: &Record) -> u16 {
    observe(&*value)
}
pub fn forwarded(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(forward(&values[index]) == values[index].word);
    }
}
pub fn lazy(values: [Record; 64], _second: [Record; 64], _third: [Record; 64], index: usize) {
    if index < 64 {
        assert!(observe(&values[index]) == values[index].word);
    }
}
#[inline(never)]
pub fn store(value: &mut Record) -> u16 {
    value.word = 19;
    value.word
}
pub fn mutable_unknown(mut values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(store(&mut values[index]) == 19);
    }
}
#[inline(never)]
pub fn pointer_is_null(value: *const Record) -> bool {
    value.is_null()
}
pub fn raw_unknown(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(!pointer_is_null(&raw const values[index]));
    }
}
#[inline(never)]
pub fn product(value: &Record) -> [u16; 2] {
    [value.word, value.guard]
}
pub fn product_unknown(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(product(&values[index])[0] == values[index].word);
    }
}
pub struct Other {
    pub word: u16,
    pub guard: u16,
}
impl Drop for Other {
    fn drop(&mut self) {
        assert!(release_guard(self.guard) == self.guard);
    }
}
#[inline(never)]
pub fn other_observe(value: &Other) -> u16 {
    value.word
}

pub struct Codecs {
    pub guard: u16,
    pub flag: bool,
    pub letter: char,
    pub signed: i32,
    pub float: f32,
    pub wide: f64,
}
impl Drop for Codecs {
    fn drop(&mut self) {
        assert!(release_guard(self.guard) == self.guard);
    }
}
#[inline(never)]
pub fn flag(value: &Codecs) -> bool {
    value.flag
}
#[inline(never)]
pub fn letter(value: &Codecs) -> char {
    value.letter
}
#[inline(never)]
pub fn signed(value: &Codecs) -> i32 {
    value.signed
}
#[inline(never)]
pub fn float(value: &Codecs) -> f32 {
    value.float
}
#[inline(never)]
pub fn wide(value: &Codecs) -> f64 {
    value.wide
}
pub fn codecs(values: [Codecs; 2], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(flag(selected) == selected.flag);
        assert!(letter(selected) == selected.letter);
        assert!(signed(selected) == selected.signed);
        assert!(float(selected).to_bits() == selected.float.to_bits());
        assert!(wide(selected).to_bits() == selected.wide.to_bits());
    }
}
#[cfg(test)]
mod native_controls {
    #[test]
    fn actual_helper_and_destructor() {
        let value = super::Record { word: 3, guard: 7 };
        assert!(super::observe(&value) == 3);
    }
}
