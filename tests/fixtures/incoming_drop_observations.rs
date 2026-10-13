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
pub fn accessor(value: &u16) -> u16 {
    *value
}
pub fn borrowed(values: [Record; 2], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(accessor(&selected.word) == selected.word);
        assert!(accessor(&selected.guard) == selected.guard);
    }
}
pub fn direct(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(accessor(&values[index].word) == values[index].word);
    }
}
pub fn nested(values: [[Record; 1]; 2], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(accessor(&selected[0].word) == selected[0].word);
    }
}
pub fn wrong(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(accessor(&values[index].word) == (values[index].word ^ 1));
    }
}
pub fn unguarded(values: [Record; 2], index: usize) {
    assert!(accessor(&values[index].word) == values[index].word);
}
#[inline(never)]
pub fn whole(value: &Record) -> u16 {
    value.word
}
pub fn whole_unknown(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(whole(&values[index]) == values[index].word);
    }
}
#[inline(never)]
pub fn store(value: &mut u16) {
    *value = 19;
}
pub fn mutable_unknown(mut values: [Record; 2], index: usize) {
    if index < 2 {
        store(&mut values[index].word);
        assert!(values[index].word == 19);
    }
}
#[inline(never)]
pub fn pointer_is_null(value: *const u16) -> bool {
    value.is_null()
}
pub fn raw_unknown(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(!pointer_is_null(&raw const values[index].word));
    }
}
pub fn reserved(values: [Record; 64], _second: [Record; 64], _third: [Record; 64], index: usize) {
    if index < 64 {
        let selected = &values[index];
        assert!(accessor(&selected.word) == selected.word);
    }
}

pub fn deferred(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(accessor(&selected.word) == selected.word);
    }
}


pub fn reserved_constant(values: [Record; 64], _second: [Record; 64], _third: [Record; 64]) {
    assert!(accessor(&values[1].word) == values[1].word);
}
pub fn reserved_wrong(values: [Record; 64], _second: [Record; 64], _third: [Record; 64]) {
    assert!(accessor(&values[1].word) == (values[1].word ^ 1));
}
pub fn deferred_wrong(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
    if index < 2 {
        assert!(accessor(&values[index].word) == (values[index].word ^ 1));
    }
}
pub fn deferred_unguarded(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
    assert!(accessor(&values[index].word) == values[index].word);
}


pub struct ScalarRecord {
    pub flag: bool,
    pub signed: i32,
    pub float: f32,
    pub wide: f64,
}
#[inline(never)]
pub fn signed_guard(value: i32) -> i32 { value }
impl Drop for ScalarRecord {
    fn drop(&mut self) { assert!(signed_guard(self.signed) == self.signed); }
}
#[inline(never)]
pub fn bool_accessor(value: &bool) -> bool { *value }
#[inline(never)]
pub fn signed_accessor(value: &i32) -> i32 { *value }
#[inline(never)]
pub fn float_accessor(value: &f32) -> f32 { *value }
#[inline(never)]
pub fn wide_accessor(value: &f64) -> f64 { *value }
pub fn scalar_codecs(values: [ScalarRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(bool_accessor(&selected.flag) == selected.flag);
        assert!(signed_accessor(&selected.signed) == selected.signed);
        assert!(float_accessor(&selected.float).to_bits() == selected.float.to_bits());
        assert!(wide_accessor(&selected.wide).to_bits() == selected.wide.to_bits());
    }
}
pub fn scalar_wrong(values: [ScalarRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(float_accessor(&selected.float).to_bits() == (selected.float.to_bits() ^ 1));
    }
}
pub struct CharRecord { pub scalar: char }
impl Drop for CharRecord {
    fn drop(&mut self) { assert!(self.scalar <= char::MAX); }
}
pub fn char_eager_pressure(values: [CharRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
    if index < 2 { assert!(values[index].scalar <= char::MAX); }
}
#[cfg(test)]
mod native_controls {
    #[test]
    fn actual_accessor_and_destructor() {
        let record = super::Record { word: 3, guard: 7 };
        assert!(super::accessor(&record.word) == 3);
    }
}
