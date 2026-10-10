#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn replacement(value: char) -> char {
    if value == 'A' { 'B' } else { 'A' }
}
#[inline(never)]
pub fn child(values: &mut [char], index: usize, value: char) {
    values[index] = replacement(value);
}
pub fn selected(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        child(values, index, value);
        assert!(values[index] == if value == 'A' { 'B' } else { 'A' });
    }
}
pub fn direct(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        values[index] = value;
        assert!(values[index] == value);
    }
}
pub fn untouched(values: &mut [char], index: usize, other: usize, value: char) {
    if index < values.len() && other < values.len() && index != other {
        let old = values[other];
        child(values, index, value);
        assert!(values[other] == old);
    }
}
pub fn sequential(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        child(values, index, value);
        child(values, index, 'A');
        assert!(values[index] == 'B');
    }
}
pub fn branches(values: &mut [char], index: usize, value: char, flag: bool) {
    if index < values.len() {
        let next = if flag {
            value
        } else {
            if value == 'A' { 'B' } else { 'A' }
        };
        values[index] = next;
        assert!(values[index] == next);
    }
}
#[inline(never)]
pub fn returning(values: &mut [char], index: usize, value: char) -> char {
    values[index] = replacement(value);
    values[index]
}
pub fn returned(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        let result = returning(values, index, value);
        assert!(result == if value == 'A' { 'B' } else { 'A' } && values[index] == result);
    }
}
pub fn ghost_length(values: &mut [char]) {
    if values.len() > 0 {
        values[0] = 'A';
    }
}
pub fn empty(values: &mut [char]) {
    if values.len() == 0 {
        assert!(values.len() == 0);
    }
}
pub fn wrong(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        child(values, index, value);
        assert!(values[index] == value);
    }
}
pub fn bounds(values: &mut [char], index: usize) {
    values[index] = 'A';
}
pub fn wrong_sibling(values: &mut [char], index: usize, other: usize) {
    if index < values.len() && other < values.len() && index != other {
        values[other] = 'B';
        values[index] = 'A';
        assert!(values[other] == 'A');
    }
}
#[inline(never)]
pub fn panic_child(values: &mut [char]) {
    let _ = values.len();
    panic!("reached");
}
pub fn reached_panic(values: &mut [char]) {
    panic_child(values);
}
#[inline(never)]
pub fn asserting_child(values: &mut [char], index: usize) {
    assert!(values[index] == 'A');
}
pub fn child_assertion(values: &mut [char], index: usize) {
    if index < values.len() {
        asserting_child(values, index);
    }
}
pub fn competing(left: &mut [char], right: &mut [char]) {
    let _ = (left.len(), right.len());
}
#[inline(never)]
pub fn shared_len(values: &[char]) -> usize {
    values.len()
}
pub fn shared(values: &mut [char]) -> usize {
    shared_len(&*values)
}
pub fn raw(values: &mut [char]) {
    let _ = values.as_mut_ptr();
}
pub fn escape(values: &mut [char]) -> &mut [char] {
    values
}
#[inline(never)]
pub fn nested_child(values: &mut [char], index: usize, value: char) {
    child(values, index, value);
}
pub fn nested(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        nested_child(values, index, value);
    }
}
pub fn float64_unknown(values: &mut [f64]) {
    if !values.is_empty() {
        values[0] = 1.0;
    }
}
pub fn float_unknown(values: &mut [f32]) {
    if !values.is_empty() {
        values[0] = 1.0;
    }
}
pub fn u8_unknown(values: &mut [u8]) {
    if !values.is_empty() {
        values[0] = 1;
    }
}
#[cfg(external_control)]
pub fn external_char(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        stage194_dependency::selected(values, index, value);
        assert!(values[index] == if value == 'A' { 'B' } else { 'A' });
    }
}
#[cfg(test)]
extern crate std;
pub fn boundaries(values: &mut [char], index: usize) {
    if index < values.len() {
        let observed = values[index] as u32;
        assert!(observed <= 0x10ffff);
        assert!(observed < 0xd800 || observed > 0xdfff);
        values[index] = '\u{10ffff}';
        assert!(values[index] as u32 == 0x10ffff);
    }
}
pub fn method(values: &mut [char], index: usize) {
    if index < values.len() {
        values[index] = 'A';
        assert!(values[index].is_ascii());
    }
}
pub fn copied_method(values: &mut [char], index: usize) {
    if index < values.len() {
        values[index] = 'A';
        let value = values[index];
        assert!(value.is_ascii());
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn finite_129_and_empty() {
        let mut values = ['B'; 129];
        for index in 0..129 {
            for value in [
                '\0',
                'A',
                'B',
                '\u{d7ff}',
                '\u{e000}',
                '\u{ffff}',
                '\u{10000}',
                '\u{10ffff}',
            ] {
                super::selected(&mut values, index, value);
                super::direct(&mut values, index, value);
                super::untouched(&mut values, index, (index + 1) % 129, value);
                super::sequential(&mut values, index, value);
                super::branches(&mut values, index, value, index % 2 == 0);
                super::boundaries(&mut values, index);
                super::method(&mut values, index);
                super::returned(&mut values, index, value);
            }
        }
        super::selected(&mut [], 0, 'B');
        super::empty(&mut []);
    }
    #[test]
    fn mutation_guard() {
        let mut values = ['B'; 129];
        super::selected(&mut values, 128, 'B');
        assert!(values[128] == 'A');
    }
    #[test]
    #[should_panic]
    fn false_original_claim() {
        super::wrong(&mut ['B'; 2], 1, 'B');
    }
}
