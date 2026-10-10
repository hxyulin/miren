#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn replacement(value: bool) -> bool {
    !value
}
#[inline(never)]
pub fn child(values: &mut [bool], index: usize, value: bool) {
    values[index] = replacement(value);
}
pub fn selected(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        child(values, index, value);
        assert!(values[index] == !value);
    }
}
pub fn direct(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        values[index] = value;
        assert!(values[index] == value);
    }
}
pub fn untouched(values: &mut [bool], index: usize, other: usize, value: bool) {
    if index < values.len() && other < values.len() && index != other {
        let old = values[other];
        child(values, index, value);
        assert!(values[other] == old);
    }
}
pub fn sequential(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        child(values, index, value);
        child(values, index, !value);
        assert!(values[index] == value);
    }
}
pub fn branches(values: &mut [bool], index: usize, value: bool, flag: bool) {
    if index < values.len() {
        let next = if flag { value } else { !value };
        values[index] = next;
        assert!(values[index] == next);
    }
}
#[inline(never)]
pub fn returning(values: &mut [bool], index: usize, value: bool) -> bool {
    values[index] = replacement(value);
    values[index]
}
pub fn returned(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        let result = returning(values, index, value);
        assert!(result == !value && values[index] == result);
    }
}
pub fn ghost_length(values: &mut [bool]) {
    if values.len() > 0 {
        values[0] = true;
    }
}
pub fn empty(values: &mut [bool]) {
    if values.len() == 0 {
        assert!(values.len() == 0);
    }
}
pub fn wrong(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        child(values, index, value);
        assert!(values[index] == value);
    }
}
pub fn bounds(values: &mut [bool], index: usize) {
    values[index] = true;
}
pub fn wrong_sibling(values: &mut [bool], index: usize, other: usize) {
    if index < values.len() && other < values.len() && index != other {
        values[other] = false;
        values[index] = true;
        assert!(values[other]);
    }
}
#[inline(never)]
pub fn panic_child(values: &mut [bool]) {
    let _ = values.len();
    panic!("reached");
}
pub fn reached_panic(values: &mut [bool]) {
    panic_child(values);
}
#[inline(never)]
pub fn asserting_child(values: &mut [bool], index: usize) {
    assert!(values[index]);
}
pub fn child_assertion(values: &mut [bool], index: usize) {
    if index < values.len() {
        asserting_child(values, index);
    }
}
pub fn competing(left: &mut [bool], right: &mut [bool]) {
    let _ = (left.len(), right.len());
}
#[inline(never)]
pub fn shared_len(values: &[bool]) -> usize {
    values.len()
}
pub fn shared(values: &mut [bool]) -> usize {
    shared_len(&*values)
}
pub fn raw(values: &mut [bool]) {
    let _ = values.as_mut_ptr();
}
pub fn escape(values: &mut [bool]) -> &mut [bool] {
    values
}
#[inline(never)]
pub fn nested_child(values: &mut [bool], index: usize, value: bool) {
    child(values, index, value);
}
pub fn nested(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        nested_child(values, index, value);
    }
}
pub fn char_unknown(values: &mut [char]) {
    if !values.is_empty() {
        values[0] = 'a';
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
pub fn external_bool(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        stage192_dependency::selected(values, index, value);
        assert!(values[index] == !value);
    }
}
#[cfg(test)]
extern crate std;
#[cfg(test)]
mod native {
    #[test]
    fn finite_129_and_empty() {
        let mut values = [false; 129];
        for index in 0..129 {
            for value in [false, true] {
                super::selected(&mut values, index, value);
                super::direct(&mut values, index, value);
                super::untouched(&mut values, index, (index + 1) % 129, value);
                super::sequential(&mut values, index, value);
                super::branches(&mut values, index, value, index % 2 == 0);
                super::returned(&mut values, index, value);
            }
        }
        super::selected(&mut [], 0, false);
        super::empty(&mut []);
    }
    #[test]
    fn mutation_guard() {
        let mut values = [false; 129];
        super::selected(&mut values, 128, false);
        assert!(values[128]);
    }
    #[test]
    #[should_panic]
    fn false_original_claim() {
        super::wrong(&mut [false; 2], 1, false);
    }
}
