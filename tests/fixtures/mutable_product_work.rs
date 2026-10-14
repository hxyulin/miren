#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
#[doc = "<!-- miren:v1:requires:value == 17 -->"]
#[doc = "<!-- miren:v1:ensures:final_value == value && result == value -->"]
pub fn scalar(value: u32) -> u32 {
    value
}

#[inline(never)]
pub fn leaf(values: &mut [(u32, bool)], index: usize, value: u32) -> u32 {
    let result = scalar(value);
    values[index] = (result, true);
    result
}

#[inline(never)]
pub fn child(values: &mut [(u32, bool)], index: usize, value: u32) -> u32 {
    leaf(values, index, value)
}

pub fn root(values: &mut [(u32, bool)], index: usize) {
    if index < values.len() {
        let result = child(values, index, 17);
        assert!(result == 17 && values[index].0 == 17 && values[index].1);
    }
}

pub fn wrong(values: &mut [(u32, bool)], index: usize) {
    if index < values.len() {
        let result = child(values, index, 17);
        assert!(result == 18);
    }
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
#[test]
fn native_owner_effect_and_wrong_claim() {
    let mut values = [(3, false), (19, false)];
    root(&mut values, 1);
    assert_eq!(values, [(3, false), (17, true)]);
    assert!(std::panic::catch_unwind(|| wrong(&mut [(3, false)], 0)).is_err());
}
