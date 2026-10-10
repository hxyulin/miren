#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn copy_selected(values: &mut [u8]) {
    values[..2].copy_from_slice(&[17, 19]);
}
pub fn selected(values: &mut [u8]) {
    if values.len() >= 2 {
        copy_selected(values);
        assert!(values[0] == 17 && values[1] == 19);
    }
}
pub fn direct(values: &mut [u8]) {
    if values.len() >= 2 {
        values[..2].copy_from_slice(&[17, 19]);
        assert!(values[0] == 17 && values[1] == 19);
    }
}
pub fn sibling(values: &mut [u8], index: usize) {
    if values.len() >= 2 && index >= 2 && index < values.len() {
        let old = values[index];
        copy_selected(values);
        assert!(values[index] == old);
    }
}
pub fn sequential(values: &mut [u8]) {
    if values.len() >= 2 {
        copy_selected(values);
        values[..1].copy_from_slice(&[23]);
        assert!(values[0] == 23 && values[1] == 19);
    }
}
pub fn nested_prefix(values: &mut [u8]) {
    if values.len() >= 3 {
        values[..3][..2].copy_from_slice(&[17, 19]);
        assert!(values[0] == 17 && values[1] == 19);
    }
}
pub fn branches(values: &mut [u8], flag: bool) {
    if values.len() >= 2 {
        if flag {
            values[..2].copy_from_slice(&[17, 19]);
        } else {
            values[..2].copy_from_slice(&[23, 29]);
        }
        assert!(values[0] == if flag { 17 } else { 23 });
    }
}
pub fn one(values: &mut [u8]) {
    if values.len() >= 1 {
        values[..1].copy_from_slice(&[17]);
        assert!(values[0] == 17);
    }
}
pub fn empty(values: &mut [u8]) {
    if values.len() == 0 {
        assert!(values.len() == 0);
    }
}
pub fn wrong(values: &mut [u8]) {
    if values.len() >= 2 {
        copy_selected(values);
        assert!(values[1] == 17);
    }
}
pub fn wrong_sibling(values: &mut [u8]) {
    if values.len() >= 3 {
        values[2] = 29;
        copy_selected(values);
        assert!(values[2] == 17);
    }
}
pub fn bounds(values: &mut [u8]) {
    values[..2].copy_from_slice(&[17, 19]);
}
pub fn mismatch(values: &mut [u8]) {
    if values.len() >= 3 {
        values[..3].copy_from_slice(&[17, 19]);
    }
}
#[inline(never)]
pub fn owned_source() -> [u8; 2] {
    [17, 19]
}
pub fn dynamic_source(values: &mut [u8]) {
    if values.len() >= 2 {
        values[..2].copy_from_slice(&owned_source());
    }
}
pub fn two_inputs(values: &mut [u8], source: &[u8]) {
    if values.len() >= 2 && source.len() == 2 {
        values[..2].copy_from_slice(source);
    }
}
pub fn shifted(values: &mut [u8]) {
    if values.len() >= 3 {
        values[1..3].copy_from_slice(&[17, 19]);
        assert!(values[1] == 17 && values[2] == 19);
    }
}
pub fn raw_exposure(values: &mut [u8]) {
    if values.len() >= 2 {
        let _pointer = &raw mut values[0];
        values[..2].copy_from_slice(&[17, 19]);
    }
}
#[inline(never)]
pub fn expose_child(values: &mut [u8]) {
    let _pointer = &raw mut values[0];
}
pub fn returned_opaque(values: &mut [u8]) {
    if values.len() >= 2 {
        expose_child(values);
        values[..2].copy_from_slice(&[17, 19]);
    }
}
#[inline(never)]
pub fn opaque_companion(pair: (u8, u8)) -> u8 {
    pair.0
}
pub fn opaque_returned(values: &mut [u8]) {
    if values.len() >= 2 {
        let _result = opaque_companion((1, 2));
        values[..2].copy_from_slice(&[17, 19]);
    }
}
pub fn exact_budget(values: &mut [u8]) {
    if values.len() >= 128 {
        values[..128].copy_from_slice(&[7; 128]);
        assert!(values[0] == 7 && values[127] == 7);
    }
}
pub fn over_budget(values: &mut [u8]) {
    if values.len() >= 129 {
        values[..129].copy_from_slice(&[7; 129]);
    }
}
pub fn zero_copy(values: &mut [u8]) {
    values[..0].copy_from_slice(&[]);
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn mutation_guard() {
        let mut values = [31; 129];
        selected(&mut values);
        assert!(values[0] == 17 && values[1] == 19);
        assert!(values[128] == 31);
    }
    #[test]
    fn siblings() {
        let mut values = [31; 129];
        sibling(&mut values, 128);
        assert!(values[128] == 31);
    }
    #[test]
    fn current_data() {
        let mut values = [31; 129];
        sequential(&mut values);
        assert!(values[0] == 23 && values[1] == 19 && values[128] == 31);
    }
    #[test]
    fn nested() {
        let mut values = [31; 129];
        nested_prefix(&mut values);
        assert!(values[2] == 31);
    }
    #[test]
    fn selected_branches() {
        let mut values = [31; 129];
        branches(&mut values, true);
        branches(&mut values, false);
        assert!(values[0] == 23 && values[1] == 29);
    }
    #[test]
    fn maximum_replacement() {
        let mut values = [31; 129];
        exact_budget(&mut values);
        assert!(values[127] == 7 && values[128] == 31);
    }
    #[test]
    fn empty_input() {
        empty(&mut []);
    }
}
