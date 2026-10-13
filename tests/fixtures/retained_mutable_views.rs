#![no_std]
#![forbid(unsafe_code)]

pub fn product_offset(values: &mut [[f32; 2]], start: usize, end: usize, sibling: usize) {
    if start < end && end <= values.len() && sibling < values.len() && sibling != start {
        let old = values[sibling][0].to_bits();
        {
            let child = &mut values[start..end];
            assert!(child.len() == end - start);
            child[0][1] = 2.0;
            child[0][0] = 1.0;
            assert!(child[0][0] == 1.0 && child[0][1] == 2.0);
        }
        assert!(values[start][0] == 1.0 && values[start][1] == 2.0);
        assert!(values[sibling][0].to_bits() == old);
    }
}
pub fn scalar_offset(values: &mut [u16], start: usize, end: usize, sibling: usize, word: u16) {
    if start < end && end <= values.len() && sibling < values.len() && sibling != start {
        let old = values[sibling];
        {
            let child = &mut values[start..end];
            assert!(child.len() == end - start);
            child[0] = word;
            assert!(child[0] == word);
        }
        assert!(values[start] == word && values[sibling] == old);
    }
}
pub fn wrong_write(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0][0] = 1.0;
        assert!(child[0][0] == 2.0);
    }
}
pub fn wrong_extent(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 2);
    }
}
pub fn invalid_range(values: &mut [[f32; 2]]) {
    let child = &mut values[0..1];
    assert!(child.len() == 1);
}
#[inline(never)]
pub fn identity(word: u16) -> u16 {
    word
}
pub fn scalar_helper_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = identity(word);
    }
}
pub fn nested_unknown(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        let nested = &mut child[0..1];
        assert!(nested.len() == 1);
    }
}
pub fn nll_unknown(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        values[0][0] = 2.0;
        assert!(values[0][0] == 2.0);
    }
}
pub fn unsupported_codec(values: &mut [[f64; 2]]) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn actual_offset_and_sibling_storage() {
        let mut products = [[3.0, 4.0], [5.0, 6.0], [7.0, 8.0]];
        super::product_offset(&mut products, 1, 3, 0);
        assert!(products[0] == [3.0, 4.0] && products[1] == [1.0, 2.0]);
        let mut scalars = [3, 5, 7];
        super::scalar_offset(&mut scalars, 1, 3, 0, 19);
        assert!(scalars == [3, 19, 7]);
    }
}
