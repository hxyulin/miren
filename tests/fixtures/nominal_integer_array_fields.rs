#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![forbid(unsafe_code)]

#[derive(Clone, Copy, PartialEq)]
pub struct Words {
    words: [u16; 2],
    marker: bool,
}
#[derive(Clone, Copy, PartialEq)]
pub struct Empty {
    words: [u16; 0],
}
#[derive(Clone, Copy, PartialEq)]
pub struct Floats {
    values: [f32; 2],
}
#[inline(never)]
fn selected(values: &[Words], index: usize) -> Words {
    let mut value = values[index];
    value.words[1] = value.words[1].wrapping_add(0);
    value
}
pub fn membership(values: &[Words], index: usize) {
    if index < values.len() {
        assert!(values.contains(&selected(values, index)));
    }
}
pub fn wrong_claim(values: &[Words], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&selected(values, index)));
    }
}
pub fn equality(values: &[Words]) {
    assert!(values == values);
}
pub fn empty(values: &[Empty]) {
    assert!(values == values);
}
pub fn floating(values: &[Floats]) -> bool {
    values == values
}

#[derive(Clone, Copy, PartialEq)]
pub struct Nested {
    payload: ([[i16; 2]; 2], [u32; 1]),
    record: Words,
}

pub fn nested(values: &[Nested], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}

pub fn different_views(values: &[Words]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] != values[1..]);
    }
}

pub fn wrong_views(values: &[Words]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}

pub fn empty_member(values: &[Empty]) {
    assert!(values.contains(&Empty { words: [] }) == !values.is_empty());
}

pub fn empty_maximum(values: &[Empty]) {
    if values.len() == usize::MAX {
        assert!(values.contains(&Empty { words: [] }));
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct Bools {
    values: [bool; 2],
}
pub fn bool_arrays(values: &[Bools]) {
    assert!(values == values);
}

#[derive(Clone, Copy, PartialEq)]
pub struct Chars {
    values: [char; 2],
}
pub fn char_arrays(values: &[Chars]) {
    assert!(values == values);
}

#[derive(Clone, Copy, PartialEq)]
pub struct FloatSibling {
    words: [u16; 2],
    value: f32,
    character: char,
}
pub fn numeric_sibling(values: &[FloatSibling], index: usize) {
    if index < values.len() && !values[index].value.is_nan() {
        assert!(values.contains(&values[index]));
    }
}
pub fn float_sibling_self(values: &[FloatSibling]) {
    assert!(values == values);
}

#[derive(Clone, Copy, PartialEq)]
pub struct VacantRef {
    values: [&'static u16; 0],
}
pub fn vacant_ref(values: &[VacantRef]) {
    assert!(values == values);
}

#[derive(Clone, Copy, PartialEq)]
pub struct VacantCore {
    values: [core::num::NonZeroU16; 0],
}
pub fn vacant_core(values: &[VacantCore]) {
    assert!(values == values);
}

#[derive(Clone, Copy, PartialEq)]
pub struct Large {
    values: [u16; 129],
}
pub fn large_type(values: &[Large]) -> usize {
    values.len()
}

#[derive(Clone, Copy, PartialEq)]
pub struct Expanded {
    values: [[[u16; 0]; 128]; 5],
}
pub fn expanded_type(values: &[Expanded]) -> usize {
    values.len()
}

#[derive(Clone, Copy)]
pub struct WrongArray {
    left: [u16; 2],
    right: [u16; 2],
}
impl PartialEq for WrongArray {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.left
    }
}
pub fn wrong_array_comparer(values: &[WrongArray]) {
    assert!(values == values);
}

#[derive(Clone, Copy)]
pub struct SameReceiver {
    words: [u16; 2],
}
impl PartialEq for SameReceiver {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool {
        self.words == self.words
    }
}
pub fn same_receiver(values: &[SameReceiver]) {
    assert!(values == values);
}

#[derive(Clone, Copy)]
pub struct OmittedArray {
    words: [u16; 2],
    marker: bool,
}
impl PartialEq for OmittedArray {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.marker == other.marker
    }
}
pub fn omitted_array(values: &[OmittedArray]) {
    assert!(values == values);
}

pub fn mutable_root(values: &mut [Words]) {
    assert!(values == values);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mutation_guard() {
        membership(
            &[Words {
                words: [3, 7],
                marker: false,
            }; 129],
            128,
        );
    }

    #[test]
    fn originals() {
        let words = [Words {
            words: [3, 7],
            marker: false,
        }; 129];
        membership(&words, 128);
        equality(&words);
        empty(&[Empty { words: [] }; 129]);
        empty_member(&[]);
        empty_maximum(&[Empty { words: [] }; usize::MAX]);
        nested(
            &[Nested {
                payload: ([[3, -7], [11, -19]], [23]),
                record: words[0],
            }; 129],
            128,
        );
        numeric_sibling(
            &[FloatSibling {
                words: [3, 7],
                value: -0.0,
                character: '\u{10ffff}',
            }; 129],
            128,
        );
        different_views(&[
            words[0],
            Words {
                words: [11, 19],
                marker: true,
            },
        ]);
    }

    #[test]
    #[should_panic]
    fn absence_witness() {
        wrong_claim(
            &[Words {
                words: [3, 7],
                marker: false,
            }; 129],
            128,
        );
    }

    #[test]
    #[should_panic]
    fn different_views_witness() {
        wrong_views(&[
            Words {
                words: [3, 7],
                marker: false,
            },
            Words {
                words: [11, 19],
                marker: true,
            },
        ]);
    }

    #[test]
    #[should_panic]
    fn nan_witness() {
        float_sibling_self(&[FloatSibling {
            words: [3, 7],
            value: f32::NAN,
            character: '\0',
        }]);
    }
}

pub fn external_selected(values: &[integer_array_dependency::External], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}

pub fn external_empty(values: &[integer_array_dependency::ExternalZero]) {
    assert!(values == values);
}

pub fn external_mismatch(values: &[integer_array_dependency::External]) {
    if values.len() > 1 {
        assert!(values[..1] != values[..]);
    }
}

#[derive(Clone, Copy)]
pub struct VacantPat {
    values: [core::pattern_type!(u16 is 1..); 0],
}
pub fn vacant_pat(values: &[VacantPat]) -> usize {
    values.len()
}
