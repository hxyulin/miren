#![no_std]
#![forbid(unsafe_code)]
#![feature(pattern_types, pattern_type_macro)]
#[derive(Clone, Copy, PartialEq)]
pub struct Booleans {
    pub values: [bool; 2],
    pub marker: u16,
}
#[derive(Clone, Copy, PartialEq)]
pub struct Characters {
    pub values: [char; 2],
    pub marker: bool,
}
#[derive(Clone, Copy, PartialEq)]
pub struct Float32 {
    pub values: [f32; 2],
    pub marker: u16,
}
#[derive(Clone, Copy, PartialEq)]
pub struct Float64 {
    pub values: [f64; 2],
    pub marker: u16,
}
#[derive(Clone, Copy, PartialEq)]
pub struct Mixed {
    pub flags: [[bool; 2]; 2],
    pub characters: [char; 2],
    pub integers: [i16; 2],
}
#[derive(Clone, Copy, PartialEq)]
pub struct Vacant {
    pub booleans: [bool; 0],
    pub characters: [[char; 0]; 2],
    pub float32: [f32; 0],
    pub float64: [f64; 0],
}
#[inline(never)]
pub fn selected(values: &[Booleans], index: usize) -> Booleans {
    values[index]
}
pub fn boolean_member(values: &[Booleans], index: usize) {
    if index < values.len() {
        assert!(values.contains(&selected(values, index)));
    }
}
pub fn boolean_absent(values: &[Booleans], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&selected(values, index)));
    }
}
pub fn boolean_self(values: &[Booleans]) {
    assert!(values == values);
}
pub fn character_member(values: &[Characters], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
pub fn mixed_member(values: &[Mixed], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
pub fn character_boundaries(values: &[Characters], index: usize) {
    if index < values.len() {
        let selected = values[index];
        assert!(selected.values[0] as u32 <= 0x10ffff);
        assert!((selected.values[1] as u32) < 0xd800 || selected.values[1] as u32 > 0xdfff);
        assert!(values.contains(&selected));
    }
}
pub fn float32_member(values: &[Float32], index: usize) {
    if index < values.len()
        && !values[index].values[0].is_nan()
        && !values[index].values[1].is_nan()
    {
        assert!(values.contains(&values[index]));
    }
}
pub fn float32_zero(values: &[Float32], index: usize) {
    if index < values.len() && values[index].values == [0.0; 2] {
        let needle = Float32 {
            values: [-0.0; 2],
            marker: values[index].marker,
        };
        assert!(values.contains(&needle));
    }
}
pub fn float32_self(values: &[Float32]) {
    assert!(values == values);
}
pub fn float64_member(values: &[Float64], index: usize) {
    if index < values.len()
        && !values[index].values[0].is_nan()
        && !values[index].values[1].is_nan()
    {
        assert!(values.contains(&values[index]));
    }
}
pub fn float64_zero(values: &[Float64], index: usize) {
    if index < values.len() && values[index].values == [0.0; 2] {
        let needle = Float64 {
            values: [-0.0; 2],
            marker: values[index].marker,
        };
        assert!(values.contains(&needle));
    }
}
pub fn float64_self(values: &[Float64]) {
    assert!(values == values);
}
pub fn nan_singleton(values: &[Float32]) {
    if values.len() == 1 && values[0].values[0].is_nan() {
        assert!(!values.contains(&values[0]));
    }
}
pub fn views(values: &[Booleans], start: usize) {
    if start <= values.len() {
        assert!(values[start..] == values[start..]);
    }
}
pub fn different_views(values: &[Booleans]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] != values[1..]);
    }
}
pub fn wrong_views(values: &[Booleans]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}
pub fn vacant_member(values: &[Vacant]) {
    let needle = Vacant {
        booleans: [],
        characters: [[], []],
        float32: [],
        float64: [],
    };
    assert!(values.contains(&needle) == !values.is_empty());
}
pub fn vacant_maximum(values: &[Vacant]) {
    if values.len() == usize::MAX {
        assert!(values == values);
    }
}
#[derive(Clone, Copy)]
pub struct BadComparer {
    pub left: [bool; 2],
    pub right: [bool; 2],
}
impl PartialEq for BadComparer {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.left
    }
}
pub fn bad_comparer(values: &[BadComparer]) {
    assert!(values == values);
}
#[derive(Clone, Copy)]
pub struct ReferenceChild {
    pub values: [&'static u16; 0],
}
pub fn reference_child(values: &[ReferenceChild]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct PatternChild {
    pub values: [core::pattern_type!(u16 is 1..); 0],
}
pub fn pattern_child(values: &[PatternChild]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct CoreChild {
    pub values: [core::num::NonZeroU16; 0],
}
pub fn core_child(values: &[CoreChild]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Oversized {
    pub values: [bool; 129],
}
pub fn oversized(values: &[Oversized]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Expanded {
    pub values: [[[char; 0]; 128]; 5],
}
pub fn expanded(values: &[Expanded]) -> usize {
    values.len()
}
pub fn external_member(values: &[primitive_array_dependency::External], index: usize) {
    if index < values.len()
        && !values[index].values[0].is_nan()
        && !values[index].values[1].is_nan()
    {
        assert!(values.contains(&values[index]));
    }
}
pub fn external_empty(values: &[primitive_array_dependency::ExternalZero]) {
    assert!(values == values);
}
pub fn external_mismatch(values: &[primitive_array_dependency::External]) {
    if values.len() > 1 {
        assert!(values[..1] != values[..]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mutation_guard() {
        boolean_member(
            &[Booleans {
                values: [false, true],
                marker: 7,
            }; 129],
            128,
        );
    }
    #[test]
    fn originals() {
        let booleans = [Booleans {
            values: [false, true],
            marker: 7,
        }; 129];
        boolean_member(&booleans, 128);
        boolean_self(&booleans);
        views(&booleans, 128);
        character_member(
            &[Characters {
                values: ['\u{d7ff}', '\u{e000}'],
                marker: true,
            }; 129],
            128,
        );
        character_boundaries(
            &[Characters {
                values: ['\0', '\u{10ffff}'],
                marker: false,
            }; 129],
            128,
        );
        mixed_member(
            &[Mixed {
                flags: [[false, true], [true, false]],
                characters: ['\u{d7ff}', '\u{10ffff}'],
                integers: [3, -7],
            }; 129],
            128,
        );
        float32_member(
            &[Float32 {
                values: [3.0, -7.0],
                marker: 11,
            }; 129],
            128,
        );
        float64_member(
            &[Float64 {
                values: [3.0, -7.0],
                marker: 11,
            }; 129],
            128,
        );
        float32_zero(
            &[Float32 {
                values: [0.0, -0.0],
                marker: 11,
            }; 129],
            128,
        );
        float64_zero(
            &[Float64 {
                values: [0.0, -0.0],
                marker: 11,
            }; 129],
            128,
        );
        nan_singleton(&[Float32 {
            values: [f32::NAN, -0.0],
            marker: 11,
        }]);
        vacant_member(&[]);
        vacant_maximum(
            &[Vacant {
                booleans: [],
                characters: [[], []],
                float32: [],
                float64: [],
            }; 129],
        );
    }
    #[test]
    #[should_panic]
    fn absent_witness() {
        boolean_absent(
            &[Booleans {
                values: [false, true],
                marker: 7,
            }; 129],
            128,
        );
    }
    #[test]
    #[should_panic]
    fn nan32_witness() {
        float32_self(&[Float32 {
            values: [f32::NAN, 0.0],
            marker: 7,
        }]);
    }
    #[test]
    #[should_panic]
    fn nan64_witness() {
        float64_self(&[Float64 {
            values: [f64::NAN, 0.0],
            marker: 7,
        }]);
    }
}
