#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}

#[inline(never)]
pub fn selected_needle(values: &[Record], index: usize) -> Record {
    values[index]
}

pub fn selected(values: &[Record], index: usize) {
    if index < values.len() {
        assert!(values.contains(&selected_needle(values, index)));
    }
}
pub fn absent(values: &[Record], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&selected_needle(values, index)));
    }
}
pub fn self_equal(values: &[Record]) {
    assert!(values == values);
}
pub fn same_views(values: &[Record], start: usize) {
    if start <= values.len() {
        assert!(values[start..] == values[start..]);
    }
}
pub fn distinct_views(values: &[Record]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] != values[1..]);
    }
}
pub fn falsely_equal_views(values: &[Record]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct Generic<T> {
    pub payload: T,
    pub marker: u32,
}
pub fn generic_selected(values: &[Generic<i16>], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct Nested {
    pub record: Record,
    pub flag: bool,
    pub character: char,
}
pub fn nested_selected(values: &[Nested], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct Floating {
    pub value: f32,
    pub marker: u16,
}
pub fn non_nan_selected(values: &[Floating], index: usize) {
    if index < values.len() && !values[index].value.is_nan() {
        assert!(values.contains(&values[index]));
    }
}
pub fn signed_zero(values: &[Floating], index: usize) {
    if index < values.len() && values[index].value == 0.0 {
        let needle = Floating {
            value: -0.0,
            marker: values[index].marker,
        };
        assert!(values.contains(&needle));
    }
}
pub fn falsely_float_self(values: &[Floating]) {
    assert!(values == values);
}
#[derive(Clone, Copy, PartialEq)]
pub struct Characters {
    pub first: char,
    pub second: char,
}
pub fn char_selected(values: &[Characters], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct Zero;
pub fn zero_contains(values: &[Zero]) {
    assert!(values.contains(&Zero) == !values.is_empty());
}
pub fn zero_maximum(values: &[Zero]) {
    if values.len() == usize::MAX {
        assert!(values.contains(&Zero));
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct ArrayRecord {
    pub fields: [u16; 2],
    pub marker: u32,
}
pub fn array_lowering(values: &[ArrayRecord], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
#[derive(Clone, Copy)]
pub struct FalseEquality(pub u16);
impl PartialEq for FalseEquality {
    #[inline(never)]
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
pub fn nonstructural(values: &[FalseEquality], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
#[derive(Clone, Copy)]
pub struct PanickingEquality(pub u16);
impl PartialEq for PanickingEquality {
    #[inline(never)]
    fn eq(&self, _other: &Self) -> bool {
        panic!("actual comparator")
    }
}
pub fn panicking_comparator(values: &[PanickingEquality], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}
pub fn mutable_root(values: &mut [Record]) {
    assert!(values == values);
}
pub fn competing_roots(left: &[Record], right: &[Record]) {
    assert!(left == right);
}
#[derive(Clone, Copy, PartialEq)]
pub struct ReferenceZero {
    pub fields: [&'static u16; 0],
    pub marker: u16,
}
pub fn reference_zero(values: &[ReferenceZero]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub struct RefinedZero {
    pub fields: [core::pattern_type!(u16 is 1..); 0],
    pub marker: u16,
}
pub fn refined_zero(values: &[RefinedZero]) {
    let _ = values.len();
}

#[cfg(not(test))]
pub mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_member(member: bool) -> bool;
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn missing_body(values: &[Record], index: usize) -> bool {
        mir! {
            let member: bool;
            {
                Call(member = selected_member(values, index), ReturnTo(called), UnwindUnreachable())
            }
            called = {
                Call(RET = opaque_member(member), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[inline(never)]
    fn selected_member(values: &[Record], index: usize) -> bool {
        index >= values.len() || values.contains(&selected_needle(values, index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mutation_guard() {
        selected(&[Record { left: 3, right: 7 }; 129], 128);
    }
    #[test]
    fn ordinary_controls() {
        let values = [Record { left: 3, right: 7 }; 129];
        selected(&[], 0);
        self_equal(&values);
        same_views(&values, 129);
        distinct_views(&[values[0], Record { left: 5, right: 11 }]);
        generic_selected(
            &[Generic {
                payload: -7,
                marker: 11,
            }; 129],
            128,
        );
        nested_selected(
            &[Nested {
                record: values[0],
                flag: true,
                character: '\u{10ffff}',
            }; 129],
            128,
        );
        non_nan_selected(
            &[Floating {
                value: 1.5,
                marker: 7,
            }; 129],
            128,
        );
        signed_zero(
            &[Floating {
                value: 0.0,
                marker: 7,
            }],
            0,
        );
        signed_zero(
            &[Floating {
                value: -0.0,
                marker: 7,
            }],
            0,
        );
        char_selected(
            &[Characters {
                first: '\u{d7ff}',
                second: '\u{e000}',
            }; 129],
            128,
        );
        zero_contains(&[Zero; 129]);
        zero_maximum(&[Zero; usize::MAX]);
    }
    #[test]
    #[should_panic]
    fn negative_absent() {
        absent(&[Record { left: 3, right: 7 }; 129], 128);
    }
    #[test]
    #[should_panic]
    fn negative_views() {
        falsely_equal_views(&[Record { left: 3, right: 7 }, Record { left: 5, right: 11 }]);
    }
    #[test]
    #[should_panic]
    fn negative_nan() {
        falsely_float_self(&[Floating {
            value: f32::NAN,
            marker: 7,
        }]);
    }
}
