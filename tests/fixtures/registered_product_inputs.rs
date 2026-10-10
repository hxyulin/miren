#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[inline(never)]
pub fn chosen(record: Record) -> u16 {
    record.left
}

pub fn repeated(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let first = a[index];
        let second = a[index];
        assert!(first.left == second.left && first.right == second.right);
    }
}
pub fn constant_paths(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index == 0 || index == 63 {
        let selected = a[index];
        if index == 0 {
            assert!(selected.left == a[0].left && selected.right == a[0].right);
        } else {
            assert!(selected.left == a[63].left && selected.right == a[63].right);
        }
    }
}
pub fn copied_root(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let copied = a;
        let original = a[index];
        let selected = copied[index];
        assert!(original.left == selected.left && original.right == selected.right);
    }
}
pub fn whole_write(mut a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        a[index] = Record { left: 3, right: 7 };
        let selected = a[index];
        assert!(selected.left == 3 && selected.right == 7);
    }
}
pub fn untouched(
    mut a: [Record; 64],
    b: [Record; 64],
    c: [Record; 64],
    index: usize,
    other: usize,
) {
    if index < 64 && other < 64 && index != other {
        let saved = a[other];
        let saved_b = b[index];
        let saved_c = c[index];
        a[index] = Record {
            left: 11,
            right: 19,
        };
        let preserved = a[other];
        let again_b = b[index];
        let again_c = c[index];
        assert!(saved.left == preserved.left && saved.right == preserved.right);
        assert!(saved_b.left == again_b.left && saved_b.right == again_b.right);
        assert!(saved_c.left == again_c.left && saved_c.right == again_c.right);
    }
}
pub fn alignment(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        assert!(core::mem::align_of_val(&selected) == core::mem::align_of::<Record>());
    }
}
pub fn root_alignment(a: [Record; 64], _b: [Record; 64], _c: [Record; 64]) {
    assert!(core::mem::align_of_val(&a) == core::mem::align_of::<[Record; 64]>());
}
pub fn mutation_claim(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        if selected.left != selected.right {
            assert!(chosen(selected) == selected.left);
        }
    }
}
pub fn roots_are_equal(a: [Record; 64], b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let left = a[index];
        let right = b[index];
        assert!(left.left == right.left);
    }
}
pub fn occurrences_are_equal(a: [Record; 64], _b: [Record; 64], _c: [Record; 64]) {
    let first = a[0];
    let last = a[63];
    assert!(first.left == last.left);
}
pub fn fields_are_equal(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        assert!(selected.left == selected.right);
    }
}
pub fn bounds(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    let selected = a[index];
    assert!(selected.left == chosen(selected));
}
pub fn retained_borrow(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let borrowed = &a[index];
        assert!(borrowed.left == borrowed.left);
    }
}
#[derive(Clone, Copy)]
pub struct ReferenceZero {
    pub references: [&'static u16; 0],
    pub scalar: u16,
}
#[derive(Clone, Copy)]
pub struct RefinedZero {
    pub refined: [core::pattern_type!(u32 is 1..); 0],
    pub scalar: u16,
}
#[derive(Clone, Copy)]
pub struct CoreZero {
    pub core: [core::marker::PhantomData<&'static u16>; 0],
    pub scalar: u16,
}
pub fn reference_zero(a: [ReferenceZero; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        assert!(selected.scalar == selected.scalar);
    }
}
pub fn refined_zero(a: [RefinedZero; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        assert!(selected.scalar == selected.scalar);
    }
}
pub fn core_zero(a: [CoreZero; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 64 {
        let selected = a[index];
        assert!(selected.scalar == selected.scalar);
    }
}
#[derive(Clone, Copy)]
pub enum Choice {
    A([Record; 64]),
    B([Record; 64]),
}
pub fn enum_origin(value: Choice, _b: [Record; 64], _c: [Record; 64], index: usize) {
    if let Choice::A(a) = value {
        if index < 64 {
            let selected = a[index];
            assert!(selected.left == selected.left);
        }
    }
}
pub fn oversized(a: [[Record; 64]; 3], _b: [Record; 64], _c: [Record; 64], index: usize) {
    if index < 3 {
        let selected = a[index];
        let item = selected[0];
        assert!(item.left == item.left);
    }
}
#[derive(Clone, Copy)]
pub struct Observation {
    pub float: f32,
    pub wide: f64,
    pub character: char,
}
pub fn observations(
    a: [Observation; 64],
    _b: [Observation; 64],
    _c: [Observation; 64],
    index: usize,
) {
    if index < 64 {
        let first = a[index];
        let again = a[index];
        assert!(first.float.to_bits() == again.float.to_bits());
        assert!(first.wide.to_bits() == again.wide.to_bits());
        assert!(first.character as u32 == again.character as u32);
    }
}

#[derive(Clone, Copy)]
pub struct Floating {
    pub float: f32,
    pub wide: f64,
}
pub fn floating_observations(
    a: [Floating; 64],
    _b: [Floating; 64],
    _c: [Floating; 64],
    index: usize,
) {
    if index < 64 {
        let first = a[index];
        let again = a[index];
        assert!(first.float.to_bits() == again.float.to_bits());
        assert!(first.wide.to_bits() == again.wide.to_bits());
    }
}

#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    unsafe extern "Rust" {
        fn unavailable(record: Record) -> u16;
    }
    pub fn missing_body(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], index: usize) {
        if index < 64 {
            let selected = a[index];
            assert!(unsafe { unavailable(selected) } == selected.left);
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let values = [Record { left: 3, right: 7 }; 64];
        for index in [0, 63, 64, usize::MAX] {
            repeated(values, values, values, index);
            constant_paths(values, values, values, index);
            copied_root(values, values, values, index);
            whole_write(values, values, values, index);
            alignment(values, values, values, index);
            mutation_claim(values, values, values, index);
        }
        let floating = [Floating {
            float: f32::NAN,
            wide: -0.0,
        }; 64];
        floating_observations(floating, floating, floating, 63);
        let mixed = [Observation {
            float: -0.0,
            wide: f64::NAN,
            character: '\u{10ffff}',
        }; 64];
        observations(mixed, mixed, mixed, 63);
        root_alignment(values, values, values);
        untouched(values, values, values, 0, 63);
        untouched(values, values, values, 63, 0);
    }
    #[test]
    fn mutation_guard() {
        let values = [Record { left: 3, right: 7 }; 64];
        mutation_claim(values, values, values, 63);
    }
    #[test]
    #[should_panic]
    fn negative_roots() {
        let left = [Record { left: 3, right: 7 }; 64];
        let right = [Record {
            left: 11,
            right: 19,
        }; 64];
        roots_are_equal(left, right, left, 63);
    }
    #[test]
    #[should_panic]
    fn negative_occurrences() {
        let mut values = [Record { left: 3, right: 7 }; 64];
        values[63].left = 11;
        occurrences_are_equal(values, values, values);
    }
    #[test]
    #[should_panic]
    fn negative_fields() {
        let values = [Record { left: 3, right: 7 }; 64];
        fields_are_equal(values, values, values, 63);
    }
    #[test]
    #[should_panic]
    fn negative_bounds() {
        let values = [Record { left: 3, right: 7 }; 64];
        bounds(values, values, values, 64);
    }
}
