#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[derive(Clone, Copy)]
pub struct Generic<T> {
    pub payload: T,
    pub flag: bool,
}
#[derive(Clone, Copy)]
pub struct Nested {
    pub pair: Record,
    pub scalar: u32,
}
#[derive(Clone, Copy)]
pub struct ZeroField {
    pub scalar: u16,
    pub empty: (),
}

#[inline(never)]
pub fn change_left(mut values: [Record; 2], index: usize) -> [Record; 2] {
    values[index].left = 19;
    values
}
#[inline(never)]
pub fn first(values: &[Record; 2]) -> u16 {
    values[0].left
}
#[inline(never)]
pub fn unit_effect(counter: &mut u16) {
    *counter += 1;
}
#[inline(never)]
pub fn unit_panic() {
    panic!("actual replacement body")
}

pub fn named(mut values: [Record; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].left = 19;
        let selected = values[index];
        assert!(selected.left == 19 && selected.right == old.right);
    }
}
pub fn tuple(mut values: [(i16, bool, u32); 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].0 = -7;
        let selected = values[index];
        assert!(selected.0 == -7 && selected.1 == old.1 && selected.2 == old.2);
    }
}
pub fn generic(mut values: [Generic<Record>; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].payload.right = 23;
        let selected = values[index];
        assert!(selected.payload.right == 23 && selected.payload.left == old.payload.left);
        assert!(selected.flag == old.flag);
    }
}
pub fn nested(mut values: [Nested; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].pair.left = 19;
        let selected = values[index];
        assert!(selected.pair.left == 19 && selected.pair.right == old.pair.right);
        assert!(selected.scalar == old.scalar);
    }
}
pub fn subtree(mut values: [Generic<(u16, bool)>; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].payload = (23, true);
        let selected = values[index];
        assert!(selected.payload == (23, true) && selected.flag == old.flag);
    }
}
pub fn byte_subtree(mut values: [Generic<[u8; 2]>; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].payload = [19, 23];
        let selected = values[index];
        assert!(selected.payload[0] == 19 && selected.payload[1] == 23);
        assert!(selected.flag == old.flag);
    }
}
pub fn sequential(mut values: [Record; 3], index: usize, other: usize) {
    if index < 3 && other < 3 && index != other {
        let saved_index = values[index];
        let saved_other = values[other];
        values[index].left = 19;
        values[index].left = 23;
        values[other].right = 29;
        let selected = values[index];
        let second = values[other];
        assert!(selected.left == 23 && selected.right == saved_index.right);
        assert!(second.left == saved_other.left && second.right == 29);
    }
}
pub fn untouched(mut values: [Record; 3], index: usize, other: usize) {
    if index < 3 && other < 3 && index != other {
        let old = values[other];
        values[index].left = 19;
        let selected = values[other];
        assert!(selected.left == old.left && selected.right == old.right);
    }
}
pub fn allocated_owner(mut values: [Record; 2], index: usize) {
    if index < 2 {
        let initial_first = first(&values);
        let old = values[index];
        values[index].right = 23;
        let selected = values[index];
        assert!(selected.right == 23 && selected.left == old.left);
        let first_copy = values[0];
        assert!(first_copy.left == initial_first);
    }
}
pub fn lazy_roots(mut a: [Record; 64], b: [Record; 64], c: [Record; 64], index: usize) {
    if index < 64 {
        let old = a[index];
        let old_b = b[index];
        let old_c = c[index];
        a[index].left = 19;
        let selected = a[index];
        let next_b = b[index];
        let next_c = c[index];
        assert!(selected.left == 19 && selected.right == old.right);
        assert!(next_b.left == old_b.left && next_b.right == old_b.right);
        assert!(next_c.left == old_c.left && next_c.right == old_c.right);
    }
}
pub fn float_char(mut values: [(f32, f64, char); 2], index: usize) {
    if index < 2 {
        let old = values[index];
        values[index].0 = -0.0;
        values[index].2 = '\u{10ffff}';
        let selected = values[index];
        assert!(selected.0.to_bits() == 0x80000000 && selected.2 == '\u{10ffff}');
        assert!(selected.1.to_bits() == old.1.to_bits());
    }
}
pub fn unit_assignment(mut values: [ZeroField; 2], index: usize) {
    if index < 2 {
        let old = values[index];
        let mut counter = 0_u16;
        let replacement = unit_effect(&mut counter);
        values[index].empty = replacement;
        let selected = values[index];
        assert!(counter == 1 && selected.scalar == old.scalar && selected.empty == ());
    }
}
pub fn mutation_claim(index: usize) {
    if index < 2 {
        let original = [Record { left: 3, right: 7 }, Record { left: 5, right: 11 }];
        let changed = change_left(original, index);
        let selected = changed[index];
        let old = original[index];
        let untouched = changed[index ^ 1];
        let old_other = original[index ^ 1];
        assert!(selected.left == 19 && selected.right == old.right);
        assert!(untouched.left == old_other.left && untouched.right == old_other.right);
    }
}
pub fn wrong_sibling(mut values: [Record; 2], index: usize) {
    if index < 2 {
        values[index].left = 19;
        let selected = values[index];
        assert!(selected.right == 19);
    }
}
pub fn wrong_other(mut values: [Record; 2], index: usize) {
    if index < 2 {
        values[index].left = 19;
        let selected = values[index ^ 1];
        assert!(selected.left == 19);
    }
}
pub fn bounds(mut values: [Record; 2], index: usize) {
    values[index].left = 19;
}
pub fn zero_body_panic(mut values: [ZeroField; 2], index: usize) {
    if index < 2 {
        let replacement = unit_panic();
        values[index].empty = replacement;
    }
}
pub fn second_index(mut values: [Generic<[u16; 2]>; 2], index: usize) {
    if index < 2 {
        values[index].payload[0] = 19;
        let selected = values[index];
        assert!(selected.payload[0] == 19);
    }
}
pub fn deferred_reader(mut values: [Record; 2], index: usize) {
    if index < 2 {
        values[index].left = 19;
        assert!(values[index].left == 19);
    }
}
pub fn retained(values: &mut [Record; 2], index: usize) {
    if index < 2 {
        values[index].left = 19;
    }
}
#[derive(Clone, Copy)]
pub struct References {
    pub scalar: u16,
    pub references: [&'static u16; 0],
}
#[derive(Clone, Copy)]
pub struct Refinement {
    pub scalar: u16,
    pub refined: [core::pattern_type!(u32 is 1..); 0],
}
pub fn reference_zero(mut values: [References; 2], index: usize) {
    if index < 2 {
        values[index].scalar = 19;
    }
}
pub fn refined_zero(mut values: [Refinement; 2], index: usize) {
    if index < 2 {
        values[index].scalar = 19;
    }
}
pub fn oversized(mut values: [Generic<[u16; 129]>; 2], index: usize) {
    if index < 2 {
        values[index].flag = true;
    }
}
pub fn deferred_field_rhs(mut values: [Record; 2], index: usize) {
    if index < 2 {
        values[index].right = values[index].left;
    }
}
pub struct Dropped {
    pub scalar: u16,
}
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn drop_field(mut values: [Dropped; 2], index: usize) {
    if index < 2 {
        values[index].scalar = 19;
    }
}

#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    pub fn missing_body(mut values: [Record; 2], index: usize) {
        if index < 2 {
            let replacement = unsafe { unavailable() };
            values[index].left = replacement;
        }
    }
    #[derive(Clone, Copy)]
    pub struct Raw {
        pub scalar: u16,
        pub pointer: *const u16,
    }
    pub fn raw(mut values: [Raw; 2], index: usize) {
        if index < 2 {
            values[index].scalar = 19;
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let records = [Record { left: 3, right: 7 }; 2];
        let three = [Record { left: 5, right: 11 }; 3];
        let generic_values = [Generic {
            payload: records[0],
            flag: false,
        }; 2];
        let nested_values = [Nested {
            pair: records[0],
            scalar: 17,
        }; 2];
        for index in [0, 1, 2, usize::MAX] {
            named(records, index);
            tuple([(-1, false, 23); 2], index);
            generic(generic_values, index);
            nested(nested_values, index);
            subtree(
                [Generic {
                    payload: (3, false),
                    flag: true,
                }; 2],
                index,
            );
            byte_subtree(
                [Generic {
                    payload: [3, 7],
                    flag: false,
                }; 2],
                index,
            );
            allocated_owner(records, index);
            float_char([(f32::NAN, f64::NAN, '\u{d7ff}'); 2], index);
            unit_assignment(
                [ZeroField {
                    scalar: 3,
                    empty: (),
                }; 2],
                index,
            );
            mutation_claim(index);
        }
        sequential(three, 0, 2);
        untouched(three, 2, 0);
        let lazy = [Record { left: 3, right: 7 }; 64];
        lazy_roots(lazy, lazy, lazy, 63);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(1);
    }
    #[test]
    #[should_panic]
    fn negative_sibling() {
        wrong_sibling([Record { left: 3, right: 7 }; 2], 1);
    }
    #[test]
    #[should_panic]
    fn negative_other() {
        wrong_other([Record { left: 3, right: 7 }; 2], 0);
    }
    #[test]
    #[should_panic]
    fn negative_bounds() {
        bounds([Record { left: 3, right: 7 }; 2], 2);
    }
    #[test]
    #[should_panic]
    fn negative_body() {
        zero_body_panic(
            [ZeroField {
                scalar: 3,
                empty: (),
            }; 2],
            1,
        );
    }
}
