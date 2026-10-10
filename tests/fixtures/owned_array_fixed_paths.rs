#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Generic<T> {
    pub payload: T,
    pub flag: bool,
}
#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[inline(never)]
pub fn change_first(mut values: [[u16; 2]; 2], outer: usize) -> [[u16; 2]; 2] {
    values[outer][0] = 19;
    values
}
#[inline(never)]
pub fn first(values: &[[u16; 2]; 2]) -> u16 {
    values[0][0]
}
#[inline(never)]
pub fn unit_effect(counter: &mut u16) {
    *counter += 1;
}

pub fn first_inner(mut values: [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer][0] = 19;
        let selected = values[outer];
        assert!(selected[0] == 19 && selected[1] == old[1]);
    }
}
pub fn last_inner(mut values: [[u16; 2]; 2], outer: usize) {
    const LAST: usize = 1;
    if outer < 2 {
        let old = values[outer];
        values[outer][LAST] = 23;
        let selected = values[outer];
        assert!(selected[0] == old[0] && selected[1] == 23);
    }
}
pub fn field_then_index(mut values: [Generic<[u16; 2]>; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer].payload[0] = 19;
        let selected = values[outer];
        assert!(selected.payload[0] == 19 && selected.payload[1] == old.payload[1]);
        assert!(selected.flag == old.flag);
    }
}
pub fn index_then_field(mut values: [[Record; 2]; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer][0].left = 19;
        let selected = values[outer];
        assert!(selected[0].left == 19 && selected[0].right == old[0].right);
        assert!(selected[1].left == old[1].left && selected[1].right == old[1].right);
    }
}
pub fn constant_levels(mut values: [[[u16; 2]; 2]; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer][1][0] = 19;
        let selected = values[outer];
        assert!(selected[0] == old[0] && selected[1][0] == 19 && selected[1][1] == old[1][1]);
    }
}
pub fn subtree(mut values: [[(u16, bool); 2]; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer][0] = (19, true);
        let selected = values[outer];
        assert!(selected[0] == (19, true) && selected[1] == old[1]);
    }
}
pub fn sequential(mut values: [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        let before = values;
        values[outer][0] = 19;
        values[outer][0] = 23;
        values[outer][1] = 29;
        let selected = values[outer];
        let untouched = values[outer ^ 1];
        assert!(selected == [23, 29] && untouched == before[outer ^ 1]);
    }
}
pub fn allocated_owner(mut values: [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        let old_first = first(&values);
        values[outer][1] = 19;
        let selected = values[outer];
        let first_row = values[0];
        assert!(selected[1] == 19 && first_row[0] == old_first);
    }
}
pub fn lazy_roots(mut a: [[u16; 2]; 64], b: [[u16; 2]; 64], c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let old = a[outer];
        let old_b = b[outer];
        let old_c = c[outer];
        a[outer][0] = 19;
        let selected = a[outer];
        assert!(selected[0] == 19 && selected[1] == old[1]);
        assert!(b[outer] == old_b && c[outer] == old_c);
    }
}
pub fn lazy_writer_first(
    mut a: [[u16; 2]; 64],
    b: [[u16; 2]; 64],
    c: [[u16; 2]; 64],
    outer: usize,
) {
    if outer < 64 {
        let old_first = a[0];
        let old_last = a[63];
        let old_b = b[0];
        let old_c = c[0];
        a[outer][0] = 19;
        let selected = a[outer];
        assert!(selected[0] == 19);
        if outer != 0 {
            assert!(a[0] == old_first);
        }
        if outer != 63 {
            assert!(a[63] == old_last);
        }
        if outer == 0 {
            assert!(selected[1] == old_first[1]);
        }
        if outer == 63 {
            assert!(selected[1] == old_last[1]);
        }
        assert!(b[0] == old_b && c[0] == old_c);
    }
}
pub fn float_char(mut values: [[(f32, f64, char); 2]; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        values[outer][0].0 = -0.0;
        values[outer][0].2 = '\u{10ffff}';
        let selected = values[outer];
        assert!(selected[0].0.to_bits() == 0x80000000 && selected[0].2 == '\u{10ffff}');
        assert!(selected[0].1.to_bits() == old[0].1.to_bits());
        assert!(selected[1].0.to_bits() == old[1].0.to_bits());
        assert!(selected[1].1.to_bits() == old[1].1.to_bits() && selected[1].2 == old[1].2);
    }
}
pub fn bytes(mut values: [[u8; 2]; 2], outer: usize) {
    if outer < 2 {
        let before = values;
        values[outer][0] = 19;
        let selected = values[outer];
        let untouched = values[outer ^ 1];
        assert!(selected[0] == 19 && selected[1] == before[outer][1]);
        assert!(untouched[0] == before[outer ^ 1][0] && untouched[1] == before[outer ^ 1][1]);
    }
}
pub fn unit_assignment(mut values: [Generic<[(); 2]>; 2], outer: usize) {
    if outer < 2 {
        let old = values[outer];
        let mut counter = 0;
        let replacement = unit_effect(&mut counter);
        values[outer].payload[0] = replacement;
        let selected = values[outer];
        assert!(counter == 1 && selected.flag == old.flag && selected.payload == [(), ()]);
    }
}
pub fn mutation_claim(outer: usize) {
    if outer < 2 {
        let original = [[3, 7], [5, 11]];
        let changed = change_first(original, outer);
        let selected = changed[outer];
        assert!(selected[0] == 19 && selected[1] == original[outer][1]);
        assert!(changed[outer ^ 1] == original[outer ^ 1]);
    }
}
pub fn wrong_inner(mut values: [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        values[outer][0] = 19;
        let selected = values[outer];
        assert!(selected[1] == 19);
    }
}
pub fn wrong_outer(mut values: [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        values[outer][0] = 19;
        let selected = values[outer ^ 1];
        assert!(selected[0] == 19);
    }
}
pub fn bounds_outer(mut values: [[u16; 2]; 2], outer: usize) {
    values[outer][0] = 19;
}
pub fn bounds_inner(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner == 2 {
        values[outer][inner] = 19;
    }
}
pub fn dynamic_inner(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer][inner] = 19;
    }
}
pub fn retained(values: &mut [[u16; 2]; 2], outer: usize) {
    if outer < 2 {
        values[outer][0] = 19;
    }
}
#[derive(Clone, Copy)]
pub struct References {
    pub scalar: [u16; 2],
    pub references: [&'static u16; 0],
}
#[derive(Clone, Copy)]
pub struct Refinement {
    pub scalar: [u16; 2],
    pub refined: [core::pattern_type!(u32 is 1..); 0],
}
pub fn reference_zero(mut values: [References; 2], outer: usize) {
    if outer < 2 {
        values[outer].scalar[0] = 19;
    }
}
pub fn refined_zero(mut values: [Refinement; 2], outer: usize) {
    if outer < 2 {
        values[outer].scalar[0] = 19;
    }
}
pub fn oversized(mut values: [[u16; 129]; 2], outer: usize) {
    if outer < 2 {
        values[outer][0] = 19;
    }
}
#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    pub fn missing_body(mut values: [[u16; 2]; 2], outer: usize) {
        if outer < 2 {
            let replacement = unsafe { unavailable() };
            values[outer][0] = replacement;
        }
    }
    pub fn raw(values: *mut [[u16; 2]; 2], outer: usize) {
        if outer < 2 {
            unsafe { (*values)[outer][0] = 19 };
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let rows = [[3, 7], [5, 11]];
        let generic_values = [Generic {
            payload: [3, 7],
            flag: true,
        }; 2];
        let records = [[Record { left: 3, right: 7 }; 2]; 2];
        for outer in [0, 1, 2, usize::MAX] {
            first_inner(rows, outer);
            last_inner(rows, outer);
            field_then_index(generic_values, outer);
            index_then_field(records, outer);
            constant_levels([[[3, 7]; 2]; 2], outer);
            subtree([[(3, false); 2]; 2], outer);
            sequential(rows, outer);
            allocated_owner(rows, outer);
            float_char([[(f32::NAN, -0.0, '\u{d7ff}'); 2]; 2], outer);
            bytes([[3, 7]; 2], outer);
            unit_assignment(
                [Generic {
                    payload: [(); 2],
                    flag: false,
                }; 2],
                outer,
            );
            mutation_claim(outer);
        }
        lazy_roots([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63);
        for outer in [0, 17, 63, 64, usize::MAX] {
            lazy_writer_first([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], outer);
        }
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(1);
    }
    #[test]
    #[should_panic]
    fn negative_inner() {
        wrong_inner([[3, 7]; 2], 1);
    }
    #[test]
    #[should_panic]
    fn negative_outer() {
        wrong_outer([[3, 7]; 2], 0);
    }
    #[test]
    #[should_panic]
    fn negative_bounds_outer() {
        bounds_outer([[3, 7]; 2], 2);
    }
    #[test]
    #[should_panic]
    fn negative_bounds_inner() {
        bounds_inner([[3, 7]; 2], 1, 2);
    }
}
