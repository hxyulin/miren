#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[inline(never)]
pub fn read_first(values: [[u16; 2]; 64], outer: usize) -> u16 {
    let selected = values[outer];
    selected[0]
}

pub fn repeated(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let first = a[outer];
        let second = a[outer];
        assert!(first[0] == second[0] && first[1] == second[1]);
    }
}
pub fn constant_paths(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer == 0 || outer == 63 {
        let selected = a[outer];
        if outer == 0 {
            assert!(selected == a[0]);
        } else {
            assert!(selected == a[63]);
        }
    }
}
pub fn copied_root(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let copy = a;
        let first = a[outer];
        let copied = copy[outer];
        assert!(first[0] == copied[0] && first[1] == copied[1]);
    }
}
pub fn tuples(a: [(u16, bool); 64], _b: [(u16, bool); 64], _c: [(u16, bool); 64], outer: usize) {
    if outer < 64 {
        let first = a[outer];
        let second = a[outer];
        assert!(first.0 == second.0 && first.1 == second.1);
    }
}
pub fn nested(
    a: [[[u16; 2]; 2]; 32],
    _b: [[[u16; 2]; 2]; 32],
    _c: [[[u16; 2]; 2]; 32],
    outer: usize,
) {
    if outer < 32 {
        let first = a[outer];
        let second = a[outer];
        assert!(first[0][0] == second[0][0] && first[0][1] == second[0][1]);
        assert!(first[1][0] == second[1][0] && first[1][1] == second[1][1]);
    }
}
pub fn zero_child(
    a: [([u16; 2], [(); 0]); 64],
    _b: [([u16; 2], [(); 0]); 64],
    _c: [([u16; 2], [(); 0]); 64],
    outer: usize,
) {
    if outer < 64 {
        let first = a[outer];
        let second = a[outer];
        assert!(first.0 == second.0 && first.1.len() == 0 && second.1.len() == 0);
    }
}
pub fn floating(a: [(f32, f64); 64], _b: [(f32, f64); 64], _c: [(f32, f64); 64], outer: usize) {
    if outer < 64 {
        let first = a[outer];
        let second = a[outer];
        assert!(first.0.to_bits() == second.0.to_bits());
        assert!(first.1.to_bits() == second.1.to_bits());
    }
}
pub fn mutation_claim(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let selected = a[outer];
        if selected[0] != selected[1] {
            assert!(read_first(a, outer) == selected[0]);
        }
    }
}
pub fn read_then_write(mut a: [[u16; 2]; 64], b: [[u16; 2]; 64], c: [[u16; 2]; 64], outer: usize) {
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
pub fn roots_equal(a: [[u16; 2]; 64], b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let first = a[outer];
        let second = b[outer];
        assert!(first[0] == second[0]);
    }
}
pub fn offsets_equal(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64]) {
    let first = a[0];
    let last = a[63];
    assert!(first[0] == last[0]);
}
pub fn fields_equal(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let selected = a[outer];
        assert!(selected[0] == selected[1]);
    }
}
pub fn bounds(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    let selected = a[outer];
    assert!(selected[0] == selected[0]);
}
pub fn retained_borrow(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let borrowed = &a[outer];
        assert!(borrowed[0] == borrowed[0]);
    }
}
pub fn character_producer(
    a: [(f32, char); 64],
    _b: [(f32, char); 64],
    _c: [(f32, char); 64],
    outer: usize,
) {
    if outer < 64 {
        let selected = a[outer];
        assert!(selected.1 as u32 <= 0x10ffff);
    }
}
#[derive(Clone, Copy)]
pub struct References {
    pub values: [u16; 2],
    pub references: [&'static u16; 0],
}
#[derive(Clone, Copy)]
pub struct Refinement {
    pub values: [u16; 2],
    pub refined: [core::pattern_type!(u32 is 1..); 0],
}
pub fn reference_zero(a: [References; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let selected = a[outer];
        assert!(selected.values[0] == selected.values[0]);
    }
}
pub fn refined_zero(a: [Refinement; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let selected = a[outer];
        assert!(selected.values[0] == selected.values[0]);
    }
}
pub fn oversized(a: [[u16; 129]; 2], outer: usize) {
    if outer < 2 {
        let selected = a[outer];
        assert!(selected[0] == selected[0]);
    }
}
pub fn over_cap(a: [[u16; 129]; 2], _b: [[u16; 129]; 2], _c: [[u16; 129]; 2], outer: usize) {
    if outer < 2 {
        let first = a[outer];
        let second = a[outer];
        assert!(first[0] == second[0] && first[128] == second[128]);
    }
}
#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn unavailable(row: [u16; 2]) -> u16;
    }
    pub fn missing_body(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
        if outer < 64 {
            let selected = a[outer];
            assert!(unsafe { unavailable(selected) } == selected[0]);
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let rows = [[3, 7]; 64];
        for outer in [0, 63, 64, usize::MAX] {
            repeated(rows, rows, rows, outer);
            constant_paths(rows, rows, rows, outer);
            copied_root(rows, rows, rows, outer);
            tuples([(3, true); 64], [(5, false); 64], [(7, true); 64], outer);
            zero_child(
                [([3, 7], []); 64],
                [([5, 11], []); 64],
                [([13, 29], []); 64],
                outer,
            );
            floating(
                [(f32::NAN, -0.0); 64],
                [(0.0, f64::NAN); 64],
                [(1.0, 2.0); 64],
                outer,
            );
            mutation_claim(rows, rows, rows, outer);
            read_then_write(rows, rows, rows, outer);
        }
        nested(
            [[[3, 7], [5, 11]]; 32],
            [[[3, 7]; 2]; 32],
            [[[5, 11]; 2]; 32],
            31,
        );
    }
    #[test]
    fn mutation_guard() {
        let rows = [[3, 7]; 64];
        mutation_claim(rows, rows, rows, 63);
    }
    #[test]
    #[should_panic]
    fn negative_roots() {
        roots_equal([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63);
    }
    #[test]
    #[should_panic]
    fn negative_offsets() {
        let mut rows = [[3, 7]; 64];
        rows[63] = [5, 11];
        offsets_equal(rows, rows, rows);
    }
    #[test]
    #[should_panic]
    fn negative_fields() {
        fields_equal([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63);
    }
    #[test]
    #[should_panic]
    fn negative_bounds() {
        bounds([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 64);
    }
}
