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
#[inline(never)]
pub fn change(mut values: [[u16; 2]; 2], outer: usize, inner: usize) -> [[u16; 2]; 2] {
    values[outer][inner] = 19;
    values
}
#[inline(never)]
pub fn first(values: &[[u16; 2]; 2]) -> u16 {
    values[0][0]
}
#[inline(never)]
pub fn effect(counter: &mut u16) {
    *counter += 1;
}
pub fn selected(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let before = values;
        values[outer][inner] = 19;
        let changed = values[outer];
        let original = before[outer];
        let untouched = values[outer ^ 1];
        assert!(changed[inner] == 19 && changed[inner ^ 1] == original[inner ^ 1]);
        assert!(untouched == before[outer ^ 1]);
    }
}
pub fn copied(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let copy = values;
        values[outer][inner] = 19;
        let changed = values[outer];
        let original = copy[outer];
        assert!(changed[inner] == 19 && changed[inner ^ 1] == original[inner ^ 1]);
        assert!(copy[outer] == original);
    }
}
pub fn sequential(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer][inner] = 19;
        values[outer][inner] = 23;
        values[outer][inner ^ 1] = 29;
        let changed = values[outer];
        assert!(changed[inner] == 23 && changed[inner ^ 1] == 29);
    }
}
pub fn field_prefix(mut values: [Generic<[u16; 2]>; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = values[outer];
        values[outer].payload[inner] = 19;
        let changed = values[outer];
        assert!(changed.payload[inner] == 19 && changed.flag == old.flag);
        assert!(changed.payload[inner ^ 1] == old.payload[inner ^ 1]);
    }
}
pub fn field_suffix(mut values: [[Record; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = values[outer];
        values[outer][inner].left = 19;
        let changed = values[outer];
        let selected = changed[inner];
        let original = old[inner];
        let sibling = changed[inner ^ 1];
        let old_sibling = old[inner ^ 1];
        assert!(selected.left == 19 && selected.right == original.right);
        assert!(sibling.left == old_sibling.left && sibling.right == old_sibling.right);
    }
}
pub fn fixed_grandchild(mut values: [[[u16; 2]; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = values[outer];
        values[outer][inner][0] = 19;
        let changed = values[outer];
        let selected = changed[inner];
        let original = old[inner];
        assert!(selected[0] == 19 && selected[1] == original[1]);
        assert!(changed[inner ^ 1] == old[inner ^ 1]);
    }
}
pub fn bytes(mut values: [[u8; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let before = values;
        values[outer][inner] = 19;
        let selected = values[outer];
        let original = before[outer];
        assert!(selected[inner] == 19 && selected[inner ^ 1] == original[inner ^ 1]);
    }
}
pub fn float_char(mut values: [[(f32, f64, char); 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = values[outer];
        values[outer][inner] = (-0.0, 1.0, '\u{10ffff}');
        let changed = values[outer];
        let selected = changed[inner];
        let sibling = changed[inner ^ 1];
        let original = old[inner ^ 1];
        assert!(selected.0.to_bits() == 0x80000000 && selected.1 == 1.0);
        assert!(selected.2 == '\u{10ffff}');
        assert!(sibling.0.to_bits() == original.0.to_bits());
        assert!(sibling.1.to_bits() == original.1.to_bits() && sibling.2 == original.2);
    }
}
pub fn unit_effect(mut values: [Generic<[(); 2]>; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = values[outer];
        let mut counter = 0;
        values[outer].payload[inner] = effect(&mut counter);
        let changed = values[outer];
        assert!(counter == 1 && changed.flag == old.flag);
    }
}
pub fn allocated(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let old = first(&values);
        values[outer][inner] = 19;
        let selected = values[outer];
        assert!(selected[inner] == 19);
        if outer != 0 || inner != 0 {
            assert!(first(&values) == old);
        }
    }
}
pub fn lazy_roots(
    mut a: [[u16; 2]; 64],
    b: [[u16; 2]; 64],
    c: [[u16; 2]; 64],
    outer: usize,
    inner: usize,
) {
    if outer < 64 && inner < 2 {
        let old = a[outer];
        let old_b = b[0];
        let old_c = c[63];
        a[outer][inner] = 19;
        let selected = a[outer];
        assert!(selected[inner] == 19 && selected[inner ^ 1] == old[inner ^ 1]);
        assert!(b[0] == old_b && c[63] == old_c);
    }
}
pub fn mutation_claim(outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        let original = [[3, 7], [5, 11]];
        let changed = change(original, outer, inner);
        let selected = changed[outer];
        let before = original[outer];
        assert!(selected[inner] == 19 && selected[inner ^ 1] == before[inner ^ 1]);
        assert!(changed[outer ^ 1] == original[outer ^ 1]);
    }
}
pub fn wrong_inner(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer][inner] = 19;
        let selected = values[outer];
        assert!(selected[inner ^ 1] == 19);
    }
}
pub fn wrong_outer(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer][inner] = 19;
        let selected = values[outer ^ 1];
        assert!(selected[inner] == 19);
    }
}
pub fn bounds_outer(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if inner < 2 {
        values[outer][inner] = 19;
    }
}
pub fn bounds_inner(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 {
        values[outer][inner] = 19;
    }
}
pub fn dynamic_twice(mut values: [[[u16; 2]; 2]; 2], outer: usize, inner: usize, last: usize) {
    if outer < 2 && inner < 2 && last < 2 {
        values[outer][inner][last] = 19;
    }
}
pub fn retained(values: &mut [[u16; 2]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer][inner] = 19;
    }
}
pub fn known_outer(mut values: [[u16; 2]; 2], inner: usize) {
    if inner < 2 {
        values[0][inner] = 19;
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
pub fn reference_zero(mut values: [References; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer].scalar[inner] = 19;
    }
}
pub fn refined_zero(mut values: [Refinement; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 2 {
        values[outer].scalar[inner] = 19;
    }
}
pub fn oversized(mut values: [[u16; 129]; 2], outer: usize, inner: usize) {
    if outer < 2 && inner < 129 {
        values[outer][inner] = 19;
    }
}
#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    pub fn missing_body(mut values: [[u16; 2]; 2], outer: usize, inner: usize) {
        if outer < 2 && inner < 2 {
            values[outer][inner] = unsafe { unavailable() };
        }
    }
    pub fn raw(pointer: *mut [[u16; 2]; 2], outer: usize, inner: usize) {
        if outer < 2 && inner < 2 {
            unsafe {
                (*pointer)[outer][inner] = 19;
            }
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for outer in 0..2 {
            for inner in 0..2 {
                let values = [[3, 7], [5, 11]];
                selected(values, outer, inner);
                copied(values, outer, inner);
                sequential(values, outer, inner);
                allocated(values, outer, inner);
                field_prefix(
                    [Generic {
                        payload: [3, 7],
                        flag: true,
                    }; 2],
                    outer,
                    inner,
                );
                field_suffix([[Record { left: 3, right: 7 }; 2]; 2], outer, inner);
                fixed_grandchild([[[3, 7]; 2]; 2], outer, inner);
                bytes([[3, 7], [5, 11]], outer, inner);
                float_char([[(f32::NAN, -0.0, '\u{10ffff}'); 2]; 2], outer, inner);
                unit_effect(
                    [Generic {
                        payload: [(), ()],
                        flag: true,
                    }; 2],
                    outer,
                    inner,
                );
                mutation_claim(outer, inner);
            }
        }
        lazy_roots([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63, 1);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(1, 0);
    }
    #[test]
    #[should_panic]
    fn negative_inner() {
        wrong_inner([[3, 7], [5, 11]], 1, 0);
    }
    #[test]
    #[should_panic]
    fn negative_outer() {
        wrong_outer([[3, 7], [5, 11]], 1, 0);
    }
    #[test]
    #[should_panic]
    fn negative_outer_bounds() {
        bounds_outer([[3, 7], [5, 11]], 2, 0);
    }
    #[test]
    #[should_panic]
    fn negative_inner_bounds() {
        bounds_inner([[3, 7], [5, 11]], 0, 2);
    }
}
