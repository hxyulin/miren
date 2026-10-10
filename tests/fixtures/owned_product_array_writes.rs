#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[derive(Clone, Copy)]
pub struct Product<T> {
    pub values: T,
    pub marker: u16,
}

pub fn selected(mut values: ([Record; 2], u16), index: usize) {
    if index < 2 {
        let old = values;
        values.0[index].left = 19;
        let changed = values.0[index];
        let original = old.0[index];
        let sibling = values.0[index ^ 1];
        let old_sibling = old.0[index ^ 1];
        assert!(changed.left == 19 && changed.right == original.right);
        assert!(sibling.left == old_sibling.left && sibling.right == old_sibling.right);
        assert!(values.1 == old.1);
    }
}

pub fn wrong_field(mut values: ([Record; 2], u16), index: usize) {
    if index < 2 {
        values.0[index].left = 19;
        let changed = values.0[index];
        assert!(changed.right == 19);
    }
}

pub fn bytes(mut values: ([u8; 2], bool), index: usize) {
    if index < 2 {
        let old = values;
        values.0[index] = 19;
        assert!(values.0[index] == 19 && values.0[index ^ 1] == old.0[index ^ 1]);
        assert!(values.1 == old.1);
    }
}

pub fn lazy_roots(
    mut a: Product<[Record; 64]>,
    b: Product<[Record; 64]>,
    c: Product<[Record; 64]>,
    index: usize,
) {
    if index < 64 {
        let old = a.values[index];
        let old_b = b.values[0];
        let old_c = c.values[63];
        let marker = a.marker;
        a.values[index].left = 19;
        let selected = a.values[index];
        assert!(selected.left == 19 && selected.right == old.right);
        assert!(a.marker == marker);
        assert!(b.values[0].left == old_b.left && b.values[0].right == old_b.right);
        assert!(c.values[63].left == old_c.left && c.values[63].right == old_c.right);
    }
}

#[inline(never)]
pub fn change(mut values: ([u16; 2], u16), index: usize) -> ([u16; 2], u16) {
    values.0[index] = 19;
    values
}
#[inline(never)]
pub fn first(values: &([u16; 2], u16)) -> u16 {
    values.0[0]
}
#[inline(never)]
pub fn observe(values: &[u16; 2], index: usize) -> u16 {
    values[index]
}
#[inline(never)]
pub fn effect(counter: &mut u16) {
    *counter += 1;
}
#[inline(never)]
pub fn panic_unit() {
    panic!("actual replacement body");
}

pub fn named(mut values: Product<[Record; 2]>, index: usize) {
    if index < 2 {
        let old = values;
        values.values[index].left = 19;
        let selected = values.values[index];
        assert!(selected.left == 19 && selected.right == old.values[index].right);
        assert!(values.marker == old.marker);
    }
}
pub fn nested(mut values: (Product<([Record; 2], bool)>, u32), index: usize) {
    if index < 2 {
        let old = values;
        values.0.values.0[index].left = 19;
        let selected = values.0.values.0[index];
        assert!(selected.left == 19 && selected.right == old.0.values.0[index].right);
        assert!(values.0.values.1 == old.0.values.1);
        assert!(values.0.marker == old.0.marker && values.1 == old.1);
    }
}
pub fn generic(mut values: Product<[[u16; 2]; 2]>, index: usize) {
    if index < 2 {
        let old = values;
        values.values[index][0] = 19;
        let selected = values.values[index];
        assert!(selected[0] == 19 && selected[1] == old.values[index][1]);
        assert!(values.values[index ^ 1] == old.values[index ^ 1]);
        assert!(values.marker == old.marker);
    }
}
pub fn sequential(mut values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let marker = values.1;
        values.0[index] = 19;
        values.0[index] = 23;
        values.0[index ^ 1] = 29;
        assert!(values.0[index] == 23 && values.0[index ^ 1] == 29);
        assert!(values.1 == marker);
    }
}
pub fn copied(mut values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let copy = values;
        values.0[index] = 19;
        assert!(values.0[index] == 19 && values.0[index ^ 1] == copy.0[index ^ 1]);
        assert!(values.1 == copy.1);
    }
}
pub fn allocated(mut values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let old = first(&values);
        values.0[index] = 19;
        assert!(values.0[index] == 19);
        if index != 0 {
            assert!(first(&values) == old);
        }
    }
}
pub fn retained_alias(mut values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let before = observe(&values.0, index);
        values.0[index] = before.wrapping_add(1);
        assert!(observe(&values.0, index) == before.wrapping_add(1));
    }
}
pub fn float_char(mut values: ([(f32, f64, char); 2], u16), index: usize) {
    if index < 2 {
        let old = values;
        values.0[index] = (-0.0, 1.0, '\u{10ffff}');
        let selected = values.0[index];
        let sibling = values.0[index ^ 1];
        let original = old.0[index ^ 1];
        assert!(selected.0.to_bits() == 0x80000000 && selected.1 == 1.0);
        assert!(selected.2 == '\u{10ffff}');
        assert!(sibling.0.to_bits() == original.0.to_bits());
        assert!(sibling.1.to_bits() == original.1.to_bits() && sibling.2 == original.2);
        assert!(values.1 == old.1);
    }
}
pub fn unit_effect(mut values: ([(); 2], u16), index: usize) {
    if index < 2 {
        let marker = values.1;
        let mut count = 0;
        values.0[index] = effect(&mut count);
        assert!(count == 1 && values.1 == marker);
    }
}
#[derive(Clone, Copy)]
pub struct Zero;
#[inline(never)]
pub fn zero_effect(counter: &mut u16) -> Zero {
    effect(counter);
    Zero
}
pub fn nominal_zero(mut values: ([Zero; 2], u16), index: usize) {
    if index < 2 {
        let marker = values.1;
        let mut count = 0;
        values.0[index] = zero_effect(&mut count);
        let _selected = values.0[index];
        assert!(count == 1 && values.1 == marker);
    }
}
pub fn mutation_claim(index: usize) {
    if index < 2 {
        let original = ([3, 7], 11);
        let changed = change(original, index);
        assert!(changed.0[index] == 19 && changed.0[index ^ 1] == original.0[index ^ 1]);
        assert!(changed.1 == original.1);
    }
}
pub fn wrong_row(mut values: Product<[[u16; 2]; 2]>, index: usize) {
    if index < 2 {
        values.values[index][0] = 19;
        assert!(values.values[index ^ 1][0] == 19);
    }
}
pub fn wrong_sibling(mut values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        values.0[index] = 19;
        assert!(values.1 == 19);
    }
}
pub fn bounds(mut values: ([u16; 2], u16), index: usize) -> ([u16; 2], u16) {
    values.0[index] = 19;
    values
}
pub fn panicking_effect(mut values: ([(); 2], u16), index: usize) -> ([(); 2], u16) {
    if index < 2 {
        values.0[index] = panic_unit();
    }
    values
}
pub fn dynamic_twice(
    mut values: ([[u16; 2]; 2], u16),
    outer: usize,
    inner: usize,
) -> ([[u16; 2]; 2], u16) {
    if outer < 2 && inner < 2 {
        values.0[outer][inner] = 19;
    }
    values
}
pub fn retained(values: &mut ([u16; 2], u16), index: usize) {
    if index < 2 {
        values.0[index] = 19;
    }
}
pub fn reference_zero(
    mut values: ([u16; 2], [&'static u16; 0]),
    index: usize,
) -> ([u16; 2], [&'static u16; 0]) {
    if index < 2 {
        values.0[index] = 19;
    }
    values
}
pub type Refined = core::pattern_type!(u16 is 1..);
pub fn refined_zero(
    mut values: ([u16; 2], [Refined; 0]),
    index: usize,
) -> ([u16; 2], [Refined; 0]) {
    if index < 2 {
        values.0[index] = 19;
    }
    values
}
pub struct Dropped;
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn drop_zero(mut values: ([u16; 2], [Dropped; 0]), index: usize) {
    if index < 2 {
        values.0[index] = 19;
    }
}
pub fn core_zero(
    mut values: ([u16; 2], [core::num::NonZeroU16; 0]),
    index: usize,
) -> ([u16; 2], [core::num::NonZeroU16; 0]) {
    if index < 2 {
        values.0[index] = 19;
    }
    values
}
pub fn oversized(mut values: ([u16; 129], u16), index: usize) -> ([u16; 129], u16) {
    if index < 129 {
        values.0[index] = 19;
    }
    values
}
#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    #[inline(never)]
    fn replacement() -> u16 {
        19
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn call_write(mut values: ([u16; 2], u16), index: usize) -> ([u16; 2], u16) {
        mir! {
            { Call(values.0[index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { RET = values; Return() }
        }
    }
    pub fn call_destination(values: ([u16; 2], u16), index: usize) {
        if index < 2 {
            let changed = call_write(values, index);
            assert!(changed.0[index] == 19);
        }
    }
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    pub fn missing_body(mut values: ([u16; 2], u16), index: usize) {
        if index < 2 {
            values.0[index] = unsafe { unavailable() };
        }
    }
    pub fn raw(pointer: *mut ([u16; 2], u16), index: usize) {
        if index < 2 {
            unsafe {
                (*pointer).0[index] = 19;
            }
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for index in 0..2 {
            let records = [Record { left: 3, right: 7 }; 2];
            selected((records, 11), index);
            named(
                Product {
                    values: records,
                    marker: 11,
                },
                index,
            );
            nested(
                (
                    Product {
                        values: (records, true),
                        marker: 11,
                    },
                    13,
                ),
                index,
            );
            generic(
                Product {
                    values: [[3, 7], [5, 11]],
                    marker: 13,
                },
                index,
            );
            sequential(([3, 7], 11), index);
            copied(([3, 7], 11), index);
            allocated(([3, 7], 11), index);
            retained_alias(([3, 7], 11), index);
            bytes(([3, 7], true), index);
            float_char(([(f32::NAN, -0.0, '\u{10ffff}'); 2], 11), index);
            unit_effect(([(); 2], 11), index);
            nominal_zero(([Zero; 2], 11), index);
            mutation_claim(index);
        }
        let a = Product {
            values: [Record { left: 3, right: 7 }; 64],
            marker: 11,
        };
        lazy_roots(a, a, a, 63);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(0);
    }
    #[test]
    #[should_panic]
    fn negative_field() {
        wrong_field(([Record { left: 3, right: 7 }; 2], 11), 0);
    }
    #[test]
    #[should_panic]
    fn negative_row() {
        wrong_row(
            Product {
                values: [[3, 7], [5, 11]],
                marker: 13,
            },
            0,
        );
    }
    #[test]
    #[should_panic]
    fn negative_sibling() {
        wrong_sibling(([3, 7], 11), 0);
    }
    #[test]
    #[should_panic]
    fn negative_bounds() {
        let _ = bounds(([3, 7], 11), 2);
    }
    #[test]
    #[should_panic]
    fn negative_effect() {
        let _ = panicking_effect(([(); 2], 11), 0);
    }
}
