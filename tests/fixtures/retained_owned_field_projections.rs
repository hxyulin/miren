#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]
#[derive(Clone, Copy)]
pub struct Product<T> {
    pub values: T,
    pub marker: u16,
}
#[inline(never)]
pub fn first(value: &[u16; 2]) -> u16 {
    value[0]
}
#[inline(never)]
pub fn identity(value: &[u16; 2]) -> &[u16; 2] {
    value
}
pub fn tuple(
    a: ([[u16; 2]; 64], u16),
    _b: ([[u16; 2]; 64], u16),
    _c: ([[u16; 2]; 64], u16),
    index: usize,
) {
    if index < 64 {
        let copied = a.0[index];
        assert!(first(&a.0[index]) == copied[0]);
    }
}
pub fn named(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let copied = a.values[index];
        let returned = identity(&a.values[index]);
        assert!(first(returned) == copied[0]);
    }
}
pub fn wrong_field(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let copied = a.values[index];
        assert!(first(&a.values[index]) == copied[1]);
    }
}
pub fn bounds(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    let _value = first(&a.values[index]);
}
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    unsafe extern "Rust" {
        fn unavailable(value: &[u16; 2]) -> u16;
    }
    pub fn missing_body(
        a: Product<[[u16; 2]; 64]>,
        _b: Product<[[u16; 2]; 64]>,
        _c: Product<[[u16; 2]; 64]>,
        index: usize,
    ) {
        if index < 64 {
            let copied = a.values[index];
            let result = unsafe { unavailable(&a.values[index]) };
            assert!(result == copied[0]);
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let arrays = [[3, 7]; 64];
        tuple((arrays, 11), (arrays, 13), (arrays, 17), 63);
        let p = Product {
            values: arrays,
            marker: 11,
        };
        named(p, p, p, 63);
    }
    #[test]
    #[should_panic]
    fn wrong() {
        let p = Product {
            values: [[3, 7]; 64],
            marker: 11,
        };
        wrong_field(p, p, p, 63);
    }
    #[test]
    #[should_panic]
    fn out_of_bounds() {
        let p = Product {
            values: [[3, 7]; 64],
            marker: 11,
        };
        bounds(p, p, p, 64);
    }
}

pub fn nested(
    a: (Product<[[u16; 2]; 64]>, bool),
    _b: (Product<[[u16; 2]; 64]>, bool),
    _c: (Product<[[u16; 2]; 64]>, bool),
    index: usize,
) {
    if index < 64 {
        let copy = a.0.values[index];
        assert!(first(&a.0.values[index]) == copy[0]);
    }
}
pub fn equality(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let copy = a.values[index];
        assert!(a.values[index] == copy);
    }
}
pub fn aliases(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let original = &a.values[index];
        let copy = original;
        assert!(first(original) == first(copy));
    }
}
pub fn refreshed(
    mut a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let old = first(&a.values[index]);
        a.values[index][1] = 19;
        assert!(first(&a.values[index]) == old && a.values[index][1] == 19);
    }
}
#[derive(Clone, Copy, PartialEq)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[inline(never)]
pub fn record_left(value: &Record) -> u16 {
    value.left
}
pub fn record(
    a: Product<[Record; 64]>,
    _b: Product<[Record; 64]>,
    _c: Product<[Record; 64]>,
    index: usize,
) {
    if index < 64 {
        let copy = a.values[index];
        assert!(record_left(&a.values[index]) == copy.left && a.values[index] == copy);
    }
}
pub fn floats(
    a: Product<[(f32, f64); 64]>,
    _b: Product<[(f32, f64); 64]>,
    _c: Product<[(f32, f64); 64]>,
    index: usize,
) {
    if index < 64 {
        let copy = a.values[index];
        let borrowed = &a.values[index];
        assert!(borrowed.0.to_bits() == copy.0.to_bits());
        assert!(borrowed.1.to_bits() == copy.1.to_bits());
    }
}
pub fn characters(a: Product<[(char, u16); 64]>, index: usize) {
    if index < 64 {
        let copy = a.values[index];
        let borrowed = &a.values[index];
        assert!(borrowed.0 == copy.0 && borrowed.1 == copy.1);
    }
}
pub fn bytes(
    a: Product<[[u8; 2]; 64]>,
    _b: Product<[[u8; 2]; 64]>,
    _c: Product<[[u8; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let copy = a.values[index];
        assert!(a.values[index] == copy);
    }
}
#[derive(Clone, Copy)]
pub struct Zero;
#[inline(never)]
pub fn zero_marker(_value: &Zero) -> u16 {
    17
}
pub fn zero(a: Product<[Zero; 64]>, index: usize) {
    if index < 64 {
        assert!(zero_marker(&a.values[index]) == 17);
    }
}
pub fn mutation_claim(
    a: Product<[[u16; 2]; 64]>,
    _b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        let copy = a.values[index];
        if copy[0] != copy[1] {
            assert!(first(&a.values[index]) == copy[0]);
        }
    }
}
pub fn different_roots(
    a: Product<[[u16; 2]; 64]>,
    b: Product<[[u16; 2]; 64]>,
    _c: Product<[[u16; 2]; 64]>,
    index: usize,
) {
    if index < 64 {
        assert!(first(&a.values[index]) == first(&b.values[index]));
    }
}
#[derive(Clone, Copy)]
pub struct FalseEquality {
    pub left: u16,
    pub right: u16,
}
impl PartialEq for FalseEquality {
    #[inline(never)]
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
pub fn actual_false_equality(
    a: Product<[FalseEquality; 64]>,
    _b: Product<[FalseEquality; 64]>,
    _c: Product<[FalseEquality; 64]>,
    index: usize,
) {
    if index < 64 {
        assert!(a.values[index] == a.values[index]);
    }
}
pub fn reference_zero(a: (Product<[[u16; 2]; 64]>, [&'static u16; 0]), index: usize) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn refined_zero(
    a: (
        Product<[[u16; 2]; 64]>,
        [core::pattern_type!(u16 is 1..); 0],
    ),
    index: usize,
) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn core_zero(a: (Product<[[u16; 2]; 64]>, [core::num::NonZeroU16; 0]), index: usize) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn over_cap(
    a: Product<[[u16; 129]; 2]>,
    _b: Product<[[u16; 129]; 2]>,
    _c: Product<[[u16; 129]; 2]>,
    index: usize,
) {
    if index < 2 {
        assert!(large_first(&a.values[index]) == a.values[index][0]);
    }
}
pub fn mutable_root(a: &mut Product<[[u16; 2]; 64]>, index: usize) {
    if index < 64 {
        let _ = first(&a.values[index]);
    }
}
#[cfg(not(test))]
mod lifecycle {
    use super::*;
    use core::intrinsics::mir::*;
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn frame_escape(a: Product<[[u16; 2]; 64]>, index: usize) -> &'static [u16; 2] {
        mir! { let selected: usize; { selected = index & 63; RET = &a.values[selected]; Return() } }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_owner(a: Product<[[u16; 2]; 64]>, index: usize) -> u16 {
        mir! {
            let selected: usize; let borrowed: &[u16; 2];
            { selected = index & 63; borrowed = &a.values[selected]; StorageDead(a);
              Call(RET = first(borrowed), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn reborrow_write(value: &[u16; 2]) -> u16 {
        mir! { let forged: &mut [u16; 2]; { forged = &mut *value; RET = 17; Return() } }
    }
    pub fn shared_to_mut(
        a: Product<[[u16; 2]; 64]>,
        _b: Product<[[u16; 2]; 64]>,
        _c: Product<[[u16; 2]; 64]>,
        index: usize,
    ) {
        if index < 64 {
            assert!(reborrow_write(&a.values[index]) == 17);
        }
    }
    pub fn raw(pointer: *const Product<[[u16; 2]; 64]>, index: usize) {
        if index < 64 {
            let _ = first(unsafe { &(*pointer).values[index] });
        }
    }
}
#[cfg(test)]
mod extra_native {
    use super::*;
    #[test]
    fn positives() {
        let p = Product {
            values: [[3, 7]; 64],
            marker: 11,
        };
        for index in [0, 63] {
            nested((p, true), (p, false), (p, true), index);
            equality(p, p, p, index);
            aliases(p, p, p, index);
            refreshed(p, p, p, index);
            mutation_claim(p, p, p, index);
            let r = Product {
                values: [Record { left: 3, right: 7 }; 64],
                marker: 11,
            };
            record(r, r, r, index);
            let f = Product {
                values: [(f32::NAN, -0.0); 64],
                marker: 11,
            };
            floats(f, f, f, index);
            characters(
                Product {
                    values: [('\u{10ffff}', 7); 64],
                    marker: 11,
                },
                index,
            );
            let b = Product {
                values: [[3, 7]; 64],
                marker: 11,
            };
            bytes(b, b, b, index);
            zero(
                Product {
                    values: [Zero; 64],
                    marker: 11,
                },
                index,
            );
        }
    }
    #[test]
    fn mutation_guard() {
        let p = Product {
            values: [[3, 7]; 64],
            marker: 11,
        };
        mutation_claim(p, p, p, 63);
    }
    #[test]
    #[should_panic]
    fn distinct_roots() {
        let a = Product {
            values: [[3, 7]; 64],
            marker: 11,
        };
        let b = Product {
            values: [[5, 7]; 64],
            marker: 11,
        };
        different_roots(a, b, a, 63);
    }
    #[test]
    #[should_panic]
    fn false_equality() {
        let p = Product {
            values: [FalseEquality { left: 3, right: 7 }; 64],
            marker: 11,
        };
        actual_false_equality(p, p, p, 63);
    }
}

#[inline(never)]
pub fn large_first(value: &[u16; 129]) -> u16 {
    value[0]
}

pub fn lazy_reference_zero(
    a: (Product<[[u16; 2]; 64]>, [&'static u16; 0]),
    _b: (Product<[[u16; 2]; 64]>, [&'static u16; 0]),
    _c: (Product<[[u16; 2]; 64]>, [&'static u16; 0]),
    index: usize,
) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn lazy_refined_zero(
    a: (
        Product<[[u16; 2]; 64]>,
        [core::pattern_type!(u16 is 1..); 0],
    ),
    _b: (
        Product<[[u16; 2]; 64]>,
        [core::pattern_type!(u16 is 1..); 0],
    ),
    _c: (
        Product<[[u16; 2]; 64]>,
        [core::pattern_type!(u16 is 1..); 0],
    ),
    index: usize,
) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn lazy_core_zero(
    a: (Product<[[u16; 2]; 64]>, [core::num::NonZeroU16; 0]),
    _b: (Product<[[u16; 2]; 64]>, [core::num::NonZeroU16; 0]),
    _c: (Product<[[u16; 2]; 64]>, [core::num::NonZeroU16; 0]),
    index: usize,
) {
    if index < 64 {
        let _ = first(&a.0.values[index]);
    }
}
pub fn direct_array(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], index: usize) {
    if index < 64 {
        let copy = a[index];
        assert!(first(&a[index]) == copy[0]);
    }
}
#[inline(never)]
pub fn byte_first(value: &[u8; 2]) -> u8 {
    value[0]
}
pub fn direct_bytes(a: [[u8; 2]; 64], _b: [[u8; 2]; 64], _c: [[u8; 2]; 64], index: usize) {
    if index < 64 {
        let copy = a[index];
        assert!(byte_first(&a[index]) == copy[0]);
    }
}
static STATIC: Product<[[u16; 2]; 2]> = Product {
    values: [[3, 7]; 2],
    marker: 11,
};
pub fn static_source(index: usize) {
    if index < 2 {
        assert!(first(&STATIC.values[index]) == 3);
    }
}
