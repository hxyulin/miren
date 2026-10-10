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
pub fn first(value: &[u16; 2]) -> u16 {
    value[0]
}
#[inline(never)]
pub fn record_left(value: &Record) -> u16 {
    value.left
}
#[inline(never)]
pub fn identity(value: &[u16; 2]) -> &[u16; 2] {
    value
}

pub fn callee(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let copied = a[outer];
        assert!(first(&a[outer]) == copied[0]);
    }
}
pub fn equality(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let copied = a[outer];
        assert!(a[outer] == copied);
    }
}
pub fn aliases(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let left = &a[outer];
        let right = left;
        assert!(first(left) == first(right));
    }
}
pub fn returned(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let copied = a[outer];
        let returned = identity(&a[outer]);
        assert!(first(returned) == copied[0]);
    }
}
pub fn refreshed(mut a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let old = first(&a[outer]);
        a[outer][1] = 19;
        assert!(first(&a[outer]) == old && a[outer][1] == 19);
    }
}
pub fn record(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], outer: usize) {
    if outer < 64 {
        let copy = a[outer];
        assert!(record_left(&a[outer]) == copy.left && a[outer] == copy);
    }
}
pub fn tuple(a: [(u16, bool); 64], _b: [(u16, bool); 64], _c: [(u16, bool); 64], outer: usize) {
    if outer < 64 {
        let copy = a[outer];
        assert!(a[outer] == copy);
    }
}
pub fn bytes(a: [[u8; 2]; 64], _b: [[u8; 2]; 64], _c: [[u8; 2]; 64], outer: usize) {
    if outer < 64 {
        let copy = a[outer];
        assert!(a[outer] == copy);
    }
}
pub fn floats(a: [(f32, f64); 64], _b: [(f32, f64); 64], _c: [(f32, f64); 64], outer: usize) {
    if outer < 64 {
        let copied = a[outer];
        let borrowed = &a[outer];
        assert!(borrowed.0.to_bits() == copied.0.to_bits());
        assert!(borrowed.1.to_bits() == copied.1.to_bits());
    }
}
pub fn zero(
    a: [([u16; 2], [(); 0]); 64],
    _b: [([u16; 2], [(); 0]); 64],
    _c: [([u16; 2], [(); 0]); 64],
    outer: usize,
) {
    if outer < 64 {
        let copied = a[outer];
        assert!(a[outer] == copied);
    }
}
pub fn mutation_claim(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        let copied = a[outer];
        if copied[0] != copied[1] {
            assert!(first(&a[outer]) == copied[0]);
        }
    }
}
pub fn different_roots(a: [[u16; 2]; 64], b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        assert!(first(&a[outer]) == first(&b[outer]));
    }
}
pub fn wrong_field(a: [Record; 64], _b: [Record; 64], _c: [Record; 64], outer: usize) {
    if outer < 64 {
        let copy = a[outer];
        assert!(record_left(&a[outer]) == copy.right);
    }
}
pub fn bounds(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    assert!(first(&a[outer]) == 0);
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
pub fn reference_zero(a: [References; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        assert!(first(&a[outer].scalar) == 0);
    }
}
pub fn refined_zero(a: [Refinement; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
    if outer < 64 {
        assert!(first(&a[outer].scalar) == 0);
    }
}
pub fn over_cap(a: [[u16; 129]; 2], _b: [[u16; 129]; 2], _c: [[u16; 129]; 2], outer: usize) {
    if outer < 2 {
        let value = &a[outer];
        assert!(value[0] == value[0]);
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
pub fn custom_equality(
    a: [FalseEquality; 64],
    _b: [FalseEquality; 64],
    _c: [FalseEquality; 64],
    outer: usize,
) {
    if outer < 64 {
        let copied = a[outer];
        assert!(a[outer] == copied);
    }
}
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn unavailable(value: &[u16; 2]) -> u16;
    }
    pub fn missing_body(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
        if outer < 64 {
            assert!(unsafe { unavailable(&a[outer]) } == 0);
        }
    }
    pub fn raw(pointer: *const [[u16; 2]; 64], outer: usize) {
        if outer < 64 {
            assert!(unsafe { first(&(*pointer)[outer]) } == 0);
        }
    }
    static VALUES: [[u16; 2]; 64] = [[3, 7]; 64];
    pub fn static_source(outer: usize) {
        if outer < 64 {
            assert!(first(&VALUES[outer]) == 3);
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn extend(value: &[u16; 2]) -> &'static [u16; 2] {
        mir! { { RET = CastTransmute(value); Return() } }
    }
    pub fn closure_escape(a: [[u16; 2]; 64], outer: usize) -> impl Fn() -> u16 {
        let borrowed = extend(&a[outer & 63]);
        move || first(borrowed)
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn extend_identity(value: &[u16; 2]) -> &'static [u16; 2] {
        mir! { { RET = value; Return() } }
    }
    pub fn closure_escape_identity(a: [[u16; 2]; 64], outer: usize) -> impl Fn() -> u16 {
        let borrowed = extend_identity(&a[outer & 63]);
        move || first(borrowed)
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn forget_handle(value: &[u16; 2]) -> u16 {
        mir! {
            let alias: &[u16; 2];
            {
                alias = value;
                StorageDead(value);
                Call(RET = first(alias), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    pub fn copied_handle(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
        if outer < 64 {
            let copy = a[outer];
            assert!(forget_handle(&a[outer]) == copy[0]);
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn owner_dead(a: [[u16; 2]; 64], outer: usize) -> u16 {
        mir! {
            let alias: &[u16; 2];
            let index: usize;
            {
                index = outer & 63;
                alias = &a[index];
                StorageDead(a);
                Call(RET = first(alias), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn frame_escape(a: [[u16; 2]; 64], outer: usize) -> &'static [u16; 2] {
        mir! {
            let index: usize;
            { index = outer & 63; RET = &a[index]; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn typed_frame_escape(
        a: [[u16; 2]; 64],
        _b: [[u16; 2]; 64],
        _c: [[u16; 2]; 64],
        outer: usize,
    ) -> &'static [u16; 2] {
        mir! {
            let index: usize;
            { index = outer & 63; RET = &a[index]; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn reborrow_write(value: &[u16; 2]) {
        mir! {
            let forged: &mut [u16; 2];
            let index: usize;
            { index = 0; forged = &mut *value; (*forged)[index] = 19; Return() }
        }
    }
    pub fn shared_reborrow(
        a: [[u16; 2]; 64],
        _b: [[u16; 2]; 64],
        _c: [[u16; 2]; 64],
        outer: usize,
    ) {
        if outer < 64 {
            reborrow_write(&a[outer]);
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn write_shared(value: &[u16; 2]) {
        mir! {
            let forged: &mut [u16; 2];
            let index: usize;
            { index = 0; forged = CastTransmute(value); (*forged)[index] = 19; Return() }
        }
    }
    pub fn shared_to_mut(a: [[u16; 2]; 64], _b: [[u16; 2]; 64], _c: [[u16; 2]; 64], outer: usize) {
        if outer < 64 {
            write_shared(&a[outer]);
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for outer in [0, 63, 64, usize::MAX] {
            let a = [[3, 7]; 64];
            callee(a, a, a, outer);
            equality(a, a, a, outer);
            aliases(a, a, a, outer);
            returned(a, a, a, outer);
            refreshed(a, a, a, outer);
            mutation_claim(a, a, a, outer);
            record(
                [Record { left: 3, right: 7 }; 64],
                [Record { left: 5, right: 11 }; 64],
                [Record {
                    left: 13,
                    right: 29,
                }; 64],
                outer,
            );
            tuple([(3, true); 64], [(5, false); 64], [(7, true); 64], outer);
            bytes([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], outer);
            floats(
                [(f32::NAN, -0.0); 64],
                [(0.0, f64::NAN); 64],
                [(1.0, 2.0); 64],
                outer,
            );
            zero(
                [([3, 7], []); 64],
                [([5, 11], []); 64],
                [([13, 29], []); 64],
                outer,
            );
        }
    }
    #[test]
    fn mutation_guard() {
        mutation_claim([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63);
    }
    #[test]
    #[should_panic]
    fn negative_roots() {
        different_roots([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 63);
    }
    #[test]
    #[should_panic]
    fn negative_field() {
        wrong_field(
            [Record { left: 3, right: 7 }; 64],
            [Record { left: 5, right: 11 }; 64],
            [Record {
                left: 13,
                right: 29,
            }; 64],
            63,
        );
    }
    #[test]
    #[should_panic]
    fn negative_custom_equality() {
        let values = [FalseEquality { left: 3, right: 7 }; 64];
        custom_equality(values, values, values, 63);
    }
    #[test]
    #[should_panic]
    fn negative_bounds() {
        bounds([[3, 7]; 64], [[5, 11]; 64], [[13, 29]; 64], 64);
    }
}
