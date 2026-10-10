#![no_std]
#![feature(pattern_types, pattern_type_macro, custom_mir, core_intrinsics)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Token<const TAG: usize> {
    pub unit: (),
    pub empty: [(); 0],
}
impl<const TAG: usize> Token<TAG> {
    #[inline(never)]
    pub fn marker(&self) -> usize {
        TAG
    }
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct Aligned<T> {
    pub payload: T,
    pub empty: [(); 0],
}
#[derive(Clone, Copy)]
pub struct Nested {
    pub aligned: Aligned<Token<7>>,
    pub products: [(Token<9>, ()); 2],
}
#[derive(Clone, Copy)]
pub struct UnitName;

pub fn marker_claim(values: [Token<7>; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        assert!(copied.marker() == 7);
    }
}
pub fn whole_write(mut values: [Token<7>; 2], index: usize) {
    if index < 2 {
        values[index] = Token { unit: (), empty: [] };
        let copied = values[index];
        assert!(copied.marker() == 7 && copied.empty.len() == 0 && copied.unit == ());
    }
}
pub fn nested(values: [Nested; 2], index: usize, field: usize) {
    if index < 2 && field < 2 {
        let copied = values[index];
        assert!(copied.aligned.payload.marker() == 7);
        let product = copied.products[field];
        assert!(product.0.marker() == 9 && product.1 == ());
        assert!(core::mem::align_of_val(&copied.aligned) == 64);
    }
}
pub fn nested_copy(values: [Nested; 2], index: usize, field: usize) {
    if index < 2 && field < 2 {
        let copied = values[index];
        assert!(copied.aligned.payload.marker() == 7);
        let product = copied.products[field];
        assert!(product.0.marker() == 9 && product.1 == ());
    }
}

pub fn unit_name(mut values: [UnitName; 2], index: usize) {
    if index < 2 {
        values[index] = UnitName;
        let copied = values[index];
        assert!(core::mem::size_of_val(&copied) == 0);
    }
}
pub fn zero_tuple(mut values: [(Token<7>, [Token<9>; 2]); 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        assert!(copied.0.marker() == 7 && copied.1[1].marker() == 9);
        values[index] = copied;
        let again = values[index];
        assert!(again.0.marker() == 7 && again.1[0].marker() == 9);
    }
}
pub fn maximum_slice(values: &[Aligned<Token<7>>]) {
    assert!(core::mem::size_of_val(values) == 0);
    assert!(core::mem::align_of_val(values) == 64);
    if values.len() == usize::MAX {
        let mut iter = values.iter();
        assert!(iter.nth(usize::MAX - 1).unwrap().payload.marker() == 7);
        assert!(iter.next().is_none());
    }
}
#[derive(Copy)]
pub struct OrdinaryClone;
impl Clone for OrdinaryClone {
    #[inline(never)]
    fn clone(&self) -> Self { Self }
}
pub fn real_clone(values: [OrdinaryClone; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        let cloned = copied.clone();
        assert!(core::mem::size_of_val(&cloned) == 0);
    }
}
pub fn wrong_marker(values: [Token<9>; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        assert!(copied.marker() == 7);
    }
}
#[derive(Clone, Copy)]
pub struct FalseEquality;
impl PartialEq for FalseEquality {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool { false }
}
pub fn real_equality(values: [FalseEquality; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        assert!(copied == copied);
    }
}
#[derive(Copy)]
pub struct PanickingClone;
impl Clone for PanickingClone {
    #[inline(never)]
    fn clone(&self) -> Self { panic!("actual clone body") }
}
pub fn clone_panic(values: [PanickingClone; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        let _ = copied.clone();
    }
}
pub fn bounds(values: [Token<7>; 2], index: usize) {
    let copied = values[index];
    assert!(copied.marker() == 7);
}
#[derive(Clone, Copy)]
pub struct ReferenceField { pub field: [&'static u16; 0] }
#[derive(Clone, Copy)]
pub struct PatField { pub field: [core::pattern_type!(u32 is 1..); 0] }
#[derive(Clone, Copy)]
pub struct CoreField { pub field: [core::marker::PhantomData<&'static u16>; 0] }
pub struct Dropped;
impl Drop for Dropped { fn drop(&mut self) {} }
pub fn reference_zero(values: [ReferenceField; 2], index: usize) {
    if index < 2 { let copied = values[index]; assert!(core::mem::size_of_val(&copied) == 0); }
}
pub fn refined_zero(values: [PatField; 2], index: usize) {
    if index < 2 { let copied = values[index]; assert!(core::mem::size_of_val(&copied) == 0); }
}
pub fn core_zero(values: [CoreField; 2], index: usize) {
    if index < 2 { let copied = values[index]; assert!(core::mem::size_of_val(&copied) == 0); }
}
pub fn drop_zero(values: [Dropped; 2], index: usize) {
    if index < 2 { let _ = &values[index]; }
}
pub fn oversized(values: [[Token<7>; 129]; 2], index: usize) {
    if index < 2 { let copied = values[index]; assert!(copied[0].marker() == 7); }
}
pub fn retained_borrow(values: [Token<7>; 2], index: usize) {
    if index < 2 { assert!(values[index].marker() == 7); }
}

#[cfg(test)]
mod native {
    use super::*;
    fn token<const N: usize>() -> Token<N> { Token {unit: (), empty: []} }
    #[test]
    fn positives() {
        for index in [0, 1, 2, usize::MAX] {
            marker_claim([token(); 2], index);
            whole_write([token(); 2], index);
            unit_name([UnitName; 2], index);
            zero_tuple([(token(), [token();2]);2], index);
            nested([Nested { aligned: Aligned {payload:token(), empty:[]},
                products:[(token(),());2] };2], index, 1);
            nested_copy([Nested { aligned: Aligned {payload:token(), empty:[]},
                products:[(token(),());2] };2], index, 1);
            real_clone([OrdinaryClone;2], index);
        }
        let values = [Aligned {payload:token::<7>(), empty:[]};usize::MAX];
        maximum_slice(&values);
    }
    #[test]
    fn mutation_guard() { marker_claim([token();2], 1); }
    #[test]
    #[should_panic]
    fn negative_marker() { wrong_marker([token();2], 1); }
    #[test]
    #[should_panic]
    fn negative_equality() { real_equality([FalseEquality;2], 1); }
    #[test]
    #[should_panic]
    fn negative_clone() { clone_panic([PanickingClone;2], 1); }
    #[test]
    #[should_panic]
    fn negative_bounds() { bounds([token();2], 2); }
}


#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    fn metadata(values: &[super::Token<7>; 0]) -> usize { values.len() }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [super::Token<7>; 0];
            let alias: &[super::Token<7>; 0];
            { backing = []; alias = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = metadata(alias), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}
