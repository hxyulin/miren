#![no_std]
#![forbid(unsafe_code)]
#![feature(pattern_types, pattern_type_macro)]
extern crate alloc;
use alloc::boxed::Box;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Marker;
impl Marker {
    #[inline(never)]
    pub fn tag(&self) -> u16 {
        17
    }
}
#[derive(Clone, Copy)]
pub struct Nested {
    pub left: Marker,
    pub empty: [Marker; 0],
    pub unit: (),
}
#[derive(Clone, Copy)]
pub struct Generic<T: Copy, const N: u16> {
    pub empty: [T; 0],
    pub marker: Marker,
}
impl<T: Copy, const N: u16> Generic<T, N> {
    #[inline(never)]
    pub fn tag(&self) -> u16 {
        N
    }
}
#[derive(Copy)]
pub struct ClonePanic;
impl Clone for ClonePanic {
    #[inline(never)]
    fn clone(&self) -> Self {
        panic!()
    }
}
#[derive(Clone, Copy)]
pub struct FalseEq;
impl PartialEq for FalseEq {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}
#[inline(never)]
pub fn selected(owner: Box<Marker>) -> u16 {
    let tag = owner.tag();
    core::mem::drop(owner);
    tag
}
#[inline(never)]
pub fn transfer(owner: Box<Marker>) -> Box<Marker> {
    owner
}
pub fn fieldless() {
    assert!(selected(Box::new(Marker)) == 17);
}
pub fn wrong_tag() {
    assert!(selected(Box::new(Marker)) == 18);
}
pub fn readonly() {
    let owner = Box::new(Marker);
    assert!((&*owner).tag() == 17);
    core::mem::drop(owner);
}
pub fn automatic_drop() {
    let owner = Box::new(Marker);
    assert!(owner.tag() == 17);
}
pub fn transferred() {
    let owner = transfer(Box::new(Marker));
    assert!(owner.tag() == 17);
    core::mem::drop(owner);
}
pub fn nested() {
    let owner = Box::new(Nested {
        left: Marker,
        empty: [],
        unit: (),
    });
    assert!(owner.left.tag() == 17);
    core::mem::drop(owner);
}
pub fn nested_copy() {
    let owner = Box::new(Nested {
        left: Marker,
        empty: [],
        unit: (),
    });
    let copy = *owner;
    assert!(copy.left.tag() == 17);
    core::mem::drop(owner);
}
pub fn generic() {
    let owner = Box::new(Generic::<Marker, 17> {
        empty: [],
        marker: Marker,
    });
    assert!(owner.tag() == 17);
    core::mem::drop(owner);
}
pub fn custom_clone() {
    let owner = Box::new(ClonePanic);
    let _ = (*owner).clone();
}
pub fn custom_eq() {
    let owner = Box::new(FalseEq);
    assert!(*owner == FalseEq);
}
#[derive(Clone, Copy)]
pub struct RefZero<'a> {
    pub empty: [&'a u16; 0],
}
#[derive(Clone, Copy)]
pub struct RawZero {
    pub empty: [*const u16; 0],
}
#[derive(Clone, Copy)]
pub struct PatZero {
    pub empty: [core::pattern_type!(u16 is 1..); 0],
}
#[derive(Clone, Copy)]
pub struct CoreZero {
    pub empty: [core::marker::PhantomData<()>; 0],
}
#[repr(align(8))]
#[derive(Clone, Copy)]
pub struct Aligned;
pub struct Dropped;
impl Drop for Dropped {
    fn drop(&mut self) {}
}
#[derive(Clone, Copy)]
pub enum EmptyEnum {
    Only,
}
pub fn ref_zero() {
    core::mem::drop(Box::new(RefZero { empty: [] }));
}
pub fn raw_zero() {
    core::mem::drop(Box::new(RawZero { empty: [] }));
}
pub fn pat_zero() {
    core::mem::drop(Box::new(PatZero { empty: [] }));
}
pub fn core_zero() {
    core::mem::drop(Box::new(CoreZero { empty: [] }));
}
pub fn aligned() {
    core::mem::drop(Box::new(Aligned));
}
pub fn drop_payload() {
    core::mem::drop(Box::new(Dropped));
}
pub fn enum_payload() {
    core::mem::drop(Box::new(EmptyEnum::Only));
}
pub fn arbitrary_input(owner: Box<Marker>) {
    assert!(owner.tag() == 17);
}
#[cfg(external_control)]
pub fn external_payload() {
    core::mem::drop(Box::new(stage188_dependency::External));
}

#[cfg(external_control)]
pub fn foreign_helper() {
    let owner = Box::new(Marker);
    assert!(owner.tag() == stage188_dependency::missing_tag());
    core::mem::drop(owner);
}

#[derive(Clone, Copy)]
pub struct Weighted {
    pub a: [Marker; 128],
    pub b: [Marker; 128],
    pub c: [Marker; 128],
    pub d: [Marker; 121],
}
pub fn weighted_raw_budget() {
    let owner = Box::new(Weighted {
        a: [Marker; 128],
        b: [Marker; 128],
        c: [Marker; 128],
        d: [Marker; 121],
    });
    let a = 0_u8;
    let _a = &raw const a;
    let b = 0_u8;
    let _b = &raw const b;
    let c = 0_u8;
    let _c = &raw const c;
    core::mem::drop(owner);
}
pub fn small_raw() {
    let a = 0_u8;
    let _a = &raw const a;
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn valid_nominal_ownership() {
        fieldless();
        readonly();
        automatic_drop();
        transferred();
        nested();
        nested_copy();
        generic();
    }
    #[test]
    fn mutation_guard() {
        fieldless();
    }
    #[test]
    #[should_panic]
    fn actual_clone_body_panics() {
        custom_clone();
    }
    #[test]
    #[should_panic]
    fn actual_false_eq_body_fails() {
        custom_eq();
    }
}
