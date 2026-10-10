#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub trait Parent {
    type Output;
    fn parent(&self) -> Self::Output;
}
pub trait Child: Parent<Output = u16> {
    fn child(&self) -> u16;
}
pub struct Number(pub u16);
impl Parent for Number {
    type Output = u16;
    #[inline(never)]
    fn parent(&self) -> u16 {
        self.0 & 15
    }
}
impl Child for Number {
    fn child(&self) -> u16 {
        self.0 & 7
    }
}
#[inline(never)]
fn parent_reader(value: &dyn Parent<Output = u16>) -> u16 {
    value.parent()
}
#[inline(never)]
fn as_parent(value: &dyn Child) -> &dyn Parent<Output = u16> {
    value
}
pub fn selected(value: u16) {
    let number = Number(value);
    let child: &dyn Child = &number;
    assert!(parent_reader(as_parent(child)) <= 15);
}
pub fn wrong_claim(value: u16) {
    let number = Number(value);
    let child: &dyn Child = &number;
    assert!(parent_reader(as_parent(child)) == 0);
}
pub trait Other {
    fn other(&self) -> u16;
}
pub trait Diamond: Other + Child {}
impl Other for Number {
    fn other(&self) -> u16 {
        self.0 & 3
    }
}
impl Diamond for Number {}
pub fn second_supertrait(value: u16) {
    let number = Number(value);
    let top: &dyn Diamond = &number;
    let parent: &dyn Parent<Output = u16> = top;
    assert!(parent_reader(parent) <= 15);
}
pub fn chained(value: u16) {
    let number = Number(value);
    let top: &dyn Diamond = &number;
    let child: &dyn Child = top;
    let parent: &dyn Parent<Output = u16> = child;
    assert!(parent.parent() <= 15);
    assert!(child.child() <= 7);
}
pub fn auto_trait_drop(value: u16) {
    let number = Number(value);
    let child: &(dyn Child + Send) = &number;
    let parent: &dyn Parent<Output = u16> = child;
    assert!(parent.parent() <= 15);
}
pub fn caller_backed(number: &Number) {
    let child: &dyn Child = number;
    let parent = as_parent(child);
    assert!(parent_reader(parent) <= 15);
}
pub trait MutParent {
    fn replace(&mut self, value: u16);
    fn read(&self) -> u16;
}
pub trait MutChild: MutParent {}
impl MutParent for Number {
    fn replace(&mut self, value: u16) {
        self.0 = value;
    }
    fn read(&self) -> u16 {
        self.0
    }
}
impl MutChild for Number {}
pub fn mutable_effect(value: u16) {
    let mut number = Number(0);
    let child: &mut dyn MutChild = &mut number;
    let parent: &mut dyn MutParent = child;
    parent.replace(value);
    assert!(parent.read() == value);
    assert!(number.0 == value);
}
pub fn wrong_effect(value: u16) {
    let mut number = Number(0);
    let child: &mut dyn MutChild = &mut number;
    let parent: &mut dyn MutParent = child;
    parent.replace(value);
    assert!(number.0 == 0);
}
pub fn incoming_object(value: &dyn Child) {
    assert!(as_parent(value).parent() <= 15);
}
struct Panic;
impl Parent for Panic {
    type Output = u16;
    fn parent(&self) -> u16 {
        panic!("actual parent method");
    }
}
impl Child for Panic {
    fn child(&self) -> u16 {
        0
    }
}
pub fn actual_panic() {
    let value: &dyn Child = &Panic;
    let _ = as_parent(value).parent();
}
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_owner(value: u16) -> u16 {
        mir! {
            let number: Number;
            let thin: &Number;
            let child: &dyn Child;
            let parent: &dyn Parent<Output = u16>;
            {
                number = Number(value);
                thin = &number;
                child = CastUnsize(thin);
                parent = CastUnsize(child);
                StorageDead(number);
                Call(RET = parent_reader(parent), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn escape(value: u16) -> &'static dyn Parent<Output = u16> {
        mir! {
            let number: Number;
            let thin: &Number;
            let child: &dyn Child;
            {
                number = Number(value);
                thin = &number;
                child = CastUnsize(thin);
                RET = CastUnsize(child);
                Return()
            }
        }
    }
}
#[cfg(test)]
mod native_tests {
    #[test]
    fn original() {
        for value in [0, 1, 15, 16, 255, u16::MAX] {
            super::selected(value);
            super::second_supertrait(value);
            super::chained(value);
            super::auto_trait_drop(value);
            super::caller_backed(&super::Number(value));
            super::mutable_effect(value);
        }
    }
    #[test]
    #[should_panic]
    fn false_claim() {
        super::wrong_claim(7);
    }
    #[test]
    #[should_panic]
    fn false_effect() {
        super::wrong_effect(7);
    }
    #[test]
    #[should_panic]
    fn actual_body_panic() {
        super::actual_panic();
    }
}
