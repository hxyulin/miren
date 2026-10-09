#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub trait Read {
    type Output;
    fn read(&self) -> Self::Output;
    fn expected(&self) -> Self::Output;
}

pub struct Number(u8);

impl Read for Number {
    type Output = u8;
    fn read(&self) -> u8 {
        self.0 & 15
    }
    fn expected(&self) -> u8 {
        self.0 & 15
    }
}

struct Different(u8);

impl Read for Different {
    type Output = u8;
    fn read(&self) -> u8 {
        self.0
    }
    fn expected(&self) -> u8 {
        self.0 & 15
    }
}

#[inline(never)]
fn through_object(value: &dyn Read<Output = u8>) -> u8 {
    value.read()
}

pub fn concrete_shared(value: u8) {
    let number = Number(value);
    let object: &dyn Read<Output = u8> = &number;
    assert!(through_object(object) <= 15);
    assert!(object.read() == object.expected());
}

pub fn incoming_concrete(value: &Number) {
    let object: &dyn Read<Output = u8> = value;
    assert!(through_object(object) <= 15);
}

pub fn selected_concrete(value: u8, choice: bool) {
    let number = Number(value);
    let different = Different(value & 15);
    let object: &dyn Read<Output = u8> = if choice { &number } else { &different };
    assert!(through_object(object) <= 15);
}

pub trait Change {
    fn replace(&mut self, value: u8);
    fn read(&self) -> u8;
}

impl Change for Number {
    fn replace(&mut self, value: u8) {
        self.0 = value;
    }
    fn read(&self) -> u8 {
        self.0
    }
}

#[inline(never)]
fn update_object(value: &mut dyn Change, replacement: u8) {
    value.replace(replacement);
    assert!(value.read() == replacement);
}

pub fn concrete_mutable(value: u8) {
    let mut number = Number(0);
    update_object(&mut number, value);
    assert!(number.0 == value);
}

pub fn concrete_panic(value: u8) {
    let number = Different(value);
    let object: &dyn Read<Output = u8> = &number;
    assert!(through_object(object) <= 15);
}

pub fn wrong_effect(value: u8) {
    let mut number = Number(0);
    update_object(&mut number, value);
    assert!(number.0 == 0);
}

pub fn arbitrary_object(value: &dyn Read<Output = u8>) {
    assert!(value.read() <= 15);
}

pub fn arbitrary_mutable(value: &mut dyn Change, replacement: u8) {
    update_object(value, replacement);
}

trait Parent {
    fn parent(&self) -> u8;
}
trait Child: Parent {
    fn child(&self) -> u8;
}
impl Parent for Number {
    fn parent(&self) -> u8 {
        self.0 & 15
    }
}
impl Child for Number {
    fn child(&self) -> u8 {
        self.0 & 7
    }
}

pub fn inherited_slot(value: u8) {
    let number = Number(value);
    let object: &dyn Child = &number;
    assert!(object.parent() <= 15);
    assert!(object.child() <= 7);
}

pub fn upcast_unknown(value: u8) {
    let number = Number(value);
    let object: &dyn Child = &number;
    let parent: &dyn Parent = object;
    assert!(parent.parent() <= 15);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn escaping_object(value: u8) -> &'static dyn Read<Output = u8> {
    mir! {
        let number: Number;
        let thin: &Number;
        {
            number = Number(value);
            thin = &number;
            RET = CastUnsize(thin);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_object(value: u8) -> u8 {
    mir! {
        let number: Number;
        let thin: &Number;
        let object: &dyn Read<Output = u8>;
        {
            number = Number(value);
            thin = &number;
            object = CastUnsize(thin);
            StorageDead(number);
            Call(RET = through_object(object), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn concrete_dispatch() {
        super::concrete_shared(255);
        super::concrete_mutable(23);
        super::inherited_slot(255);
    }
}
