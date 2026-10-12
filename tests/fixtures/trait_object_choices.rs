#![no_std]
#![forbid(unsafe_code)]

pub trait Parent {
    fn read(&self) -> u8;
}
trait Child: Parent {
    fn extra(&self) -> u8;
}
struct Masked(u8);
struct Different(u8);
impl Parent for Masked {
    #[inline(never)]
    fn read(&self) -> u8 {
        self.0 & 15
    }
}
impl Parent for Different {
    #[inline(never)]
    fn read(&self) -> u8 {
        self.0 % 16
    }
}
impl Child for Masked {
    fn extra(&self) -> u8 {
        self.0 & 7
    }
}
impl Child for Different {
    fn extra(&self) -> u8 {
        self.0 % 8
    }
}
#[inline(never)]
fn invoke(value: &dyn Parent) -> u8 {
    value.read()
}
#[inline(never)]
fn choose(values: &[&dyn Parent], index: usize) -> u8 {
    if index >= values.len() {
        return 0;
    }
    invoke(values[index])
}
pub fn constant(value: u8) {
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    assert!(invoke(values[0]) <= 15);
}
pub fn symbolic(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    assert!(invoke(values[index]) <= 15);
}
pub fn wrong(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    assert!(invoke(values[index]) == 16);
}
pub fn slice_helper(value: u8, index: usize) {
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    assert!(choose(&values, index) <= 15);
}
pub fn inherited(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Child; 2] = [&first, &second];
    assert!(values[index].extra() <= 7);
    assert!(values[index].read() <= 15);
}
pub fn upcast(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Child; 2] = [&first, &second];
    let parent: &dyn Parent = values[index];
    assert!(invoke(parent) <= 15);
}
pub fn opaque(value: &dyn Parent) {
    assert!(invoke(value) <= 15);
}
#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        for value in 0..=255 {
            super::constant(value);
            for index in 0..2 {
                super::symbolic(value, index);
                super::slice_helper(value, index);
                super::inherited(value, index);
                super::upcast(value, index);
                super::caller_backed_return(value, index);
                super::captured_index(value, index);
                super::repeated(value, index);
                super::returned_memory(value, index);
            }
        }
    }
}

#[inline(never)]
fn returned<'a>(values: &[&'a dyn Parent], index: usize) -> &'a dyn Parent {
    values[index]
}

pub fn caller_backed_return(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    let selected = returned(&values, index);
    assert!(invoke(selected) <= 15);
}

pub fn captured_index(value: u8, mut index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    let selected = values[index];
    index ^= 1;
    assert!(invoke(selected) <= 15);
    assert!(index < 2);
}

pub fn repeated(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn Parent; 2] = [&first, &second];
    let selected = values[index];
    assert!(invoke(selected) <= 15);
    assert!(invoke(selected) <= 15);
}

trait WithEffect {
    fn apply(&self, counter: &mut u8) -> u8;
}
impl WithEffect for Masked {
    fn apply(&self, counter: &mut u8) -> u8 {
        *counter = 1;
        self.0 % 16
    }
}
impl WithEffect for Different {
    fn apply(&self, counter: &mut u8) -> u8 {
        *counter = 1;
        self.0 % 16
    }
}
pub fn returned_memory(value: u8, index: usize) {
    if index >= 2 {
        return;
    }
    let first = Masked(value);
    let second = Different(value);
    let values: [&dyn WithEffect; 2] = [&first, &second];
    let mut counter = 0;
    assert!(values[index].apply(&mut counter) <= 15);
    assert!(counter == 1);
}
