#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn identity(value: u16) -> u16 {
    value ^ 0
}

#[inline(never)]
pub fn pair(a: u16, b: i32) -> i64 {
    ((a as i64) - (b as i64)) ^ 0
}

pub fn unary(index: usize, word: u16) {
    let table: [fn(u16) -> u16; 16] = [identity; 16];
    if index < 16 {
        assert!(table[index](word) == word);
    }
}

pub fn unary_wrong(index: usize, word: u16) {
    let table: [fn(u16) -> u16; 16] = [identity; 16];
    if index < 16 {
        assert!(table[index](word) != word);
    }
}

pub fn binary(index: usize, a: u16, b: i32) {
    let table: [fn(u16, i32) -> i64; 2] = [pair; 2];
    if index < 2 {
        assert!(table[index](a, b) == (a as i64) - (b as i64));
    }
}

pub fn binary_wrong(index: usize, a: u16, b: i32) {
    let table: [fn(u16, i32) -> i64; 2] = [pair; 2];
    if index < 2 {
        assert!(table[index](a, b) != (a as i64) - (b as i64));
    }
}

pub fn last(word: u16) {
    let table: [fn(u16) -> u16; 128] = [identity; 128];
    assert!(table[127](word) == word);
}

pub fn dispatch_budget(index: usize, word: u16) {
    let table: [fn(u16) -> u16; 128] = [identity; 128];
    if index < 128 {
        assert!(table[index](word) == word);
    }
}

pub fn count_budget(word: u16) {
    let table: [fn(u16) -> u16; 129] = [identity; 129];
    assert!(table[0](word) == word);
}

pub fn zero() {
    let table: [fn(u16) -> u16; 0] = [identity; 0];
    assert!(table.len() == 0);
}

pub fn sequential(word: u16) {
    let table: [fn(u16) -> u16; 1] = [identity; 1];
    assert!(table[0](word) == word);
    assert!(table[0](word) == word);
}

pub fn opaque(callback: fn(u16) -> u16, word: u16) {
    let table = [callback; 2];
    assert!(table[0](word) == word);
}

pub fn product(word: u16) {
    let table: [(fn(u16) -> u16, u16); 2] = [(identity, word); 2];
    assert!(table[0].0(table[0].1) == word);
}

#[cfg(test)]
mod native {
    extern crate std;

    #[test]
    fn mutation_guard() {
        for word in [0, 1, 129, u16::MAX] {
            for index in 0..16 {
                super::unary(index, word);
            }
            super::last(word);
            super::sequential(word);
            for other in [i32::MIN, -1, 0, 129, i32::MAX] {
                for index in 0..2 {
                    super::binary(index, word, other);
                }
            }
        }
        super::zero();
        let count = std::cell::Cell::new(0);
        let empty: [fn(u16) -> u16; 0] = [{
            count.set(count.get() + 1);
            super::identity
        }; 0];
        assert_eq!(count.get(), 1);
        assert!(empty.is_empty());
    }
}
