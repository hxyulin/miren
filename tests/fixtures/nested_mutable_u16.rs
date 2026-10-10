#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

#[inline(never)]
fn scalar(word: u16) -> u16 {
    word ^ 0
}

#[inline(never)]
fn leaf(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        values[0] = scalar(word);
    }
}

#[inline(never)]
fn outer(values: &mut [u16], word: u16) {
    leaf(&mut *(&mut *values), word);
}

#[inline(never)]
fn outer_twice(values: &mut [u16], word: u16) {
    leaf(&mut *values, word);
    leaf(values, word);
}

#[inline(never)]
fn outer_return(values: &mut [u16], word: u16) -> u16 {
    leaf(values, word);
    scalar(word)
}

pub fn selected(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        outer(values, word);
        assert!(values[0] == word);
    }
}

pub fn explicit(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        outer(&mut *values, word);
        assert!(values[0] == word);
    }
}

pub fn scalar_return(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        let returned = outer_return(values, word);
        assert!(returned == word);
        assert!(values[0] == returned);
    }
}

pub fn sequential(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        outer(values, word);
        assert!(values[0] == word);
        let next = word.wrapping_add(1);
        outer(values, next);
        assert!(values[0] == next);
    }
}

pub fn two_children(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        outer_twice(values, word);
        assert!(values[0] == word);
    }
}

pub fn sibling(values: &mut [u16], word: u16) {
    if values.len() > 1 {
        let untouched = values[1];
        outer(values, word);
        assert!(values[0] == word);
        assert!(values[1] == untouched);
    }
}

pub fn branches(values: &mut [u16], word: u16, choose: bool) {
    if values.len() > 0 {
        if choose {
            outer(values, word);
        } else {
            outer_twice(values, word);
        }
        assert!(values[0] == word);
    }
}

pub fn empty(values: &mut [u16], word: u16) {
    if values.len() == 0 {
        outer(values, word);
        assert!(values.len() == 0);
    }
}

pub fn length(values: &mut [u16], word: u16) {
    let before = values.len();
    outer(values, word);
    assert!(values.len() == before);
}

pub fn whole_anchor(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        leaf(values, word);
        assert!(values[0] == word);
    }
}

pub fn wrong(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        outer(values, word);
        assert!(values[0] == word.wrapping_add(1));
    }
}

pub fn wrong_sibling(values: &mut [u16], word: u16) {
    if values.len() > 1 {
        outer(values, word);
        assert!(values[1] == word);
    }
}

pub fn bounds(values: &mut [u16], word: u16) {
    outer(values, word);
    assert!(values[0] == word);
}

#[inline(never)]
fn leaf_assert(values: &mut [u16], word: u16) {
    assert!(word == 7);
    leaf(values, word);
}

#[inline(never)]
fn outer_assert(values: &mut [u16], word: u16) {
    leaf_assert(values, word);
}

pub fn child_assertion(values: &mut [u16], word: u16) {
    outer_assert(values, word);
}

#[inline(never)]
fn another_parent(values: &mut [u16], word: u16) {
    outer(values, word);
}

pub fn deeper(values: &mut [u16], word: u16) {
    another_parent(values, word);
}

pub fn retained(values: &mut [u16], word: u16) {
    let view = &mut *values;
    outer(view, word);
    if view.len() > 0 {
        assert!(view[0] == word);
    }
}

#[inline(never)]
fn observe(values: &[u16]) -> usize {
    values.len()
}

#[inline(never)]
fn outer_shared(values: &mut [u16], word: u16) {
    leaf(values, word);
    let _ = observe(values);
}

pub fn shared(values: &mut [u16], word: u16) {
    outer_shared(values, word);
}

pub fn raw(values: &mut [u16], word: u16) {
    let _ = values.as_mut_ptr();
    outer(values, word);
}

pub fn interval(values: &mut [u16], word: u16, start: usize, end: usize) {
    if start <= end && end <= values.len() {
        outer(&mut values[start..end], word);
    }
}

#[inline(never)]
fn leaf32(values: &mut [i32], word: i32) {
    if values.len() > 0 {
        values[0] = word;
    }
}

#[inline(never)]
fn outer32(values: &mut [i32], word: i32) {
    leaf32(values, word);
}

pub fn signed32(values: &mut [i32], word: i32) {
    outer32(values, word);
}

#[cfg(test)]
mod native_tests {
    use super::*;

    #[test]
    fn safe_nested_native() {
        for size in 0..=128 {
            let original: std::vec::Vec<u16> = (0..size).map(|n| n as u16).collect();
            for word in [0, 7, 19, u16::MAX] {
                selected(&mut original.clone(), word);
                explicit(&mut original.clone(), word);
                scalar_return(&mut original.clone(), word);
                sequential(&mut original.clone(), word);
                two_children(&mut original.clone(), word);
                sibling(&mut original.clone(), word);
                branches(&mut original.clone(), word, false);
                branches(&mut original.clone(), word, true);
                empty(&mut original.clone(), word);
                length(&mut original.clone(), word);
                whole_anchor(&mut original.clone(), word);
            }
        }
    }

    #[test]
    fn mutation_guard() {
        let mut values = [5, 11];
        selected(&mut values, 19);
        assert_eq!(values, [19, 11]);
    }
}
