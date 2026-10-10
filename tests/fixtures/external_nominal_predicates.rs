#![no_std]
#![forbid(unsafe_code)]

use stage185_dependency::{Record, Zero};

#[inline(never)]
pub fn selected_needle(values: &[Record], index: usize) -> Record {
    values[index]
}

pub fn selected(values: &[Record], index: usize) {
    if index < values.len() {
        let selected = selected_needle(values, index);
        assert!(values.contains(&selected));
    }
}

pub fn self_equal(values: &[Record]) {
    assert!(values == values);
}

pub fn empty_contains(values: &[Record], needle: Record) {
    if values.is_empty() {
        assert!(!values.contains(&needle));
    }
}

pub fn unequal_views(values: &[Record]) {
    if values.len() > 1 {
        assert!(values[..1] != values[..]);
    }
}

pub fn zero_contains(values: &[Zero]) {
    if !values.is_empty() {
        assert!(values.contains(&Zero));
    }
}

pub fn zero_empty(values: &[Zero]) {
    if values.is_empty() {
        assert!(!values.contains(&Zero));
    }
}

pub fn direct_owned(value: Record) {
    let copy = value;
    assert!(value == copy);
}

pub fn direct_false(value: Record) {
    if value.left != value.right {
        let swapped = Record {
            left: value.right,
            right: value.left,
        };
        assert!(value == swapped);
    }
}

pub fn direct_zero(value: Zero) {
    assert!(value == Zero);
}

pub fn absent(values: &[Record], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&selected_needle(values, index)));
    }
}

pub fn falsely_equal_views(values: &[Record]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}

pub fn zero_maximum(values: &[Zero]) {
    if values.len() == usize::MAX {
        assert!(values.contains(&Zero));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mutation_guard() {
        selected(&[Record { left: 3, right: 7 }; 129], 128);
    }

    #[test]
    fn originals() {
        let values = [Record { left: 3, right: 7 }; 129];
        selected(&values, 128);
        self_equal(&values);
        empty_contains(&[], values[0]);
        unequal_views(&values);
        zero_contains(&[Zero; 129]);
        zero_empty(&[]);
        zero_maximum(&[Zero; usize::MAX]);
        direct_owned(values[0]);
        direct_zero(Zero);
    }

    #[test]
    #[should_panic]
    fn absent_witness() {
        absent(&[Record { left: 3, right: 7 }; 129], 128);
    }

    #[test]
    #[should_panic]
    fn different_fields_witness() {
        direct_false(Record { left: 3, right: 7 });
    }

    #[test]
    #[should_panic]
    fn different_views_witness() {
        falsely_equal_views(&[
            Record { left: 3, right: 7 },
            Record {
                left: 11,
                right: 19,
            },
        ]);
    }
}
