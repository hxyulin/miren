#![no_std]

#[inline(never)]
fn selected_word(values: [[u16; 2]; 2], index: usize) -> u16 {
    values[index][0]
}

pub fn nested_integer_arrays(index: usize) {
    let values = [[3_u16, 7], [5, 11], [9, 19]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[1] == selected[0] * 2 + 1);
        assert!(selected[0] == values[index][0]);
    }
}

pub fn incoming_array_correlation(values: [[u16; 2]; 2], index: usize) {
    if index < values.len() {
        let selected = values[index];
        if index == 0 {
            assert!(selected[0] == values[0][0]);
            assert!(selected[1] == values[0][1]);
        } else {
            assert!(selected[0] == values[1][0]);
            assert!(selected[1] == values[1][1]);
        }
    }
}

pub fn array_of_tuples(index: usize) {
    let values = [[(3_u16, true), (7, false)], [(5, false), (11, true)]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[1].0 == selected[0].0 * 2 + 1);
        assert!(selected[0].1 != selected[1].1);
    }
}

pub fn tuple_containing_arrays(index: usize) {
    let values = [
        ([3_u16, 7], (true, [11_i16, -11])),
        ([5, 11], (false, [13, -13])),
    ];
    if index < values.len() {
        let selected = values[index];
        assert!(selected.0[1] == selected.0[0] * 2 + 1);
        assert!(selected.1.1[1] == -selected.1.1[0]);
        if selected.1.0 {
            assert!(selected.0[0] == 3);
        } else {
            assert!(selected.0[0] == 5);
        }
    }
}

pub fn float_and_char_choices(index: usize) {
    let values = [
        [
            (f32::from_bits(0x80000000), '\0', 0x80000000_u32),
            (f32::from_bits(0x7fc00015), '\u{d7ff}', 0x7fc00015),
        ],
        [
            (f32::from_bits(0x7fc00025), '\u{e000}', 0x7fc00025),
            (1.0_f32, '\u{10ffff}', 0x3f800000),
        ],
    ];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0].0.to_bits() == selected[0].2);
        assert!(selected[1].0.to_bits() == selected[1].2);
        let code = selected[1].1 as u32;
        assert!(code <= 0x10ffff);
        assert!(code < 0xd800 || code > 0xdfff);
        if index == 0 {
            assert!(selected[0].0 == 0.0);
            assert!(selected[1].0.is_nan());
            assert!(selected[1].1 == '\u{d7ff}');
        } else {
            assert!(selected[0].0.is_nan());
            assert!(selected[1].1 == '\u{10ffff}');
        }
    }
}

pub fn float64_bits(index: usize) {
    let values = [
        [
            f64::from_bits(0x8000000000000000),
            f64::from_bits(0x7ff8000000000015),
        ],
        [
            f64::from_bits(0x7ff8000000000025),
            f64::from_bits(0x3ff0000000000000),
        ],
    ];
    if index < values.len() {
        let selected = values[index];
        if index == 0 {
            assert!(selected[0].to_bits() == 0x8000000000000000);
            assert!(selected[1].to_bits() == 0x7ff8000000000015);
        } else {
            assert!(selected[0].to_bits() == 0x7ff8000000000025);
            assert!(selected[1].to_bits() == 0x3ff0000000000000);
        }
    }
}

pub fn empty_nested_arrays(index: usize) {
    let values: [[u16; 0]; 2] = [[], []];
    if index < values.len() {
        assert!(values[index].len() == 0);
    }
}

pub fn singleton_reference(index: usize) {
    let source = 7_u16;
    let values = [[&source]];
    if index < values.len() {
        assert!(*values[index][0] == source);
    }
}

pub fn constant_reference() {
    let first = 3_u16;
    let second = 7_u16;
    let values = [[&first], [&second]];
    assert!(*values[0][0] == first);
    assert!(*values[1][0] == second);
}

pub fn mutation_claim(index: usize) {
    let values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        assert!(selected_word(values, index) == values[index][0]);
    }
}

pub fn wrong_field_relation(index: usize) {
    let values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0] == selected[1]);
    }
}

pub fn wrong_index_relation(index: usize) {
    let values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        assert!(values[index][0] == values[0][0]);
    }
}

pub fn bounds_failure(index: usize) -> [u16; 2] {
    let values = [[3_u16, 7], [5, 11]];
    values[index]
}

pub fn nan_numeric_reflexivity(index: usize) {
    let values = [[f32::from_bits(0x7fc00015)], [1.0]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0] == selected[0]);
    }
}

pub fn ambiguous_references(index: usize) {
    let first = 3_u16;
    let second = 7_u16;
    let values = [[&first], [&second]];
    if index < values.len() {
        let selected = values[index];
        assert!(*selected[0] == if index == 0 { first } else { second });
    }
}

#[derive(Clone, Copy)]
struct Wrapper(u16);

pub fn ambiguous_adt(index: usize) {
    let values = [[Wrapper(3)], [Wrapper(7)]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0].0 == if index == 0 { 3 } else { 7 });
    }
}

struct Dropped(u16);

impl Drop for Dropped {
    fn drop(&mut self) {
        let _ = self.0;
    }
}

pub fn ambiguous_drop(index: usize) {
    let values = [[Dropped(3)], [Dropped(7)]];
    if index < values.len() {
        let selected = &values[index];
        assert!(selected[0].0 == if index == 0 { 3 } else { 7 });
    }
}

pub fn incoming_composite_row(values: &[[[u16; 2]; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let selected = values[outer];
        let row = selected[inner];
        if inner == 0 {
            assert!(row[0] == values[outer][0][0]);
            assert!(row[1] == values[outer][0][1]);
        } else {
            assert!(row[0] == values[outer][1][0]);
            assert!(row[1] == values[outer][1][1]);
        }
    }
}

pub fn owned_selected_copy_mutation(values: [[u16; 2]; 2], index: usize) {
    if index < values.len() {
        let original = values[index][0];
        let mut copied = values[index];
        let other_copy = values[index];
        copied[0] = copied[0].wrapping_add(1);
        assert!(copied[0] == original.wrapping_add(1));
        assert!(values[index][0] == original);
        assert!(other_copy[0] == original);
        assert!(copied[1] == other_copy[1]);
    }
}

pub fn byte_array_choices(index: usize) {
    let values = [[3_u8, 7], [5, 11]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[1] == selected[0] * 2 + 1);
    }
}

pub fn symbolic_mutation(index: usize) {
    let mut values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        values[index][0] = 19;
        assert!(values[index][0] == 19);
    }
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positives() {
        for index in 0..3 {
            nested_integer_arrays(index);
            incoming_array_correlation([[3, 7], [5, 11]], index);
            owned_selected_copy_mutation([[3, 7], [5, 11]], index);
            array_of_tuples(index);
            tuple_containing_arrays(index);
            float_and_char_choices(index);
            float64_bits(index);
            empty_nested_arrays(index);
            singleton_reference(index);
            mutation_claim(index);
        }
        constant_reference();
        for outer in [0, 128, 129] {
            for inner in [0, 1, 2] {
                incoming_composite_row(&[[[3, 7], [5, 11]]; 129], outer, inner);
                incoming_composite_row(&[], outer, inner);
            }
        }
    }

    #[test]
    fn mutation_guard() {
        mutation_claim(0);
        mutation_claim(1);
    }

    #[test]
    #[should_panic]
    fn field_failure() {
        wrong_field_relation(0);
    }

    #[test]
    #[should_panic]
    fn index_failure() {
        wrong_index_relation(1);
    }

    #[test]
    #[should_panic]
    fn bounds_panic() {
        let _ = bounds_failure(2);
    }

    #[test]
    #[should_panic]
    fn nan_failure() {
        nan_numeric_reflexivity(0);
    }
}
