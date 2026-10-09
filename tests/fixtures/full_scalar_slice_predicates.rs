#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

// All ordinary roots retain one arbitrary immutable incoming slice and owned scalar arguments.

#[inline(never)]
fn selected_needle(values: &[u16], index: usize) -> u16 {
    values[index]
}

pub fn integer_member(values: &[u16], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}

pub fn integer_self_equality(values: &[u16]) {
    assert!(values == values);
    assert!(values[..] == values[..]);
}

pub fn bool_member_and_equality(values: &[bool], index: usize) {
    assert!(values == values);
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
}

pub fn char_member_and_equality(values: &[char], index: usize) {
    assert!(values == values);
    if index < values.len() {
        assert!(values.contains(&values[index]));
    }
    // Char comparison must use valid decoded observations, not abstract seed equality.
    if values.len() == 1 && values[0] == '\0' {
        assert!(values == ['\0']);
    }
}

pub fn float32_selected_member(values: &[f32], index: usize) {
    if index < values.len() && !values[index].is_nan() {
        assert!(values.contains(&values[index]));
    }
}

pub fn float64_selected_member(values: &[f64], index: usize) {
    if index < values.len() && !values[index].is_nan() {
        assert!(values.contains(&values[index]));
    }
}

pub fn float32_nan_is_absent(values: &[f32], needle: f32) {
    if needle.is_nan() {
        assert!(!values.contains(&needle));
    }
}

pub fn float64_nan_is_absent(values: &[f64], needle: f64) {
    if needle.is_nan() {
        assert!(!values.contains(&needle));
    }
}

pub fn float32_zero_signs(values: &[f32], index: usize) {
    if index < values.len() && values[index] == 0.0 {
        assert!(values.contains(&-0.0));
        assert!(values.contains(&0.0));
    }
}

pub fn float64_zero_signs(values: &[f64], index: usize) {
    if index < values.len() && values[index] == 0.0 {
        assert!(values.contains(&-0.0));
        assert!(values.contains(&0.0));
    }
}

pub fn derived_views(values: &[u16], offset: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(suffix == &values[offset..]);
        if offset < values.len() {
            assert!(suffix.contains(&values[offset]));
        }
    }
}

pub fn large_domain_and_empty_end(values: &[u16]) {
    if values.len() > 128 {
        assert!(values == values);
        assert!(values.contains(&values[128]));
        assert!(values != &values[..128]);
    }
    let end = values.len();
    assert!(!values[end..end].contains(&7));
    assert!(values[end..end] == []);
}

pub fn different_scalar_views(values: &[u16]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] != values[1..]);
    }
}

pub fn wrong_scalar_view_equality(values: &[u16]) {
    if values.len() == 2 && values[0] != values[1] {
        assert!(values[..1] == values[1..]);
    }
}

pub fn finite_array_counterpart(values: &[u16]) {
    if values.len() == 2 && values[0] == 3 && values[1] == 7 {
        assert!(values == [3, 7]);
        assert!([3, 7] == values);
    }
}

pub fn mutation_claim(values: &[u16], index: usize) {
    if index < values.len() {
        assert!(values.contains(&selected_needle(values, index)));
    }
}

// This is the exact existing capability frontier, with no changed root/type/length guard.
pub fn unbounded_scalar_contains(values: &[u16], needle: u16) -> bool {
    values.contains(&needle)
}

pub fn false_zero_claim(values: &[u16]) {
    if values.len() > 128 {
        assert!(values.contains(&0));
    }
}

pub fn float32_self_equality(values: &[f32]) {
    assert!(values == values);
}

pub fn float64_self_equality(values: &[f64]) {
    assert!(values == values);
}

pub fn different_lengths_are_equal(values: &[u16]) {
    if values.len() > 128 {
        assert!(values == &values[..128]);
    }
}

pub fn mutable_root(values: &mut [u16]) -> bool {
    values.contains(&7)
}

pub fn competing_roots(left: &[u16], right: &[u16]) -> bool {
    left == right
}

pub struct Custom(u16);

impl PartialEq for Custom {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

pub fn open_custom_root(values: &[Custom]) -> bool {
    values.contains(&Custom(7))
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    unsafe extern "Rust" {
        fn opaque_equal(left: u16, right: u16) -> bool;
    }

    struct Opaque(u16);

    impl PartialEq for Opaque {
        fn eq(&self, other: &Self) -> bool {
            unsafe { opaque_equal(self.0, other.0) }
        }
    }

    pub fn missing_custom_body() -> bool {
        [Opaque(3)].contains(&Opaque(7))
    }

    struct Panics;

    impl PartialEq for Panics {
        fn eq(&self, _other: &Self) -> bool {
            panic!("actual custom comparison body")
        }
    }

    pub fn custom_comparison_panics() -> bool {
        [Panics].contains(&Panics)
    }

    fn empty_contains(values: &[u16; 0]) -> bool {
        values.contains(&7)
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty_source() -> bool {
        mir! {
            let backing: [u16; 0];
            let view: &[u16; 0];
            {
                backing = [];
                view = &backing;
                StorageDead(backing);
                Call(RET = empty_contains(view), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    fn mismatch(values: &[u16; 0]) -> bool {
        values.as_slice() == [7]
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_mismatch_source() -> bool {
        mir! {
            let backing: [u16; 0];
            let view: &[u16; 0];
            {
                backing = [];
                view = &backing;
                StorageDead(backing);
                Call(RET = mismatch(view), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positives() {
        let large = [7_u16; 257];
        for values in [&[][..], &[3, 7][..], &large[..]] {
            integer_self_equality(values);
            large_domain_and_empty_end(values);
            finite_array_counterpart(values);
            different_scalar_views(values);
            for index in [0, 1, 128, 256, values.len()] {
                integer_member(values, index);
                derived_views(values, index);
                mutation_claim(values, index);
            }
        }
        let bools = [true; 129];
        for values in [&[][..], &[false, true][..], &bools[..]] {
            for index in [0, 128, values.len()] {
                bool_member_and_equality(values, index);
            }
        }
        let characters = ['\u{10ffff}'; 129];
        for values in [
            &[][..],
            &['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'][..],
            &characters[..],
        ] {
            for index in [0, 1, 128, values.len()] {
                char_member_and_equality(values, index);
            }
        }
        char_member_and_equality(&['\0'], 0);
        let narrow = [f32::from_bits(0x7fc00015); 129];
        for values in [
            &[][..],
            &[0.0, -0.0, f32::MIN_POSITIVE, f32::MAX][..],
            &narrow[..],
        ] {
            float32_nan_is_absent(values, f32::from_bits(0x7fc00015));
            for index in [0, 1, 128, values.len()] {
                float32_selected_member(values, index);
                float32_zero_signs(values, index);
            }
        }
        let wide = [f64::from_bits(0x7ff8000000000015); 129];
        for values in [
            &[][..],
            &[0.0, -0.0, f64::MIN_POSITIVE, f64::MAX][..],
            &wide[..],
        ] {
            float64_nan_is_absent(values, f64::from_bits(0x7ff8000000000015));
            for index in [0, 1, 128, values.len()] {
                float64_selected_member(values, index);
                float64_zero_signs(values, index);
            }
        }
    }

    #[test]
    fn mutation_guard() {
        mutation_claim(&[7; 129], 128);
    }

    #[test]
    #[should_panic]
    fn zero_claim_failure() {
        false_zero_claim(&[7; 129]);
    }

    #[test]
    #[should_panic]
    fn nan32_equality_failure() {
        float32_self_equality(&[f32::from_bits(0x7fc00015); 129]);
    }

    #[test]
    #[should_panic]
    fn nan64_equality_failure() {
        float64_self_equality(&[f64::from_bits(0x7ff8000000000015); 129]);
    }

    #[test]
    #[should_panic]
    fn scalar_view_failure() {
        wrong_scalar_view_equality(&[3, 7]);
    }

    #[test]
    #[should_panic]
    fn length_failure() {
        different_lengths_are_equal(&[7; 129]);
    }
}
