#![no_std]
#![feature(custom_mir, core_intrinsics)]

#[inline(never)]
pub fn selected_needle(values: &[u16]) -> u16 {
    values[0]
}

pub fn integer_member(values: &[u16]) {
    if !values.is_empty() && values.len() <= 4 {
        assert!(values.contains(&values[0]));
    }
    if values.len() == 128 {
        assert!(values.contains(&values[127]));
    }
}

pub fn bool_member(values: &[bool]) {
    if !values.is_empty() && values.len() <= 3 {
        assert!(values.contains(&values[0]));
    }
}

pub fn char_member(values: &[char]) {
    if !values.is_empty() && values.len() <= 3 {
        assert!(values.contains(&values[0]));
    }
    if values.len() == 1 && values[0] == '\0' {
        assert!(values == ['\0']);
    }
}

pub fn float32_numeric(values: &[f32]) {
    if values.len() == 1 {
        if values[0] == 0.0 {
            assert!(values.contains(&-0.0));
        }
        if values[0] != values[0] {
            assert!(!values.contains(&values[0]));
        }
    }
}

pub fn float64_numeric(values: &[f64]) {
    if values.len() == 1 {
        if values[0] == 0.0 {
            assert!(values == [-0.0]);
        }
        if values[0] != values[0] {
            assert!(values != values);
        }
    }
}

pub fn integer_equality(values: &[i32]) {
    if values.len() <= 4 {
        assert!(values == values);
        assert!(values[..] == values[..]);
    }
}

pub fn local_array_equality(values: &[u16]) {
    if values.len() == 2 && values[0] == 3 && values[1] == 7 {
        assert!(values == [3, 7]);
    }
}

pub fn large_parent_short_views(values: &[u16]) {
    if values.len() > 128 {
        let prefix = &values[..2];
        assert!(prefix.contains(&values[1]));
        assert!(prefix == &values[..2]);
        let end = values.len();
        assert!(!values[end..end].contains(&7));
        assert!(values[end..end] == []);
    }
}

pub fn mismatch_is_not_a_scan(values: &[u16]) {
    if values.len() > 128 {
        assert!(values != [3]);
    }
}

pub fn mutation_claim(values: &[u16]) {
    if values.len() >= 2 {
        assert!(values[..1].contains(&selected_needle(values)));
    }
}

pub fn wrong_membership(values: &[u16]) {
    if values.len() == 1 {
        assert!(values.contains(&0));
    }
}

pub fn wrong_float_reflexivity(values: &[f32]) {
    if values.len() == 1 {
        assert!(values == values);
    }
}

pub fn unbounded_contains(values: &[u16], needle: u16) -> bool {
    values.contains(&needle)
}

pub fn unbounded_equality(values: &[u16]) -> bool {
    values == values
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positives() {
        integer_member(&[]);
        integer_member(&[3, 7]);
        integer_member(&[7; 128]);
        bool_member(&[false, true]);
        char_member(&['\0', '\u{d7ff}', '\u{e000}']);
        float32_numeric(&[f32::NAN]);
        float32_numeric(&[-0.0]);
        float64_numeric(&[f64::NAN]);
        float64_numeric(&[-0.0]);
        integer_equality(&[i32::MIN, 0, i32::MAX]);
        local_array_equality(&[3, 7]);
        large_parent_short_views(&[7; 129]);
        mismatch_is_not_a_scan(&[7; 129]);
    }

    #[test]
    fn mutation_guard() {
        mutation_claim(&[3, 7]);
    }
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

    fn empty_contains(values: &[u16; 0]) -> bool {
        values.contains(&7)
    }

    fn mismatch(values: &[u16; 0]) -> bool {
        values.as_slice() == [7]
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
