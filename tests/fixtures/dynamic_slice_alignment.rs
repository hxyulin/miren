#![no_std]
#![feature(custom_mir, core_intrinsics, layout_for_ptr)]
#![allow(internal_features)]

#[inline(never)]
fn dynamic_alignment(values: &[(u8, u32)]) -> usize {
    core::mem::align_of_val(values)
}

pub fn padded_tuple(values: &[(u8, u32)]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<(u8, u32)>());
}

pub fn nested_array(values: &[([u16; 3], (bool, char))]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<([u16; 3], (bool, char))>());
}

pub fn views(values: &[(u8, u32)], offset: usize) {
    if offset <= values.len() {
        assert!(core::mem::align_of_val(&values[offset..]) == core::mem::align_of::<(u8, u32)>());
    }
    let end = values.len();
    assert!(core::mem::align_of_val(&values[end..end]) == core::mem::align_of::<(u8, u32)>());
}

pub fn characters(values: &[char]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<char>());
}

pub fn floats(values: &[f64]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<f64>());
}

pub fn units(values: &[()]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<()>());
    if values.len() == usize::MAX {
        assert!(core::mem::align_of_val(&values[usize::MAX - 1..]) == 1);
    }
}

pub fn aligned_zero(values: &[[u64; 0]]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<u64>());
}

pub fn helper_claim(values: &[(u8, u32)]) {
    assert!(dynamic_alignment(values) == core::mem::align_of::<(u8, u32)>());
}

pub fn wrong_size_as_alignment(values: &[(u8, u32)]) {
    assert!(core::mem::align_of_val(values) == core::mem::size_of::<(u8, u32)>());
}

pub fn wrong_unit(values: &[()]) {
    assert!(core::mem::align_of_val(values) != 1);
}

#[inline(never)]
fn align_of_val(values: &[(u8, u32)]) -> usize {
    values.len() + 1
}
pub fn lookalike_wrong_body(values: &[(u8, u32)]) {
    assert!(align_of_val(values) == values.len());
}

#[allow(deprecated)]
pub fn deprecated_alias(values: &[(u8, u32)]) -> usize {
    core::mem::min_align_of_val(values)
}

pub fn mutable_root(values: &mut [(u8, u32)]) -> usize {
    core::mem::align_of_val(values)
}
pub fn competing_roots(left: &[(u8, u32)], right: &[(u8, u32)]) -> bool {
    core::mem::align_of_val(left) == core::mem::align_of_val(right)
}
pub trait Custom {
    fn value(&self) -> u16;
}
pub fn trait_object(values: &dyn Custom) -> usize {
    core::mem::align_of_val(values)
}
pub fn reference_elements(values: &[(&u16, u32)]) -> usize {
    core::mem::align_of_val(values)
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_alignment(value: usize) -> usize;
    }
    pub fn missing_body(values: &[(u8, u32)]) {
        let alignment = core::mem::align_of_val(values);
        assert!(unsafe { opaque_alignment(alignment) } == alignment);
    }
    pub fn raw_source(pointer: *const (u8, u32), length: usize) -> usize {
        let values = unsafe { core::slice::from_raw_parts(pointer, length) };
        core::mem::align_of_val(values)
    }
    pub fn raw_alignment_api(values: &[(u8, u32)]) -> usize {
        unsafe { core::mem::align_of_val_raw(values as *const [(u8, u32)]) }
    }
    fn empty_alignment(values: &[(u8, u32); 0]) -> usize {
        core::mem::align_of_val(&values[..])
    }
    fn zero_alignment(values: &[(); 0]) -> usize {
        core::mem::align_of_val(&values[..])
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [(u8, u32); 0];
            let source: &[(u8, u32); 0];
            { backing = []; source = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = empty_alignment(source), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_zero() -> usize {
        mir! {
            let backing: [(); 0];
            let source: &[(); 0];
            { backing = []; source = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = zero_alignment(source), ReturnTo(done), UnwindUnreachable())
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
        let long = [(3, 7); 129];
        for values in [&[][..], &[(3, 7)][..], &long[..]] {
            padded_tuple(values);
            views(values, values.len());
            helper_claim(values);
        }
        nested_array(&[([1, 2, 3], (true, '\u{10ffff}')); 129]);
        characters(&['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}']);
        floats(&[f64::from_bits(0x7ff8000000001234), -0.0, f64::MAX]);
        units(&[(); usize::MAX]);
        aligned_zero(&[[]; usize::MAX]);
    }
    #[test]
    fn mutation_guard() {
        helper_claim(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn size_negative() {
        wrong_size_as_alignment(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn unit_negative() {
        wrong_unit(&[(); 129]);
    }
    #[test]
    #[should_panic]
    fn lookalike_negative() {
        lookalike_wrong_body(&[(3, 7); 129]);
    }
}
