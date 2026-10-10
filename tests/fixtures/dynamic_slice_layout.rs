#![no_std]
#![feature(
    custom_mir,
    core_intrinsics,
    layout_for_ptr,
    pattern_types,
    pattern_type_macro
)]
#![allow(internal_features)]

#[inline(never)]
fn dynamic_size(values: &[(u8, u32)]) -> usize {
    core::mem::size_of_val(values)
}

pub fn padded_tuple(values: &[(u8, u32)]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<(u8, u32)>());
}

pub fn nested_array(values: &[([u16; 3], (bool, char))]) {
    assert!(
        core::mem::size_of_val(values)
            == values.len() * core::mem::size_of::<([u16; 3], (bool, char))>()
    );
}

pub fn views(values: &[(u8, u32)], offset: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(
            core::mem::size_of_val(suffix)
                == (values.len() - offset) * core::mem::size_of::<(u8, u32)>()
        );
    }
    let end = values.len();
    assert!(core::mem::size_of_val(&values[end..end]) == 0);
}

pub fn extent(values: &[(u8, u32)]) {
    let stride = core::mem::size_of::<(u8, u32)>();
    let size = core::mem::size_of_val(values);
    assert!(size <= isize::MAX as usize);
    assert!(size / stride == values.len());
}

pub fn pure_zero(values: &[((), [u16; 0])]) {
    assert!(core::mem::size_of_val(values) == 0);
    if values.len() == usize::MAX {
        assert!(core::mem::size_of_val(&values[usize::MAX - 1..]) == 0);
    }
}

pub fn empty_array(values: &[[char; 0]]) {
    assert!(core::mem::size_of_val(values) == 0);
}

pub fn helper_claim(values: &[(u8, u32)]) {
    assert!(dynamic_size(values) == values.len() * core::mem::size_of::<(u8, u32)>());
}

pub fn wrong_padding(values: &[(u8, u32)]) {
    if !values.is_empty() {
        assert!(
            core::mem::size_of_val(values)
                == values.len() * (core::mem::size_of::<u8>() + core::mem::size_of::<u32>())
        );
    }
}

pub fn wrong_product(values: &[(u8, u32)]) {
    if !values.is_empty() {
        assert!(core::mem::size_of_val(values) == values.len());
    }
}

pub fn wrong_zero(values: &[()]) {
    assert!(core::mem::size_of_val(values) != 0);
}

#[inline(never)]
fn size_of_val(values: &[(u8, u32)]) -> usize {
    values.len() + 1
}
pub fn lookalike_wrong_body(values: &[(u8, u32)]) {
    assert!(size_of_val(values) == values.len());
}

pub fn unsupported_alignment(values: &[(u8, u32)]) -> usize {
    core::mem::align_of_val(values)
}

pub fn mutable_root(values: &mut [(u8, u32)]) -> usize {
    core::mem::size_of_val(values)
}
pub fn competing_roots(left: &[(u8, u32)], right: &[(u8, u32)]) -> bool {
    core::mem::size_of_val(left) == core::mem::size_of_val(right)
}
pub trait Custom {
    fn value(&self) -> u16;
}
pub fn trait_object(values: &dyn Custom) -> usize {
    core::mem::size_of_val(values)
}
pub fn reference_elements(values: &[(&u16, u32)]) -> usize {
    core::mem::size_of_val(values)
}
type Positive = core::pattern_type!(u32 is 1..);
pub fn refined_elements(values: &[[Positive; 0]]) -> usize {
    core::mem::size_of_val(values)
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_size(value: usize) -> usize;
    }
    pub fn missing_body(values: &[(u8, u32)]) {
        let size = core::mem::size_of_val(values);
        assert!(unsafe { opaque_size(size) } == size);
    }
    pub fn raw_source(pointer: *const (u8, u32), length: usize) -> usize {
        let values = unsafe { core::slice::from_raw_parts(pointer, length) };
        core::mem::size_of_val(values)
    }
    pub fn raw_size_api(values: &[(u8, u32)]) -> usize {
        unsafe { core::mem::size_of_val_raw(values as *const [(u8, u32)]) }
    }
    fn empty_size(values: &[(u8, u32); 0]) -> usize {
        core::mem::size_of_val(&values[..])
    }
    fn zero_size(values: &[(); 0]) -> usize {
        core::mem::size_of_val(&values[..])
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [(u8, u32); 0];
            let source: &[(u8, u32); 0];
            { backing = []; source = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = empty_size(source), ReturnTo(done), UnwindUnreachable())
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
                Call(RET = zero_size(source), ReturnTo(done), UnwindUnreachable())
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
            extent(values);
            helper_claim(values);
        }
        nested_array(&[([1, 2, 3], (true, '\u{10ffff}')); 129]);
        pure_zero(&[((), []); usize::MAX]);
        empty_array(&[[]; usize::MAX]);
    }
    #[test]
    fn mutation_guard() {
        helper_claim(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn padding_negative() {
        wrong_padding(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn product_negative() {
        wrong_product(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn zero_negative() {
        wrong_zero(&[(); 129]);
    }
    #[test]
    #[should_panic]
    fn lookalike_negative() {
        lookalike_wrong_body(&[(3, 7); 129]);
    }
}
