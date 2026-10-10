#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Padded {
    pub small: u8,
    pub word: u32,
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct Aligned(pub u16);
#[derive(Clone, Copy)]
pub struct Generic<T> {
    pub payload: T,
    pub flag: bool,
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct Zero;

#[inline(never)]
pub fn measured_alignment<T>(value: &T) -> usize {
    core::mem::align_of_val(value)
}
#[inline(never)]
pub fn returned_word(values: &[Padded], index: usize) -> &u32 {
    &values[index].word
}

pub fn primitive(value: (u16, bool, char, f32, f64)) {
    assert!(core::mem::align_of_val(&value.0) == core::mem::align_of::<u16>());
    assert!(core::mem::align_of_val(&value.1) == core::mem::align_of::<bool>());
    assert!(core::mem::align_of_val(&value.2) == core::mem::align_of::<char>());
    assert!(core::mem::align_of_val(&value.3) == core::mem::align_of::<f32>());
    assert!(core::mem::align_of_val(&value.4) == core::mem::align_of::<f64>());
    assert!(core::mem::size_of_val(&value) == core::mem::size_of::<(u16, bool, char, f32, f64)>());
}
pub fn padded(value: Padded) {
    assert!(core::mem::size_of_val(&value) == core::mem::size_of::<Padded>());
    assert!(core::mem::align_of_val(&value) == core::mem::align_of::<Padded>());
}
pub fn aligned(value: Aligned) {
    assert!(core::mem::align_of_val(&value) == 64);
    assert!(core::mem::size_of_val(&value) == core::mem::size_of::<Aligned>());
}
pub fn generic(value: Generic<([u16; 2], (bool, char))>) {
    assert!(
        core::mem::align_of_val(&value)
            == core::mem::align_of::<Generic<([u16; 2], (bool, char))>>()
    );
    assert!(
        core::mem::size_of_val(&value) == core::mem::size_of::<Generic<([u16; 2], (bool, char))>>()
    );
}
pub fn zero(value: Zero) {
    assert!(core::mem::align_of_val(&value) == 64);
    assert!(core::mem::size_of_val(&value) == 0);
}
pub fn copied(values: [Aligned; 2], index: usize) {
    if index < 2 {
        let copied = values[index];
        assert!(core::mem::align_of_val(&copied) == 64);
    }
}
pub fn returned_view(values: &[Padded], index: usize) {
    if index < values.len() {
        let word = returned_word(values, index);
        assert!(core::mem::align_of_val(word) == core::mem::align_of::<u32>());
        assert!(core::mem::size_of_val(word) == core::mem::size_of::<u32>());
    }
}
pub fn mutation_claim(values: &[Aligned], index: usize) {
    if index < values.len() {
        assert!(measured_alignment(&values[index]) == core::mem::align_of::<Aligned>());
    }
}
pub fn shared_reference(value: &Padded) {
    assert!(core::mem::align_of_val(value) == core::mem::align_of::<Padded>());
}
pub fn wrong_padding(value: Padded) {
    assert!(
        core::mem::size_of_val(&value) == core::mem::size_of::<u8>() + core::mem::size_of::<u32>()
    );
}
pub fn wrong_zero_alignment(value: Zero) {
    assert!(core::mem::align_of_val(&value) == 1);
}
#[inline(never)]
fn align_of_val<T>(_: &T) -> usize {
    19
}
pub fn lookalike(value: Aligned) {
    assert!(align_of_val(&value) == 64);
}
pub fn wrong_helper(value: Aligned) {
    assert!(measured_alignment(&value) == 1);
}
pub fn wrapper() -> usize {
    let value = core::mem::MaybeUninit::<u32>::uninit();
    core::mem::align_of_val(&value)
}
pub fn trait_object(value: &dyn core::fmt::Debug) -> usize {
    core::mem::align_of_val(value)
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    pub fn raw_alignment(value: usize) -> usize {
        unsafe { core::mem::align_of_val_raw(value as *const u32) }
    }
    pub fn legacy_raw_size(value: usize) {
        assert!(unsafe { core::mem::size_of_val_raw(value as *const u32) } == 4);
    }
    pub fn invalid_reference(value: usize) -> usize {
        let reference = unsafe { &*(value as *const u32) };
        core::mem::align_of_val(reference)
    }
    #[allow(deprecated)]
    pub fn deprecated(value: super::Aligned) -> usize {
        core::mem::min_align_of_val(&value)
    }
    fn metadata(value: &super::Aligned) -> usize {
        core::mem::align_of_val(value)
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_backing() -> usize {
        mir! {
            let backing: super::Aligned;
            let alias: &super::Aligned;
            { backing = super::Aligned(7); alias = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = metadata(alias), ReturnTo(done), UnwindUnreachable())
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
        primitive((u16::MAX, true, '\u{10ffff}', -0.0, f64::NAN));
        padded(Padded {
            small: 3,
            word: u32::MAX,
        });
        aligned(Aligned(7));
        generic(Generic {
            payload: ([3, 7], (false, '\u{d7ff}')),
            flag: true,
        });
        zero(Zero);
        shared_reference(&Padded { small: 3, word: 7 });
        let padded_values = [Padded { small: 3, word: 7 }; 129];
        let aligned_values = [Aligned(7); 129];
        for index in [0, 128, 129, usize::MAX] {
            returned_view(&padded_values, index);
            mutation_claim(&aligned_values, index);
        }
        copied([Aligned(3), Aligned(7)], 1);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(&[Aligned(7); 129], 128);
    }
    #[test]
    #[should_panic]
    fn negative_padding() {
        wrong_padding(Padded { small: 3, word: 7 });
    }
    #[test]
    #[should_panic]
    fn negative_zero() {
        wrong_zero_alignment(Zero);
    }
    #[test]
    #[should_panic]
    fn negative_lookalike() {
        lookalike(Aligned(7));
    }
    #[test]
    #[should_panic]
    fn negative_helper() {
        wrong_helper(Aligned(7));
    }
}
