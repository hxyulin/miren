#![no_std]
#![feature(custom_mir, core_intrinsics, type_alias_impl_trait)]
#![allow(internal_features)]

#[inline(never)]
fn apply<F: Fn() -> u16>(read: F) -> u16 {
    read()
}

#[inline(never)]
fn reader(values: &[u16]) -> impl Fn(usize) -> u16 + '_ {
    move |index| values[index]
}

#[inline(never)]
fn counted_reader<'a>(values: &'a [u16], count: &'a mut u8) -> impl FnMut(usize) -> u16 + 'a {
    move |index| {
        *count += 1;
        values[index]
    }
}

struct Token(u16);

#[inline(never)]
fn consume(token: Token) -> u16 {
    token.0
}

#[inline(never)]
fn apply_once<F: FnOnce() -> (u16, u16)>(read: F) -> (u16, u16) {
    read()
}

#[inline(never)]
fn selected_reader(values: &[u16]) -> impl Fn() -> u16 + '_ {
    move || values[0]
}

pub fn direct_capture(values: &[u16]) {
    if !values.is_empty() {
        let read = || values[0];
        assert!(read() == values[0]);
        assert!(apply(read) == values[0]);
    }
}

pub fn returned_capture(values: &[u16], index: usize) {
    if index < values.len() {
        assert!(reader(values)(index) == values[index]);
    }
}

#[inline(never)]
fn owned_reader(values: &[u16]) -> impl Fn(usize) -> (u16, u16) + '_ {
    let owned = [3_u16, 7];
    move |index| (values[index], owned[1])
}

pub fn returned_owned_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let (borrowed, owned) = owned_reader(values)(index);
        assert!(borrowed == values[index]);
        assert!(owned == 7);
    }
}

pub fn nested_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let inner = reader(values);
        let outer = move || inner(index);
        assert!(apply(outer) == values[index]);
    }
}

pub fn mutable_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let mut count = 0_u8;
        {
            let mut read = || {
                count += 1;
                values[index]
            };
            assert!(read() == values[index]);
            assert!(read() == values[index]);
        }
        assert!(count == 2);
    }
}

pub fn returned_mutable_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let mut count = 0_u8;
        {
            let mut read = counted_reader(values, &mut count);
            assert!(read(index) == values[index]);
            assert!(read(index) == values[index]);
        }
        assert!(count == 2);
    }
}

#[inline(never)]
fn apply_mut_once<F: FnOnce(usize) -> u16>(read: F, index: usize) -> u16 {
    read(index)
}

#[inline(never)]
fn apply_value_once<F: FnOnce() -> u16>(read: F) -> u16 {
    read()
}

pub fn mutable_once_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let mut count = 0_u8;
        let read = counted_reader(values, &mut count);
        assert!(apply_mut_once(read, index) == values[index]);
        assert!(count == 1);
    }
}

struct DropWitness<'a>(&'a core::cell::Cell<u8>);

impl Drop for DropWitness<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get().wrapping_add(1));
    }
}

pub fn drop_capture(values: &[u16]) {
    if !values.is_empty() {
        let count = core::cell::Cell::new(0);
        let token = DropWitness(&count);
        let read = move || {
            let _ = &token;
            values[0]
        };
        assert!(apply_value_once(read) == values[0]);
        assert!(count.get() == 1);
    }
}

struct PanickingDrop;

impl Drop for PanickingDrop {
    fn drop(&mut self) {
        panic!("retained capture drop body");
    }
}

pub fn drop_body_panics(values: &[u16]) {
    if !values.is_empty() {
        let token = PanickingDrop;
        let read = move || {
            let _ = &token;
            values[0]
        };
        let _ = apply_value_once(read);
    }
}

pub fn once_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let token = Token(7);
        let read = move || (values[index], consume(token));
        let (selected, token) = apply_once(read);
        assert!(selected == values[index]);
        assert!(token == 7);
    }
}

pub fn captured_find(values: &[u16]) {
    if !values.is_empty() {
        let selected = values.iter().find(|value| **value == values[0]);
        assert!(*selected.unwrap() == values[0]);
    }
}

pub fn float32_capture(values: &[f32], index: usize) {
    if index < values.len() {
        let read = move || values[index];
        assert!(read().to_bits() == values[index].to_bits());
        if values[index].is_nan() {
            assert!(read().is_nan());
        }
        if values[index].to_bits() == 0x80000000 {
            assert!(read() == 0.0);
        }
    }
}

pub fn float64_capture(values: &[f64], index: usize) {
    if index < values.len() {
        let read = move || values[index];
        assert!(read().to_bits() == values[index].to_bits());
        if values[index].is_nan() {
            assert!(read().is_nan());
        }
        if values[index].to_bits() == 0x8000000000000000 {
            assert!(read() == 0.0);
        }
    }
}

pub fn char_capture(values: &[char], index: usize) {
    if index < values.len() {
        let read = move || values[index];
        assert!(read() == values[index]);
        let bits = read() as u32;
        assert!(bits <= 0x10ffff);
        assert!(bits < 0xd800 || bits > 0xdfff);
    }
}

pub fn initialized_wrapper_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let storage = core::mem::MaybeUninit::new((values[index], true));
        let read = move || {
            // Valid constructor state; no uninitialized native extraction.
            let (selected, initialized) = unsafe { storage.assume_init() };
            assert!(initialized);
            (selected, values[index])
        };
        let (selected, original) = read();
        assert!(selected == original);
    }
}

pub fn mutation_claim(values: &[u16]) {
    if values.len() >= 2 {
        assert!(selected_reader(values)() == values[0]);
    }
}

pub fn wrong_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let read = move || values[index];
        assert!(read() == 0);
    }
}

pub fn wrong_counter(values: &[u16]) {
    if !values.is_empty() {
        let mut count = 0_u8;
        {
            let mut read = counted_reader(values, &mut count);
            let _ = read(0);
            let _ = read(0);
        }
        assert!(count == 1);
    }
}

pub fn float_reflexivity(values: &[f32]) {
    if !values.is_empty() {
        let read = move || values[0];
        assert!(read() == read());
    }
}

pub fn mutable_root(values: &mut [u16]) {
    if !values.is_empty() {
        let read = || values[0];
        assert!(read() == values[0]);
    }
}

pub fn unbounded_capture_scan(values: &[u16], needle: u16) -> usize {
    values.iter().fold(0_usize, |count, value| {
        count.wrapping_add(usize::from(*value == needle))
    })
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    unsafe extern "Rust" {
        fn opaque_read(value: u16) -> u16;
    }

    pub fn missing_body(values: &[u16]) {
        if !values.is_empty() {
            let read = || unsafe { opaque_read(values[0]) };
            assert!(read() == values[0]);
        }
    }

    type HolderReader<'a> = impl Fn() -> usize + 'a;

    #[define_opaque(HolderReader)]
    #[inline(never)]
    fn holder_reader<'a>(holder: &'a [&'a [u16]; 1]) -> HolderReader<'a> {
        move || holder[0].len()
    }

    #[inline(never)]
    fn invoke<F: FnOnce() -> usize>(read: F) -> usize {
        read()
    }

    #[inline(never)]
    fn length_reader(values: &[u16]) -> impl Fn() -> usize + '_ {
        move || values.len()
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn opaque_local_handle_dead(values: &[u16]) -> usize {
        mir! {
            let read;
            {
                Call(read = length_reader(values), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(values);
                Call(RET = invoke(read), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn forget_handle<F: FnOnce() -> usize>(values: &[u16], read: F) -> usize {
        mir! {
            {
                StorageDead(values);
                Call(RET = invoke(read), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    pub fn original_handle_dead(values: &[u16]) -> usize {
        let read = move || values.len();
        forget_handle(values, read)
    }

    pub fn uninitialized_wrapper_capture(values: &[u16]) -> u16 {
        let storage = core::mem::MaybeUninit::<u16>::uninit();
        let read = move || {
            let _ = values.len();
            // Analysis-only: never execute this uninitialized extraction.
            unsafe { storage.assume_init() }
        };
        read()
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_capture_storage(values: &[u16]) -> usize {
        mir! {
            let holder: [&[u16]; 1];
            let source: &[&[u16]; 1];
            let read;
            {
                holder = [values];
                source = &holder;
                Call(read = holder_reader(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(holder);
                Call(RET = invoke(read), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn escaped_frame_capture(values: &[u16]) -> HolderReader<'_> {
        mir! {
            let holder: [&[u16]; 1];
            let source: &[&[u16]; 1];
            {
                holder = [values];
                source = &holder;
                Call(RET = holder_reader(source), ReturnTo(done), UnwindUnreachable())
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
        for values in [&[][..], &[3, 7][..], &[7; 129][..]] {
            direct_capture(values);
            captured_find(values);
            drop_capture(values);
            mutation_claim(values);
            for index in [0, 1, 128, values.len()] {
                returned_capture(values, index);
                returned_owned_capture(values, index);
                nested_capture(values, index);
                mutable_capture(values, index);
                returned_mutable_capture(values, index);
                once_capture(values, index);
                mutable_once_capture(values, index);
                initialized_wrapper_capture(values, index);
            }
        }
        let narrow = [f32::from_bits(0x7fc00015), -0.0, f32::MIN_POSITIVE];
        let wide = [f64::from_bits(0x7ff8000000000015), -0.0, f64::MAX];
        let characters = ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'];
        for index in 0..characters.len() {
            float32_capture(&narrow, index);
            float64_capture(&wide, index);
            char_capture(&characters, index);
        }
    }

    #[test]
    fn mutation_guard() {
        mutation_claim(&[3, 7]);
    }

    #[test]
    #[should_panic]
    fn captured_counter_failure() {
        wrong_counter(&[3]);
    }

    #[test]
    #[should_panic]
    fn captured_drop_failure() {
        drop_body_panics(&[3]);
    }

    #[test]
    #[should_panic]
    fn captured_nan_failure() {
        float_reflexivity(&[f32::NAN]);
    }
}
