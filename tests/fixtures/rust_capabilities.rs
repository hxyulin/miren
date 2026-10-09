#![no_std]

use core::future::Future;
use core::pin::pin;
use core::task::{Context, Poll};

pub fn integers(value: u8) {
    if value < 200 {
        assert!(value + 1 > value);
    }
    assert!(value.wrapping_add(1).wrapping_sub(1) == value);
}

pub fn integer_overflow(value: u8) {
    let _ = value + 1;
}

pub enum Message {
    Idle,
    Number(u16),
    Pair(u8, u8),
}

pub fn enum_payload(value: Message) {
    match value {
        Message::Idle => {}
        Message::Number(number) => assert!(number.wrapping_add(1).wrapping_sub(1) == number),
        Message::Pair(left, right) => {
            let pair = (left, right);
            assert!(pair.0 == left && pair.1 == right);
        }
    }
}

pub fn enum_wrong_claim(value: Message) {
    if let Message::Number(number) = value {
        assert!(number == 0);
    }
}

pub fn array_index(index: usize) {
    let values = [3_u16, 5, 7, 9];
    if index < values.len() {
        assert!(values[index] <= 9);
    }
}

pub fn array_out_of_bounds(index: usize) {
    let values = [3_u16, 5, 7, 9];
    let _ = values[index];
}

fn increment(value: &mut u16) {
    *value += 1;
}

pub fn reference_effects() {
    let mut values = [10_u16, 20, 30];
    increment(&mut values[1]);
    assert!(values == [10, 21, 30]);
}

pub fn retained_prefix_index() {
    let mut values = [10_u16, 20, 30];
    let prefix = &mut values[..2];
    increment(&mut prefix[1]);
    assert!(values == [10, 21, 30]);
}

pub fn reference_wrong_claim() {
    let mut value = 10_u16;
    increment(&mut value);
    assert!(value == 10);
}

fn identity<T: Copy>(value: T) -> T {
    value
}

pub fn generic_call(value: (u16, bool)) {
    assert!(identity(value) == value);
}

pub fn closure_call(value: u8) {
    let mask = 15;
    let selected = |input: u8| input & mask;
    assert!(selected(value) <= 15);
}

pub fn closure_wrong_claim(value: u8) {
    let selected = |input: u8| input & 15;
    assert!(selected(value) == 0);
}

pub fn iterator_effects() {
    let mut values = [1_u16, 2, 3];
    values.iter_mut().for_each(|value| *value += 1);
    assert!(values == [2, 3, 4]);
}

pub fn iterator_wrong_claim() {
    let values = [1_u16, 2, 3];
    let sum = values.iter().fold(0_u16, |sum, value| sum + *value);
    assert!(sum == 5);
}

pub fn finite_loop() {
    let mut count = 0_u8;
    while count < 4 {
        count += 1;
    }
    assert!(count == 4);
}

pub fn finite_loop_wrong_claim() {
    let mut count = 0_u8;
    while count < 4 {
        count += 1;
    }
    assert!(count == 3);
}

struct SetOnDrop<'a>(&'a mut u8);

impl Drop for SetOnDrop<'_> {
    fn drop(&mut self) {
        *self.0 = 7;
    }
}

pub fn drop_effects() {
    let mut value = 0;
    {
        let _guard = SetOnDrop(&mut value);
    }
    assert!(value == 7);
}

pub fn drop_wrong_claim() {
    let mut value = 0;
    {
        let _guard = SetOnDrop(&mut value);
    }
    assert!(value == 0);
}

async fn immediate(value: u8) -> u8 {
    value & 7
}

pub fn async_poll(value: u8, context: &mut Context<'_>) {
    let mut future = pin!(immediate(value));
    assert!(future.as_mut().poll(context) == Poll::Ready(value & 7));
}

pub fn async_wrong_claim(value: u8, context: &mut Context<'_>) {
    let mut future = pin!(immediate(value));
    assert!(future.as_mut().poll(context) == Poll::Ready(8));
}

pub fn open_function_pointer(callback: fn(u8) -> u8, value: u8) {
    assert!(callback(value) == value);
}

pub trait Read {
    fn read(&self) -> u8;
}

pub fn open_trait_object(value: &dyn Read) {
    assert!(value.read() == 0);
}

pub fn open_slice(values: &[u16]) {
    if !values.is_empty() {
        assert!(values[0] == 0);
    }
}

pub fn raw_pointer_metadata(length: usize) {
    let pointer = core::ptr::slice_from_raw_parts(core::ptr::null::<u8>(), length);
    assert!(pointer.len() == length);
}

pub fn wrong_raw_pointer_metadata(length: usize) {
    let pointer = core::ptr::slice_from_raw_parts(core::ptr::null::<u8>(), length);
    assert!(pointer.len() != length);
}

pub fn raw_reference_grant() {
    let mut values = [1_u16, 2];
    let references = values.each_mut();
    assert!(*references[0] == 1);
}

pub fn tuple_array_choice(index: usize) {
    let values = [(3_u32, 7_u32), (5, 11), (9, 19)];
    if index < values.len() {
        let selected = values[index];
        assert!(selected.1 == selected.0 * 2 + 1);
    }
}

pub fn tuple_array_wrong_claim(index: usize) {
    let values = [(3_u32, 7_u32), (5, 11)];
    if index < values.len() {
        assert!(values[index].1 == 7);
    }
}

pub fn tuple_array_symbolic_write(index: usize) {
    let mut values = [(3_u32, 7_u32), (5, 11)];
    if index < values.len() {
        values[index] = (9, 19);
        assert!(values[index].1 == 19);
    }
}

pub fn maybe_uninit_round_trip(value: u32, flag: bool) {
    let storage = core::mem::MaybeUninit::new((value, flag));
    let result = unsafe { storage.assume_init() };
    assert!(result == (value, flag));
}

pub fn maybe_uninit_wrong_claim(value: u32, flag: bool) {
    let storage = core::mem::MaybeUninit::new((value, flag));
    let result = unsafe { storage.assume_init() };
    assert!(result.0 == value && result.1 != flag);
}

pub fn maybe_uninit_uninitialized() -> u32 {
    // Analysis-only: never execute this uninitialized payload extraction.
    unsafe { core::mem::MaybeUninit::<u32>::uninit().assume_init() }
}

pub fn maybe_uninit_array(value: [u16; 3]) {
    let storage = core::mem::MaybeUninit::new(value);
    let result = unsafe { storage.assume_init() };
    assert!(result == value);
}

pub fn maybe_uninit_array_wrong_claim(value: [u16; 3]) {
    let storage = core::mem::MaybeUninit::new(value);
    let result = unsafe { storage.assume_init() };
    assert!(result[0] == 0);
}

pub fn maybe_uninit_array_uninitialized() -> [u16; 3] {
    // Analysis-only: never execute this uninitialized payload extraction.
    unsafe { core::mem::MaybeUninit::<[u16; 3]>::uninit().assume_init() }
}

#[cfg(test)]
mod native {
    use super::*;
    use core::task::Waker;

    #[test]
    fn positives() {
        integers(199);
        raw_pointer_metadata(usize::MAX);
        maybe_uninit_round_trip(0, false);
        maybe_uninit_round_trip(u32::MAX, true);
        maybe_uninit_array([0, 1, u16::MAX]);
        maybe_uninit_array([u16::MAX, 0, 7]);
        for index in 0..3 {
            tuple_array_choice(index);
        }
        enum_payload(Message::Pair(4, 9));
        array_index(3);
        reference_effects();
        generic_call((44, true));
        closure_call(255);
        iterator_effects();
        finite_loop();
        drop_effects();
        let mut context = Context::from_waker(Waker::noop());
        async_poll(15, &mut context);
    }

    #[test]
    #[should_panic]
    fn negative_control() {
        reference_wrong_claim();
    }
}
