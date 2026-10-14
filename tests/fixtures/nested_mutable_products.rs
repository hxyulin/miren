#![no_std]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![cfg_attr(not(test), allow(internal_features))]
#![cfg_attr(test, feature(custom_mir, core_intrinsics))]
#![cfg_attr(test, allow(internal_features))]

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

pub fn open_slice_read_correlation(values: &[u16], index: usize) {
    if index < values.len() {
        let first = values[index];
        let second = values[index];
        assert!(first == second);
    }
}

pub fn open_aggregate_slice(values: &[(u16, u16)]) {
    if !values.is_empty() {
        assert!(values[0].0 == 0);
    }
}

pub fn scalar_slice_nth(values: &[u16], index: usize) {
    match values.iter().nth(index) {
        Some(value) => {
            assert!(index < values.len());
            assert!(*value == values[index]);
        }
        None => assert!(index >= values.len()),
    }
}

pub fn scalar_slice_iterator_wrong_claim(values: &[u16]) {
    if !values.is_empty() {
        assert!(*values.iter().nth(0).unwrap() == 0);
    }
}

pub fn scalar_slice_unbounded_fold(values: &[u16]) -> u64 {
    values
        .iter()
        .fold(0_u64, |sum, value| sum.wrapping_add(u64::from(*value)))
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

pub fn checked_char(value: u32) {
    if let Some(character) = core::char::from_u32(value) {
        assert!(character as u32 == value);
    } else {
        assert!(value > 0x10ffff || (0xd800 <= value && value <= 0xdfff));
    }
}

pub fn checked_char_wrong_claim(value: u32) {
    if let Some(character) = core::char::from_u32(value) {
        assert!(character as u32 != value);
    }
}

pub fn char_invalid_float_bits() -> char {
    // Analysis-only: never execute this invalid character formation.
    unsafe { core::mem::transmute(f32::from_bits(0xd800)) }
}

pub fn maybe_uninit_char(value: char) {
    let storage = core::mem::MaybeUninit::new(value);
    let result = unsafe { storage.assume_init() };
    assert!(result == value);
}

pub fn maybe_uninit_char_wrong_claim(value: char) {
    let storage = core::mem::MaybeUninit::new(value);
    let result = unsafe { storage.assume_init() };
    assert!(result != value);
}

pub fn maybe_uninit_char_uninitialized() -> char {
    // Analysis-only: never execute this uninitialized character extraction.
    unsafe { core::mem::MaybeUninit::<char>::uninit().assume_init() }
}

pub fn float_remainder(negative: bool) {
    let value = if negative { -5.0f32 } else { 5.0f32 };
    assert!(value % 3.0 == if negative { -2.0 } else { 2.0 });
}

pub fn float_remainder_wrong_claim(negative: bool) {
    let value = if negative { -5.0f32 } else { 5.0f32 };
    assert!(value % 3.0 == if negative { 2.0 } else { -1.0 });
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_float_remainder(value: f32, divisor: f32) -> f32;
}

#[cfg(not(test))]
pub fn external_float_remainder(value: f32) -> f32 {
    // A declaration is not a verified body, even when its name suggests remainder.
    unsafe { opaque_float_remainder(value, 3.0) }
}

pub fn bounded_scalar_contains(values: &[u16]) {
    if !values.is_empty() && values.len() <= 4 {
        assert!(values.contains(&values[0]));
    }
}

pub fn bounded_scalar_contains_wrong_claim(values: &[u16]) {
    if !values.is_empty() && values.len() <= 4 {
        assert!(!values.contains(&values[0]));
    }
}

pub fn unbounded_scalar_contains(values: &[u16], needle: u16) -> bool {
    values.contains(&needle)
}

#[inline(never)]
fn scalar_reader(values: &[u16], index: usize) -> impl Fn() -> u16 + '_ {
    move || values[index]
}

pub fn scalar_slice_capture(values: &[u16], index: usize) {
    if index < values.len() {
        let reader = scalar_reader(values, index);
        assert!(reader() == values[index]);
    }
}

pub fn scalar_slice_capture_wrong_claim(values: &[u16], index: usize) {
    if index < values.len() {
        let reader = scalar_reader(values, index);
        assert!(reader() == 0);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_captured_word(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn scalar_slice_capture_missing_body(values: &[u16], index: usize) -> u16 {
    if index < values.len() {
        let reader = move || unsafe { opaque_captured_word(values[index]) };
        reader()
    } else {
        0
    }
}

pub fn scalar_slice_full_member(values: &[u16], index: usize) {
    if index < values.len() {
        assert!(values.contains(&values[index]));
        assert!(values[index..] == values[index..]);
    }
}

pub fn scalar_slice_full_wrong_claim(values: &[u16]) {
    if values.len() > 128 {
        assert!(values.contains(&0));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_full_scalar_predicate(value: bool) -> bool;
}

#[cfg(not(test))]
pub fn scalar_slice_full_missing_body(values: &[u16], needle: u16) -> bool {
    unsafe { opaque_full_scalar_predicate(values.contains(&needle)) }
}

pub fn composite_slice_views(values: &[(u16, [u16; 2])], index: usize) {
    if index < values.len() {
        let suffix = &values[index..];
        let owned = suffix[0];
        assert!(owned.0 == values[index].0);
        assert!(owned.1[1] == values[index].1[1]);
        assert!(suffix.len() == values.len() - index);
    }
}

pub fn composite_slice_wrong_field(values: &[(u16, [u16; 2])]) {
    if values.len() > 128 {
        assert!(values[128].0 == values[128].1[1]);
    }
}

pub fn composite_slice_iteration(values: &[(u16, u16)]) -> usize {
    values.iter().count()
}

pub fn nested_array_choice(index: usize) {
    let values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[1] == selected[0] * 2 + 1);
    }
}

pub fn nested_array_choice_wrong_claim(index: usize) {
    let values = [[3_u16, 7], [5, 11]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0] == selected[1]);
    }
}

pub fn nested_byte_array_choice(index: usize) -> [u8; 2] {
    let values = [[3_u8, 7], [5, 11]];
    if index < values.len() {
        values[index]
    } else {
        [0, 0]
    }
}

pub fn composite_iterator_nth(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let item = values.iter().nth(index).unwrap();
        assert!(item.0 == values[index].0);
        assert!(item.1 == values[index].1);
    }
}

pub fn composite_iterator_wrong_claim(values: &[(u16, u16)]) {
    if values.len() > 128 {
        assert!(values.iter().nth(128).unwrap().0 == 0);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_composite_iterator_word(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn composite_iterator_missing_body(values: &[(u16, u16)], index: usize) -> u16 {
    if index < values.len() {
        let item = values.iter().nth(index).unwrap();
        unsafe { opaque_composite_iterator_word(item.0) }
    } else {
        0
    }
}

pub fn zero_sized_slice_cursor(values: &[()], index: usize) {
    let mut iter = values.iter();
    assert!(iter.len() == values.len());
    if index < values.len() {
        assert!(iter.nth(index).is_some());
        assert!(iter.count() == values.len() - index - 1);
    } else {
        assert!(iter.nth(index).is_none());
        assert!(iter.count() == 0);
    }
}

pub fn zero_sized_slice_wrong_claim(values: &[()]) {
    if values.len() > 128 {
        assert!(values.iter().nth(128).is_none());
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_zero_sized_slice_length(length: usize) -> usize;
}

#[cfg(not(test))]
pub fn zero_sized_slice_missing_body(values: &[[u32; 0]]) -> usize {
    unsafe { opaque_zero_sized_slice_length(values.len()) }
}

pub fn composite_slice_byte_size(values: &[(u8, u32)]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<(u8, u32)>());
}

pub fn composite_slice_byte_size_wrong_claim(values: &[(u8, u32)]) {
    if !values.is_empty() {
        let leaf_sizes = core::mem::size_of::<u8>() + core::mem::size_of::<u32>();
        assert!(core::mem::size_of_val(values) == values.len() * leaf_sizes);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_composite_slice_size(size: usize) -> usize;
}

#[cfg(not(test))]
pub fn composite_slice_byte_size_missing_body(values: &[(u8, u32)]) -> usize {
    unsafe { opaque_composite_slice_size(core::mem::size_of_val(values)) }
}

pub fn slice_dynamic_alignment(values: &[(u8, u32)]) {
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<(u8, u32)>());
}

pub fn slice_dynamic_alignment_wrong_claim(values: &[[u32; 0]]) {
    assert!(core::mem::align_of_val(values) == core::mem::size_of::<[u32; 0]>());
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_slice_dynamic_alignment(alignment: usize) -> usize;
}

#[cfg(not(test))]
pub fn slice_dynamic_alignment_missing_body(values: &[[u32; 0]]) -> usize {
    unsafe { opaque_slice_dynamic_alignment(core::mem::align_of_val(values)) }
}

#[derive(Clone, Copy, PartialEq)]
pub struct SliceSample {
    pub left: u16,
    pub right: u16,
}

pub fn local_struct_slice_read(values: &[SliceSample], index: usize) {
    if index < values.len() {
        let selected = values.iter().nth(index).unwrap();
        assert!(selected.left == values[index].left);
        assert!(selected.right == values[index].right);
    }
}

pub fn local_struct_slice_wrong_claim(values: &[SliceSample]) {
    if values.len() > 128 {
        assert!(values[128].left == values[128].right);
    }
}

pub fn local_struct_slice_membership(values: &[SliceSample], needle: SliceSample) -> bool {
    values.contains(&needle)
}

#[derive(Clone, Copy)]
pub struct NominalZero;

pub fn local_zero_struct_cursor(values: &[NominalZero], index: usize) {
    let mut iter = values.iter();
    if index < values.len() {
        assert!(iter.nth(index).is_some());
        assert!(iter.len() == values.len() - index - 1);
    } else {
        assert!(iter.nth(index).is_none());
        assert!(iter.len() == 0);
    }
}

pub fn local_zero_struct_wrong_claim(values: &[NominalZero]) {
    assert!(values.len() <= isize::MAX as usize);
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_local_zero_struct_length(length: usize) -> usize;
}

#[cfg(not(test))]
pub fn local_zero_struct_missing_body(values: &[NominalZero]) -> usize {
    unsafe { opaque_local_zero_struct_length(values.iter().count()) }
}

pub fn typed_struct_array_choice(index: usize) {
    let values = [
        SliceSample { left: 3, right: 7 },
        SliceSample {
            left: 11,
            right: 13,
        },
    ];
    if index < values.len() {
        let selected = values[index];
        assert!(selected.left == if index == 0 { 3 } else { 11 });
        assert!(selected.right == if index == 0 { 7 } else { 13 });
    }
}

pub fn typed_struct_array_wrong_claim(index: usize) {
    let values = [
        SliceSample { left: 3, right: 7 },
        SliceSample {
            left: 11,
            right: 13,
        },
    ];
    if index < values.len() {
        assert!(values[index].left == 0);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_typed_struct_field(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn typed_struct_array_missing_body(index: usize) -> u16 {
    let values = [
        SliceSample { left: 3, right: 7 },
        SliceSample {
            left: 11,
            right: 13,
        },
    ];
    if index < values.len() {
        unsafe { opaque_typed_struct_field(values[index].left) }
    } else {
        0
    }
}

pub fn typed_byte_array_choice(index: usize) {
    let values = [[3_u8, 7], [11, 13]];
    if index < values.len() {
        let selected = values[index];
        assert!(selected[0] == if index == 0 { 3 } else { 11 });
        assert!(selected[1] == if index == 0 { 7 } else { 13 });
    }
}

pub fn typed_byte_array_wrong_claim(index: usize) {
    let values = [[3_u8, 7], [11, 13]];
    if index < values.len() {
        assert!(values[index][0] == 0);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_typed_byte(value: u8) -> u8;
}

#[cfg(not(test))]
pub fn typed_byte_array_missing_body(index: usize) -> u8 {
    let values = [[3_u8, 7], [11, 13]];
    if index < values.len() {
        unsafe { opaque_typed_byte(values[index][0]) }
    } else {
        0
    }
}

#[inline(never)]
fn owned_array_replacement(value: u32) -> (u32, u32) {
    (value, value.wrapping_add(1))
}

pub fn owned_array_whole_write(index: usize, value: u32) {
    let mut values = [(3_u32, 7_u32), (5, 11)];
    if index < values.len() {
        values[index] = owned_array_replacement(value);
        let selected = values[index];
        assert!(selected.0 == value);
        assert!(selected.1 == value.wrapping_add(1));
    }
}

pub fn owned_array_whole_wrong_claim(index: usize, value: u32) {
    let mut values = [(3_u32, 7_u32), (5, 11)];
    if index < values.len() {
        values[index] = owned_array_replacement(value);
        assert!(values[index].0 == value.wrapping_add(1));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_owned_array_replacement(value: u32) -> u32;
}

#[cfg(not(test))]
pub fn owned_array_whole_missing_body(index: usize, value: u32) {
    let mut values = [(3_u32, 7_u32), (5, 11)];
    if index < values.len() {
        let replacement = unsafe { opaque_owned_array_replacement(value) };
        values[index] = (replacement, value);
        assert!(values[index].1 == value);
    }
}

#[derive(Clone, Copy)]
pub struct DeferredZero<const TAG: usize>;

impl<const TAG: usize> DeferredZero<TAG> {
    #[inline(never)]
    fn marker(&self) -> usize {
        TAG
    }
}

pub fn deferred_zero_owned_write(mut values: [DeferredZero<7>; 2], index: usize) {
    if index < values.len() {
        values[index] = DeferredZero;
        let copied = values[index];
        assert!(copied.marker() == 7);
    }
}

pub fn deferred_zero_owned_wrong_claim(mut values: [DeferredZero<7>; 2], index: usize) {
    if index < values.len() {
        values[index] = DeferredZero;
        let copied = values[index];
        assert!(copied.marker() == 8);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_deferred_zero_marker(value: usize) -> usize;
}

#[cfg(not(test))]
pub fn deferred_zero_owned_missing_body(mut values: [DeferredZero<7>; 2], index: usize) -> usize {
    if index < values.len() {
        values[index] = DeferredZero;
        let copied = values[index];
        unsafe { opaque_deferred_zero_marker(copied.marker()) }
    } else {
        0
    }
}

#[repr(align(64))]
#[derive(Clone, Copy)]
pub struct SizedLayoutZero;

#[inline(never)]
fn sized_layout_alignment(value: &SizedLayoutZero) -> usize {
    core::mem::align_of_val(value)
}

pub fn safe_sized_alignment(value: SizedLayoutZero) {
    assert!(sized_layout_alignment(&value) == 64);
    assert!(core::mem::size_of_val(&value) == 0);
}

pub fn safe_sized_alignment_wrong_claim(value: SizedLayoutZero) {
    assert!(sized_layout_alignment(&value) == 0);
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_sized_alignment(alignment: usize) -> usize;
}

#[cfg(not(test))]
pub fn safe_sized_alignment_missing_body(value: SizedLayoutZero) -> usize {
    unsafe { opaque_sized_alignment(sized_layout_alignment(&value)) }
}

#[derive(Clone, Copy)]
pub struct ReservedRecord {
    left: u16,
    right: u16,
}

pub fn registered_product_choice(
    first: [ReservedRecord; 64],
    _second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
) {
    if index < first.len() {
        let selected = first[index];
        let again = first[index];
        assert!(selected.left == again.left);
        assert!(selected.right == again.right);
    }
}

pub fn registered_product_wrong_claim(
    first: [ReservedRecord; 64],
    second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
) {
    if index < first.len() {
        let left = first[index];
        let right = second[index];
        assert!(left.left == right.left);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_registered_field(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn registered_product_missing_body(
    first: [ReservedRecord; 64],
    _second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
) -> u16 {
    if index < first.len() {
        let selected = first[index];
        unsafe { opaque_registered_field(selected.left) }
    } else {
        0
    }
}

pub fn owned_array_field_write(
    mut first: [ReservedRecord; 64],
    _second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        let before = first[index];
        first[index].left = value;
        let selected = first[index];
        assert!(selected.left == value);
        assert!(selected.right == before.right);
    }
}

pub fn owned_array_field_wrong_claim(
    mut first: [ReservedRecord; 64],
    _second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        first[index].left = value;
        let selected = first[index];
        assert!(selected.left == value.wrapping_add(1));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_owned_field_replacement(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn owned_array_field_missing_body(
    mut first: [ReservedRecord; 64],
    _second: [ReservedRecord; 64],
    _third: [ReservedRecord; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        let replacement = unsafe { opaque_owned_field_replacement(value) };
        first[index].left = replacement;
        let selected = first[index];
        assert!(selected.left == replacement);
    }
}

pub fn owned_array_fixed_write(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        let before = first[index];
        first[index][0] = value;
        let selected = first[index];
        assert!(selected[0] == value);
        assert!(selected[1] == before[1]);
    }
}

pub fn owned_array_fixed_selected_write(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        first[index][0] = value;
        let selected = first[index];
        assert!(selected[0] == value);
    }
}

pub fn owned_array_fixed_wrong_claim(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        first[index][0] = value;
        let selected = first[index];
        assert!(selected[0] == value.wrapping_add(1));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_owned_fixed_replacement(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn owned_array_fixed_missing_body(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
    value: u16,
) {
    if index < first.len() {
        let replacement = unsafe { opaque_owned_fixed_replacement(value) };
        first[index][0] = replacement;
        let selected = first[index];
        assert!(selected[0] == replacement);
    }
}

pub fn registered_pure_array_read(
    first: [(u16, [u16; 2]); 64],
    _second: [(u16, [u16; 2]); 64],
    _third: [(u16, [u16; 2]); 64],
    index: usize,
) {
    if index < first.len() {
        let selected = first[index];
        let repeated = first[index];
        assert!(selected.0 == repeated.0);
        assert!(selected.1[0] == repeated.1[0]);
        assert!(selected.1[1] == repeated.1[1]);
    }
}

pub fn registered_pure_array_wrong_claim(
    first: [(u16, [u16; 2]); 64],
    second: [(u16, [u16; 2]); 64],
    _third: [(u16, [u16; 2]); 64],
    index: usize,
) {
    if index < first.len() {
        let selected = first[index];
        let different = second[index];
        assert!(selected.0 == different.0);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_registered_pure_field(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn registered_pure_array_missing_body(
    first: [(u16, [u16; 2]); 64],
    _second: [(u16, [u16; 2]); 64],
    _third: [(u16, [u16; 2]); 64],
    index: usize,
) -> u16 {
    if index < first.len() {
        let selected = first[index];
        unsafe { opaque_registered_pure_field(selected.0) }
    } else {
        0
    }
}

pub fn owned_array_dynamic_write(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    outer: usize,
    inner: usize,
    value: u16,
) {
    if outer < first.len() && inner < 2 {
        let before = first[outer];
        let other_before = first[outer ^ 1];
        first[outer][inner] = value;
        let selected = first[outer];
        let unchanged = first[outer ^ 1];
        assert!(selected[inner] == value);
        assert!(selected[inner ^ 1] == before[inner ^ 1]);
        assert!(unchanged[0] == other_before[0]);
        assert!(unchanged[1] == other_before[1]);
    }
}

pub fn owned_array_dynamic_wrong_claim(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    outer: usize,
    inner: usize,
    value: u16,
) {
    if outer < first.len() && inner < 2 {
        first[outer][inner] = value;
        let selected = first[outer];
        assert!(selected[inner] == value.wrapping_add(1));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_owned_dynamic_replacement(value: u16) -> u16;
}

#[cfg(not(test))]
pub fn owned_array_dynamic_missing_body(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    outer: usize,
    inner: usize,
    value: u16,
) {
    if outer < first.len() && inner < 2 {
        let replacement = unsafe { opaque_owned_dynamic_replacement(value) };
        first[outer][inner] = replacement;
        let selected = first[outer];
        assert!(selected[inner] == replacement);
    }
}

#[inline(never)]
pub fn retained_array_first(value: &[u16; 2]) -> u16 {
    value[0]
}

pub fn retained_owned_array_read(
    first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
) {
    if index < first.len() {
        let copied = first[index];
        let selected = &first[index];
        let alias = selected;
        assert!(retained_array_first(alias) == copied[0]);
        assert!(selected[1] == copied[1]);
    }
}

pub fn retained_owned_array_wrong_claim(
    first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
) {
    if index < first.len() {
        let copied = first[index];
        let selected = &first[index];
        assert!(retained_array_first(selected) == copied[1]);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_retained_array_getter(value: &[u16; 2]) -> u16;
}

#[cfg(not(test))]
pub fn retained_owned_array_missing_body(
    first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    index: usize,
) -> u16 {
    if index < first.len() {
        let selected = &first[index];
        unsafe { opaque_retained_array_getter(selected) }
    } else {
        0
    }
}

pub fn known_owned_array_write(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    inner: usize,
    replacement: u16,
) {
    if inner < 2 {
        let before = first[0];
        let other = first[63];
        first[0][inner] = replacement;
        let selected = first[0];
        assert!(selected[inner] == replacement);
        assert!(selected[inner ^ 1] == before[inner ^ 1]);
        assert!(first[63] == other);
    }
}

pub fn known_owned_array_wrong_claim(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    inner: usize,
    replacement: u16,
) {
    if inner < 2 {
        first[0][inner] = replacement;
        let selected = first[0];
        assert!(selected[inner ^ 1] == replacement);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_known_array_replacement() -> u16;
}

#[cfg(not(test))]
pub fn known_owned_array_missing_body(
    mut first: [[u16; 2]; 64],
    _second: [[u16; 2]; 64],
    _third: [[u16; 2]; 64],
    inner: usize,
) {
    if inner < 2 {
        let replacement = unsafe { opaque_known_array_replacement() };
        first[0][inner] = replacement;
        let selected = first[0];
        assert!(selected[inner] == replacement);
    }
}

#[derive(Clone, Copy)]
pub struct OwnedArrayProduct {
    pub rows: [ReservedRecord; 64],
    pub ready: bool,
}

pub fn owned_product_array_write(
    mut first: OwnedArrayProduct,
    _second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
    replacement: u16,
) {
    if index < first.rows.len() {
        let before = first.rows[index];
        let other = first.rows[63];
        let ready = first.ready;
        first.rows[index].left = replacement;
        let selected = first.rows[index];
        assert!(selected.left == replacement);
        assert!(selected.right == before.right);
        assert!(first.ready == ready);
        if index != 63 {
            let after = first.rows[63];
            assert!(after.left == other.left);
            assert!(after.right == other.right);
        }
    }
}

pub fn owned_product_array_wrong_claim(
    mut first: OwnedArrayProduct,
    _second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
    replacement: u16,
) {
    if index < first.rows.len() {
        first.rows[index].left = replacement;
        let selected = first.rows[index];
        assert!(selected.right == replacement);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_product_array_replacement() -> u16;
}

#[cfg(not(test))]
pub fn owned_product_array_missing_body(
    mut first: OwnedArrayProduct,
    _second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
) {
    if index < first.rows.len() {
        let replacement = unsafe { opaque_product_array_replacement() };
        first.rows[index].left = replacement;
        let selected = first.rows[index];
        assert!(selected.left == replacement);
    }
}

#[inline(never)]
fn retained_owned_field_getter(record: &ReservedRecord) -> u16 {
    record.left
}

pub fn retained_owned_field_read(
    first: OwnedArrayProduct,
    _second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
) {
    if index < first.rows.len() {
        let borrowed = &first.rows[index];
        let repeated = &first.rows[index];
        let selected = first.rows[index];
        assert!(retained_owned_field_getter(borrowed) == selected.left);
        assert!(borrowed.right == repeated.right);
    }
}

pub fn retained_owned_field_wrong_claim(
    first: OwnedArrayProduct,
    second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
) {
    if index < first.rows.len() {
        let borrowed = &first.rows[index];
        let different = second.rows[index];
        assert!(retained_owned_field_getter(borrowed) == different.left);
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_retained_owned_field_getter(record: &ReservedRecord) -> u16;
}

#[cfg(not(test))]
pub fn retained_owned_field_missing_body(
    first: OwnedArrayProduct,
    _second: OwnedArrayProduct,
    _third: OwnedArrayProduct,
    index: usize,
) -> u16 {
    if index < first.rows.len() {
        let borrowed = &first.rows[index];
        unsafe { opaque_retained_owned_field_getter(borrowed) }
    } else {
        0
    }
}

#[inline(never)]
fn owned_call_advance(index: &mut usize) -> u16 {
    *index ^= 1;
    19
}
#[cfg(not(test))]
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn owned_call_update(mut values: ([u16; 2], u16), mut index: usize) -> (([u16; 2], u16), usize) {
    use core::intrinsics::mir::*;
    mir! {
        let pointer: &mut usize;
        {
            pointer = &mut index;
            Call(values.0[index] = owned_call_advance(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (values, index); Return() }
    }
}
#[cfg(test)]
fn owned_call_update(mut values: ([u16; 2], u16), mut index: usize) -> (([u16; 2], u16), usize) {
    let selected = index;
    let result = owned_call_advance(&mut index);
    values.0[selected] = result;
    (values, index)
}
pub fn owned_call_destination(values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let (changed, advanced) = owned_call_update(values, index);
        assert!(changed.0[index] == 19);
        assert!(changed.0[index ^ 1] == values.0[index ^ 1]);
        assert!(changed.1 == values.1);
        assert!(advanced == index ^ 1);
    }
}
pub fn owned_call_destination_wrong_claim(values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let (changed, _) = owned_call_update(values, index);
        assert!(changed.0[index] == 20);
    }
}
#[cfg(not(test))]
unsafe extern "Rust" {
    fn owned_call_unavailable() -> u16;
}
#[cfg(not(test))]
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn owned_call_missing_update(mut values: ([u16; 2], u16), index: usize) {
    use core::intrinsics::mir::*;
    mir! {
        { Call(values.0[index] = owned_call_unavailable(), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[cfg(not(test))]
pub fn owned_call_destination_missing_body(values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        owned_call_missing_update(values, index);
    }
}

#[inline(never)]
fn tracked_call_redirect<'a>(pointer: &mut &'a mut u16, other: &'a mut u16) -> u16 {
    *pointer = other;
    19
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn tracked_call_update(mut left: u16, mut right: u16) -> (u16, u16) {
    use core::intrinsics::mir::*;
    mir! {
        let pointer: &mut u16;
        let other: &mut u16;
        let indirect: &mut &mut u16;
        {
            pointer = &mut left;
            other = &mut right;
            indirect = &mut pointer;
            Call(*pointer = tracked_call_redirect(indirect, other),
                ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (left, right); Return() }
    }
}

pub fn tracked_call_destination(left: u16, right: u16) {
    let (changed_left, changed_right) = tracked_call_update(left, right);
    assert!(changed_left == 19);
    assert!(changed_right == right);
}

pub fn tracked_call_destination_wrong_claim(left: u16, right: u16) {
    let (changed_left, changed_right) = tracked_call_update(left, right);
    assert!(changed_left == left);
    assert!(changed_right == 19);
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn tracked_call_unavailable() -> u16;
}

#[cfg(not(test))]
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn tracked_call_destination_missing_body(mut value: u16) {
    use core::intrinsics::mir::*;
    mir! {
        let target: &mut u16;
        {
            target = &mut value;
            Call(*target = tracked_call_unavailable(), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[inline(never)]
fn full_composite_selected(values: &[(u16, [u16; 2])], index: usize) -> (u16, [u16; 2]) {
    values[index]
}

pub fn full_composite_predicates(values: &[(u16, [u16; 2])], index: usize) {
    if index < values.len() {
        let selected = full_composite_selected(values, index);
        assert!(values.contains(&selected));
        assert!(values == values);
    }
}

pub fn full_composite_predicates_wrong_claim(values: &[(u16, [u16; 2])], index: usize) {
    if index < values.len() {
        let selected = full_composite_selected(values, index);
        assert!(!values.contains(&selected));
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_full_composite_predicate(value: (u16, [u16; 2])) -> bool;
}

#[cfg(not(test))]
pub fn full_composite_predicates_missing_body(values: &[(u16, [u16; 2])], index: usize) -> bool {
    if index < values.len() {
        let selected = full_composite_selected(values, index);
        assert!(values.contains(&selected));
        unsafe { opaque_full_composite_predicate(selected) }
    } else {
        false
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum TaggedReading {
    Empty = 3,
    Pair(u16, u16) = 11,
}

#[inline(never)]
fn tagged_sum_selected(value: TaggedReading) -> u16 {
    match value {
        TaggedReading::Pair(left, _) => left,
        TaggedReading::Empty => 0,
    }
}

pub fn tagged_sum_slice(values: &[TaggedReading], index: usize) {
    if index < values.len() {
        if let TaggedReading::Pair(left, _) = values[index] {
            assert!(tagged_sum_selected(values[index]) == left);
        }
    }
}

pub fn tagged_sum_slice_wrong_claim(values: &[TaggedReading], index: usize) {
    if index < values.len() {
        if let TaggedReading::Pair(left, _) = values[index] {
            assert!(left == 0);
        }
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_tagged_sum_slice(value: TaggedReading) -> u16;
}

#[cfg(not(test))]
pub fn tagged_sum_slice_missing_body(values: &[TaggedReading], index: usize) -> u16 {
    if index < values.len() {
        if let TaggedReading::Pair(left, _) = values[index] {
            assert!(tagged_sum_selected(values[index]) == left);
            return unsafe { opaque_tagged_sum_slice(values[index]) };
        }
    }
    0
}

#[derive(Clone, Copy)]
pub enum BoolNicheReading {
    Empty,
    Flag(bool),
}

#[inline(never)]
fn bool_niche_selected(value: BoolNicheReading) -> bool {
    match value {
        BoolNicheReading::Flag(flag) => flag,
        BoolNicheReading::Empty => false,
    }
}

pub fn bool_niche_slice(values: &[BoolNicheReading], index: usize) {
    if index < values.len() {
        if let BoolNicheReading::Flag(flag) = values[index] {
            assert!(bool_niche_selected(values[index]) == flag);
        }
    }
}

pub fn bool_niche_slice_wrong_claim(values: &[BoolNicheReading], index: usize) {
    if index < values.len() {
        if let BoolNicheReading::Flag(flag) = values[index] {
            assert!(!flag);
        }
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_bool_niche_slice(value: BoolNicheReading) -> bool;
}

#[cfg(not(test))]
pub fn bool_niche_slice_missing_body(values: &[BoolNicheReading], index: usize) -> bool {
    if index < values.len() {
        if let BoolNicheReading::Flag(flag) = values[index] {
            assert!(bool_niche_selected(values[index]) == flag);
            return unsafe { opaque_bool_niche_slice(values[index]) };
        }
    }
    false
}

#[derive(Clone, Copy)]
pub struct NominalTaggedRecord {
    left: u16,
    right: u16,
}

impl NominalTaggedRecord {
    #[inline(never)]
    fn selected(self) -> u16 {
        self.left
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum NominalTaggedReading {
    Empty,
    Data(NominalTaggedRecord),
}

pub fn nominal_enum_slice(values: &[NominalTaggedReading], index: usize) {
    if index < values.len() {
        if let NominalTaggedReading::Data(record) = values[index] {
            assert!(record.selected() == record.left);
        }
    }
}

pub fn nominal_enum_slice_wrong_claim(values: &[NominalTaggedReading], index: usize) {
    if index < values.len() {
        if let NominalTaggedReading::Data(record) = values[index] {
            assert!(record.left == 0);
        }
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_nominal_enum_slice(value: NominalTaggedReading) -> u16;
}

#[cfg(not(test))]
pub fn nominal_enum_slice_missing_body(values: &[NominalTaggedReading], index: usize) -> u16 {
    if index < values.len() {
        if let NominalTaggedReading::Data(record) = values[index] {
            assert!(record.selected() == record.left);
            return unsafe { opaque_nominal_enum_slice(values[index]) };
        }
    }
    0
}

#[inline(never)]
fn char_niche_selected(value: Option<char>) -> char {
    match value {
        Some(character) => character,
        None => '\0',
    }
}

pub fn char_niche_slice(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(character) = values[index] {
            assert!(char_niche_selected(values[index]) == character);
        }
    }
}

pub fn char_niche_slice_wrong_claim(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(character) = values[index] {
            assert!(character == 'A');
        }
    }
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_char_niche_slice(value: Option<char>) -> char;
}

#[cfg(not(test))]
pub fn char_niche_slice_missing_body(values: &[Option<char>], index: usize) -> char {
    if index < values.len() {
        if let Some(character) = values[index] {
            assert!(char_niche_selected(values[index]) == character);
            return unsafe { opaque_char_niche_slice(values[index]) };
        }
    }
    '\0'
}

pub struct OwnedMovePacket {
    word: u16,
}

#[inline(never)]
fn owned_move_selected(value: OwnedMovePacket) -> u16 {
    value.word
}

pub fn owned_move(word: u16) {
    assert!(owned_move_selected(OwnedMovePacket { word }) == word);
}

pub fn owned_move_wrong_claim(word: u16) {
    assert!(owned_move_selected(OwnedMovePacket { word }) == word.wrapping_add(1));
}

// Unsupported stale-load sequence is analyzer-only and never executed natively.
#[cfg(not(test))]
mod owned_move_analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale(value: OwnedMovePacket) -> u16 {
        mir! {
            let ignored: u16;
            {
                Call(ignored = owned_move_selected(Move(value)),
                    ReturnTo(done), UnwindUnreachable())
            }
            done = {
                RET = value.word;
                Return()
            }
        }
    }
}

#[cfg(not(test))]
pub fn owned_move_stale(word: u16) {
    assert!(owned_move_analyzer_only::stale(OwnedMovePacket { word }) == word);
}

trait UpcastParent {
    fn selected(&self) -> u8;
}

trait UpcastChild: UpcastParent {
    fn child(&self) -> u8;
}

struct UpcastNumber(u8);

impl UpcastParent for UpcastNumber {
    #[inline(never)]
    fn selected(&self) -> u8 {
        self.0 & 15
    }
}

impl UpcastChild for UpcastNumber {
    fn child(&self) -> u8 {
        self.0
    }
}

#[inline(never)]
fn trait_upcast_selected(value: &dyn UpcastChild) -> u8 {
    let parent: &dyn UpcastParent = value;
    parent.selected()
}

pub fn trait_upcast(value: u8) {
    let number = UpcastNumber(value);
    let child: &dyn UpcastChild = &number;
    assert!(child.child() == value);
    assert!(trait_upcast_selected(child) < 16);
}

pub fn trait_upcast_wrong_claim(value: u8) {
    let number = UpcastNumber(value);
    let child: &dyn UpcastChild = &number;
    assert!(trait_upcast_selected(child) == 0);
}

#[cfg(not(test))]
unsafe extern "Rust" {
    fn opaque_trait_upcast(value: u8) -> u8;
}

#[cfg(not(test))]
pub fn trait_upcast_missing_body(value: u8) -> u8 {
    let number = UpcastNumber(value);
    let child: &dyn UpcastChild = &number;
    let selected = trait_upcast_selected(child);
    assert!(selected < 16);
    unsafe { opaque_trait_upcast(selected) }
}

#[cfg(test)]
mod native {
    #[test]
    fn nominal_enum_slice_controls() {
        let data = NominalTaggedReading::Data(NominalTaggedRecord { left: 3, right: 7 });
        for index in [0, 1, 128, 129, usize::MAX] {
            nominal_enum_slice(&[data; 129], index);
        }
        nominal_enum_slice(&[NominalTaggedReading::Empty], 0);
    }

    #[test]
    #[should_panic]
    fn nominal_enum_slice_wrong_claim_panics() {
        nominal_enum_slice_wrong_claim(&[
            NominalTaggedReading::Data(NominalTaggedRecord { left: 3, right: 7 }),
        ], 0);
    }

    #[test]
    fn owned_move_controls() {
        for word in [0, 1, 19, u16::MAX] {
            owned_move(word);
        }
    }

    #[test]
    #[should_panic]
    fn owned_move_wrong_claim_panics() {
        owned_move_wrong_claim(19);
    }

    #[test]
    fn trait_upcast_controls() {
        for value in [0, 1, 19, 255] {
            trait_upcast(value);
        }
    }

    #[test]
    #[should_panic]
    fn trait_upcast_wrong_claim_panics() {
        trait_upcast_wrong_claim(19);
    }

    #[test]
    fn char_niche_slice_controls() {
        for index in [0, 1, 128, 129, usize::MAX] {
            char_niche_slice(&[Some('A'); 129], index);
        }
        for character in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            char_niche_slice(&[None, Some(character)], 0);
            char_niche_slice(&[None, Some(character)], 1);
        }
    }

    #[test]
    #[should_panic]
    fn char_niche_slice_wrong_claim_panics() {
        char_niche_slice_wrong_claim(&[Some('B')], 0);
    }

    #[test]
    fn bool_niche_slice_controls() {
        for index in [0, 1, 128, 129, usize::MAX] {
            bool_niche_slice(&[BoolNicheReading::Flag(true); 129], index);
        }
        bool_niche_slice(&[BoolNicheReading::Empty, BoolNicheReading::Flag(false)], 0);
        bool_niche_slice(&[BoolNicheReading::Empty, BoolNicheReading::Flag(false)], 1);
    }

    #[test]
    #[should_panic]
    fn bool_niche_slice_wrong_claim_panics() {
        bool_niche_slice_wrong_claim(&[BoolNicheReading::Flag(true)], 0);
    }

    #[test]
    fn tagged_sum_slice_controls() {
        for index in [0, 1, 128, 129, usize::MAX] {
            tagged_sum_slice(&[TaggedReading::Pair(3, 7); 129], index);
        }
        tagged_sum_slice(&[TaggedReading::Empty], 0);
    }

    #[test]
    #[should_panic]
    fn tagged_sum_slice_wrong_claim_panics() {
        tagged_sum_slice_wrong_claim(&[TaggedReading::Pair(3, 7)], 0);
    }

    #[test]
    fn full_composite_predicate_controls() {
        for index in [0, 1, 128, 129, usize::MAX] {
            full_composite_predicates(&[(3, [5, 7]); 129], index);
        }
    }

    #[test]
    #[should_panic]
    fn full_composite_predicates_wrong_claim_panics() {
        full_composite_predicates_wrong_claim(&[(3, [5, 7]); 129], 128);
    }

    #[test]
    fn tracked_call_destination_controls() {
        for (left, right) in [(3, 7), (0, u16::MAX), (19, 19)] {
            tracked_call_destination(left, right);
        }
    }

    #[test]
    #[should_panic]
    fn tracked_call_destination_wrong_claim_panics() {
        tracked_call_destination_wrong_claim(3, 7);
    }

    #[test]
    fn owned_call_destination_controls() {
        for index in [0, 1, 2, usize::MAX] {
            owned_call_destination(([3, 7], 11), index);
        }
    }
    #[test]
    #[should_panic]
    fn owned_call_destination_wrong_claim_panics() {
        owned_call_destination_wrong_claim(([3, 7], 11), 0);
    }

    use super::*;
    use core::task::Waker;

    #[test]
    fn positives() {
        integers(199);
        let records = [ReservedRecord { left: 3, right: 7 }; 64];
        for index in [0, 63, 64, usize::MAX] {
            registered_product_choice(records, records, records, index);
            owned_array_field_write(records, records, records, index, u16::MAX);
            owned_array_fixed_write([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], index, 0);
            owned_array_fixed_selected_write([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], index, 0);
        }
        for index in [0, 63, 64, usize::MAX] {
            registered_pure_array_read([(3, [5, 7]); 64], [(11, [13, 17]); 64],
                [(19, [23, 29]); 64], index);
        }
        for outer in [0, 63, 64, usize::MAX] {
            for inner in [0, 1, 2, usize::MAX] {
                owned_array_dynamic_write([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64],
                    outer, inner, u16::MAX);
            }
        }
        for index in [0, 63, 64, usize::MAX] {
            retained_owned_array_read([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], index);
        }
        for inner in [0, 1, 2, usize::MAX] {
            known_owned_array_write([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64],
                inner, u16::MAX);
        }
        let product = OwnedArrayProduct { rows: records, ready: true };
        for index in [0, 63, 64, usize::MAX] {
            owned_product_array_write(product, product, product, index, u16::MAX);
            retained_owned_field_read(product, product, product, index);
        }
        safe_sized_alignment(SizedLayoutZero);
        deferred_zero_owned_write([DeferredZero; 2], 0);
        deferred_zero_owned_write([DeferredZero; 2], 1);
        deferred_zero_owned_write([DeferredZero; 2], usize::MAX);
        owned_array_whole_write(0, 0);
        owned_array_whole_write(1, u32::MAX);
        owned_array_whole_write(usize::MAX, 7);
        typed_byte_array_choice(0);
        typed_byte_array_choice(1);
        typed_byte_array_choice(usize::MAX);
        typed_struct_array_choice(0);
        typed_struct_array_choice(1);
        typed_struct_array_choice(usize::MAX);
        local_zero_struct_cursor(&[], usize::MAX);
        local_zero_struct_cursor(&[NominalZero; 129], 128);
        local_zero_struct_cursor(&[NominalZero; usize::MAX], usize::MAX - 1);
        local_struct_slice_read(&[], usize::MAX);
        local_struct_slice_read(&[SliceSample { left: 3, right: 7 }; 129], 128);
        slice_dynamic_alignment(&[]);
        slice_dynamic_alignment(&[(3, 7); 129]);
        composite_slice_byte_size(&[]);
        composite_slice_byte_size(&[(3, 7); 129]);
        zero_sized_slice_cursor(&[], usize::MAX);
        zero_sized_slice_cursor(&[(); 129], 128);
        zero_sized_slice_cursor(&[(); 129], usize::MAX);
        composite_iterator_nth(&[], usize::MAX);
        composite_iterator_nth(&[(3, 7), (11, 13)], 1);
        composite_iterator_nth(&[(3, 7); 129], 128);
        nested_array_choice(0);
        nested_array_choice(1);
        nested_array_choice(usize::MAX);
        composite_slice_views(&[], usize::MAX);
        composite_slice_views(&[(3, [5, 7]), (11, [13, 17])], 1);
        composite_slice_views(&[(3, [5, 7]); 129], 128);
        scalar_slice_full_member(&[], usize::MAX);
        scalar_slice_full_member(&[3, 7], 1);
        scalar_slice_full_member(&[7; 129], 128);
        scalar_slice_full_member(&[7; 257], 256);
        scalar_slice_capture(&[], usize::MAX);
        scalar_slice_capture(&[0, 1, u16::MAX], 2);
        scalar_slice_capture(&[u16::MAX; 129], 128);
        bounded_scalar_contains(&[]);
        bounded_scalar_contains(&[0, u16::MAX]);
        bounded_scalar_contains(&[3, 7, 11, 13]);
        bounded_scalar_contains(&[7; 129]);
        open_slice_read_correlation(&[], 0);
        open_slice_read_correlation(&[0, 1, u16::MAX], 2);
        open_slice_read_correlation(&[u16::MAX; 129], 128);
        scalar_slice_nth(&[], 0);
        scalar_slice_nth(&[0, 1, u16::MAX], 2);
        scalar_slice_nth(&[u16::MAX; 129], 128);
        scalar_slice_nth(&[7; 129], usize::MAX);
        assert!(scalar_slice_unbounded_fold(&[3, 7]) == 10);
        float_remainder(false);
        float_remainder(true);
        raw_pointer_metadata(usize::MAX);
        maybe_uninit_round_trip(0, false);
        maybe_uninit_round_trip(u32::MAX, true);
        maybe_uninit_array([0, 1, u16::MAX]);
        maybe_uninit_array([u16::MAX, 0, 7]);
        for value in ['\0', 'A', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            maybe_uninit_char(value);
        }
        for value in [
            0,
            0x41,
            0xd7ff,
            0xd800,
            0xdfff,
            0xe000,
            0x10ffff,
            0x110000,
            u32::MAX,
        ] {
            checked_char(value);
        }
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
    fn scalar_contains_negative_control() {
        bounded_scalar_contains_wrong_claim(&[3, 7]);
    }

    #[test]
    #[should_panic]
    fn full_scalar_contains_negative_control() {
        scalar_slice_full_wrong_claim(&[7; 129]);
    }

    #[test]
    #[should_panic]
    fn negative_control() {
        reference_wrong_claim();
    }
    #[test]
    #[should_panic]
    fn composite_slice_wrong_field_panics() {
        composite_slice_wrong_field(&[(3, [5, 7]); 129]);
    }

    #[test]
    #[should_panic]
    fn open_aggregate_slice_panics() {
        open_aggregate_slice(&[(1, 0)]);
    }
    #[test]
    #[should_panic]
    fn nested_array_choice_wrong_claim_panics() {
        nested_array_choice_wrong_claim(0);
    }
    #[test]
    #[should_panic]
    fn composite_iterator_wrong_claim_panics() {
        composite_iterator_wrong_claim(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn zero_sized_slice_wrong_claim_panics() {
        zero_sized_slice_wrong_claim(&[(); 129]);
    }
    #[test]
    #[should_panic]
    fn composite_slice_byte_size_wrong_claim_panics() {
        composite_slice_byte_size_wrong_claim(&[(3, 7); 129]);
    }
    #[test]
    #[should_panic]
    fn slice_dynamic_alignment_wrong_claim_panics() {
        slice_dynamic_alignment_wrong_claim(&[[0; 0]; 129]);
    }
    #[test]
    #[should_panic]
    fn local_struct_slice_wrong_claim_panics() {
        local_struct_slice_wrong_claim(&[SliceSample { left: 3, right: 7 }; 129]);
    }
    #[test]
    #[should_panic]
    fn local_zero_struct_wrong_claim_panics() {
        local_zero_struct_wrong_claim(&[NominalZero; usize::MAX]);
    }
    #[test]
    #[should_panic]
    fn typed_struct_array_wrong_claim_panics() {
        typed_struct_array_wrong_claim(1);
    }
    #[test]
    #[should_panic]
    fn typed_byte_array_wrong_claim_panics() {
        typed_byte_array_wrong_claim(1);
    }
    #[test]
    #[should_panic]
    fn owned_array_whole_wrong_claim_panics() {
        owned_array_whole_wrong_claim(1, u32::MAX);
    }
    #[test]
    #[should_panic]
    fn deferred_zero_owned_wrong_claim_panics() {
        deferred_zero_owned_wrong_claim([DeferredZero; 2], 1);
    }
    #[test]
    #[should_panic]
    fn safe_sized_alignment_wrong_claim_panics() {
        safe_sized_alignment_wrong_claim(SizedLayoutZero);
    }

    #[test]
    #[should_panic]
    fn registered_product_wrong_claim_panics() {
        let first = [ReservedRecord { left: 3, right: 7 }; 64];
        let second = [ReservedRecord { left: 5, right: 11 }; 64];
        registered_product_wrong_claim(first, second, first, 63);
    }
    #[test]
    #[should_panic]
    fn retained_owned_field_wrong_claim_panics() {
        let first = OwnedArrayProduct {
            rows: [ReservedRecord { left: 3, right: 7 }; 64], ready: true,
        };
        let second = OwnedArrayProduct {
            rows: [ReservedRecord { left: 5, right: 11 }; 64], ready: false,
        };
        retained_owned_field_wrong_claim(first, second, first, 63);
    }
    #[test]
    #[should_panic]
    fn owned_product_array_wrong_claim_panics() {
        let product = OwnedArrayProduct {
            rows: [ReservedRecord { left: 3, right: 7 }; 64], ready: true,
        };
        owned_product_array_wrong_claim(product, product, product, 63, 19);
    }
    #[test]
    #[should_panic]
    fn known_owned_array_wrong_claim_panics() {
        known_owned_array_wrong_claim([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], 1, 19);
    }
    #[test]
    #[should_panic]
    fn retained_owned_array_wrong_claim_panics() {
        retained_owned_array_wrong_claim([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], 63);
    }
    #[test]
    #[should_panic]
    fn owned_array_dynamic_wrong_claim_panics() {
        owned_array_dynamic_wrong_claim([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], 63, 1, 0);
    }
    #[test]
    #[should_panic]
    fn registered_pure_array_wrong_claim_panics() {
        registered_pure_array_wrong_claim([(3, [5, 7]); 64], [(11, [13, 17]); 64],
            [(19, [23, 29]); 64], 63);
    }
    #[test]
    #[should_panic]
    fn owned_array_fixed_wrong_claim_panics() {
        owned_array_fixed_wrong_claim([[3, 7]; 64], [[5, 11]; 64], [[13, 17]; 64], 63, 0);
    }
    #[test]
    #[should_panic]
    fn owned_array_field_wrong_claim_panics() {
        let records = [ReservedRecord { left: 3, right: 7 }; 64];
        owned_array_field_wrong_claim(records, records, records, 63, 0);
    }
}


#[inline(never)]
fn nominal_struct_selected_needle(values: &[SliceSample], index: usize) -> SliceSample {
    let mut selected = values[index];
    selected.right = selected.right.wrapping_add(0);
    selected
}

pub fn nominal_struct_predicates(values: &[SliceSample], index: usize) {
    if index < values.len() {
        let needle = nominal_struct_selected_needle(values, index);
        assert!(values.contains(&needle));
    }
}

pub fn nominal_struct_wrong_claim(values: &[SliceSample], index: usize) {
    if index < values.len() {
        let needle = nominal_struct_selected_needle(values, index);
        assert!(!values.contains(&needle));
    }
}

#[derive(Clone, Copy)]
pub struct NonstructuralComparison {
    pub left: u16,
    pub right: u16,
}

impl PartialEq for NonstructuralComparison {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left
    }
}

pub fn nominal_struct_comparator_unknown(
    values: &[NonstructuralComparison],
    needle: NonstructuralComparison,
) -> bool {
    values.contains(&needle)
}

#[cfg(test)]
mod native_nominal_struct_predicates {
    use super::*;

    #[test]
    fn selected_struct_body_preserves_member() {
        nominal_struct_predicates(&[SliceSample { left: 3, right: 7 }; 129], 128);
    }

    #[test]
    #[should_panic]
    fn false_struct_member_claim_panics() {
        nominal_struct_wrong_claim(&[SliceSample { left: 3, right: 7 }; 129], 128);
    }
}


extern crate alloc;

#[inline(never)]
fn zst_box_selected(value: alloc::boxed::Box<()>) -> u16 {
    let borrowed: &() = &value;
    let () = *borrowed;
    core::mem::drop(value);
    19
}

pub fn zst_box() {
    assert!(zst_box_selected(alloc::boxed::Box::new(())) == 19);
}

pub fn zst_box_wrong_claim() {
    assert!(zst_box_selected(alloc::boxed::Box::new(())) == 20);
}

pub fn nonzero_box_unknown(word: u16) {
    let value = alloc::boxed::Box::new(word);
    assert!(*value == word);
}

#[cfg(test)]
mod native_zst_boxes {
    use super::*;

    #[test]
    fn zst_owner_executes_selected_body() {
        zst_box();
    }

    #[test]
    #[should_panic]
    fn zst_false_claim_panics() {
        zst_box_wrong_claim();
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct ComparedArrayRecord {
    words: [u16; 2],
    marker: bool,
}

#[inline(never)]
fn nominal_array_selected(values: &[ComparedArrayRecord], index: usize) -> ComparedArrayRecord {
    let mut selected = values[index];
    selected.words[1] = selected.words[1].wrapping_add(0);
    selected
}

pub fn nominal_array_predicates(values: &[ComparedArrayRecord], index: usize) {
    if index < values.len() {
        assert!(values.contains(&nominal_array_selected(values, index)));
    }
}

pub fn nominal_array_wrong_claim(values: &[ComparedArrayRecord], index: usize) {
    if index < values.len() {
        assert!(!values.contains(&nominal_array_selected(values, index)));
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct ComparedFloatArray {
    values: [f32; 2],
}

pub fn nominal_float_array_unknown(values: &[ComparedFloatArray]) -> bool {
    values == values
}

#[cfg(test)]
mod native_nominal_array_predicates {
    use super::*;

    #[test]
    fn selected_array_body_preserves_member() {
        let value = ComparedArrayRecord { words: [3, 7], marker: true };
        nominal_array_predicates(&[value; 129], 128);
    }

    #[test]
    #[should_panic]
    fn array_false_claim_panics() {
        let value = ComparedArrayRecord { words: [3, 7], marker: true };
        nominal_array_wrong_claim(&[value; 129], 128);
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct ComparedPrimitiveArrays {
    flags: [bool; 2],
    characters: [char; 2],
    numbers: [f32; 2],
}

#[inline(never)]
fn primitive_array_selected(
    values: &[ComparedPrimitiveArrays],
    index: usize,
) -> ComparedPrimitiveArrays {
    let mut selected = values[index];
    selected.flags[0] ^= false;
    selected
}

pub fn nominal_primitive_array_predicates(values: &[ComparedPrimitiveArrays], index: usize) {
    if index < values.len()
        && !values[index].numbers[0].is_nan()
        && !values[index].numbers[1].is_nan()
    {
        assert!(values.contains(&primitive_array_selected(values, index)));
    }
}

pub fn nominal_primitive_array_wrong_claim(values: &[ComparedPrimitiveArrays], index: usize) {
    if index < values.len()
        && !values[index].numbers[0].is_nan()
        && !values[index].numbers[1].is_nan()
    {
        assert!(!values.contains(&primitive_array_selected(values, index)));
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct ComparedReferenceArray<'a> {
    references: [&'a u16; 0],
}

pub fn nominal_reference_array_unknown(values: &[ComparedReferenceArray<'_>]) -> bool {
    values == values
}

#[cfg(test)]
mod native_primitive_array_predicates {
    use super::*;

    fn values() -> [ComparedPrimitiveArrays; 129] {
        [ComparedPrimitiveArrays {
            flags: [true, false],
            characters: ['A', '\u{10FFFF}'],
            numbers: [0.0, -0.0],
        }; 129]
    }

    #[test]
    fn selected_primitive_body_preserves_member() {
        nominal_primitive_array_predicates(&values(), 128);
    }

    #[test]
    #[should_panic]
    fn false_primitive_claim_panics() {
        nominal_primitive_array_wrong_claim(&values(), 128);
    }
}

#[inline(never)]
pub fn mutable_u16_replacement(word: u16) -> u16 {
    word ^ 0
}

pub fn mutable_u16_store(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = mutable_u16_replacement(word);
        assert!(values[index] == word);
    }
}

pub fn mutable_u16_wrong_claim(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = mutable_u16_replacement(word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn mutable_u16_child(values: &mut [u16], index: usize, word: u16) {
    values[index] = word;
}

pub fn mutable_u16_child_unknown(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        mutable_u16_child(values, index, word);
        assert!(values[index] == word);
    }
}

#[cfg(test)]
mod native_mutable_u16_store {
    use super::*;

    #[test]
    fn replacement_body_preserves_word() {
        let mut values = [0_u16; 129];
        mutable_u16_store(&mut values, 128, u16::MAX);
        assert_eq!(values[128], u16::MAX);
    }
}

#[derive(Clone, Copy)]
pub struct NominalBoxMarker;

#[inline(never)]
pub fn nominal_box_marker_tag(_marker: &NominalBoxMarker) -> u8 {
    17
}

pub fn nominal_zst_box() {
    let marker = alloc::boxed::Box::new(NominalBoxMarker);
    assert!(nominal_box_marker_tag(&marker) == 17);
}

pub fn nominal_zst_box_wrong_claim() {
    let marker = alloc::boxed::Box::new(NominalBoxMarker);
    assert!(nominal_box_marker_tag(&marker) != 17);
}

#[derive(Clone, Copy)]
#[repr(align(8))]
pub struct NominalAlignedBoxMarker;

pub fn nominal_aligned_box_unknown() {
    let _marker = alloc::boxed::Box::new(NominalAlignedBoxMarker);
}

#[cfg(test)]
mod native_nominal_zst_box {
    use super::*;

    #[test]
    fn selected_tag_body_preserves_claim() {
        nominal_zst_box();
    }
}

#[inline(never)]
pub fn scoped_mutable_child_word(word: u16) -> u16 {
    word ^ 0
}

#[inline(never)]
pub fn scoped_mutable_child(values: &mut [u16], index: usize, word: u16) {
    values[index] = scoped_mutable_child_word(word);
}

pub fn scoped_mutable_child_call(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        scoped_mutable_child(values, index, word);
        assert!(values[index] == word);
    }
}

pub fn scoped_mutable_child_wrong_claim(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        scoped_mutable_child(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn scoped_mutable_nested(values: &mut [u16], index: usize, word: u16) {
    scoped_mutable_child(values, index, word);
}

pub fn scoped_mutable_nested_unknown(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        scoped_mutable_nested(values, index, word);
        assert!(values[index] == word);
    }
}

#[cfg(test)]
mod native_scoped_mutable_child {
    use super::*;

    #[test]
    fn scalar_child_body_preserves_word() {
        let mut values = [0_u16; 129];
        scoped_mutable_child_call(&mut values, 128, u16::MAX);
        assert_eq!(values[128], u16::MAX);
    }
}

#[repr(align(4096))]
#[derive(Clone, Copy)]
pub struct AlignedZeroBoxMarker;

impl AlignedZeroBoxMarker {
    #[inline(never)]
    pub fn tag(&self) -> u16 {
        17
    }
}

#[inline(never)]
pub fn aligned_zero_box_selected(owner: alloc::boxed::Box<AlignedZeroBoxMarker>) -> u16 {
    let tag = owner.tag();
    core::mem::drop(owner);
    tag
}

pub fn aligned_zero_box() {
    assert!(aligned_zero_box_selected(alloc::boxed::Box::new(AlignedZeroBoxMarker)) == 17);
}

pub fn aligned_zero_box_wrong_claim() {
    assert!(aligned_zero_box_selected(alloc::boxed::Box::new(AlignedZeroBoxMarker)) == 18);
}

#[repr(align(4096))]
pub struct AlignedZeroBoxDrop;

impl Drop for AlignedZeroBoxDrop {
    fn drop(&mut self) {}
}

pub fn aligned_zero_box_drop_unknown() {
    let _owner = alloc::boxed::Box::new(AlignedZeroBoxDrop);
}

#[cfg(test)]
mod native_aligned_zero_box {
    use super::*;

    #[test]
    fn selected_tag_body_preserves_claim() {
        aligned_zero_box();
    }
}

#[inline(never)]
pub fn integer_slice_child_word(word: i32) -> i32 {
    word ^ 0
}

#[inline(never)]
pub fn integer_slice_child(values: &mut [i32], index: usize, word: i32) {
    values[index] = integer_slice_child_word(word);
}

pub fn integer_slice_child_call(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        integer_slice_child(values, index, word);
        assert!(values[index] == word);
    }
}

pub fn integer_slice_child_wrong_claim(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        integer_slice_child(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn integer_slice_nested(values: &mut [i32], index: usize, word: i32) {
    integer_slice_child(values, index, word);
}

pub fn integer_slice_nested_unknown(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        integer_slice_nested(values, index, word);
        assert!(values[index] == word);
    }
}

#[cfg(test)]
mod native_integer_slice_child {
    use super::*;

    #[test]
    fn signed_scalar_body_preserves_word() {
        let mut values = [0_i32; 129];
        integer_slice_child_call(&mut values, 128, i32::MIN);
        assert_eq!(values[128], i32::MIN);
    }
}


#[inline(never)]
pub fn bool_slice_child_value(value: bool) -> bool {
    !value
}

#[inline(never)]
pub fn bool_slice_child(values: &mut [bool], index: usize, value: bool) {
    values[index] = bool_slice_child_value(value);
}

pub fn bool_slice_child_call(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        bool_slice_child(values, index, value);
        assert!(values[index] == !value);
    }
}

pub fn bool_slice_child_wrong_claim(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        bool_slice_child(values, index, value);
        assert!(values[index] == value);
    }
}

#[inline(never)]
pub fn bool_slice_nested(values: &mut [bool], index: usize, value: bool) {
    bool_slice_child(values, index, value);
}

pub fn bool_slice_nested_unknown(values: &mut [bool], index: usize, value: bool) {
    if index < values.len() {
        bool_slice_nested(values, index, value);
        assert!(values[index] == !value);
    }
}

#[cfg(test)]
mod native_bool_slice_child {
    #[test]
    fn boolean_scalar_body_preserves_negation() {
        for value in [false, true] {
            let mut values = [value; 129];
            super::bool_slice_child_call(&mut values, 128, value);
            assert_eq!(values[128], !value);
        }
    }
}


#[inline(never)]
pub fn char_slice_child_value(value: char) -> char {
    if value == 'A' { 'B' } else { 'A' }
}

#[inline(never)]
pub fn char_slice_child(values: &mut [char], index: usize, value: char) {
    values[index] = char_slice_child_value(value);
}

pub fn char_slice_child_call(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        char_slice_child(values, index, value);
        assert!(values[index] == if value == 'A' { 'B' } else { 'A' });
    }
}

pub fn char_slice_child_wrong_claim(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        char_slice_child(values, index, value);
        assert!(values[index] == value);
    }
}

#[inline(never)]
pub fn char_slice_nested(values: &mut [char], index: usize, value: char) {
    char_slice_child(values, index, value);
}

pub fn char_slice_nested_unknown(values: &mut [char], index: usize, value: char) {
    if index < values.len() {
        char_slice_nested(values, index, value);
        assert!(values[index] == if value == 'A' { 'B' } else { 'A' });
    }
}

#[cfg(test)]
mod native_char_slice_child {
    #[test]
    fn character_scalar_body_preserves_replacement() {
        for value in ['A', 'B', '\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            let mut values = [value; 129];
            super::char_slice_child_call(&mut values, 128, value);
            assert_eq!(values[128], if value == 'A' { 'B' } else { 'A' });
        }
    }
}


pub fn fixed_byte_prefix_copy(values: &mut [u8]) {
    if values.len() >= 2 {
        values[..2].copy_from_slice(&[17, 19]);
        assert!(values[0] == 17 && values[1] == 19);
    }
}

pub fn fixed_byte_prefix_wrong_claim(values: &mut [u8]) {
    if values.len() >= 2 {
        values[..2].copy_from_slice(&[17, 19]);
        assert!(values[0] == 17 && values[1] == 17);
    }
}

#[inline(never)]
pub fn fixed_byte_prefix_source() -> [u8; 2] {
    [17, 19]
}

pub fn fixed_byte_prefix_dynamic_unknown(values: &mut [u8]) {
    if values.len() >= 2 {
        let source = fixed_byte_prefix_source();
        values[..2].copy_from_slice(&source);
        assert!(values[0] == 17 && values[1] == 19);
    }
}

#[cfg(test)]
mod native_fixed_byte_prefix {
    #[test]
    fn copied_constant_payload_preserves_prefix_and_tail() {
        let mut values = [0xa5; 129];
        super::fixed_byte_prefix_copy(&mut values);
        assert_eq!(&values[..2], &[17, 19]);
        assert!(values[2..].iter().all(|value| *value == 0xa5));
        super::fixed_byte_prefix_copy(&mut []);
    }
}


#[inline(never)]
pub fn float_slice_child_value(value: f32) -> f32 {
    value + 0.0
}

#[inline(never)]
pub fn float_slice_child(values: &mut [f32], index: usize, value: f32) {
    values[index] = float_slice_child_value(value);
}

pub fn float_slice_child_call(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() && value >= -100.0 && value <= 100.0 {
        float_slice_child(values, index, value);
        assert!(values[index] == value);
    }
}

pub fn float_slice_child_wrong_claim(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() && value >= -100.0 && value <= 100.0 {
        float_slice_child(values, index, value);
        assert!(values[index] != value);
    }
}

#[inline(never)]
pub fn float_slice_nested(values: &mut [f32], index: usize, value: f32) {
    float_slice_child(values, index, value);
}

pub fn float_slice_nested_unknown(values: &mut [f32], index: usize, value: f32) {
    if index < values.len() && value >= -100.0 && value <= 100.0 {
        float_slice_nested(values, index, value);
        assert!(values[index] == value);
    }
}

#[cfg(test)]
mod native_float_slice_child {
    #[test]
    fn finite_float_arithmetic_preserves_numeric_value() {
        for value in [-100.0_f32, -1.0, -0.0, 0.0, 1.0, 100.0] {
            let mut values = [-7.0; 129];
            super::float_slice_child_call(&mut values, 128, value);
            assert_eq!(values[128], value);
        }
    }
}


#[inline(never)]
pub fn checked_subslice_child(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = word ^ 0;
    }
}

pub fn checked_subslice_child_call(
    values: &mut [u16], start: usize, end: usize, index: usize, word: u16,
) {
    if start <= end && end <= values.len() && index < end - start {
        checked_subslice_child(&mut values[start..end], index, word);
        assert!(values[start + index] == word);
    }
}

pub fn checked_subslice_wrong_claim(
    values: &mut [u16], start: usize, end: usize, index: usize, word: u16,
) {
    if start <= end && end <= values.len() && index < end - start {
        checked_subslice_child(&mut values[start..end], index, word);
        assert!(values[start + index] != word);
    }
}

#[inline(never)]
pub fn checked_subslice_nested(values: &mut [u16]) {
    checked_subslice_child(values, 0, 19);
}

pub fn checked_subslice_nested_unknown(values: &mut [u16], start: usize, end: usize) {
    if start <= end && end <= values.len() {
        checked_subslice_nested(&mut values[start..end]);
    }
}

#[cfg(test)]
mod native_checked_subslice {
    #[test]
    fn translated_child_write_preserves_root_and_tail() {
        let mut values = [7; 129];
        super::checked_subslice_child_call(&mut values, 1, 128, 126, 19);
        assert_eq!(values[127], 19);
        assert_eq!(values[0], 7);
        assert_eq!(values[128], 7);
        super::checked_subslice_child_call(&mut values, 129, 129, 0, 31);
        assert_eq!(values[128], 7);
    }
}


#[inline(never)]
pub fn known_table_first(word: u16) -> u16 { word }

#[inline(never)]
pub fn known_table_second(word: u16) -> u16 { word ^ 1 }

pub fn known_function_table(index: usize, word: u16) {
    let table: [fn(u16) -> u16; 2] = [known_table_first, known_table_second];
    if index < 2 {
        assert!(table[index](word) == if index == 0 { word } else { word ^ 1 });
    }
}

pub fn known_function_table_wrong(index: usize, word: u16) {
    let table: [fn(u16) -> u16; 2] = [known_table_first, known_table_second];
    if index < 2 { assert!(table[index](word) == word); }
}

pub fn known_function_table_opaque(index: usize, word: u16, callback: fn(u16) -> u16) {
    let table: [fn(u16) -> u16; 2] = [known_table_first, callback];
    if index < 2 { assert!(table[index](word) == word); }
}

#[cfg(test)]
mod native_known_function_table {
    #[test]
    fn target_body_and_order_match_original_assertion() {
        super::known_function_table(0, 129);
        super::known_function_table(1, 129);
        super::known_function_table(2, 129);
    }
}

#[inline(never)]
pub fn integer_table_first(word: isize) -> isize { word }

#[inline(never)]
pub fn integer_table_second(word: isize) -> isize { word.wrapping_add(1) }

pub fn integer_function_table(index: usize, word: isize) {
    let table: [fn(isize) -> isize; 2] = [integer_table_first, integer_table_second];
    if index < 2 {
        assert!(table[index](word) == if index == 0 { word } else { word.wrapping_add(1) });
    }
}

pub fn integer_function_table_wrong(index: usize, word: isize) {
    let table: [fn(isize) -> isize; 2] = [integer_table_first, integer_table_second];
    if index < 2 { assert!(table[index](word) == word); }
}

#[inline(never)]
pub fn integer_table_converted_first(word: isize) -> usize { word as usize }

#[inline(never)]
pub fn integer_table_converted_second(word: isize) -> usize { word as usize ^ 1 }

pub fn integer_function_table_signature_unknown(index: usize, word: isize) {
    let table: [fn(isize) -> usize; 2] =
        [integer_table_converted_first, integer_table_converted_second];
    if index < 2 { assert!(table[index](word) == word as usize); }
}

#[cfg(test)]
mod native_integer_function_table {
    #[test]
    fn original_target_body_matches_at_target_width_boundaries() {
        for word in [isize::MIN, isize::MAX, 0, 1] {
            for index in 0..3 { super::integer_function_table(index, word); }
        }
    }
}


#[inline(never)]
pub fn nested_whole_word(word: u16) -> u16 { word ^ 0 }

#[inline(never)]
pub fn nested_whole_leaf(values: &mut [u16], index: usize, word: u16) {
    values[index] = nested_whole_word(word);
}

#[inline(never)]
pub fn nested_whole_outer(values: &mut [u16], index: usize, word: u16) {
    nested_whole_leaf(values, index, word);
}

pub fn nested_whole_child_call(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        nested_whole_outer(values, index, word);
        assert!(values[index] == word);
    }
}

pub fn nested_whole_wrong_claim(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        nested_whole_outer(values, index, word);
        assert!(values[index] != word);
    }
}

#[inline(never)]
pub fn nested_whole_extra_parent(values: &mut [u16], index: usize, word: u16) {
    nested_whole_outer(values, index, word);
}

pub fn nested_whole_deeper_unknown(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() { nested_whole_extra_parent(values, index, word); }
}

#[cfg(test)]
mod native_nested_whole_u16 {
    #[test]
    fn valid_nested_child_preserves_current_data_and_tail() {
        for size in 0..=128 {
            let mut values = alloc::vec![7_u16; size];
            if size > 0 {
                super::nested_whole_child_call(&mut values, size - 1, 19);
                assert_eq!(values[size - 1], 19);
                assert!(values[..size - 1].iter().all(|word| *word == 7));
            }
            super::nested_whole_child_call(&mut values, size, 31);
        }
    }

    #[test]
    fn nested_data_mutation_guard() {
        let mut values = [7; 129];
        super::nested_whole_child_call(&mut values, 128, 19);
        assert_eq!(values[128], 19);
        assert_eq!(values[0], 7);
    }
}


#[inline(never)]
pub fn nonzero_niche_selected_value(value: Option<core::num::NonZeroU16>) -> u16 {
    match value {
        None => 0,
        Some(value) => value.get(),
    }
}

pub fn readonly_nonzero_niche_selected(values: &[Option<core::num::NonZeroU16>], index: usize) {
    if index < values.len() {
        let value = values[index];
        match value {
            None => assert!(nonzero_niche_selected_value(value) == 0),
            Some(word) => assert!(nonzero_niche_selected_value(value) == word.get()),
        }
    }
}

pub fn readonly_nonzero_niche_wrong_claim(values: &[Option<core::num::NonZeroU16>], index: usize) {
    if index < values.len() {
        if let Some(word) = values[index] {
            assert!(nonzero_niche_selected_value(Some(word)) == 0);
        }
    }
}

pub fn readonly_nonzero_niche_contains_unknown(
    values: &[Option<core::num::NonZeroU16>],
    needle: Option<core::num::NonZeroU16>,
) {
    let _ = values.contains(&needle);
}

#[cfg(test)]
mod native_readonly_nonzero_niche {
    #[test]
    fn selected_nonzero_values_keep_actual_getter() {
        let mut values = [None; 129];
        for (index, value) in values.iter_mut().enumerate() {
            if index % 3 != 0 {
                *value = core::num::NonZeroU16::new(index as u16 + 1);
            }
        }
        values[128] = core::num::NonZeroU16::new(u16::MAX);
        for index in 0..values.len() {
            super::readonly_nonzero_niche_selected(&values, index);
        }
    }
}
#[inline(never)]
pub fn integer_pair_narrow_first(word: i128) -> u8 {
    word as u8
}

#[inline(never)]
pub fn integer_pair_narrow_second(word: i128) -> u8 {
    (word ^ 1) as u8
}

pub fn integer_function_table_pair(index: usize, word: i128) {
    let table: [fn(i128) -> u8; 2] = [integer_pair_narrow_first, integer_pair_narrow_second];
    if index < 2 {
        let actual = table[index](word);
        let expected = if index == 0 {
            word as u8
        } else {
            (word ^ 1) as u8
        };
        assert!(actual == expected);
    }
}

pub fn integer_function_table_pair_wrong(index: usize, word: i128) {
    let table: [fn(i128) -> u8; 2] = [integer_pair_narrow_first, integer_pair_narrow_second];
    if index < 2 {
        assert!(table[index](word) == word as u8);
    }
}

pub fn integer_function_table_pair_opaque(index: usize, word: i128, other: fn(i128) -> u8) {
    let table: [fn(i128) -> u8; 2] = [integer_pair_narrow_first, other];
    if index < 2 {
        assert!(table[index](word) == word as u8);
    }
}


#[inline(never)]
pub fn nested_integer_word(word: i32) -> i32 {
    word ^ 0
}

#[inline(never)]
pub fn nested_integer_leaf(values: &mut [i32], word: i32) {
    if values.len() > 0 {
        values[0] = nested_integer_word(word);
    }
}

#[inline(never)]
pub fn nested_integer_outer(values: &mut [i32], word: i32) {
    nested_integer_leaf(&mut *(&mut *values), word);
}

#[inline(never)]
pub fn nested_integer_deeper(values: &mut [i32], word: i32) {
    nested_integer_outer(values, word);
}

pub fn nested_integer_child_call(values: &mut [i32], word: i32) {
    if values.len() > 1 {
        let sibling = values[1];
        nested_integer_outer(values, word);
        assert!(values[0] == word);
        assert!(values[1] == sibling);
    }
}

pub fn nested_integer_wrong_claim(values: &mut [i32], word: i32) {
    if values.len() > 0 {
        nested_integer_outer(values, word);
        assert!(values[0] == (word ^ 1));
    }
}

pub fn nested_integer_deeper_unknown(values: &mut [i32], word: i32) {
    if values.len() > 0 {
        nested_integer_deeper(values, word);
        assert!(values[0] == word);
    }
}

#[cfg(test)]
mod native_nested_integer {
    #![forbid(unsafe_code)]
    extern crate std;
    #[test]
    fn actual_data_and_sibling() {
        for length in 0..=129 {
            for word in [i32::MIN, -17, 0, 17, i32::MAX] {
                let mut values = std::vec![23; length];
                super::nested_integer_child_call(&mut values, word);
            }
        }
    }
    #[test]
    fn mutation_guard() {
        super::nested_integer_child_call(&mut [23; 129], -17);
    }
}

#[inline(never)]
pub fn stage205_interval_value(word: i32) -> i32 {
    word ^ 0
}
#[inline(never)]
pub fn stage205_interval_leaf(values: &mut [i32], word: i32) {
    values[0] = stage205_interval_value(word);
}
#[inline(never)]
pub fn stage205_interval_outer(values: &mut [i32], word: i32) {
    stage205_interval_leaf(values, word);
}
pub fn checked_integer_interval(values: &mut [i32], start: usize, end: usize, word: i32) {
    if start < end && end <= values.len() {
        stage205_interval_leaf(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
pub fn checked_integer_interval_wrong(values: &mut [i32], start: usize, end: usize, word: i32) {
    if start < end && end <= values.len() {
        stage205_interval_leaf(&mut values[start..end], word);
        assert!(values[start] != word);
    }
}
pub fn checked_integer_interval_nested_unknown(
    values: &mut [i32], start: usize, end: usize, word: i32,
) {
    if start < end && end <= values.len() {
        stage205_interval_outer(&mut values[start..end], word);
        assert!(values[start] == word);
    }
}
#[cfg(test)]
mod stage205_interval_native {
    use super::*;
    #[test]
    fn mutation_guard() {
        for word in [i32::MIN, -1, 0, 1, i32::MAX] {
            for start in 0..129 {
                let mut values = [0_i32; 129];
                checked_integer_interval(&mut values, start, 129, word);
                assert!(values[start] == word);
            }
        }
    }
}

#[inline(never)]
pub fn stage207_metadata_word(value: u16) -> u16 {
    value ^ 0
}

#[inline(never)]
pub fn stage207_metadata_child(values: &mut [u16], value: u16) {
    if !values.is_empty() {
        values[0] = stage207_metadata_word(value);
    }
}

pub fn issued_metadata_is_empty(values: &mut [u16], value: u16) {
    assert!(values.is_empty() == (values.len() == 0));
    if values.len() > 0 {
        stage207_metadata_child(values, value);
        assert!(values[0] == value);
    }
}

pub fn issued_metadata_wrong_claim(values: &mut [u16]) {
    assert!(values.is_empty() != (values.len() == 0));
}

pub fn issued_metadata_other_element_unknown(values: &mut [i32]) {
    assert!(values.is_empty() == (values.len() == 0));
}

#[cfg(test)]
mod stage207_metadata_native {
    extern crate std;
    #[test]
    fn mutation_guard() {
        for length in 0..=129 {
            for value in [0, 1, u16::MAX] {
                super::issued_metadata_is_empty(&mut std::vec![23; length], value);
            }
        }
    }
}

#[inline(never)]
pub fn nested_bool_word(word: bool) -> bool {
    word ^ false
}
#[inline(never)]
pub fn nested_bool_leaf(values: &mut [bool], word: bool) {
    if values.len() > 0 {
        values[0] = nested_bool_word(word);
    }
}
#[inline(never)]
pub fn nested_bool_outer(values: &mut [bool], word: bool) -> bool {
    nested_bool_leaf(&mut *(&mut *values), word);
    nested_bool_word(word)
}
#[inline(never)]
pub fn nested_bool_deeper(values: &mut [bool], word: bool) {
    nested_bool_outer(values, word);
}
pub fn nested_bool_child_call(values: &mut [bool], word: bool) {
    if values.len() > 1 {
        let sibling = values[1];
        let returned = nested_bool_outer(values, word);
        assert!(values[0] == word && returned == word);
        assert!(values[1] == sibling);
    }
}
pub fn nested_bool_wrong_claim(values: &mut [bool], word: bool) {
    if values.len() > 0 {
        nested_bool_outer(values, word);
        assert!(values[0] != word);
    }
}
pub fn nested_bool_deeper_unknown(values: &mut [bool], word: bool) {
    if values.len() > 0 {
        nested_bool_deeper(values, word);
        assert!(values[0] == word);
    }
}
#[cfg(test)]
mod native_nested_bool {
    extern crate std;
    #[test]
    fn actual_data_and_sibling() {
        for length in 0..=129 {
            for word in [false, true] {
                let mut values = std::vec![false; length];
                super::nested_bool_child_call(&mut values, word);
            }
        }
    }
    #[test]
    fn mutation_guard() {
        super::nested_bool_child_call(&mut [false; 129], true);
    }
}

#[inline(never)]
pub fn nested_char_word(word: char) -> char {
    if word == '\0' { '\0' } else { word }
}
#[inline(never)]
pub fn nested_char_leaf(values: &mut [char], word: char) {
    if values.len() > 0 {
        values[0] = nested_char_word(word);
    }
}
#[inline(never)]
pub fn nested_char_outer(values: &mut [char], word: char) -> char {
    nested_char_leaf(&mut *(&mut *values), word);
    nested_char_word(word)
}
#[inline(never)]
pub fn nested_char_deeper(values: &mut [char], word: char) {
    nested_char_outer(values, word);
}
pub fn nested_char_child_call(values: &mut [char], word: char) {
    if values.len() > 1 {
        let old = values[1];
        let returned = nested_char_outer(values, word);
        assert!(values[0] == word && returned == word);
        assert!(values[1] == old);
    }
}
pub fn nested_char_wrong_claim(values: &mut [char], word: char) {
    if values.len() > 0 {
        nested_char_outer(values, word);
        assert!(values[0] != word);
    }
}
pub fn nested_char_deeper_unknown(values: &mut [char], word: char) {
    if values.len() > 0 {
        nested_char_deeper(values, word);
        assert!(values[0] == word);
    }
}
#[cfg(test)]
mod native_nested_char {
    extern crate std;
    #[test]
    fn actual_data_and_sibling() {
        for length in 0..=129 {
            for word in ['\0', 'a', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
                super::nested_char_child_call(&mut std::vec!['x'; length], word);
            }
        }
    }
    #[test]
    fn mutation_guard() {
        super::nested_char_child_call(&mut ['x'; 129], '\0');
    }
}

#[inline(never)]
pub fn issued_scalar_metadata_boolean(value: bool) -> bool {
    value ^ false
}

pub fn issued_scalar_metadata(values: &mut [bool]) {
    assert!(issued_scalar_metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn issued_scalar_metadata_wrong(values: &mut [bool]) {
    assert!(issued_scalar_metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn issued_scalar_float_unknown(values: &mut [f32]) {
    assert!(values.is_empty() == (values.len() == 0));
}

#[cfg(test)]
mod native_issued_scalar_metadata {
    extern crate std;

    #[test]
    fn finite_lengths() {
        for length in 0..=129 {
            super::issued_scalar_metadata(&mut std::vec![false; length]);
        }
    }

    #[test]
    fn mutation_guard() {
        super::issued_scalar_metadata(&mut [false; 129]);
    }
}

#[inline(never)]
fn float_hierarchy_word(value: f32) -> f32 {
    value
}

#[inline(never)]
fn float_hierarchy_leaf(values: &mut [f32], value: f32) {
    let copied = float_hierarchy_word(value);
    if values.len() > 0 {
        values[0] = copied;
    }
}

#[inline(never)]
fn float_hierarchy_outer(values: &mut [f32], value: f32) {
    float_hierarchy_leaf(&mut *(&mut *values), value);
}

#[inline(never)]
fn float_hierarchy_deeper(values: &mut [f32], value: f32) {
    float_hierarchy_outer(values, value);
}

pub fn float_hierarchy_selected(values: &mut [f32], value: f32) {
    if values.len() > 0 {
        float_hierarchy_outer(values, value);
        assert!(values[0].to_bits() == value.to_bits());
    }
}

pub fn float_hierarchy_wrong_claim(values: &mut [f32], value: f32) {
    if values.len() > 0 {
        float_hierarchy_outer(values, value);
        assert!(values[0].to_bits() != value.to_bits());
    }
}

pub fn float_hierarchy_deeper_unknown(values: &mut [f32], value: f32) {
    if values.len() > 0 {
        float_hierarchy_deeper(values, value);
        assert!(values[0].to_bits() == value.to_bits());
    }
}

#[cfg(test)]
mod float_hierarchy_native {
    extern crate std;

    const VALUES: [u32; 8] = [
        0,
        0x8000_0000,
        1,
        0x7f7f_ffff,
        0x7f80_0000,
        0xff80_0000,
        0x7fc0_1234,
        0xffc0_4321,
    ];

    #[test]
    fn finite_lengths_and_bits() {
        for length in 0..=129 {
            for bits in VALUES {
                super::float_hierarchy_selected(&mut std::vec![0.0; length], f32::from_bits(bits));
            }
        }
    }

    #[test]
    fn mutation_guard() {
        super::float_hierarchy_selected(&mut [0.0; 129], f32::from_bits(0x7fc0_1234));
    }
}
struct AssociatedHierarchyLocal;
impl AssociatedHierarchyLocal {
    #[inline(never)]
    fn scalar(word: u16) -> u16 {
        word ^ 0
    }
    #[inline(never)]
    fn leaf(values: &mut [u16], word: u16) {
        if values.len() > 0 {
            values[0] = Self::scalar(word);
        }
    }
    #[inline(never)]
    fn outer(values: &mut [u16], word: u16) {
        Self::leaf(&mut *values, word);
    }
    #[inline(never)]
    fn deeper(values: &mut [u16], word: u16) {
        Self::outer(values, word);
    }
}
pub fn local_associated_hierarchy_selected(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        AssociatedHierarchyLocal::outer(values, word);
        assert!(values[0] == word);
    }
}
pub fn local_associated_hierarchy_wrong_claim(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        AssociatedHierarchyLocal::outer(values, word);
        assert!(values[0] != word);
    }
}
pub fn local_associated_hierarchy_deeper_unknown(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        AssociatedHierarchyLocal::deeper(values, word);
        assert!(values[0] == word);
    }
}
#[cfg(test)]
mod local_associated_hierarchy_native {
    #[test]
    fn mutation_guard() {
        for word in [0, 1, 17, u16::MAX] {
            super::local_associated_hierarchy_selected(&mut [0; 129], word);
        }
    }
}

#[inline(never)]
fn owned_suffix_word(word: u16) -> u16 {
    word ^ 0
}

pub fn owned_suffix_selected(
    mut values: [[[u16; 2]; 2]; 2],
    i: usize,
    j: usize,
    k: usize,
    word: u16,
) {
    if i < 2 && j < 2 && k < 2 {
        let old = values;
        values[i][j][k] = owned_suffix_word(word);
        assert!(values[i][j][k] == word);
        assert!(values[i ^ 1][j][k] == old[i ^ 1][j][k]);
    }
}

pub fn owned_suffix_wrong_claim(
    mut values: [[[u16; 2]; 2]; 2],
    i: usize,
    j: usize,
    k: usize,
    word: u16,
) {
    if i < 2 && j < 2 && k < 2 {
        values[i][j][k] = owned_suffix_word(word);
        assert!(values[i][j][k] == word ^ 1);
    }
}

pub fn owned_suffix_budget_unknown(
    mut values: [[[u16; 4]; 4]; 4],
    i: usize,
    j: usize,
    k: usize,
    word: u16,
) {
    if i < 4 && j < 4 && k < 4 {
        values[i][j][k] = owned_suffix_word(word);
        assert!(values[i][j][k] == word);
    }
}

#[cfg(test)]
mod owned_suffix_native {
    #[test]
    fn mutation_guard() {
        for i in 0..2 {
            for j in 0..2 {
                for k in 0..2 {
                    for word in [0, 1, 17, u16::MAX] {
                        super::owned_suffix_selected([[[3; 2]; 2]; 2], i, j, k, word);
                    }
                }
            }
        }
    }
}

#[inline(never)]
fn integer_table_two_args_first(a: u16, b: i32) -> i64 {
    (a as i64).wrapping_add(b as i64)
}
#[inline(never)]
fn integer_table_two_args_second(a: u16, b: i32) -> i64 {
    (a as i64).wrapping_add(b as i64) ^ 1
}
pub fn integer_table_two_args_selected(index: usize, a: u16, b: i32) {
    let table: [fn(u16, i32) -> i64; 2] =
        [integer_table_two_args_first, integer_table_two_args_second];
    if index < 2 {
        let actual = table[index](a, b);
        let expected = (a as i64).wrapping_add(b as i64);
        assert!(actual == if index == 0 { expected } else { expected ^ 1 });
    }
}
pub fn integer_table_two_args_wrong(index: usize, a: u16, b: i32) {
    let table: [fn(u16, i32) -> i64; 2] =
        [integer_table_two_args_first, integer_table_two_args_second];
    if index < 2 {
        let actual = table[index](a, b);
        let expected = (a as i64).wrapping_add(b as i64);
        assert!(actual != if index == 0 { expected } else { expected ^ 1 });
    }
}
pub fn integer_table_two_args_repeat_unknown(index: usize, a: u16, b: i32) {
    let table: [fn(u16, i32) -> i64; 2] = [integer_table_two_args_first; 2];
    if index < 2 {
        assert!(table[index](a, b) == (a as i64).wrapping_add(b as i64));
    }
}
#[cfg(test)]
mod integer_table_two_args_native {
    extern crate std;
    #[test]
    fn mutation_guard() {
        for index in [0, 1] {
            for a in [0, 1, 129, u16::MAX] {
                for b in [i32::MIN, -1, 0, 129, i32::MAX] {
                    super::integer_table_two_args_selected(index, a, b);
                }
            }
        }
    }
}
mod primitive_unary_bool {
    #[inline(never)]
    pub fn identity(value: bool) -> bool {
        value ^ false
    }
    #[inline(never)]
    pub fn flip(value: bool) -> bool {
        !value
    }
}

pub fn primitive_table_bool_selected(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 2] = [primitive_unary_bool::identity, primitive_unary_bool::flip];
    if index < 2 {
        let actual = table[index](value);
        assert!(actual == if index == 0 { value } else { !value });
    }
}

pub fn primitive_table_bool_wrong(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 2] = [primitive_unary_bool::identity, primitive_unary_bool::flip];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

pub fn primitive_table_bool_opaque(index: usize, value: bool, callback: fn(bool) -> bool) {
    let table: [fn(bool) -> bool; 2] = [primitive_unary_bool::identity, callback];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

mod primitive_unary_char {
    #[inline(never)]
    pub fn identity(value: char) -> char {
        value
    }
    #[inline(never)]
    pub fn next(value: char) -> char {
        if value == 'A' { 'B' } else { 'A' }
    }
}

pub fn primitive_table_char_selected(index: usize, value: char) {
    let table: [fn(char) -> char; 2] = [primitive_unary_char::identity, primitive_unary_char::next];
    if index < 2 {
        let actual = table[index](value);
        let expected = if index == 0 {
            value
        } else if value == 'A' {
            'B'
        } else {
            'A'
        };
        assert!(actual == expected);
    }
}

pub fn primitive_table_char_wrong(index: usize, value: char) {
    let table: [fn(char) -> char; 2] = [primitive_unary_char::identity, primitive_unary_char::next];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}

pub fn primitive_table_char_opaque(index: usize, value: char, callback: fn(char) -> char) {
    let table: [fn(char) -> char; 2] = [primitive_unary_char::identity, callback];
    if index < 2 {
        assert!(table[index](value) == value);
    }
}


#[inline(never)]
pub fn float_table_first32(value: f32) -> f32 { value }
#[inline(never)]
pub fn float_table_second32(value: f32) -> f32 { -value }
#[inline(never)]
pub fn float_table_first64(value: f64) -> f64 { value }
#[inline(never)]
pub fn float_table_second64(value: f64) -> f64 { -value }

pub fn float_table_selected32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [float_table_first32, float_table_second32];
    if index < 2 {
        let actual = table[index](value);
        let expected = value.to_bits() ^ if index == 0 { 0 } else { 0x8000_0000 };
        assert!(actual.to_bits() == expected);
    }
}
pub fn float_table_wrong32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [float_table_first32, float_table_second32];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn float_table_opaque32(index: usize, value: f32, callback: fn(f32) -> f32) {
    let table: [fn(f32) -> f32; 2] = [float_table_first32, callback];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn float_table_repeat32(index: usize, value: f32) {
    let callback: fn(f32) -> f32 = float_table_first32;
    let table = [callback; 2];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn float_table_selected64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [float_table_first64, float_table_second64];
    if index < 2 {
        let actual = table[index](value);
        let expected = value.to_bits() ^ if index == 0 { 0 } else { 0x8000_0000_0000_0000 };
        assert!(actual.to_bits() == expected);
    }
}
pub fn float_table_wrong64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [float_table_first64, float_table_second64];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn float_table_opaque64(index: usize, value: f64, callback: fn(f64) -> f64) {
    let table: [fn(f64) -> f64; 2] = [float_table_first64, callback];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn float_table_repeat64(index: usize, value: f64) {
    let callback: fn(f64) -> f64 = float_table_first64;
    let table = [callback; 2];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}

mod primitive_repeat_bool {
    #[inline(never)]
    pub fn identity(value: bool) -> bool {
        value ^ false
    }
}

pub fn primitive_repeat_bool_selected(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 16] = [primitive_repeat_bool::identity; 16];
    if index < 16 {
        assert!(table[index](value) == value);
    }
}

pub fn primitive_repeat_bool_wrong(index: usize, value: bool) {
    let table: [fn(bool) -> bool; 16] = [primitive_repeat_bool::identity; 16];
    if index < 16 {
        assert!(table[index](value) != value);
    }
}

pub fn primitive_repeat_bool_opaque(value: bool, callback: fn(bool) -> bool) {
    let table = [callback; 2];
    assert!(table[0](value) == value);
}

mod primitive_repeat_char {
    #[inline(never)]
    pub fn identity(value: char) -> char {
        value
    }
}

pub fn primitive_repeat_char_selected(index: usize, value: char) {
    let table: [fn(char) -> char; 16] = [primitive_repeat_char::identity; 16];
    if index < 16 {
        assert!(table[index](value) == value);
    }
}

pub fn primitive_repeat_char_wrong(index: usize, value: char) {
    let table: [fn(char) -> char; 16] = [primitive_repeat_char::identity; 16];
    if index < 16 {
        assert!(table[index](value) != value);
    }
}

pub fn primitive_repeat_char_opaque(value: char, callback: fn(char) -> char) {
    let table = [callback; 2];
    assert!(table[0](value) == value);
}

#[cfg(test)]
mod primitive_repeat_native {
    #[test]
    fn genuine_claims() {
        for index in 0..16 {
            for value in [false, true] {
                super::primitive_repeat_bool_selected(index, value);
            }
            for value in ['\0', 'A', 'B', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
                super::primitive_repeat_char_selected(index, value);
            }
        }
    }
}

#[inline(never)]
pub fn niche_membership_member(
    values: &[Option<core::num::NonZeroU16>],
    needle: Option<core::num::NonZeroU16>,
) -> bool {
    values.contains(&needle)
}

pub fn niche_membership_selected_none(values: &[Option<core::num::NonZeroU16>]) {
    if !values.is_empty() && values[0].is_none() {
        assert!(niche_membership_member(values, None));
    }
}

pub fn niche_membership_selected_some(
    values: &[Option<core::num::NonZeroU16>],
    needle: core::num::NonZeroU16,
) {
    if !values.is_empty()
        && let Some(first) = values[0]
        && first.get() == needle.get()
    {
        assert!(niche_membership_member(values, Some(needle)));
    }
}

pub fn niche_membership_empty(values: &[Option<core::num::NonZeroU16>]) {
    if values.is_empty() {
        assert!(!niche_membership_member(values, None));
    }
}

pub fn niche_membership_wrong_empty(values: &[Option<core::num::NonZeroU16>]) {
    if values.is_empty() {
        assert!(niche_membership_member(values, None));
    }
}

pub fn niche_membership_unsupported_width(
    values: &[Option<core::num::NonZeroU32>],
    needle: Option<core::num::NonZeroU32>,
) {
    assert!(values.contains(&needle));
}


pub trait CapabilityChoiceRead {
    fn read(&self) -> u8;
}
struct CapabilityChoiceMask(u8);
struct CapabilityChoiceRemainder(u8);
impl CapabilityChoiceRead for CapabilityChoiceMask {
    #[inline(never)]
    fn read(&self) -> u8 { self.0 & 15 }
}
impl CapabilityChoiceRead for CapabilityChoiceRemainder {
    #[inline(never)]
    fn read(&self) -> u8 { self.0 % 16 }
}
#[inline(never)]
fn capability_choice_invoke(value: &dyn CapabilityChoiceRead) -> u8 { value.read() }
#[inline(never)]
fn capability_choice_return<'a>(
    values: &[&'a dyn CapabilityChoiceRead], index: usize,
) -> &'a dyn CapabilityChoiceRead { values[index] }

pub fn trait_choice_symbolic(value: u8, index: usize) {
    if index >= 2 { return; }
    let first = CapabilityChoiceMask(value);
    let second = CapabilityChoiceRemainder(value);
    let values: [&dyn CapabilityChoiceRead; 2] = [&first, &second];
    assert!(capability_choice_invoke(values[index]) <= 15);
}

pub fn trait_choice_wrong(value: u8, index: usize) {
    if index >= 2 { return; }
    let first = CapabilityChoiceMask(value);
    let second = CapabilityChoiceRemainder(value);
    let values: [&dyn CapabilityChoiceRead; 2] = [&first, &second];
    assert!(capability_choice_invoke(values[index]) == 16);
}

pub fn trait_choice_returned(value: u8, index: usize) {
    if index >= 2 { return; }
    let first = CapabilityChoiceMask(value);
    let second = CapabilityChoiceRemainder(value);
    let values: [&dyn CapabilityChoiceRead; 2] = [&first, &second];
    let selected = capability_choice_return(&values, index);
    assert!(capability_choice_invoke(selected) <= 15);
}

pub fn trait_choice_repeated(value: u8, index: usize) {
    if index >= 2 { return; }
    let first = CapabilityChoiceMask(value);
    let second = CapabilityChoiceRemainder(value);
    let values: [&dyn CapabilityChoiceRead; 2] = [&first, &second];
    let selected = values[index];
    assert!(capability_choice_invoke(selected) <= 15);
    assert!(capability_choice_invoke(selected) <= 15);
}

pub fn trait_choice_opaque(value: &dyn CapabilityChoiceRead) {
    assert!(capability_choice_invoke(value) <= 15);
}

#[inline(never)]
pub fn niche_membership_member_u32(
    values: &[Option<core::num::NonZeroU32>],
    needle: Option<core::num::NonZeroU32>,
) -> bool {
    values.contains(&needle)
}

pub fn niche_membership_selected_none_u32(values: &[Option<core::num::NonZeroU32>]) {
    if !values.is_empty() && values[0].is_none() {
        assert!(niche_membership_member_u32(values, None));
    }
}

pub fn niche_membership_selected_some_u32(
    values: &[Option<core::num::NonZeroU32>],
    needle: core::num::NonZeroU32,
) {
    if !values.is_empty()
        && let Some(first) = values[0]
        && first.get() == needle.get()
    {
        assert!(niche_membership_member_u32(values, Some(needle)));
    }
}

pub fn niche_membership_empty_u32(values: &[Option<core::num::NonZeroU32>]) {
    if values.is_empty() {
        assert!(!niche_membership_member_u32(values, None));
    }
}

pub fn niche_membership_wrong_empty_u32(values: &[Option<core::num::NonZeroU32>]) {
    if values.is_empty() {
        assert!(niche_membership_member_u32(values, None));
    }
}

pub fn niche_membership_byte_frontier(values: &[Option<core::num::NonZeroU8>]) {
    let _ = values.contains(&None);
}


pub fn issued_scalar_f64_metadata(values: &mut [f64]) {
    assert!(issued_scalar_metadata_boolean(values.is_empty()) == (values.len() == 0));
}

pub fn issued_scalar_f32_wrong_empty(values: &mut [f32]) {
    assert!(issued_scalar_metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn issued_scalar_f64_wrong_empty(values: &mut [f64]) {
    assert!(issued_scalar_metadata_boolean(values.is_empty()) != (values.len() == 0));
}

pub fn issued_scalar_nested_float_unknown(values: &mut [[f32; 2]]) {
    assert!(values.is_empty() == (values.len() == 0));
}

#[inline(never)]
pub fn local_byte_copy_source() -> [u8; 2] {
    [17, 19]
}

pub fn local_byte_copy_positive(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = local_byte_copy_source();
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 19);
    }
}

pub fn local_byte_copy_wrong(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = local_byte_copy_source();
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 17);
    }
}

pub fn local_byte_copy_symbolic(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 2 {
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == second);
    }
}

pub fn local_byte_copy_symbolic_wrong(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 2 {
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == first);
    }
}

pub fn local_byte_copy_tail(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 3 {
        let old = values[2];
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == second && values[2] == old);
    }
}

pub fn local_byte_copy_empty(values: &mut [u8]) {
    let bytes: [u8; 0] = [];
    values[..0].copy_from_slice(&bytes);
    assert!(values.len() == values.len());
}

#[inline(never)]
unsafe fn local_byte_copy_unsafe_source() -> [u8; 2] {
    [17, 19]
}

pub fn local_byte_copy_unsafe_transport(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = unsafe { local_byte_copy_unsafe_source() };
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 19);
    }
}


use core::num::{NonZeroI8, NonZeroU8};

#[inline(never)]
pub fn selected_observer(value: Option<NonZeroU8>) -> u8 {
    match value {
        None => 0,
        Some(word) => word.get(),
    }
}

#[inline(never)]
pub fn selected_equal8(left: Option<NonZeroU8>, right: Option<NonZeroU8>) -> bool {
    left == right
}

#[inline(never)]
pub fn selected_not_equal8(left: Option<NonZeroU8>, right: Option<NonZeroU8>) -> bool {
    left != right
}

pub fn same_observation_ne8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(!selected_not_equal8(value, value));
    }
}

pub fn observe_correlated8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        match value {
            None => assert!(selected_observer(value) == 0),
            Some(word) => assert!(selected_observer(value) == word.get() && word.get() != 0),
        }
    }
}

pub fn wrong_some_zero8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len()
        && let Some(word) = values[index]
    {
        assert!(word.get() == 0);
    }
}

pub fn same_observation_eq8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(selected_equal8(value, value));
    }
}

pub fn wrong_ne8(values: &[Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        let value = values[index];
        assert!(selected_not_equal8(value, value));
    }
}

#[inline(never)]
pub fn selected_member8(values: &[Option<NonZeroU8>], needle: Option<NonZeroU8>) -> bool {
    values.contains(&needle)
}

pub fn asserted_contains8(values: &[Option<NonZeroU8>]) {
    if !values.is_empty() && values[0].is_none() {
        assert!(selected_member8(values, None));
    }
}

#[derive(Clone, Copy)]
pub enum Local8 {
    Empty,
    Word(NonZeroU8),
}

pub fn local_enum_unknown(values: &[Local8], index: usize) {
    if index < values.len()
        && let Local8::Word(word) = values[index]
    {
        assert!(word.get() != 0);
    }
}

pub fn mutable_unknown(values: &mut [Option<NonZeroU8>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}

pub fn signed_unknown(values: &[Option<NonZeroI8>], index: usize) {
    if index < values.len()
        && let Some(word) = values[index]
    {
        assert!(word.get() != 0);
    }
}

pub fn pointer_unknown(values: &[Option<&u8>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}

// Typed mutable product owners: standalone survey copies retain all helper bodies.
mod mutable_product_survey {
    pub fn metadata32(values: &mut [[f32; 2]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    pub fn metadata64(values: &mut [[f64; 2]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    pub fn wrong_metadata(values: &mut [[f32; 2]]) {
        let length = values.len();
        assert!(values.is_empty() != (length == 0));
    }

    #[inline(never)]
    pub fn observe_bits(value: f32) -> u32 {
        value.to_bits()
    }

    pub fn copied_helper(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            let value = values[index][0];
            assert!(observe_bits(value) == value.to_bits());
        }
    }

    #[inline(never)]
    pub fn stored_word() -> f32 {
        f32::from_bits(0x7fc0_1234)
    }

    pub fn store_nan(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            let untouched = values[index][1].to_bits();
            values[index][0] = stored_word();
            assert!(values[index][0].to_bits() == 0x7fc0_1234);
            assert!(values[index][1].to_bits() == untouched);
        }
    }

    pub fn wrong_stored_bits(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            values[index][0] = stored_word();
            assert!(values[index][0].to_bits() == 0x7fc0_1235);
        }
    }

    pub fn wrong_untouched_leaf(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            let untouched = values[index][1].to_bits();
            values[index][0] = stored_word();
            assert!(values[index][1].to_bits() != untouched);
        }
    }

    pub fn whole64(values: &mut [[f64; 2]], index: usize) {
        if index < values.len() {
            values[index] = [-0.0, f64::from_bits(0x7ff8_0000_0000_1234)];
            assert!(values[index][0].to_bits() == 0x8000_0000_0000_0000);
            assert!(values[index][1].to_bits() == 0x7ff8_0000_0000_1234);
        }
    }

    pub fn outer_retention(values: &mut [[f32; 2]]) {
        if values.len() >= 2 {
            let untouched = values[1][0].to_bits();
            values[0][0] = stored_word();
            assert!(values[0][0].to_bits() == 0x7fc0_1234);
            assert!(values[1][0].to_bits() == untouched);
        }
    }

    pub fn unguarded(values: &mut [[f32; 2]], index: usize) {
        let _ = values[index][0].to_bits();
    }

    pub fn integer_pair(values: &mut [[u16; 2]], index: usize) {
        if index < values.len() {
            let untouched = values[index][1];
            values[index][0] = 42;
            assert!(values[index][0] == 42 && values[index][1] == untouched);
        }
    }

    pub fn tuple_pair(values: &mut [(bool, char)], index: usize) {
        if index < values.len() {
            values[index] = (true, '\u{10ffff}');
            assert!(values[index].0 && values[index].1 as u32 == 0x10ffff);
        }
    }

    #[derive(Clone, Copy)]
    pub struct Reading {
        pub number: u16,
        pub ready: bool,
        pub character: char,
        pub temperature: f64,
    }

    pub fn struct_fields(values: &mut [Reading], index: usize, word: f64) {
        if index < values.len() {
            let number = values[index].number;
            values[index].temperature = -word;
            values[index].ready = true;
            values[index].character = '\u{1f980}';
            assert!(values[index].temperature.to_bits() == (-word).to_bits());
            assert!(values[index].ready && values[index].character as u32 == 0x1f980);
            assert!(values[index].number == number);
        }
    }

    pub fn zero_inner(values: &mut [[f32; 0]], index: usize) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
        if index < values.len() {
            values[index] = [];
        }
    }

    pub fn proper_reborrow(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
        }
    }

    #[inline(never)]
    pub fn owner_child(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            values[0][0] = stored_word();
        }
    }

    pub fn unsupported_child(values: &mut [[f32; 2]]) {
        owner_child(values);
    }

    pub fn symbolic_suffix(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            values[outer][inner] = stored_word();
        }
    }

    pub fn pointer_product(values: &mut [[*const u8; 2]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    pub fn reference_product(values: &mut [[&u16; 2]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    pub fn niche_product(values: &mut [[Option<core::num::NonZeroU8>; 2]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    pub fn oversized(values: &mut [[f32; 129]]) {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn copied_helper_claims() {
            for bits in [0, 0x8000_0000, 0x7fc0_4567, 0x7f80_0000, 0xff80_0000] {
                let mut values = [[f32::from_bits(bits), 3.0], [4.0, -0.0]];
                super::copied_helper(&mut values, 0);
                super::copied_helper(&mut values, 1);
            }
        }

        #[test]
        fn actual_store_claims() {
            let mut values = [[1.0_f32, -0.0], [f32::from_bits(0x7fc0_4567), 3.0]];
            super::store_nan(&mut values, 0);
            super::store_nan(&mut values, 1);
            super::outer_retention(&mut values);
            let mut wide = [[1.0_f64, 2.0]];
            super::whole64(&mut wide, 0);
            assert_eq!(wide[0][0].to_bits(), 0x8000_0000_0000_0000);
            let mut pair = [(false, 'a')];
            super::tuple_pair(&mut pair, 0);
            let mut readings = [super::Reading {
                number: 7,
                ready: false,
                character: 'a',
                temperature: 1.0,
            }];
            super::struct_fields(&mut readings, 0, -0.0);
            assert_eq!(readings[0].number, 7);
            let mut zero = [[]; 2];
            super::zero_inner(&mut zero, 1);
            super::metadata32(&mut []);
            super::metadata64(&mut wide);
        }
    }
}

pub mod mutable_product_child_survey {
    #[inline(never)]
    pub fn stored_float() -> f32 {
        f32::from_bits(0x7fc0_1234)
    }

    #[inline(never)]
    pub fn write_float(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            values[index][0] = stored_float();
        }
    }

    pub fn float_call(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            let untouched = values[index][1].to_bits();
            write_float(values, index);
            assert!(values[index][0].to_bits() == 0x7fc0_1234);
            assert!(values[index][1].to_bits() == untouched);
        }
    }

    pub fn wrong_float_call(values: &mut [[f32; 2]], index: usize) {
        if index < values.len() {
            write_float(values, index);
            assert!(values[index][0].to_bits() == 0x7fc0_1235);
        }
    }

    pub fn sequential(values: &mut [[f32; 2]]) {
        if values.len() >= 2 {
            let untouched = values[1][1].to_bits();
            write_float(values, 0);
            write_float(values, 1);
            assert!(values[0][0].to_bits() == 0x7fc0_1234);
            assert!(values[1][0].to_bits() == 0x7fc0_1234);
            assert!(values[1][1].to_bits() == untouched);
        }
    }

    pub fn false_retention(values: &mut [[f32; 2]]) {
        if values.len() >= 2 {
            let untouched = values[1][1].to_bits();
            write_float(values, 0);
            assert!(values[1][1].to_bits() != untouched);
        }
    }

    #[inline(never)]
    pub fn wide_return(values: &mut [[f64; 2]], index: usize) -> u64 {
        if index < values.len() {
            values[index] = [-0.0, f64::from_bits(0x7ff8_0000_0000_1234)];
            values[index][0].to_bits()
        } else {
            0
        }
    }

    pub fn wide_call(values: &mut [[f64; 2]], index: usize) {
        if index < values.len() {
            let bits = wide_return(values, index);
            assert!(bits == 0x8000_0000_0000_0000);
            assert!(values[index][1].to_bits() == 0x7ff8_0000_0000_1234);
        }
    }

    #[inline(never)]
    pub fn write_tuple(values: &mut [(bool, char)], index: usize) {
        if index < values.len() {
            values[index] = (true, '\u{1f980}');
        }
    }

    pub fn tuple_call(values: &mut [(bool, char)], index: usize) {
        if index < values.len() {
            write_tuple(values, index);
            assert!(values[index].0 && values[index].1 as u32 == 0x1f980);
        }
    }

    #[derive(Clone, Copy)]
    pub struct Record {
        pub word: u16,
        pub ready: bool,
    }

    #[inline(never)]
    pub fn write_record(values: &mut [Record], index: usize) {
        if index < values.len() {
            values[index].ready = true;
        }
    }

    pub fn record_call(values: &mut [Record], index: usize) {
        if index < values.len() {
            let old = values[index].word;
            write_record(values, index);
            assert!(values[index].ready && values[index].word == old);
        }
    }

    #[inline(never)]
    pub fn metadata_child(values: &mut [[f32; 2]]) -> bool {
        let length = values.len();
        assert!(values.is_empty() == (length == 0));
        values.is_empty()
    }

    pub fn metadata_call(values: &mut [[f32; 2]]) {
        let empty = metadata_child(values);
        assert!(empty == (values.len() == 0));
    }

    #[inline(never)]
    pub fn zero_child(values: &mut [()], index: usize) {
        if index < values.len() {
            values[index] = ();
        }
    }

    pub fn zero_call(values: &mut [()], index: usize) {
        let length = values.len();
        zero_child(values, index);
        assert!(values.len() == length);
    }

    #[inline(never)]
    pub fn unchecked_child(values: &mut [[f32; 2]], index: usize) {
        values[index][0] = stored_float();
    }

    pub fn unchecked_call(values: &mut [[f32; 2]], index: usize) {
        unchecked_child(values, index);
        let _ = values.len();
    }

    #[inline(never)]
    pub fn nested_child(values: &mut [[f32; 2]], index: usize) {
        write_float(values, index);
        let _ = values.len();
    }

    pub fn nested_owner_unknown(values: &mut [[f32; 2]], index: usize) {
        nested_child(values, index);
        let _ = values.len();
    }

    pub fn moved_parent_unknown(values: &mut [[f32; 2]], index: usize) {
        let moved = values;
        write_float(moved, index);
    }

    pub fn interval_unknown(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            write_float(&mut values[0..1], 0);
            let _ = values.len();
        }
    }

    #[inline(never)]
    pub fn symbolic_child(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            values[outer][inner] = stored_float();
        }
    }

    pub fn symbolic_unknown(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        symbolic_child(values, outer, inner);
        let _ = values.len();
    }

    #[inline(never)]
    pub fn returned_owner(values: &mut [[f32; 2]]) -> &mut [[f32; 2]] {
        values
    }

    pub fn escape_unknown(values: &mut [[f32; 2]]) {
        let child = returned_owner(values);
        let _ = child.len();
    }

    pub fn scalar_seed(value: u16) -> u16 {
        value
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn callers_keep_their_actual_store_claims() {
            let mut values = [[1.0, -0.0], [f32::from_bits(0x7fc0_4567), 3.0]];
            super::float_call(&mut values, 0);
            super::float_call(&mut values, 1);
            super::sequential(&mut values);
            super::metadata_call(&mut values);
            super::metadata_call(&mut []);
            let mut wide = [[1.0, 2.0]];
            super::wide_call(&mut wide, 0);
            let mut tuple = [(false, 'a')];
            super::tuple_call(&mut tuple, 0);
            let mut record = [super::Record {
                word: 7,
                ready: false,
            }];
            super::record_call(&mut record, 0);
            assert!(record[0].word == 7);
            super::zero_call(&mut [(), ()], 1);
        }
    }

    // Standalone compiler identity controls; never called by an analyzed guest claim.
    pub mod host_float_impostor {
        pub fn from_bits(_: u32) -> f32 {
            0.0
        }
    }
}

pub mod mutable_product_symbolic_survey {
    #[inline(never)]
    pub fn actual_float() -> f32 {
        f32::from_bits(0x7fc0_1234)
    }
    #[inline(never)]
    pub fn actual_double() -> f64 {
        f64::from_bits(0x7ff8_0000_0000_1234)
    }
    #[inline(never)]
    pub fn actual_word() -> u16 {
        37
    }
    #[inline(never)]
    pub fn actual_inner(index: usize) -> usize {
        index ^ 0
    }

    pub fn float_selected(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner].to_bits();
            let target = actual_inner(inner);
            values[outer][target] = actual_float();
            assert!(values[outer][inner].to_bits() == 0x7fc0_1234);
            assert!(values[outer][1 - inner].to_bits() == old);
        }
    }

    pub fn float_other_outer(values: &mut [[f32; 2]], outer: usize, inner: usize, other: usize) {
        if outer < values.len() && other < values.len() && inner < 2 && outer != other {
            let old = values[other][inner].to_bits();
            values[outer][inner] = actual_float();
            assert!(values[other][inner].to_bits() == old);
        }
    }

    pub fn two_indices(values: &mut [[[u16; 2]; 2]], outer: usize, i: usize, j: usize) {
        if outer < values.len() && i < 2 && j < 2 {
            let old = values[outer][1 - i][j];
            values[outer][i][j] = actual_word();
            assert!(values[outer][i][j] == 37);
            assert!(values[outer][1 - i][j] == old);
        }
    }

    pub fn correlated(values: &mut [[[i32; 2]; 2]], outer: usize, i: usize) {
        if outer < values.len() && i < 2 {
            let old = values[outer][i][1 - i];
            values[outer][i][i] = -19;
            assert!(values[outer][i][i] == -19);
            assert!(values[outer][i][1 - i] == old);
        }
    }

    pub fn bool_selected(values: &mut [[bool; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner];
            values[outer][inner] = true;
            assert!(values[outer][inner]);
            assert!(values[outer][1 - inner] == old);
        }
    }

    pub fn char_selected(values: &mut [[char; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner];
            values[outer][inner] = 'λ';
            assert!(values[outer][inner] == 'λ');
            assert!(values[outer][1 - inner] == old);
        }
    }

    pub fn whole_tuple(values: &mut [[(u16, bool, char, f32); 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner].0;
            values[outer][inner] = (actual_word(), true, 'λ', actual_float());
            let packet = values[outer][inner];
            assert!(packet.0 == 37 && packet.1 && packet.2 == 'λ');
            assert!(packet.3.to_bits() == 0x7fc0_1234);
            assert!(values[outer][1 - inner].0 == old);
        }
    }

    pub fn whole_array(values: &mut [[[f64; 2]; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner][0].to_bits();
            values[outer][inner] = [actual_double(), -0.0];
            let packet = values[outer][inner];
            assert!(packet[0].to_bits() == 0x7ff8_0000_0000_1234);
            assert!(packet[1].to_bits() == 0x8000_0000_0000_0000);
            assert!(values[outer][1 - inner][0].to_bits() == old);
        }
    }

    #[derive(Clone, Copy)]
    pub struct Record {
        pub ints: [u16; 2],
        pub flag: bool,
        pub mark: char,
        pub wide: f64,
    }

    pub fn record_fields(values: &mut [[Record; 2]], outer: usize, inner: usize, field: usize) {
        if outer < values.len() && inner < 2 && field < 2 {
            let old = values[outer][inner].ints[1 - field];
            values[outer][inner].ints[field] = actual_word();
            values[outer][inner].flag = true;
            values[outer][inner].mark = 'λ';
            values[outer][inner].wide = actual_double();
            assert!(values[outer][inner].ints[field] == 37);
            assert!(values[outer][inner].ints[1 - field] == old);
            assert!(values[outer][inner].flag && values[outer][inner].mark == 'λ');
            assert!(values[outer][inner].wide.to_bits() == 0x7ff8_0000_0000_1234);
        }
    }

    pub fn tuple_fields(values: &mut [([u16; 2], bool)], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer].1;
            values[outer].0[inner] = actual_word();
            assert!(values[outer].0[inner] == 37);
            assert!(values[outer].1 == old);
        }
    }

    pub fn whole_record(values: &mut [[Record; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner].mark;
            values[outer][inner] = Record {
                ints: [37, 38],
                flag: true,
                mark: 'λ',
                wide: actual_double(),
            };
            let record = values[outer][inner];
            assert!(record.ints[0] == 37 && record.ints[1] == 38);
            assert!(record.flag && record.mark == 'λ');
            assert!(record.wide.to_bits() == 0x7ff8_0000_0000_1234);
            assert!(values[outer][1 - inner].mark == old);
        }
    }

    pub fn zero_selected(values: &mut [[(); 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let length = values.len();
            values[outer][inner] = ();
            let _selected = values[outer][inner];
            assert!(values.len() == length);
        }
    }

    pub fn sequential(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            values[outer][inner] = actual_float();
            values[outer][1 - inner] = 0.0;
            assert!(values[outer][inner].to_bits() == 0x7fc0_1234);
            assert!(values[outer][1 - inner].to_bits() == 0);
        }
    }

    pub fn branch(values: &mut [[u32; 2]], outer: usize, inner: usize, choose: bool) {
        if outer < values.len() && inner < 2 {
            values[outer][inner] = if choose { 17 } else { 19 };
            assert!(values[outer][inner] == if choose { 17 } else { 19 });
        }
    }

    pub fn current_child(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        float_selected(values, outer, inner);
    }

    pub fn wrong_float(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            values[outer][inner] = actual_float();
            assert!(values[outer][inner].to_bits() == 0x7fc0_1235);
        }
    }

    pub fn wrong_retention(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let old = values[outer][1 - inner].to_bits();
            values[outer][inner] = actual_float();
            assert!(values[outer][1 - inner].to_bits() != old);
        }
    }

    pub fn unguarded_inner(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() {
            values[outer][inner] = actual_float();
        }
    }

    pub fn alias_unknown(values: &mut [[f32; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let alias = &mut values[outer][inner];
            *alias = actual_float();
        }
    }

    pub fn budget_unknown(values: &mut [[u16; 128]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 128 {
            values[outer][inner] = actual_word();
        }
    }

    pub fn whole_budget(
        values: &mut [[(u16, bool, char, f32, f64); 16]],
        outer: usize,
        inner: usize
    ) {
        if outer < values.len() && inner < 16 {
            values[outer][inner] = (37, true, 'λ', actual_float(), actual_double());
        }
    }

    pub fn scalar_seed(value: u16) -> u16 {
        value
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn actual_symbolic_callers_preserve_the_same_store_claims() {
            for outer in 0..2 {
                for inner in 0..2 {
                    let mut values = [[-0.0; 2]; 2];
                    super::float_selected(&mut values, outer, inner);
                    super::current_child(&mut values, outer, inner);
                    super::sequential(&mut values, outer, inner);
                    super::bool_selected(&mut [[false; 2]; 2], outer, inner);
                    super::char_selected(&mut [['x'; 2]; 2], outer, inner);
                    super::whole_tuple(&mut [[(0, false, 'x', 0.0); 2]; 2], outer, inner);
                    super::whole_array(&mut [[[0.0; 2]; 2]; 2], outer, inner);
                    let record = super::Record {
                        ints: [0; 2],
                        flag: false,
                        mark: 'x',
                        wide: 0.0,
                    };
                    let mut records = [[record; 2]; 2];
                    super::record_fields(&mut records, outer, inner, inner);
                    super::whole_record(&mut records, outer, inner);
                    super::tuple_fields(&mut [([0; 2], false); 2], outer, inner);
                    super::zero_selected(&mut [[(); 2]; 2], outer, inner);
                    super::branch(&mut [[0; 2]; 2], outer, inner, true);
                    super::branch(&mut [[0; 2]; 2], outer, inner, false);
                    for other in 0..2 {
                        super::float_other_outer(&mut values, outer, inner, other);
                        super::two_indices(&mut [[[0; 2]; 2]; 2], outer, inner, other);
                        super::correlated(&mut [[[0; 2]; 2]; 2], outer, inner);
                    }
                }
            }
        }
    }
}

pub mod array_move_initialization_survey {
    pub struct Token {
        pub word: u16,
    }

    pub struct Rows {
        pub values: [[Token; 2]; 2],
    }

    #[inline(never)]
    pub fn unpack(values: [Token; 2]) -> (Token, Token) {
        let [left, right] = values;
        (left, right)
    }

    #[inline(never)]
    pub fn unpack_rows(rows: Rows) -> (Token, Token, Token, Token) {
        let Rows {
            values: [[a, b], [c, d]],
        } = rows;
        (a, b, c, d)
    }

    pub fn array_claim(a: u16, b: u16) {
        let (left, right) = unpack([Token { word: a }, Token { word: b }]);
        assert!(left.word == a && right.word == b);
    }

    pub fn array_wrong(a: u16, b: u16) {
        let (left, right) = unpack([Token { word: a }, Token { word: b }]);
        assert!(left.word == (a ^ 1) && right.word == b);
    }

    pub fn nested_claim(a: u16, b: u16, c: u16, d: u16) {
        let (x, y, z, w) = unpack_rows(Rows {
            values: [
                [Token { word: a }, Token { word: b }],
                [Token { word: c }, Token { word: d }],
            ],
        });
        assert!(x.word == a && y.word == b && z.word == c && w.word == d);
    }

    pub fn nested_wrong(a: u16, b: u16, c: u16, d: u16) {
        let (x, y, z, w) = unpack_rows(Rows {
            values: [
                [Token { word: a }, Token { word: b }],
                [Token { word: c }, Token { word: d }],
            ],
        });
        assert!(x.word == a && y.word == b && z.word == c && w.word == (d ^ 1));
    }

    // A whole covering assignment after destructuring is ordinary safe Rust. This repairs the whole
    // array, rather than pretending indexed repair of a partially moved array is Rust-legal.
    pub fn covering_array_repair(a: u16, b: u16, next: u16) {
        let mut values = [Token { word: a }, Token { word: b }];
        let [left, right] = values;
        assert!(left.word == a && right.word == b);
        values = [Token { word: next }, Token { word: next }];
        let [left, right] = values;
        assert!(left.word == next && right.word == next);
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn array() {
            super::array_claim(9, 17);
        }
        #[test]
        fn nested() {
            super::nested_claim(9, 17, 23, 29);
        }
        #[test]
        fn repair() {
            super::covering_array_repair(9, 17, 23);
        }
    }

    #[cfg(test)]
    mod counterexamples {
        #[test]
        fn array_wrong() {
            super::array_wrong(9, 17);
        }
        #[test]
        fn nested_wrong() {
            super::nested_wrong(9, 17, 23, 29);
        }
    }
}

pub mod effect_free_zst_box_drop_survey {
    extern crate alloc;
    use alloc::boxed::Box;

    #[repr(align(4096))]
    pub struct Marker;
    impl Drop for Marker {
        fn drop(&mut self) {}
    }
    #[inline(never)]
    pub fn actual_tag() -> u16 {
        17
    }
    #[inline(never)]
    pub fn selected(owner: Box<Marker>) -> u16 {
        core::mem::drop(owner);
        actual_tag()
    }
    pub fn implicit() {
        let _owner = Box::new(Marker);
        assert!(actual_tag() == 17);
    }
    pub fn explicit() {
        core::mem::drop(Box::new(Marker));
        assert!(actual_tag() == 17);
    }
    pub fn transfer() {
        assert!(selected(Box::new(Marker)) == 17);
    }
    pub fn independent() {
        let first = Box::new(Marker);
        let second = Box::new(Marker);
        core::mem::drop(first);
        core::mem::drop(second);
        assert!(actual_tag() == 17);
    }
    pub fn branches(choose: bool) {
        let owner = Box::new(Marker);
        if choose {
            core::mem::drop(owner);
        } else {
            let moved = owner;
            core::mem::drop(moved);
        }
        assert!(actual_tag() == 17);
    }
    pub fn wrong_tag() {
        assert!(selected(Box::new(Marker)) == 18);
    }

    pub struct Panicking;
    impl Drop for Panicking {
        fn drop(&mut self) {
            panic!("actual payload destructor panic");
        }
    }
    pub fn panicking() {
        let _owner = Box::new(Panicking);
    }
    static SIDE_EFFECT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
    pub struct Effectful;
    impl Drop for Effectful {
        fn drop(&mut self) {
            SIDE_EFFECT.store(1, core::sync::atomic::Ordering::Relaxed);
        }
    }
    pub fn effectful() {
        let _owner = Box::new(Effectful);
    }
    pub struct Nested(pub Marker);
    pub fn nested() {
        let _owner = Box::new(Nested(Marker));
    }
    pub struct Nonzero(pub u8);
    impl Drop for Nonzero {
        fn drop(&mut self) {}
    }
    pub fn nonzero() {
        let _owner = Box::new(Nonzero(7));
    }
    pub struct ZeroArray(pub [Marker; 0]);
    impl Drop for ZeroArray {
        fn drop(&mut self) {}
    }
    pub fn zero_array() {
        let _owner = Box::new(ZeroArray([]));
    }
    pub struct NotFreeze(pub core::cell::UnsafeCell<()>);
    impl Drop for NotFreeze {
        fn drop(&mut self) {}
    }
    pub fn not_freeze() {
        let _owner = Box::new(NotFreeze(core::cell::UnsafeCell::new(())));
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn unchanged_claims_execute_actual_destructor_and_helper() {
            super::implicit();
            super::explicit();
            super::transfer();
            super::independent();
            super::branches(true);
            super::branches(false);
        }
    }
}


pub mod partial_array_drops_survey {
    use core::cell::Cell;

    struct Stamp<'a> {
        log: &'a Cell<u32>,
        digit: u32,
    }
    impl Drop for Stamp<'_> {
        fn drop(&mut self) {
            self.log
                .set(self.log.get().wrapping_mul(10).wrapping_add(self.digit));
        }
    }
    #[inline(never)]
    fn partial(log: &Cell<u32>) {
        let values = [
            Stamp { log, digit: 1 },
            Stamp { log, digit: 2 },
            Stamp { log, digit: 3 },
        ];
        let [first, ..] = values;
        drop(first);
        assert!(log.get() == 1);
    }
    #[inline(never)]
    fn nested(log: &Cell<u32>) {
        let values = [
            [Stamp { log, digit: 1 }, Stamp { log, digit: 2 }],
            [Stamp { log, digit: 3 }, Stamp { log, digit: 4 }],
        ];
        let [[first, ..], ..] = values;
        drop(first);
        assert!(log.get() == 1);
    }
    #[inline(never)]
    fn covering(log: &Cell<u32>) {
        let mut values = [Stamp { log, digit: 1 }, Stamp { log, digit: 2 }];
        let [first, ..] = values;
        drop(first);
        values = [Stamp { log, digit: 3 }, Stamp { log, digit: 4 }];
        assert!(log.get() == 12);
        drop(values);
    }
    pub fn partial_claim() {
        let log = Cell::new(0);
        partial(&log);
        assert!(log.get() == 123);
    }
    pub fn partial_wrong() {
        let log = Cell::new(0);
        partial(&log);
        assert!(log.get() == 132);
    }
    pub fn nested_claim() {
        let log = Cell::new(0);
        nested(&log);
        assert!(log.get() == 1342);
    }
    pub fn covering_claim() {
        let log = Cell::new(0);
        covering(&log);
        assert!(log.get() == 1234);
    }
    pub fn iterator_claim() {
        let log = Cell::new(0);
        {
            let mut pending = [
                Stamp {
                    log: &log,
                    digit: 1,
                },
                Stamp {
                    log: &log,
                    digit: 2,
                },
                Stamp {
                    log: &log,
                    digit: 3,
                },
            ]
            .into_iter();
            drop(pending.next().unwrap());
            assert!(log.get() == 1);
        }
        assert!(log.get() == 123);
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn partial() {
            super::partial_claim();
        }
        #[test]
        fn nested() {
            super::nested_claim();
        }
        #[test]
        fn covering() {
            super::covering_claim();
        }
        #[test]
        fn iterator() {
            super::iterator_claim();
        }
    }

    // Body-owned scalar product storage for original-type/namespace controls, not a Drop shortcut.
    pub struct Plain {
        pub word: u16,
    }
    #[inline(never)]
    pub fn owner_probe(values: [Plain; 2]) -> [Plain; 2] {
        values
    }
    pub fn zero_claim() {
        let log = Cell::new(0);
        let values: [Stamp<'_>; 0] = [];
        drop(values);
        assert!(log.get() == 0);
    }

    #[inline(never)]
    fn symbolic_partial_trace(log: &Cell<u32>, a: u32, b: u32, c: u32) {
        let values = [
            Stamp { log, digit: a },
            Stamp { log, digit: b },
            Stamp { log, digit: c },
        ];
        let [first, ..] = values;
        drop(first);
        assert!(log.get() == a);
    }
    #[inline(never)]
    fn symbolic_nested_trace(log: &Cell<u32>, a: u32, b: u32, c: u32, d: u32) {
        let values = [
            [Stamp { log, digit: a }, Stamp { log, digit: b }],
            [Stamp { log, digit: c }, Stamp { log, digit: d }],
        ];
        let [[first, ..], ..] = values;
        drop(first);
        assert!(log.get() == a);
    }
    #[inline(never)]
    fn symbolic_covering_trace(log: &Cell<u32>, a: u32, b: u32, c: u32, d: u32) {
        let mut values = [Stamp { log, digit: a }, Stamp { log, digit: b }];
        let [first, ..] = values;
        drop(first);
        values = [Stamp { log, digit: c }, Stamp { log, digit: d }];
        assert!(log.get() == a.wrapping_mul(10).wrapping_add(b));
        drop(values);
    }
    fn append_digit(previous: u32, digit: u32) -> u32 {
        previous.wrapping_mul(10).wrapping_add(digit)
    }
    pub fn symbolic_partial(a: u32, b: u32, c: u32) {
        let log = Cell::new(0);
        symbolic_partial_trace(&log, a, b, c);
        assert!(log.get() == append_digit(append_digit(a, b), c));
    }
    pub fn symbolic_partial_wrong(a: u32, b: u32, c: u32) {
        let log = Cell::new(0);
        symbolic_partial_trace(&log, a, b, c);
        assert!(log.get() == append_digit(append_digit(a, c), b));
    }
    pub fn symbolic_nested(a: u32, b: u32, c: u32, d: u32) {
        let log = Cell::new(0);
        symbolic_nested_trace(&log, a, b, c, d);
        assert!(log.get() == append_digit(append_digit(append_digit(a, c), d), b));
    }
    pub fn symbolic_nested_wrong(a: u32, b: u32, c: u32, d: u32) {
        let log = Cell::new(0);
        symbolic_nested_trace(&log, a, b, c, d);
        assert!(log.get() == append_digit(append_digit(append_digit(a, d), c), b));
    }
    pub fn symbolic_covering(a: u32, b: u32, c: u32, d: u32) {
        let log = Cell::new(0);
        symbolic_covering_trace(&log, a, b, c, d);
        assert!(log.get() == append_digit(append_digit(append_digit(a, b), c), d));
    }
    pub fn symbolic_covering_wrong(a: u32, b: u32, c: u32, d: u32) {
        let log = Cell::new(0);
        symbolic_covering_trace(&log, a, b, c, d);
        assert!(log.get() == append_digit(append_digit(append_digit(a, b), d), c));
    }

    #[cfg(test)]
    mod symbolic_positive_native {
        #[test]
        fn positive() {
            for (a, b, c, d) in [
                (1, 2, 3, 4),
                (u32::MAX, 0, 1, u32::MAX),
                (17, 11, u32::MAX, 23),
            ] {
                super::symbolic_partial(a, b, c);
                super::symbolic_nested(a, b, c, d);
                super::symbolic_covering(a, b, c, d);
            }
        }
    }

    #[cfg(test)]
    mod counterexamples {
        #[test]
        fn wrong() {
            super::partial_wrong();
        }
    }

    #[cfg(test)]
    mod symbolic_counterexamples {
        #[test]
        fn partial_wrong() {
            super::symbolic_partial_wrong(1, 2, 3);
        }
        #[test]
        fn nested_wrong() {
            super::symbolic_nested_wrong(1, 2, 3, 4);
        }
        #[test]
        fn covering_wrong() {
            super::symbolic_covering_wrong(1, 2, 3, 4);
        }
    }
}

// Signed readonly niches: retain exact standalone helper bodies and caller claims.
pub mod signed_nonzero_niche_survey {
    use core::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroIsize};

    #[inline(never)]
    pub fn actual_get8(value: NonZeroI8) -> i8 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_get16(value: NonZeroI16) -> i16 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_get32(value: NonZeroI32) -> i32 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal16(left: Option<NonZeroI16>, right: Option<NonZeroI16>) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member16(values: &[Option<NonZeroI16>], needle: Option<NonZeroI16>) -> bool {
        values.contains(&needle)
    }

    pub fn correlated8(values: &[Option<NonZeroI8>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get8(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn correlated16(values: &[Option<NonZeroI16>], index: usize) {
        if index < values.len() {
            if let Some(value) = values[index] {
                assert!(actual_get16(value) != 0);
                if value.get() < 0 {
                    assert!(value.get() <= -1);
                } else {
                    assert!(value.get() >= 1);
                }
            }
        }
    }
    pub fn correlated32(values: &[Option<NonZeroI32>], index: usize) {
        if index < values.len() {
            if let Some(value) = values[index] {
                assert!(actual_get32(value) != 0);
                if value.get() < 0 {
                    assert!(value.get() <= -1);
                }
            }
        }
    }
    pub fn same16(values: &[Option<NonZeroI16>], index: usize) {
        if index < values.len() {
            assert!(actual_equal16(values[index], values[index]));
        }
    }
    pub fn minimums() {
        let values = [NonZeroI8::new(i8::MIN), NonZeroI8::new(-1), None];
        assert!(actual_get8(values[0].unwrap()) == i8::MIN);
        assert!(actual_get8(values[1].unwrap()) == -1);
        assert!(values[2].is_none());
        assert!(actual_get16(NonZeroI16::new(i16::MIN).unwrap()) == i16::MIN);
        assert!(actual_get32(NonZeroI32::new(i32::MIN).unwrap()) == i32::MIN);
    }
    pub fn fixed_array(values: &[Option<NonZeroI32>; 2]) {
        if let Some(value) = values[1] {
            assert!(actual_get32(value) != 0);
        }
    }
    pub fn contains_selected(values: &[Option<NonZeroI16>], index: usize) {
        if index < values.len() {
            assert!(actual_member16(values, values[index]));
        }
    }
    pub fn wrong_nonnegative(values: &[Option<NonZeroI16>], index: usize) {
        if index < values.len() {
            if let Some(value) = values[index] {
                assert!(actual_get16(value) > 0);
            }
        }
    }
    pub fn wrong_zero(values: &[Option<NonZeroI8>], index: usize) {
        if index < values.len() {
            if let Some(value) = values[index] {
                assert!(actual_get8(value) == 0);
            }
        }
    }
    pub fn wrong_minimum() {
        assert!(actual_get32(NonZeroI32::new(i32::MIN).unwrap()) == i32::MAX);
    }

    #[derive(Clone, Copy)]
    pub enum SignedLocal {
        Empty,
        Value(NonZeroI16),
    }
    pub fn local_enum_unknown(values: &[SignedLocal], index: usize) {
        if index < values.len() {
            if let SignedLocal::Value(value) = values[index] {
                assert!(value.get() != 0);
            }
        }
    }
    pub fn mutable_unknown(values: &mut [Option<NonZeroI16>]) {
        if !values.is_empty() {
            values[0] = None;
        }
    }
    pub fn pointer_unknown(values: &[Option<NonZeroIsize>], index: usize) {
        if index < values.len() {
            assert!(values[index].is_none() || values[index].is_some());
        }
    }
    pub fn width64_unknown(values: &[Option<NonZeroI64>], index: usize) {
        if index < values.len() {
            assert!(values[index].is_none() || values[index].is_some());
        }
    }
    pub fn signed_byte_unknown(values: &[Option<NonZeroI8>], index: usize) {
        if index < values.len() {
            assert!(values.contains(&values[index]));
        }
    }

    #[cfg(test)]
    mod native {
        #[test]
        fn actual_signed_helpers_preserve_negative_claims() {
            let a = [
                None,
                NonZeroI8::new(i8::MIN),
                NonZeroI8::new(-1),
                NonZeroI8::new(1),
            ];
            let b = [
                None,
                NonZeroI16::new(i16::MIN),
                NonZeroI16::new(-1),
                NonZeroI16::new(1),
            ];
            let c = [
                None,
                NonZeroI32::new(i32::MIN),
                NonZeroI32::new(-1),
                NonZeroI32::new(1),
            ];
            for i in 0..4 {
                super::correlated8(&a, i);
                super::correlated16(&b, i);
                super::correlated32(&c, i);
                super::same16(&b, i);
                super::contains_selected(&b, i);
            }
            super::fixed_array(&[NonZeroI32::new(-1), NonZeroI32::new(i32::MIN)]);
            super::minimums();
        }
        use core::num::{NonZeroI8, NonZeroI16, NonZeroI32};
    }
}

mod full_integer_nonzero_niche_survey {

    #[inline(never)]
    pub fn actual_get_u64(value: core::num::NonZeroU64) -> u64 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_u64(
        left: Option<core::num::NonZeroU64>,
        right: Option<core::num::NonZeroU64>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_u64(
        values: &[Option<core::num::NonZeroU64>],
        needle: Option<core::num::NonZeroU64>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_u64(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_u64(value) == 0);
        }
    }
    pub fn same_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_u64(values[index], values[index]));
        }
    }
    pub fn member_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
        if index < values.len() {
            assert!(actual_member_u64(values, values[index]));
        }
    }

    #[inline(never)]
    pub fn actual_get_u128(value: core::num::NonZeroU128) -> u128 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_u128(
        left: Option<core::num::NonZeroU128>,
        right: Option<core::num::NonZeroU128>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_u128(
        values: &[Option<core::num::NonZeroU128>],
        needle: Option<core::num::NonZeroU128>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_u128(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_u128(value) == 0);
        }
    }
    pub fn same_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_u128(values[index], values[index]));
        }
    }
    pub fn member_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
        if index < values.len() {
            assert!(actual_member_u128(values, values[index]));
        }
    }

    #[inline(never)]
    pub fn actual_get_usize(value: core::num::NonZeroUsize) -> usize {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_usize(
        left: Option<core::num::NonZeroUsize>,
        right: Option<core::num::NonZeroUsize>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_usize(
        values: &[Option<core::num::NonZeroUsize>],
        needle: Option<core::num::NonZeroUsize>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_usize(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_usize(value) == 0);
        }
    }
    pub fn same_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_usize(values[index], values[index]));
        }
    }
    pub fn member_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
        if index < values.len() {
            assert!(actual_member_usize(values, values[index]));
        }
    }

    #[inline(never)]
    pub fn actual_get_i64(value: core::num::NonZeroI64) -> i64 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_i64(
        left: Option<core::num::NonZeroI64>,
        right: Option<core::num::NonZeroI64>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_i64(
        values: &[Option<core::num::NonZeroI64>],
        needle: Option<core::num::NonZeroI64>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_i64(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_i64(value) == 0);
        }
    }
    pub fn same_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_i64(values[index], values[index]));
        }
    }
    pub fn member_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
        if index < values.len() {
            assert!(actual_member_i64(values, values[index]));
        }
    }

    #[inline(never)]
    pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_i128(
        left: Option<core::num::NonZeroI128>,
        right: Option<core::num::NonZeroI128>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_i128(
        values: &[Option<core::num::NonZeroI128>],
        needle: Option<core::num::NonZeroI128>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_i128(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_i128(value) == 0);
        }
    }
    pub fn same_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_i128(values[index], values[index]));
        }
    }
    pub fn member_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
        if index < values.len() {
            assert!(actual_member_i128(values, values[index]));
        }
    }

    #[inline(never)]
    pub fn actual_get_isize(value: core::num::NonZeroIsize) -> isize {
        value.get()
    }
    #[inline(never)]
    pub fn actual_equal_isize(
        left: Option<core::num::NonZeroIsize>,
        right: Option<core::num::NonZeroIsize>,
    ) -> bool {
        left == right
    }
    #[inline(never)]
    pub fn actual_member_isize(
        values: &[Option<core::num::NonZeroIsize>],
        needle: Option<core::num::NonZeroIsize>,
    ) -> bool {
        values.contains(&needle)
    }
    pub fn niche_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
        if index < values.len() {
            let first = values[index];
            if let Some(value) = first {
                assert!(actual_get_isize(value) != 0);
                assert!(values[index].is_some());
            } else {
                assert!(values[index].is_none());
            }
        }
    }
    pub fn wrong_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            assert!(actual_get_isize(value) == 0);
        }
    }
    pub fn same_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
        if index < values.len() {
            assert!(actual_equal_isize(values[index], values[index]));
        }
    }
    pub fn member_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
        if index < values.len() {
            assert!(actual_member_isize(values, values[index]));
        }
    }

    pub fn extremes(values: &[Option<core::num::NonZeroI128>], index: usize) {
        if index < values.len()
            && let Some(value) = values[index]
        {
            let value = actual_get_i128(value);
            if value == i128::MIN {
                assert!(value as u128 == (1_u128 << 127));
            }
            if value == i128::MAX {
                assert!(value as u128 == (u128::MAX >> 1));
            }
        }
    }
    #[derive(Clone, Copy)]
    pub enum LocalWide {
        Empty,
        Word(core::num::NonZeroU64),
    }
    pub fn local_unknown(values: &[LocalWide], index: usize) {
        if index < values.len()
            && let LocalWide::Word(value) = values[index]
        {
            assert!(value.get() != 0);
        }
    }
    pub fn mutable_unknown(values: &mut [Option<core::num::NonZeroU128>], index: usize) {
        if index < values.len() {
            assert!(values[index].is_some() || values[index].is_none());
        }
    }
    pub fn pointer_unknown(values: &[Option<&u128>], index: usize) {
        if index < values.len() {
            assert!(values[index].is_some() || values[index].is_none());
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn actual_integer_helpers_keep_original_claims() {
            let mut values = [None, None];
            for number in [1, u64::MAX] {
                values[1] = core::num::NonZeroU64::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_u64(&values, index);
                    super::same_u64(&values, index);
                    super::member_u64(&values, index);
                }
            }
            let mut values = [None, None];
            for number in [1, u128::MAX] {
                values[1] = core::num::NonZeroU128::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_u128(&values, index);
                    super::same_u128(&values, index);
                    super::member_u128(&values, index);
                }
            }
            let mut values = [None, None];
            for number in [1, usize::MAX] {
                values[1] = core::num::NonZeroUsize::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_usize(&values, index);
                    super::same_usize(&values, index);
                    super::member_usize(&values, index);
                }
            }
            let mut values = [None, None];
            for number in [i64::MIN, -1, 1, i64::MAX] {
                values[1] = core::num::NonZeroI64::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_i64(&values, index);
                    super::same_i64(&values, index);
                    super::member_i64(&values, index);
                }
            }
            let mut values = [None, None];
            for number in [i128::MIN, -1, 1, i128::MAX] {
                values[1] = core::num::NonZeroI128::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_i128(&values, index);
                    super::extremes(&values, index);
                    super::same_i128(&values, index);
                    super::member_i128(&values, index);
                }
            }
            let mut values = [None, None];
            for number in [isize::MIN, -1, 1, isize::MAX] {
                values[1] = core::num::NonZeroIsize::new(number);
                for index in [0, 1, 2, usize::MAX] {
                    super::niche_isize(&values, index);
                    super::same_isize(&values, index);
                    super::member_isize(&values, index);
                }
            }
        }
    }
}

mod drop_shared_projection_survey {

    pub struct Dropped {
        pub word: u16,
        pub guard: u16,
        pub flag: bool,
        pub character: char,
        pub number: i32,
        pub floating: f32,
    }
    impl Drop for Dropped {
        fn drop(&mut self) {
            assert!(self.guard == 7);
        }
    }
    fn item(word: u16, flag: bool, character: char, number: i32, floating: f32) -> Dropped {
        Dropped {
            word,
            guard: 7,
            flag,
            character,
            number,
            floating,
        }
    }
    #[inline(never)]
    pub fn actual_word(value: &u16) -> u16 {
        *value
    }
    #[inline(never)]
    pub fn borrowed(index: usize) {
        let values = [
            item(3, false, 'a', -7, -0.0),
            item(7, true, '\u{10ffff}', i32::MIN, 0.0),
        ];
        if index < 2 {
            let selected = &values[index];
            assert!(actual_word(&selected.word) == if index == 0 { 3 } else { 7 });
        }
    }
    pub fn direct(index: usize) {
        let values = [
            item(3, false, 'a', -7, -0.0),
            item(7, true, '\u{10ffff}', i32::MIN, 0.0),
        ];
        if index < 2 {
            assert!(values[index].word == if index == 0 { 3 } else { 7 });
        }
    }
    pub fn nested(index: usize) {
        let values = [
            [item(3, false, 'a', -7, -0.0)],
            [item(7, true, 'z', -9, 0.0)],
        ];
        if index < 2 {
            let selected = &values[index];
            assert!(actual_word(&selected[0].word) == if index == 0 { 3 } else { 7 });
        }
    }
    pub fn scalar_codecs(index: usize) {
        let values = [
            item(3, false, 'a', -7, -0.0),
            item(7, true, '\u{10ffff}', i32::MIN, 0.0),
        ];
        if index < 2 {
            let selected = &values[index];
            assert!(selected.flag == (index == 1));
            assert!(selected.character == if index == 0 { 'a' } else { '\u{10ffff}' });
            assert!(selected.number == if index == 0 { -7 } else { i32::MIN });
            assert!(selected.floating.to_bits() == if index == 0 { 0x8000_0000 } else { 0 });
        }
    }
    pub fn wrong(index: usize) {
        let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        if index < 2 {
            let selected = &values[index];
            assert!(actual_word(&selected.word) == if index == 0 { 7 } else { 3 });
        }
    }
    pub fn unguarded(index: usize) {
        let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        assert!(values[index].word != 0);
    }
    #[inline(never)]
    pub fn whole_accessor(value: &Dropped) -> u16 {
        value.word
    }
    pub fn whole_receiver_unknown(index: usize) {
        let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        if index < 2 {
            assert!(whole_accessor(&values[index]) != 0);
        }
    }
    #[inline(never)]
    pub fn actual_store(value: &mut u16) {
        *value = 19;
    }
    pub fn mutable_unknown(index: usize) {
        let mut values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        if index < 2 {
            actual_store(&mut values[index].word);
            assert!(values[index].word == 19);
        }
    }
    #[inline(never)]
    pub fn pointer_observer(value: *const u16) -> bool {
        value.is_null()
    }
    pub fn raw_unknown(index: usize) {
        let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        if index < 2 {
            let selected = &raw const values[index].word;
            assert!(!pointer_observer(selected));
        }
    }
    pub struct Probe {
        pub word: u16,
        pub guard: u16,
    }
    impl Drop for Probe {
        fn drop(&mut self) {
            assert!(self.guard == 7);
        }
    }
    #[inline(never)]
    pub fn probe_borrow(values: [Probe; 2], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(actual_word(&selected.word) != 0);
        }
    }
    #[cfg(external_control)]
    pub fn missing_accessor(index: usize) {
        let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
        if index < 2 {
            assert!(drop_observer_dependency::observe(&values[index].word) != 0);
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn genuine_borrows_observe_fields_and_execute_destructors() {
            for index in [0, 1, 2, usize::MAX] {
                super::borrowed(index);
                super::direct(index);
                super::nested(index);
                super::scalar_codecs(index);
            }
        }
    }

    #[inline(never)]
    pub fn activation_seed(word: u16) -> u16 {
        word
    }

    pub mod fieldless_drop {
        pub struct Fieldless;
        #[cfg(not(fieldless_missing))]
        #[inline(never)]
        pub fn fieldless_tag() -> u16 {
            7
        }
        #[cfg(fieldless_missing)]
        #[inline(never)]
        pub fn fieldless_tag() -> u16 {
            drop_observer_dependency::observe(&7)
        }
        impl Drop for Fieldless {
            fn drop(&mut self) {
                assert!(fieldless_tag() == 7);
            }
        }
        pub fn incoming(values: [Fieldless; 2], index: usize) {
            if index < 2 {
                let _selected = &values[index];
                assert!(index < 2);
            }
        }
        pub fn local(index: usize) {
            let values = [Fieldless, Fieldless];
            if index < 2 {
                let _selected = &values[index];
                assert!(index < 2);
            }
        }
        pub fn wrong(values: [Fieldless; 2], index: usize) {
            if index < 2 {
                let _selected = &values[index];
                assert!(index >= 2);
            }
        }
        pub fn unguarded(values: [Fieldless; 2], index: usize) {
            let _selected = &values[index];
            assert!(index < 2);
        }
        #[inline(never)]
        pub fn whole(_value: &Fieldless) -> u16 {
            7
        }
        pub fn whole_unknown(values: [Fieldless; 2], index: usize) {
            if index < 2 {
                assert!(whole(&values[index]) == 7);
            }
        }
        #[cfg(test)]
        mod native {
            #[test]
            fn fieldless_borrows_execute_nonempty_destructors() {
                for index in [0, 1, 2, usize::MAX] {
                    super::local(index);
                    super::incoming([super::Fieldless, super::Fieldless], index);
                }
            }
        }
    }
}


pub mod deeper_mutable_survey {

    #[inline(never)]
    pub fn payload_u16(word: u16) -> u16 {
        word
    }
    #[inline(never)]
    pub fn leaf_u16(values: &mut [u16], index: usize, word: u16) {
        values[index] = payload_u16(word);
    }
    #[inline(never)]
    pub fn level1_u16(values: &mut [u16], index: usize, word: u16) {
        leaf_u16(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_u16(values: &mut [u16], index: usize, word: u16) {
        level1_u16(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_u16(values: &mut [u16], index: usize, word: u16) {
        level2_u16(&mut *(&mut *values), index, word);
    }
    pub fn claim_u16(values: &mut [u16], index: usize, word: u16) {
        if index < values.len() {
            let old_length = values.len();
            level3_u16(values, index, word);
            assert!(values[index] == word);
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_u16(values: &mut [u16], index: usize, word: u16) {
        if index < values.len() {
            level3_u16(values, index, word);
            assert!(values[index] != word);
        }
    }

    #[inline(never)]
    pub fn payload_i32(word: i32) -> i32 {
        word
    }
    #[inline(never)]
    pub fn leaf_i32(values: &mut [i32], index: usize, word: i32) {
        values[index] = payload_i32(word);
    }
    #[inline(never)]
    pub fn level1_i32(values: &mut [i32], index: usize, word: i32) {
        leaf_i32(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_i32(values: &mut [i32], index: usize, word: i32) {
        level1_i32(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_i32(values: &mut [i32], index: usize, word: i32) {
        level2_i32(&mut *(&mut *values), index, word);
    }
    pub fn claim_i32(values: &mut [i32], index: usize, word: i32) {
        if index < values.len() {
            let old_length = values.len();
            level3_i32(values, index, word);
            assert!(values[index] == word);
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_i32(values: &mut [i32], index: usize, word: i32) {
        if index < values.len() {
            level3_i32(values, index, word);
            assert!(values[index] != word);
        }
    }

    #[inline(never)]
    pub fn payload_bool(word: bool) -> bool {
        word
    }
    #[inline(never)]
    pub fn leaf_bool(values: &mut [bool], index: usize, word: bool) {
        values[index] = payload_bool(word);
    }
    #[inline(never)]
    pub fn level1_bool(values: &mut [bool], index: usize, word: bool) {
        leaf_bool(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_bool(values: &mut [bool], index: usize, word: bool) {
        level1_bool(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_bool(values: &mut [bool], index: usize, word: bool) {
        level2_bool(&mut *(&mut *values), index, word);
    }
    pub fn claim_bool(values: &mut [bool], index: usize, word: bool) {
        if index < values.len() {
            let old_length = values.len();
            level3_bool(values, index, word);
            assert!(values[index] == word);
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_bool(values: &mut [bool], index: usize, word: bool) {
        if index < values.len() {
            level3_bool(values, index, word);
            assert!(values[index] != word);
        }
    }

    #[inline(never)]
    pub fn payload_char(word: char) -> char {
        word
    }
    #[inline(never)]
    pub fn leaf_char(values: &mut [char], index: usize, word: char) {
        values[index] = payload_char(word);
    }
    #[inline(never)]
    pub fn level1_char(values: &mut [char], index: usize, word: char) {
        leaf_char(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_char(values: &mut [char], index: usize, word: char) {
        level1_char(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_char(values: &mut [char], index: usize, word: char) {
        level2_char(&mut *(&mut *values), index, word);
    }
    pub fn claim_char(values: &mut [char], index: usize, word: char) {
        if index < values.len() {
            let old_length = values.len();
            level3_char(values, index, word);
            assert!(values[index] == word);
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_char(values: &mut [char], index: usize, word: char) {
        if index < values.len() {
            level3_char(values, index, word);
            assert!(values[index] != word);
        }
    }

    #[inline(never)]
    pub fn payload_f32(word: f32) -> f32 {
        word
    }
    #[inline(never)]
    pub fn leaf_f32(values: &mut [f32], index: usize, word: f32) {
        values[index] = payload_f32(word);
    }
    #[inline(never)]
    pub fn level1_f32(values: &mut [f32], index: usize, word: f32) {
        leaf_f32(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_f32(values: &mut [f32], index: usize, word: f32) {
        level1_f32(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_f32(values: &mut [f32], index: usize, word: f32) {
        level2_f32(&mut *(&mut *values), index, word);
    }
    pub fn claim_f32(values: &mut [f32], index: usize, word: f32) {
        if index < values.len() {
            let old_length = values.len();
            level3_f32(values, index, word);
            assert!(values[index].to_bits() == word.to_bits());
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_f32(values: &mut [f32], index: usize, word: f32) {
        if index < values.len() {
            level3_f32(values, index, word);
            assert!(values[index].to_bits() != word.to_bits());
        }
    }

    #[inline(never)]
    pub fn payload_f64(word: f64) -> f64 {
        word
    }
    #[inline(never)]
    pub fn leaf_f64(values: &mut [f64], index: usize, word: f64) {
        values[index] = payload_f64(word);
    }
    #[inline(never)]
    pub fn level1_f64(values: &mut [f64], index: usize, word: f64) {
        leaf_f64(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level2_f64(values: &mut [f64], index: usize, word: f64) {
        level1_f64(&mut *(&mut *values), index, word);
    }
    #[inline(never)]
    pub fn level3_f64(values: &mut [f64], index: usize, word: f64) {
        level2_f64(&mut *(&mut *values), index, word);
    }
    pub fn claim_f64(values: &mut [f64], index: usize, word: f64) {
        if index < values.len() {
            let old_length = values.len();
            level3_f64(values, index, word);
            assert!(values[index].to_bits() == word.to_bits());
            assert!(values.len() == old_length);
        }
    }
    pub fn wrong_f64(values: &mut [f64], index: usize, word: f64) {
        if index < values.len() {
            level3_f64(values, index, word);
            assert!(values[index].to_bits() != word.to_bits());
        }
    }

    pub struct Associated;
    impl Associated {
        #[inline(never)]
        pub fn payload(word: u16) -> u16 {
            word
        }
        #[inline(never)]
        pub fn leaf(values: &mut [u16], index: usize, word: u16) {
            values[index] = Self::payload(word);
        }
        #[inline(never)]
        pub fn level1(values: &mut [u16], index: usize, word: u16) {
            Self::leaf(&mut *values, index, word);
        }
        #[inline(never)]
        pub fn level2(values: &mut [u16], index: usize, word: u16) {
            Self::level1(&mut *values, index, word);
        }
        #[inline(never)]
        pub fn level3(values: &mut [u16], index: usize, word: u16) {
            Self::level2(&mut *values, index, word);
        }
    }
    pub fn claim_associated(values: &mut [u16], index: usize, word: u16) {
        if index < values.len() {
            Associated::level3(values, index, word);
            assert!(values[index] == word);
        }
    }
    pub fn wrong_associated(values: &mut [u16], index: usize, word: u16) {
        if index < values.len() {
            Associated::level3(values, index, word);
            assert!(values[index] != word);
        }
    }
    pub fn sibling_retention(values: &mut [i32], word: i32) {
        if values.len() > 1 {
            let sibling = values[1];
            level3_i32(values, 0, word);
            assert!(values[0] == word);
            assert!(values[1] == sibling);
        }
    }
    pub fn unchecked_bounds(values: &mut [u16], index: usize, word: u16) {
        level3_u16(values, index, word);
    }
    pub fn interval_unknown(values: &mut [u16], start: usize, end: usize, word: u16) {
        if start <= end && end <= values.len() && start < end {
            level3_u16(&mut values[start..end], 0, word);
        }
    }
    #[inline(never)]
    pub fn product_leaf(values: &mut [[u16; 2]], word: u16) {
        values[0][0] = word;
    }
    #[inline(never)]
    pub fn product_outer(values: &mut [[u16; 2]], word: u16) {
        product_leaf(values, word);
    }
    pub fn product_unknown(values: &mut [[u16; 2]], word: u16) {
        if !values.is_empty() {
            product_outer(values, word);
        }
    }
    // A compiler probe enters this actual call and follows all normal Frames/Returns.
    pub fn probe_root(values: &mut [u16]) {
        probe_level3(values);
    }
    #[inline(never)]
    pub fn probe_level3(values: &mut [u16]) {
        probe_level2(values);
    }
    #[inline(never)]
    pub fn probe_level2(values: &mut [u16]) {
        probe_level1(values);
    }
    #[inline(never)]
    pub fn probe_level1(values: &mut [u16]) {
        probe_leaf(values);
    }
    #[inline(never)]
    pub fn probe_leaf(values: &mut [u16]) {
        if !values.is_empty() {
            values[0] = 37;
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn actual_deep_helpers_preserve_original_claims() {
            for index in [0, 1, 2, usize::MAX] {
                super::claim_u16(&mut [0; 2], index, 37);
            }
            for index in [0, 1, 2, usize::MAX] {
                super::claim_i32(&mut [0; 2], index, -19);
            }
            for index in [0, 1, 2, usize::MAX] {
                super::claim_bool(&mut [false; 2], index, true);
            }
            for index in [0, 1, 2, usize::MAX] {
                super::claim_char(&mut ['\0'; 2], index, 'λ');
            }
            for index in [0, 1, 2, usize::MAX] {
                super::claim_f32(&mut [0.0_f32; 2], index, f32::from_bits(0x7fc0_1234));
            }
            for index in [0, 1, 2, usize::MAX] {
                super::claim_f64(
                    &mut [0.0_f64; 2],
                    index,
                    f64::from_bits(0x7ff8_0000_0000_1234),
                );
            }
            super::claim_associated(&mut [0; 2], 1, 37);
            super::sibling_retention(&mut [1, 2, 3], -19);
        }
    }
}


pub mod incoming_drop_survey {

    pub struct Record {
        pub word: u16,
        pub guard: u16,
    }
    #[inline(never)]
    pub fn release_guard(value: u16) -> u16 {
        value
    }
    impl Drop for Record {
        fn drop(&mut self) {
            assert!(release_guard(self.guard) == self.guard);
        }
    }
    #[inline(never)]
    pub fn accessor(value: &u16) -> u16 {
        *value
    }
    pub fn borrowed(values: [Record; 2], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(accessor(&selected.word) == selected.word);
            assert!(accessor(&selected.guard) == selected.guard);
        }
    }
    pub fn direct(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(accessor(&values[index].word) == values[index].word);
        }
    }
    pub fn nested(values: [[Record; 1]; 2], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(accessor(&selected[0].word) == selected[0].word);
        }
    }
    pub fn wrong(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(accessor(&values[index].word) == (values[index].word ^ 1));
        }
    }
    pub fn unguarded(values: [Record; 2], index: usize) {
        assert!(accessor(&values[index].word) == values[index].word);
    }
    #[inline(never)]
    pub fn whole(value: &Record) -> u16 {
        value.word
    }
    pub fn whole_unknown(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(whole(&values[index]) == values[index].word);
        }
    }
    #[inline(never)]
    pub fn store(value: &mut u16) {
        *value = 19;
    }
    pub fn mutable_unknown(mut values: [Record; 2], index: usize) {
        if index < 2 {
            store(&mut values[index].word);
            assert!(values[index].word == 19);
        }
    }
    #[inline(never)]
    pub fn pointer_is_null(value: *const u16) -> bool {
        value.is_null()
    }
    pub fn raw_unknown(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(!pointer_is_null(&raw const values[index].word));
        }
    }
    pub fn reserved(
        values: [Record; 64],
        _second: [Record; 64],
        _third: [Record; 64],
        index: usize,
    ) {
        if index < 64 {
            let selected = &values[index];
            assert!(accessor(&selected.word) == selected.word);
        }
    }

    pub fn deferred(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(accessor(&selected.word) == selected.word);
        }
    }


    pub fn reserved_constant(values: [Record; 64], _second: [Record; 64], _third: [Record; 64]) {
        assert!(accessor(&values[1].word) == values[1].word);
    }
    pub fn reserved_wrong(values: [Record; 64], _second: [Record; 64], _third: [Record; 64]) {
        assert!(accessor(&values[1].word) == (values[1].word ^ 1));
    }
    pub fn deferred_wrong(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
        if index < 2 {
            assert!(accessor(&values[index].word) == (values[index].word ^ 1));
        }
    }
    pub fn deferred_unguarded(values: [Record; 2], _pressure: [[u16; 2]; 128], index: usize) {
        assert!(accessor(&values[index].word) == values[index].word);
    }


    pub struct ScalarRecord {
        pub flag: bool,
        pub signed: i32,
        pub float: f32,
        pub wide: f64,
    }
    #[inline(never)]
    pub fn signed_guard(value: i32) -> i32 { value }
    impl Drop for ScalarRecord {
        fn drop(&mut self) { assert!(signed_guard(self.signed) == self.signed); }
    }
    #[inline(never)]
    pub fn bool_accessor(value: &bool) -> bool { *value }
    #[inline(never)]
    pub fn signed_accessor(value: &i32) -> i32 { *value }
    #[inline(never)]
    pub fn float_accessor(value: &f32) -> f32 { *value }
    #[inline(never)]
    pub fn wide_accessor(value: &f64) -> f64 { *value }
    pub fn scalar_codecs(values: [ScalarRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(bool_accessor(&selected.flag) == selected.flag);
            assert!(signed_accessor(&selected.signed) == selected.signed);
            assert!(float_accessor(&selected.float).to_bits() == selected.float.to_bits());
            assert!(wide_accessor(&selected.wide).to_bits() == selected.wide.to_bits());
        }
    }
    pub fn scalar_wrong(values: [ScalarRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(float_accessor(&selected.float).to_bits() == (selected.float.to_bits() ^ 1));
        }
    }
    pub struct CharRecord { pub scalar: char }
    impl Drop for CharRecord {
        fn drop(&mut self) { assert!(self.scalar <= char::MAX); }
    }
    pub fn char_eager_pressure(values: [CharRecord; 2], _pressure: [[u16; 2]; 128], index: usize) {
        if index < 2 { assert!(values[index].scalar <= char::MAX); }
    }
    #[cfg(test)]
    mod native_controls {
        #[test]
        fn actual_accessor_and_destructor() {
            let record = super::Record { word: 3, guard: 7 };
            assert!(super::accessor(&record.word) == 3);
        }
    }
}


mod array_iterator_constructors_survey {

    pub struct Stamp(pub u16);
    impl Drop for Stamp {
        fn drop(&mut self) {}
    }

    pub fn constructor(input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
        input.into_iter()
    }

    pub fn constructor_move(a: Stamp, b: Stamp) -> core::array::IntoIter<Stamp, 2> {
        [a, b].into_iter()
    }

    pub fn constructor_wrong(flag: bool, input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
        assert!(!flag);
        input.into_iter()
    }

    pub fn remaining_drop_unknown(input: [Stamp; 2]) {
        drop(input.into_iter());
    }

    pub fn next_unknown(input: [Stamp; 2]) {
        let mut iterator = input.into_iter();
        let _ = iterator.next();
    }

    fn pass(iterator: core::array::IntoIter<Stamp, 2>) -> core::array::IntoIter<Stamp, 2> {
        iterator
    }

    pub fn helper_argument_unknown(input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
        pass(input.into_iter())
    }
}


mod shared_drop_calls_survey {

    pub struct Record {
        pub word: u16,
        pub guard: u16,
    }
    #[inline(never)]
    pub fn release_guard(value: u16) -> u16 {
        value
    }
    impl Drop for Record {
        fn drop(&mut self) {
            assert!(release_guard(self.guard) == self.guard);
        }
    }
    #[inline(never)]
    pub fn word(value: &u16) -> u16 {
        *value
    }
    #[inline(never)]
    pub fn observe(value: &Record) -> u16 {
        word(&value.word)
    }
    pub fn claim(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(observe(&values[index]) == values[index].word);
        }
    }
    pub fn wrong(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(observe(&values[index]) == (values[index].word ^ 1));
        }
    }
    pub fn unguarded(values: [Record; 2], index: usize) {
        assert!(observe(&values[index]) == values[index].word);
    }
    #[inline(never)]
    pub fn forward(value: &Record) -> u16 {
        observe(&*value)
    }
    pub fn forwarded(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(forward(&values[index]) == values[index].word);
        }
    }
    pub fn lazy(values: [Record; 64], _second: [Record; 64], _third: [Record; 64], index: usize) {
        if index < 64 {
            assert!(observe(&values[index]) == values[index].word);
        }
    }
    #[inline(never)]
    pub fn store(value: &mut Record) -> u16 {
        value.word = 19;
        value.word
    }
    pub fn mutable_unknown(mut values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(store(&mut values[index]) == 19);
        }
    }
    #[inline(never)]
    pub fn pointer_is_null(value: *const Record) -> bool {
        value.is_null()
    }
    pub fn raw_unknown(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(!pointer_is_null(&raw const values[index]));
        }
    }
    #[inline(never)]
    pub fn product(value: &Record) -> [u16; 2] {
        [value.word, value.guard]
    }
    pub fn product_unknown(values: [Record; 2], index: usize) {
        if index < 2 {
            assert!(product(&values[index])[0] == values[index].word);
        }
    }
    pub struct Other {
        pub word: u16,
        pub guard: u16,
    }
    impl Drop for Other {
        fn drop(&mut self) {
            assert!(release_guard(self.guard) == self.guard);
        }
    }
    #[inline(never)]
    pub fn other_observe(value: &Other) -> u16 {
        value.word
    }

    pub struct Codecs {
        pub guard: u16,
        pub flag: bool,
        pub letter: char,
        pub signed: i32,
        pub float: f32,
        pub wide: f64,
    }
    impl Drop for Codecs {
        fn drop(&mut self) {
            assert!(release_guard(self.guard) == self.guard);
        }
    }
    #[inline(never)]
    pub fn flag(value: &Codecs) -> bool {
        value.flag
    }
    #[inline(never)]
    pub fn letter(value: &Codecs) -> char {
        value.letter
    }
    #[inline(never)]
    pub fn signed(value: &Codecs) -> i32 {
        value.signed
    }
    #[inline(never)]
    pub fn float(value: &Codecs) -> f32 {
        value.float
    }
    #[inline(never)]
    pub fn wide(value: &Codecs) -> f64 {
        value.wide
    }
    pub fn codecs(values: [Codecs; 2], index: usize) {
        if index < 2 {
            let selected = &values[index];
            assert!(flag(selected) == selected.flag);
            assert!(letter(selected) == selected.letter);
            assert!(signed(selected) == selected.signed);
            assert!(float(selected).to_bits() == selected.float.to_bits());
            assert!(wide(selected).to_bits() == selected.wide.to_bits());
        }
    }
    #[cfg(test)]
    mod native_controls {
        #[test]
        fn actual_helper_and_destructor() {
            let value = super::Record { word: 3, guard: 7 };
            assert!(super::observe(&value) == 3);
        }
    }
}


pub mod local_integer_nonzero_niche_survey {
    #[derive(Clone, Copy)]
    pub enum WordU8 {
        Empty,
        Word(core::num::NonZeroU8),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseU8 {
        Word(core::num::NonZeroU8),
        Empty,
    }
    #[inline(never)]
    pub fn get_u8(value: core::num::NonZeroU8) -> u8 {
        value.get()
    }
    pub fn read_u8(values: &[WordU8], index: usize) {
        if index < values.len()
            && let WordU8::Word(value) = values[index]
        {
            assert!(get_u8(value) == value.get());
            assert!(get_u8(value) != 0);
        }
    }
    pub fn reverse_u8(values: &[ReverseU8], index: usize) {
        if index < values.len()
            && let ReverseU8::Word(value) = values[index]
        {
            assert!(get_u8(value) == value.get());
            assert!(get_u8(value) != 0);
        }
    }
    pub fn wrong_u8(values: &[WordU8], index: usize) {
        if index < values.len()
            && let WordU8::Word(value) = values[index]
        {
            assert!(get_u8(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordU16 {
        Empty,
        Word(core::num::NonZeroU16),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseU16 {
        Word(core::num::NonZeroU16),
        Empty,
    }
    #[inline(never)]
    pub fn get_u16(value: core::num::NonZeroU16) -> u16 {
        value.get()
    }
    pub fn read_u16(values: &[WordU16], index: usize) {
        if index < values.len()
            && let WordU16::Word(value) = values[index]
        {
            assert!(get_u16(value) == value.get());
            assert!(get_u16(value) != 0);
        }
    }
    pub fn reverse_u16(values: &[ReverseU16], index: usize) {
        if index < values.len()
            && let ReverseU16::Word(value) = values[index]
        {
            assert!(get_u16(value) == value.get());
            assert!(get_u16(value) != 0);
        }
    }
    pub fn wrong_u16(values: &[WordU16], index: usize) {
        if index < values.len()
            && let WordU16::Word(value) = values[index]
        {
            assert!(get_u16(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordU32 {
        Empty,
        Word(core::num::NonZeroU32),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseU32 {
        Word(core::num::NonZeroU32),
        Empty,
    }
    #[inline(never)]
    pub fn get_u32(value: core::num::NonZeroU32) -> u32 {
        value.get()
    }
    pub fn read_u32(values: &[WordU32], index: usize) {
        if index < values.len()
            && let WordU32::Word(value) = values[index]
        {
            assert!(get_u32(value) == value.get());
            assert!(get_u32(value) != 0);
        }
    }
    pub fn reverse_u32(values: &[ReverseU32], index: usize) {
        if index < values.len()
            && let ReverseU32::Word(value) = values[index]
        {
            assert!(get_u32(value) == value.get());
            assert!(get_u32(value) != 0);
        }
    }
    pub fn wrong_u32(values: &[WordU32], index: usize) {
        if index < values.len()
            && let WordU32::Word(value) = values[index]
        {
            assert!(get_u32(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordU64 {
        Empty,
        Word(core::num::NonZeroU64),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseU64 {
        Word(core::num::NonZeroU64),
        Empty,
    }
    #[inline(never)]
    pub fn get_u64(value: core::num::NonZeroU64) -> u64 {
        value.get()
    }
    pub fn read_u64(values: &[WordU64], index: usize) {
        if index < values.len()
            && let WordU64::Word(value) = values[index]
        {
            assert!(get_u64(value) == value.get());
            assert!(get_u64(value) != 0);
        }
    }
    pub fn reverse_u64(values: &[ReverseU64], index: usize) {
        if index < values.len()
            && let ReverseU64::Word(value) = values[index]
        {
            assert!(get_u64(value) == value.get());
            assert!(get_u64(value) != 0);
        }
    }
    pub fn wrong_u64(values: &[WordU64], index: usize) {
        if index < values.len()
            && let WordU64::Word(value) = values[index]
        {
            assert!(get_u64(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordU128 {
        Empty,
        Word(core::num::NonZeroU128),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseU128 {
        Word(core::num::NonZeroU128),
        Empty,
    }
    #[inline(never)]
    pub fn get_u128(value: core::num::NonZeroU128) -> u128 {
        value.get()
    }
    pub fn read_u128(values: &[WordU128], index: usize) {
        if index < values.len()
            && let WordU128::Word(value) = values[index]
        {
            assert!(get_u128(value) == value.get());
            assert!(get_u128(value) != 0);
        }
    }
    pub fn reverse_u128(values: &[ReverseU128], index: usize) {
        if index < values.len()
            && let ReverseU128::Word(value) = values[index]
        {
            assert!(get_u128(value) == value.get());
            assert!(get_u128(value) != 0);
        }
    }
    pub fn wrong_u128(values: &[WordU128], index: usize) {
        if index < values.len()
            && let WordU128::Word(value) = values[index]
        {
            assert!(get_u128(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordUsize {
        Empty,
        Word(core::num::NonZeroUsize),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseUsize {
        Word(core::num::NonZeroUsize),
        Empty,
    }
    #[inline(never)]
    pub fn get_usize(value: core::num::NonZeroUsize) -> usize {
        value.get()
    }
    pub fn read_usize(values: &[WordUsize], index: usize) {
        if index < values.len()
            && let WordUsize::Word(value) = values[index]
        {
            assert!(get_usize(value) == value.get());
            assert!(get_usize(value) != 0);
        }
    }
    pub fn reverse_usize(values: &[ReverseUsize], index: usize) {
        if index < values.len()
            && let ReverseUsize::Word(value) = values[index]
        {
            assert!(get_usize(value) == value.get());
            assert!(get_usize(value) != 0);
        }
    }
    pub fn wrong_usize(values: &[WordUsize], index: usize) {
        if index < values.len()
            && let WordUsize::Word(value) = values[index]
        {
            assert!(get_usize(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordI8 {
        Empty,
        Word(core::num::NonZeroI8),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseI8 {
        Word(core::num::NonZeroI8),
        Empty,
    }
    #[inline(never)]
    pub fn get_i8(value: core::num::NonZeroI8) -> i8 {
        value.get()
    }
    pub fn read_i8(values: &[WordI8], index: usize) {
        if index < values.len()
            && let WordI8::Word(value) = values[index]
        {
            assert!(get_i8(value) == value.get());
            assert!(get_i8(value) != 0);
        }
    }
    pub fn reverse_i8(values: &[ReverseI8], index: usize) {
        if index < values.len()
            && let ReverseI8::Word(value) = values[index]
        {
            assert!(get_i8(value) == value.get());
            assert!(get_i8(value) != 0);
        }
    }
    pub fn wrong_i8(values: &[WordI8], index: usize) {
        if index < values.len()
            && let WordI8::Word(value) = values[index]
        {
            assert!(get_i8(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordI16 {
        Empty,
        Word(core::num::NonZeroI16),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseI16 {
        Word(core::num::NonZeroI16),
        Empty,
    }
    #[inline(never)]
    pub fn get_i16(value: core::num::NonZeroI16) -> i16 {
        value.get()
    }
    pub fn read_i16(values: &[WordI16], index: usize) {
        if index < values.len()
            && let WordI16::Word(value) = values[index]
        {
            assert!(get_i16(value) == value.get());
            assert!(get_i16(value) != 0);
        }
    }
    pub fn reverse_i16(values: &[ReverseI16], index: usize) {
        if index < values.len()
            && let ReverseI16::Word(value) = values[index]
        {
            assert!(get_i16(value) == value.get());
            assert!(get_i16(value) != 0);
        }
    }
    pub fn wrong_i16(values: &[WordI16], index: usize) {
        if index < values.len()
            && let WordI16::Word(value) = values[index]
        {
            assert!(get_i16(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordI32 {
        Empty,
        Word(core::num::NonZeroI32),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseI32 {
        Word(core::num::NonZeroI32),
        Empty,
    }
    #[inline(never)]
    pub fn get_i32(value: core::num::NonZeroI32) -> i32 {
        value.get()
    }
    pub fn read_i32(values: &[WordI32], index: usize) {
        if index < values.len()
            && let WordI32::Word(value) = values[index]
        {
            assert!(get_i32(value) == value.get());
            assert!(get_i32(value) != 0);
        }
    }
    pub fn reverse_i32(values: &[ReverseI32], index: usize) {
        if index < values.len()
            && let ReverseI32::Word(value) = values[index]
        {
            assert!(get_i32(value) == value.get());
            assert!(get_i32(value) != 0);
        }
    }
    pub fn wrong_i32(values: &[WordI32], index: usize) {
        if index < values.len()
            && let WordI32::Word(value) = values[index]
        {
            assert!(get_i32(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordI64 {
        Empty,
        Word(core::num::NonZeroI64),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseI64 {
        Word(core::num::NonZeroI64),
        Empty,
    }
    #[inline(never)]
    pub fn get_i64(value: core::num::NonZeroI64) -> i64 {
        value.get()
    }
    pub fn read_i64(values: &[WordI64], index: usize) {
        if index < values.len()
            && let WordI64::Word(value) = values[index]
        {
            assert!(get_i64(value) == value.get());
            assert!(get_i64(value) != 0);
        }
    }
    pub fn reverse_i64(values: &[ReverseI64], index: usize) {
        if index < values.len()
            && let ReverseI64::Word(value) = values[index]
        {
            assert!(get_i64(value) == value.get());
            assert!(get_i64(value) != 0);
        }
    }
    pub fn wrong_i64(values: &[WordI64], index: usize) {
        if index < values.len()
            && let WordI64::Word(value) = values[index]
        {
            assert!(get_i64(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordI128 {
        Empty,
        Word(core::num::NonZeroI128),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseI128 {
        Word(core::num::NonZeroI128),
        Empty,
    }
    #[inline(never)]
    pub fn get_i128(value: core::num::NonZeroI128) -> i128 {
        value.get()
    }
    pub fn read_i128(values: &[WordI128], index: usize) {
        if index < values.len()
            && let WordI128::Word(value) = values[index]
        {
            assert!(get_i128(value) == value.get());
            assert!(get_i128(value) != 0);
        }
    }
    pub fn reverse_i128(values: &[ReverseI128], index: usize) {
        if index < values.len()
            && let ReverseI128::Word(value) = values[index]
        {
            assert!(get_i128(value) == value.get());
            assert!(get_i128(value) != 0);
        }
    }
    pub fn wrong_i128(values: &[WordI128], index: usize) {
        if index < values.len()
            && let WordI128::Word(value) = values[index]
        {
            assert!(get_i128(value) == 0);
        }
    }

    #[derive(Clone, Copy)]
    pub enum WordIsize {
        Empty,
        Word(core::num::NonZeroIsize),
    }
    #[derive(Clone, Copy)]
    pub enum ReverseIsize {
        Word(core::num::NonZeroIsize),
        Empty,
    }
    #[inline(never)]
    pub fn get_isize(value: core::num::NonZeroIsize) -> isize {
        value.get()
    }
    pub fn read_isize(values: &[WordIsize], index: usize) {
        if index < values.len()
            && let WordIsize::Word(value) = values[index]
        {
            assert!(get_isize(value) == value.get());
            assert!(get_isize(value) != 0);
        }
    }
    pub fn reverse_isize(values: &[ReverseIsize], index: usize) {
        if index < values.len()
            && let ReverseIsize::Word(value) = values[index]
        {
            assert!(get_isize(value) == value.get());
            assert!(get_isize(value) != 0);
        }
    }
    pub fn wrong_isize(values: &[WordIsize], index: usize) {
        if index < values.len()
            && let WordIsize::Word(value) = values[index]
        {
            assert!(get_isize(value) == 0);
        }
    }

    pub fn mutable_unknown(values: &mut [WordU32], index: usize) {
        if index < values.len() {
            let _ = values[index];
        }
    }
    #[derive(Clone, Copy)]
    pub enum ReferenceNiche<'a> {
        Empty,
        Word(&'a u32),
    }
    pub fn reference_unknown(values: &[ReferenceNiche<'_>], index: usize) {
        if index < values.len()
            && let ReferenceNiche::Word(value) = values[index]
        {
            assert!(*value == *value);
        }
    }
    #[derive(Clone, Copy)]
    pub enum Extra {
        Empty,
        Word(core::num::NonZeroU32, u32),
    }
    pub fn extra_unknown(values: &[Extra], index: usize) {
        if index < values.len()
            && let Extra::Word(value, _) = values[index]
        {
            assert!(value.get() != 0);
        }
    }
    pub enum Dropping {
        Empty,
        Word(core::num::NonZeroI32),
    }
    impl Drop for Dropping {
        fn drop(&mut self) {}
    }
    pub fn drop_unknown(values: &[Dropping], index: usize) {
        if index < values.len()
            && let Dropping::Word(value) = &values[index]
        {
            assert!(value.get() != 0);
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn original_local_integer_rows() {
            for raw in [1, u8::MAX, 1 << (u8::BITS - 1)] {
                let value = core::num::NonZeroU8::new(raw).unwrap();
                let values = [super::WordU8::Empty, super::WordU8::Word(value)];
                let reversed = [super::ReverseU8::Empty, super::ReverseU8::Word(value)];
                for index in 0..2 {
                    super::read_u8(&values, index);
                    super::reverse_u8(&reversed, index);
                }
            }

            for raw in [1, u16::MAX, 1 << (u16::BITS - 1)] {
                let value = core::num::NonZeroU16::new(raw).unwrap();
                let values = [super::WordU16::Empty, super::WordU16::Word(value)];
                let reversed = [super::ReverseU16::Empty, super::ReverseU16::Word(value)];
                for index in 0..2 {
                    super::read_u16(&values, index);
                    super::reverse_u16(&reversed, index);
                }
            }

            for raw in [1, u32::MAX, 1 << (u32::BITS - 1)] {
                let value = core::num::NonZeroU32::new(raw).unwrap();
                let values = [super::WordU32::Empty, super::WordU32::Word(value)];
                let reversed = [super::ReverseU32::Empty, super::ReverseU32::Word(value)];
                for index in 0..2 {
                    super::read_u32(&values, index);
                    super::reverse_u32(&reversed, index);
                }
            }

            for raw in [1, u64::MAX, 1 << (u64::BITS - 1)] {
                let value = core::num::NonZeroU64::new(raw).unwrap();
                let values = [super::WordU64::Empty, super::WordU64::Word(value)];
                let reversed = [super::ReverseU64::Empty, super::ReverseU64::Word(value)];
                for index in 0..2 {
                    super::read_u64(&values, index);
                    super::reverse_u64(&reversed, index);
                }
            }

            for raw in [1, u128::MAX, 1 << (u128::BITS - 1)] {
                let value = core::num::NonZeroU128::new(raw).unwrap();
                let values = [super::WordU128::Empty, super::WordU128::Word(value)];
                let reversed = [super::ReverseU128::Empty, super::ReverseU128::Word(value)];
                for index in 0..2 {
                    super::read_u128(&values, index);
                    super::reverse_u128(&reversed, index);
                }
            }

            for raw in [1, usize::MAX, 1 << (usize::BITS - 1)] {
                let value = core::num::NonZeroUsize::new(raw).unwrap();
                let values = [super::WordUsize::Empty, super::WordUsize::Word(value)];
                let reversed = [super::ReverseUsize::Empty, super::ReverseUsize::Word(value)];
                for index in 0..2 {
                    super::read_usize(&values, index);
                    super::reverse_usize(&reversed, index);
                }
            }

            for raw in [1, -1, i8::MIN, i8::MAX] {
                let value = core::num::NonZeroI8::new(raw).unwrap();
                let values = [super::WordI8::Empty, super::WordI8::Word(value)];
                let reversed = [super::ReverseI8::Empty, super::ReverseI8::Word(value)];
                for index in 0..2 {
                    super::read_i8(&values, index);
                    super::reverse_i8(&reversed, index);
                }
            }

            for raw in [1, -1, i16::MIN, i16::MAX] {
                let value = core::num::NonZeroI16::new(raw).unwrap();
                let values = [super::WordI16::Empty, super::WordI16::Word(value)];
                let reversed = [super::ReverseI16::Empty, super::ReverseI16::Word(value)];
                for index in 0..2 {
                    super::read_i16(&values, index);
                    super::reverse_i16(&reversed, index);
                }
            }

            for raw in [1, -1, i32::MIN, i32::MAX] {
                let value = core::num::NonZeroI32::new(raw).unwrap();
                let values = [super::WordI32::Empty, super::WordI32::Word(value)];
                let reversed = [super::ReverseI32::Empty, super::ReverseI32::Word(value)];
                for index in 0..2 {
                    super::read_i32(&values, index);
                    super::reverse_i32(&reversed, index);
                }
            }

            for raw in [1, -1, i64::MIN, i64::MAX] {
                let value = core::num::NonZeroI64::new(raw).unwrap();
                let values = [super::WordI64::Empty, super::WordI64::Word(value)];
                let reversed = [super::ReverseI64::Empty, super::ReverseI64::Word(value)];
                for index in 0..2 {
                    super::read_i64(&values, index);
                    super::reverse_i64(&reversed, index);
                }
            }

            for raw in [1, -1, i128::MIN, i128::MAX] {
                let value = core::num::NonZeroI128::new(raw).unwrap();
                let values = [super::WordI128::Empty, super::WordI128::Word(value)];
                let reversed = [super::ReverseI128::Empty, super::ReverseI128::Word(value)];
                for index in 0..2 {
                    super::read_i128(&values, index);
                    super::reverse_i128(&reversed, index);
                }
            }

            for raw in [1, -1, isize::MIN, isize::MAX] {
                let value = core::num::NonZeroIsize::new(raw).unwrap();
                let values = [super::WordIsize::Empty, super::WordIsize::Word(value)];
                let reversed = [super::ReverseIsize::Empty, super::ReverseIsize::Word(value)];
                for index in 0..2 {
                    super::read_isize(&values, index);
                    super::reverse_isize(&reversed, index);
                }
            }
        }
    }
}


mod retained_mutable_views_survey {

    pub fn product_offset(values: &mut [[f32; 2]], start: usize, end: usize, sibling: usize) {
        if start < end && end <= values.len() && sibling < values.len() && sibling != start {
            let old = values[sibling][0].to_bits();
            {
                let child = &mut values[start..end];
                assert!(child.len() == end - start);
                child[0][1] = 2.0;
                child[0][0] = 1.0;
                assert!(child[0][0] == 1.0 && child[0][1] == 2.0);
            }
            assert!(values[start][0] == 1.0 && values[start][1] == 2.0);
            assert!(values[sibling][0].to_bits() == old);
        }
    }
    pub fn scalar_offset(values: &mut [u16], start: usize, end: usize, sibling: usize, word: u16) {
        if start < end && end <= values.len() && sibling < values.len() && sibling != start {
            let old = values[sibling];
            {
                let child = &mut values[start..end];
                assert!(child.len() == end - start);
                child[0] = word;
                assert!(child[0] == word);
            }
            assert!(values[start] == word && values[sibling] == old);
        }
    }
    pub fn wrong_write(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0][0] = 1.0;
            assert!(child[0][0] == 2.0);
        }
    }
    pub fn wrong_extent(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 2);
        }
    }
    pub fn invalid_range(values: &mut [[f32; 2]]) {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
    }
    #[inline(never)]
    pub fn identity(word: u16) -> u16 {
        word
    }
    pub fn scalar_helper_unknown(values: &mut [u16], word: u16) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = identity(word);
        }
    }
    pub fn nested_unknown(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let nested = &mut child[0..1];
            assert!(nested.len() == 1);
        }
    }
    pub fn nll_unknown(values: &mut [[f32; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            values[0][0] = 2.0;
            assert!(values[0][0] == 2.0);
        }
    }
    pub fn unsupported_codec(values: &mut [[f64; 2]]) {
        if !values.is_empty() {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn actual_offset_and_sibling_storage() {
            let mut products = [[3.0, 4.0], [5.0, 6.0], [7.0, 8.0]];
            super::product_offset(&mut products, 1, 3, 0);
            assert!(products[0] == [3.0, 4.0] && products[1] == [1.0, 2.0]);
            let mut scalars = [3, 5, 7];
            super::scalar_offset(&mut scalars, 1, 3, 0, 19);
            assert!(scalars == [3, 19, 7]);
        }
    }
    pub fn earlier_staging_parent(values: &mut [u16]) {
        let original_len = values.len();
        if original_len >= 2 {
            let borrowed = &mut *values;
            let child = &mut borrowed[0..1];
            assert!(child.len() == 1);
            assert!(borrowed.len() == original_len);
        }
    }
}


mod retained_primitive_helpers_survey {

#[inline(never)]
pub fn flip(word: u16) -> u16 {
    let mask = 1;
    let first = word ^ mask;
    let second = first ^ 0;
    let third = second ^ 0;
    let fourth = third ^ 0;
    let result = fourth ^ 0;
    result
}

pub fn scalar(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}

pub fn product(values: &mut [[f32; 2]], word: u16) {
    if values.len() >= 2 {
        let old = values[1][0].to_bits();
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let mapped = flip(word);
            assert!(mapped == word ^ 1);
            child[0][0] = 1.0;
        }
        assert!(values[0][0] == 1.0);
        assert!(values[1][0].to_bits() == old);
    }
}

pub fn wrong(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = flip(word);
        assert!(child[0] == word);
    }
}

#[inline(never)]
fn nested_flip(word: u16) -> u16 {
    flip(word)
}
pub fn nested_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = nested_flip(word);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn helper_results_and_parent_sibling_storage() {
        let mut scalars = [0, 7];
        super::scalar(&mut scalars, 14);
        assert!(scalars == [15, 7]);
        let mut products = [[3.0, 4.0], [5.0, 6.0]];
        super::product(&mut products, 14);
        assert!(products == [[1.0, 4.0], [5.0, 6.0]]);
        for value in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            super::character(&mut scalars, value);
        }
        super::boolean(&mut scalars, false);
        super::boolean(&mut scalars, true);
        for raw in [0, 0x8000_0000, 0x7fc0_0042] {
            let value = f32::from_bits(raw);
            super::float32(&mut scalars, value);
            assert!(super::id_f32(value).to_bits() == raw);
        }
        for raw in [0, 0x8000_0000_0000_0000, 0x7ff8_0000_0000_0042] {
            let value = f64::from_bits(raw);
            super::float64(&mut scalars, value);
            assert!(super::id_f64(value).to_bits() == raw);
        }
        super::unit(&mut scalars);
        super::associated(&mut scalars, 14);
        super::mixed(&mut scalars, false, i32::MIN, i32::MAX);
        super::mixed(&mut scalars, true, i32::MIN, i32::MAX);
        super::integer_i8(&mut scalars, i8::MIN);
        super::integer_i16(&mut scalars, i16::MIN);
        super::integer_i32(&mut scalars, i32::MIN);
        super::integer_i64(&mut scalars, i64::MIN);
        super::integer_i128(&mut scalars, i128::MIN);
        super::integer_isize(&mut scalars, isize::MIN);
        super::integer_u8(&mut scalars, u8::MAX);
        super::integer_u16(&mut scalars, u16::MAX);
        super::integer_u32(&mut scalars, u32::MAX);
        super::integer_u64(&mut scalars, u64::MAX);
        super::integer_u128(&mut scalars, u128::MAX);
        super::integer_usize(&mut scalars, usize::MAX);
    }
}

macro_rules! identity_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        #[inline(never)]
        pub fn $helper(value: $ty) -> $ty { value }
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
identity_case!(id_u8, integer_u8, u8);
identity_case!(id_u16, integer_u16, u16);
identity_case!(id_u32, integer_u32, u32);
identity_case!(id_u64, integer_u64, u64);
identity_case!(id_u128, integer_u128, u128);
identity_case!(id_usize, integer_usize, usize);
identity_case!(id_i8, integer_i8, i8);
identity_case!(id_i16, integer_i16, i16);
identity_case!(id_i32, integer_i32, i32);
identity_case!(id_i64, integer_i64, i64);
identity_case!(id_i128, integer_i128, i128);
identity_case!(id_isize, integer_isize, isize);
identity_case!(id_bool, boolean, bool);
identity_case!(id_char, character, char);

#[inline(never)]
pub fn id_f32(value: f32) -> f32 { value }
#[inline(never)]
pub fn id_f64(value: f64) -> f64 { value }
macro_rules! float_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value || value != value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
float_case!(id_f32, float32, f32);
float_case!(id_f64, float64, f64);
#[inline(never)]
pub fn id_unit(value: ()) { value }
pub fn unit(values: &mut [u16]) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            id_unit(());
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}

#[inline(never)]
pub fn guarded(word: u16) -> u16 { word ^ 1 }
pub fn contract_positive(values: &mut [u16], word: u16) {
    if !values.is_empty() && word < 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
        assert!(child[0] == word ^ 1);
    }
}
pub fn contract_negative(values: &mut [u16], word: u16) {
    if !values.is_empty() && word >= 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
    }
}


pub struct Associated;
impl Associated {
    #[inline(never)]
    pub fn flip(value: u16) -> u16 { value ^ 1 }
}
pub fn associated(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = Associated::flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}
#[inline(never)]
pub fn choose(flag: bool, left: i32, right: i32) -> i32 {
    if flag { left } else { right }
}
pub fn mixed(values: &mut [u16], flag: bool, left: i32, right: i32) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let value = choose(flag, left, right);
            assert!(if flag { value == left } else { value == right });
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}

}


mod nested_retained_primitive_helpers_survey {

#[inline(never)]
pub fn flip(word: u16) -> u16 {
    middle(word)
}
#[inline(never)]
fn middle(word: u16) -> u16 {
    leaf(word)
}
#[inline(never)]
fn leaf(word: u16) -> u16 {
    word ^ 1
}

pub fn scalar(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}

pub fn product(values: &mut [[f32; 2]], word: u16) {
    if values.len() >= 2 {
        let old = values[1][0].to_bits();
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let mapped = middle(word);
            assert!(mapped == word ^ 1);
            child[0][0] = 1.0;
        }
        assert!(values[0][0] == 1.0);
        assert!(values[1][0].to_bits() == old);
    }
}

pub fn wrong(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = flip(word);
        assert!(child[0] == word);
    }
}

#[inline(never)]
fn nested_flip(word: u16) -> u16 {
    flip(word)
}
pub fn nested_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = nested_flip(word);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn helper_results_and_parent_sibling_storage() {
        let mut scalars = [0, 7];
        super::scalar(&mut scalars, 14);
        assert!(scalars == [15, 7]);
        let mut products = [[3.0, 4.0], [5.0, 6.0]];
        super::product(&mut products, 14);
        assert!(products == [[1.0, 4.0], [5.0, 6.0]]);
        for value in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            super::character(&mut scalars, value);
        }
        super::boolean(&mut scalars, false);
        super::boolean(&mut scalars, true);
        for raw in [0, 0x8000_0000, 0x7fc0_0042] {
            let value = f32::from_bits(raw);
            super::float32(&mut scalars, value);
            assert!(super::id_f32(value).to_bits() == raw);
        }
        for raw in [0, 0x8000_0000_0000_0000, 0x7ff8_0000_0000_0042] {
            let value = f64::from_bits(raw);
            super::float64(&mut scalars, value);
            assert!(super::id_f64(value).to_bits() == raw);
        }
        super::unit(&mut scalars);
        super::associated(&mut scalars, 14);
        super::mixed(&mut scalars, false, i32::MIN, i32::MAX);
        super::mixed(&mut scalars, true, i32::MIN, i32::MAX);
        super::integer_i8(&mut scalars, i8::MIN);
        super::integer_i16(&mut scalars, i16::MIN);
        super::integer_i32(&mut scalars, i32::MIN);
        super::integer_i64(&mut scalars, i64::MIN);
        super::integer_i128(&mut scalars, i128::MIN);
        super::integer_isize(&mut scalars, isize::MIN);
        super::integer_u8(&mut scalars, u8::MAX);
        super::integer_u16(&mut scalars, u16::MAX);
        super::integer_u32(&mut scalars, u32::MAX);
        super::integer_u64(&mut scalars, u64::MAX);
        super::integer_u128(&mut scalars, u128::MAX);
        super::integer_usize(&mut scalars, usize::MAX);
    }
}

macro_rules! identity_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        #[inline(never)]
        pub fn $helper(value: $ty) -> $ty {
            #[inline(never)]
            fn inner(value: $ty) -> $ty { value }
            inner(value)
        }
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
identity_case!(id_u8, integer_u8, u8);
identity_case!(id_u16, integer_u16, u16);
identity_case!(id_u32, integer_u32, u32);
identity_case!(id_u64, integer_u64, u64);
identity_case!(id_u128, integer_u128, u128);
identity_case!(id_usize, integer_usize, usize);
identity_case!(id_i8, integer_i8, i8);
identity_case!(id_i16, integer_i16, i16);
identity_case!(id_i32, integer_i32, i32);
identity_case!(id_i64, integer_i64, i64);
identity_case!(id_i128, integer_i128, i128);
identity_case!(id_isize, integer_isize, isize);
identity_case!(id_bool, boolean, bool);
identity_case!(id_char, character, char);

#[inline(never)]
pub fn id_f32(value: f32) -> f32 { float32_leaf(value) }
#[inline(never)]
fn float32_leaf(value: f32) -> f32 { value }
#[inline(never)]
pub fn id_f64(value: f64) -> f64 { float64_leaf(value) }
#[inline(never)]
fn float64_leaf(value: f64) -> f64 { value }
macro_rules! float_case {
    ($helper:ident, $entry:ident, $ty:ty) => {
        pub fn $entry(values: &mut [u16], value: $ty) {
            if !values.is_empty() {
                {
                    let child = &mut values[0..1];
                    assert!(child.len() == 1);
                    let returned = $helper(value);
                    assert!(returned == value || value != value);
                    child[0] = 1;
                }
                assert!(values[0] == 1);
            }
        }
    };
}
float_case!(id_f32, float32, f32);
float_case!(id_f64, float64, f64);
#[inline(never)]
pub fn id_unit(value: ()) { unit_leaf(value) }
#[inline(never)]
fn unit_leaf(value: ()) { value }
pub fn unit(values: &mut [u16]) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            id_unit(());
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}

#[inline(never)]
pub fn guarded(word: u16) -> u16 { guarded_leaf(word) }
#[inline(never)]
pub fn guarded_leaf(word: u16) -> u16 { word ^ 1 }
pub fn contract_positive(values: &mut [u16], word: u16) {
    if !values.is_empty() && word < 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
        assert!(child[0] == word ^ 1);
    }
}
pub fn contract_negative(values: &mut [u16], word: u16) {
    if !values.is_empty() && word >= 10 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = guarded(word);
    }
}


pub struct Associated;
impl Associated {
    #[inline(never)]
    pub fn flip(value: u16) -> u16 { leaf(value) }
}
pub fn associated(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = Associated::flip(word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}
#[inline(never)]
pub fn choose(flag: bool, left: i32, right: i32) -> i32 {
    if flag { choose_leaf(left) } else { choose_leaf(right) }
}
pub fn mixed(values: &mut [u16], flag: bool, left: i32, right: i32) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            let value = choose(flag, left, right);
            assert!(if flag { value == left } else { value == right });
            child[0] = 1;
        }
        assert!(values[0] == 1);
    }
}

#[inline(never)]
fn recursive(count: u8, word: u16) -> u16 {
    if count == 0 { word ^ 1 } else { recursive(count - 1, word) }
}
pub fn finite_recursive(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        {
            let child = &mut values[0..1];
            assert!(child.len() == 1);
            child[0] = recursive(1, word);
            assert!(child[0] == word ^ 1);
        }
        assert!(values[0] == word ^ 1);
    }
}
#[inline(never)]
fn endless(word: u16) -> u16 {
    if word == 0 { 0 } else { endless(word) }
}
pub fn unbounded_recursive(values: &mut [u16], word: u16) {
    if !values.is_empty() && word != 0 {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = endless(word);
    }
}
#[inline(never)]
fn indirect_middle(word: u16) -> u16 {
    let function: fn(u16) -> u16 = leaf;
    function(word)
}
pub fn indirect_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = indirect_middle(word);
    }
}
pub extern "C" fn foreign(word: u16) -> u16 { word }
#[inline(never)]
fn foreign_middle(word: u16) -> u16 { foreign(word) }
pub fn foreign_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = foreign_middle(word);
    }
}
fn owner_leaf(word: &mut u16) { *word = 1; }
#[inline(never)]
fn owner_middle(word: u16) -> u16 {
    let mut local = word;
    owner_leaf(&mut local);
    local
}
pub fn owner_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = owner_middle(word);
    }
}
#[cfg(test)]
mod nested_native {
    #[test]
    fn actual_finite_recursive_owner_return() {
        let mut words = [0, 7];
        super::finite_recursive(&mut words, 14);
        assert!(words == [15, 7]);
    }
}

#[inline(never)]
fn choose_leaf(value: i32) -> i32 { value }

#[inline(never)]
fn closure_middle(word: u16) -> u16 {
    let function = || leaf(word);
    function()
}
pub fn closure_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = closure_middle(word);
    }
}

}


#[forbid(unsafe_code)]
#[path = "nested_function_choice_cases.rs"]
pub mod nested_function_choices_survey;

#[path = "nested_mutable_product_cases.rs"]
pub mod nested_mutable_products;
