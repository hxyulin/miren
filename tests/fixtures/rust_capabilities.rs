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
