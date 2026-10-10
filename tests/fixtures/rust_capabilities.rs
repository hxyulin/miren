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

#[cfg(test)]
mod native {
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
