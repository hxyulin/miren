#![no_std]
#![forbid(unsafe_code)]
use core::num::*;

macro_rules! domain {
    ($word:ty, $nonzero:ty, $option:ident, $empty:ident, $payload:ident,
     $empty_fn:ident, $payload_fn:ident) => {
        #[derive(Clone, Copy)]
        pub enum $empty { Empty, Payload($nonzero) }
        #[derive(Clone, Copy)]
        pub enum $payload { Payload($nonzero), Empty }
        pub fn $option(values: &mut [(Option<$nonzero>, bool)], index: usize, _: $word) {
            if index < values.len() {
                let copied = values[index].0;
                values[index].0 = copied;
            }
        }
        pub fn $empty_fn(values: &mut [($empty, bool)], index: usize, _: $word) {
            if index < values.len() {
                let copied = values[index].0;
                values[index].0 = copied;
            }
        }
        pub fn $payload_fn(values: &mut [($payload, bool)], index: usize, _: $word) {
            if index < values.len() {
                let copied = values[index].0;
                values[index].0 = copied;
            }
        }
    };
}

domain!(u8, NonZeroU8, option_u8, EmptyU8, PayloadU8, empty_u8, payload_u8);
domain!(u16, NonZeroU16, option_u16, EmptyU16, PayloadU16, empty_u16, payload_u16);
domain!(u32, NonZeroU32, option_u32, EmptyU32, PayloadU32, empty_u32, payload_u32);
domain!(u64, NonZeroU64, option_u64, EmptyU64, PayloadU64, empty_u64, payload_u64);
domain!(u128, NonZeroU128, option_u128, EmptyU128, PayloadU128, empty_u128, payload_u128);
domain!(usize, NonZeroUsize, option_usize, EmptyUsize, PayloadUsize, empty_usize, payload_usize);
domain!(i8, NonZeroI8, option_i8, EmptyI8, PayloadI8, empty_i8, payload_i8);
domain!(i16, NonZeroI16, option_i16, EmptyI16, PayloadI16, empty_i16, payload_i16);
domain!(i32, NonZeroI32, option_i32, EmptyI32, PayloadI32, empty_i32, payload_i32);
domain!(i64, NonZeroI64, option_i64, EmptyI64, PayloadI64, empty_i64, payload_i64);
domain!(i128, NonZeroI128, option_i128, EmptyI128, PayloadI128, empty_i128, payload_i128);
domain!(isize, NonZeroIsize, option_isize, EmptyIsize, PayloadIsize, empty_isize, payload_isize);

#[derive(Clone, Copy)]
pub enum UnicodeNiche { 空, 値(NonZeroU8) }
pub fn name_bound_unicode(values: &mut [(UnicodeNiche, bool)], index: usize) {
    if index < values.len() {
        let copied = values[index].0;
        values[index].0 = copied;
    }
}

#[derive(Clone, Copy)]
pub enum OversizedNiche { Empty, 値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値値(NonZeroU8) }
pub fn name_bound_oversized(values: &mut [(OversizedNiche, bool)], index: usize) {
    if index < values.len() {
        let copied = values[index].0;
        values[index].0 = copied;
    }
}
