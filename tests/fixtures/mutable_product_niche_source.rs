#![no_std]
#![forbid(unsafe_code)]
use core::num::*;

macro_rules! domain {
    ($word:ty, $nonzero:ty, $option:ident, $empty:ident, $payload:ident,
     $empty_fn:ident, $payload_fn:ident) => {
        #[derive(Clone, Copy)]
        pub enum $empty {
            Empty,
            Payload($nonzero),
        }
        #[derive(Clone, Copy)]
        pub enum $payload {
            Payload($nonzero),
            Empty,
        }
        pub fn $option(values: &mut [(Option<$nonzero>, bool)], index: usize, word: $word) {
            if index < values.len() {
                values[index].0 = None;
                if let Some(payload) = <$nonzero>::new(word) {
                    values[index].0 = Some(payload);
                    let copied = values[index].0;
                    values[index].0 = copied;
                    match values[index].0 {
                        Some(payload) => assert!(payload.get() == word),
                        None => panic!("payload construction lost its active variant"),
                    }
                }
                values[index].0 = None;
                assert!(values[index].0.is_none());
            }
        }
        pub fn $empty_fn(values: &mut [($empty, bool)], index: usize, word: $word) {
            if index < values.len() {
                values[index].0 = $empty::Empty;
                if let Some(payload) = <$nonzero>::new(word) {
                    values[index].0 = $empty::Payload(payload);
                    let copied = values[index].0;
                    values[index].0 = copied;
                    match values[index].0 {
                        $empty::Payload(payload) => assert!(payload.get() == word),
                        $empty::Empty => {
                            panic!("local payload construction lost its active variant")
                        }
                    }
                }
                values[index].0 = $empty::Empty;
            }
        }
        pub fn $payload_fn(values: &mut [($payload, bool)], index: usize, word: $word) {
            if index < values.len() {
                values[index].0 = $payload::Empty;
                if let Some(payload) = <$nonzero>::new(word) {
                    values[index].0 = $payload::Payload(payload);
                    let copied = values[index].0;
                    values[index].0 = copied;
                    match values[index].0 {
                        $payload::Payload(payload) => assert!(payload.get() == word),
                        $payload::Empty => panic!("reversed payload lost its active variant"),
                    }
                }
                values[index].0 = $payload::Empty;
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
