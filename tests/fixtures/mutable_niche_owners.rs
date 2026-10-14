#![no_std]
#![forbid(unsafe_code)]

#[cfg(test)]
extern crate std;

macro_rules! family {
    ($word:ty, $nonzero:ty, $niche:ident, $empty:ident, $payload:ident) => {
        pub fn snapshot(value: $niche) -> (bool, $word) {
            match value {
                $niche::$empty => (false, 0),
                $niche::$payload(payload) => (true, payload.get()),
            }
        }

        pub fn make(word: $word) -> $niche {
            match <$nonzero>::new(word) {
                Some(payload) => $niche::$payload(payload),
                None => $niche::$empty,
            }
        }

        pub fn copy_fields(values: &mut [($niche, bool)], source: usize, destination: usize) {
            if source < values.len() && destination < values.len() {
                let expected = snapshot(values[source].0);
                let sibling = values[destination].1;
                let copied = values[source].0;
                values[destination].0 = copied;
                let actual = snapshot(values[destination].0);
                assert!(actual.0 == expected.0 && actual.1 == expected.1);
                assert!(values[destination].1 == sibling);
                if source != destination {
                    let retained = snapshot(values[source].0);
                    assert!(retained.0 == expected.0 && retained.1 == expected.1);
                }
            }
        }

        pub fn whole_product(values: &mut [($niche, bool)], source: usize, destination: usize) {
            if source < values.len() && destination < values.len() {
                let expected = snapshot(values[source].0);
                let sibling = values[source].1;
                let copied = values[source];
                values[destination] = copied;
                let actual = snapshot(values[destination].0);
                assert!(actual.0 == expected.0 && actual.1 == expected.1);
                assert!(values[destination].1 == sibling);
                if source != destination {
                    let retained = snapshot(values[source].0);
                    assert!(retained.0 == expected.0 && retained.1 == expected.1);
                    assert!(values[source].1 == sibling);
                }
            }
        }

        pub fn replace(values: &mut [($niche, bool)], destination: usize, word: $word) {
            if destination < values.len() {
                let sibling = values[destination].1;
                match <$nonzero>::new(word) {
                    Some(payload) => values[destination].0 = $niche::$payload(payload),
                    None => values[destination].0 = $niche::$empty,
                }
                let actual = snapshot(values[destination].0);
                assert!(actual.0 == (word != 0) && actual.1 == word);
                assert!(values[destination].1 == sibling);
            }
        }

        pub fn outer_preservation(values: &mut [($niche, bool)], word: $word) {
            if values.len() >= 2 {
                let expected = snapshot(values[1].0);
                let sibling = values[1].1;
                replace(values, 0, word);
                let actual = snapshot(values[1].0);
                assert!(actual.0 == expected.0 && actual.1 == expected.1);
                assert!(values[1].1 == sibling);
            }
        }

        #[inline(never)]
        pub fn transfer(values: &mut [($niche, bool)], source: usize, destination: usize) -> $word {
            if source < values.len() && destination < values.len() {
                copy_fields(values, source, destination);
                snapshot(values[destination].0).1
            } else {
                0
            }
        }

        #[inline(never)]
        pub fn nested_transfer(
            values: &mut [($niche, bool)],
            source: usize,
            destination: usize,
        ) -> $word {
            transfer(values, source, destination)
        }

        pub fn via_helper(values: &mut [($niche, bool)], source: usize, destination: usize) {
            if source < values.len() && destination < values.len() {
                let expected = snapshot(values[source].0);
                let source_sibling = values[source].1;
                let sibling = values[destination].1;
                let returned = nested_transfer(values, source, destination);
                let actual = snapshot(values[destination].0);
                assert!(returned == expected.1);
                assert!(actual.0 == expected.0 && actual.1 == expected.1);
                assert!(values[destination].1 == sibling);
                if source != destination {
                    let retained = snapshot(values[source].0);
                    assert!(retained.0 == expected.0 && retained.1 == expected.1);
                    assert!(values[source].1 == source_sibling);
                }
            }
        }

        pub fn wrong_sibling(values: &mut [($niche, bool)], index: usize) {
            if index < values.len() {
                let sibling = values[index].1;
                values[index].0 = $niche::$empty;
                assert!(values[index].1 != sibling);
            }
        }

        pub fn partial_payload(values: &mut [($niche, bool)], index: usize, word: $word) {
            if index < values.len()
                && let $niche::$payload(payload) = &mut values[index].0
                && let Some(replacement) = <$nonzero>::new(word)
            {
                *payload = replacement;
            }
        }

        pub fn bare_owner(values: &mut [$niche], index: usize) {
            if index < values.len() {
                values[index] = $niche::$empty;
                assert!(!snapshot(values[index]).0);
            }
        }
    };
}

pub mod option_u8 {
    use core::num::NonZeroU8;
    pub type Niche = Option<NonZeroU8>;
    family!(u8, NonZeroU8, Niche, None, Some);
}

pub mod empty_u8 {
    use core::num::NonZeroU8;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroU8),
    }
    family!(u8, NonZeroU8, Niche, Empty, Payload);
}

pub mod payload_u8 {
    use core::num::NonZeroU8;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroU8),
        Empty,
    }
    family!(u8, NonZeroU8, Niche, Empty, Payload);
}

pub mod option_u16 {
    use core::num::NonZeroU16;
    pub type Niche = Option<NonZeroU16>;
    family!(u16, NonZeroU16, Niche, None, Some);
}

pub mod empty_u16 {
    use core::num::NonZeroU16;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroU16),
    }
    family!(u16, NonZeroU16, Niche, Empty, Payload);
}

pub mod payload_u16 {
    use core::num::NonZeroU16;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroU16),
        Empty,
    }
    family!(u16, NonZeroU16, Niche, Empty, Payload);
}

pub mod option_u32 {
    use core::num::NonZeroU32;
    pub type Niche = Option<NonZeroU32>;
    family!(u32, NonZeroU32, Niche, None, Some);
}

pub mod empty_u32 {
    use core::num::NonZeroU32;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroU32),
    }
    family!(u32, NonZeroU32, Niche, Empty, Payload);
}

pub mod payload_u32 {
    use core::num::NonZeroU32;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroU32),
        Empty,
    }
    family!(u32, NonZeroU32, Niche, Empty, Payload);
}

pub mod option_u64 {
    use core::num::NonZeroU64;
    pub type Niche = Option<NonZeroU64>;
    family!(u64, NonZeroU64, Niche, None, Some);
}

pub mod empty_u64 {
    use core::num::NonZeroU64;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroU64),
    }
    family!(u64, NonZeroU64, Niche, Empty, Payload);
}

pub mod payload_u64 {
    use core::num::NonZeroU64;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroU64),
        Empty,
    }
    family!(u64, NonZeroU64, Niche, Empty, Payload);
}

pub mod option_u128 {
    use core::num::NonZeroU128;
    pub type Niche = Option<NonZeroU128>;
    family!(u128, NonZeroU128, Niche, None, Some);
}

pub mod empty_u128 {
    use core::num::NonZeroU128;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroU128),
    }
    family!(u128, NonZeroU128, Niche, Empty, Payload);
}

pub mod payload_u128 {
    use core::num::NonZeroU128;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroU128),
        Empty,
    }
    family!(u128, NonZeroU128, Niche, Empty, Payload);
}

pub mod option_usize {
    use core::num::NonZeroUsize;
    pub type Niche = Option<NonZeroUsize>;
    family!(usize, NonZeroUsize, Niche, None, Some);
}

pub mod empty_usize {
    use core::num::NonZeroUsize;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroUsize),
    }
    family!(usize, NonZeroUsize, Niche, Empty, Payload);
}

pub mod payload_usize {
    use core::num::NonZeroUsize;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroUsize),
        Empty,
    }
    family!(usize, NonZeroUsize, Niche, Empty, Payload);
}

pub mod option_i8 {
    use core::num::NonZeroI8;
    pub type Niche = Option<NonZeroI8>;
    family!(i8, NonZeroI8, Niche, None, Some);
}

pub mod empty_i8 {
    use core::num::NonZeroI8;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroI8),
    }
    family!(i8, NonZeroI8, Niche, Empty, Payload);
}

pub mod payload_i8 {
    use core::num::NonZeroI8;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroI8),
        Empty,
    }
    family!(i8, NonZeroI8, Niche, Empty, Payload);
}

pub mod option_i16 {
    use core::num::NonZeroI16;
    pub type Niche = Option<NonZeroI16>;
    family!(i16, NonZeroI16, Niche, None, Some);
}

pub mod empty_i16 {
    use core::num::NonZeroI16;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroI16),
    }
    family!(i16, NonZeroI16, Niche, Empty, Payload);
}

pub mod payload_i16 {
    use core::num::NonZeroI16;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroI16),
        Empty,
    }
    family!(i16, NonZeroI16, Niche, Empty, Payload);
}

pub mod option_i32 {
    use core::num::NonZeroI32;
    pub type Niche = Option<NonZeroI32>;
    family!(i32, NonZeroI32, Niche, None, Some);
}

pub mod empty_i32 {
    use core::num::NonZeroI32;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroI32),
    }
    family!(i32, NonZeroI32, Niche, Empty, Payload);
}

pub mod payload_i32 {
    use core::num::NonZeroI32;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroI32),
        Empty,
    }
    family!(i32, NonZeroI32, Niche, Empty, Payload);
}

pub mod option_i64 {
    use core::num::NonZeroI64;
    pub type Niche = Option<NonZeroI64>;
    family!(i64, NonZeroI64, Niche, None, Some);
}

pub mod empty_i64 {
    use core::num::NonZeroI64;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroI64),
    }
    family!(i64, NonZeroI64, Niche, Empty, Payload);
}

pub mod payload_i64 {
    use core::num::NonZeroI64;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroI64),
        Empty,
    }
    family!(i64, NonZeroI64, Niche, Empty, Payload);
}

pub mod option_i128 {
    use core::num::NonZeroI128;
    pub type Niche = Option<NonZeroI128>;
    family!(i128, NonZeroI128, Niche, None, Some);
}

pub mod empty_i128 {
    use core::num::NonZeroI128;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroI128),
    }
    family!(i128, NonZeroI128, Niche, Empty, Payload);
}

pub mod payload_i128 {
    use core::num::NonZeroI128;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroI128),
        Empty,
    }
    family!(i128, NonZeroI128, Niche, Empty, Payload);
}

pub mod option_isize {
    use core::num::NonZeroIsize;
    pub type Niche = Option<NonZeroIsize>;
    family!(isize, NonZeroIsize, Niche, None, Some);
}

pub mod empty_isize {
    use core::num::NonZeroIsize;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Empty,
        Payload(NonZeroIsize),
    }
    family!(isize, NonZeroIsize, Niche, Empty, Payload);
}

pub mod payload_isize {
    use core::num::NonZeroIsize;
    #[derive(Clone, Copy)]
    pub enum Niche {
        Payload(NonZeroIsize),
        Empty,
    }
    family!(isize, NonZeroIsize, Niche, Empty, Payload);
}

#[cfg(test)]
macro_rules! native_family {
    ($module:ident, $word:ty) => {{
        use $module::{make, snapshot};
        let words: [$word; 4] = [0, 1, <$word>::MIN, <$word>::MAX];
        for source_word in words {
            for replacement in words {
                for source in [0, 1, 2, 99] {
                    for destination in [0, 1, 2, 99] {
                        let mut values = [(make(source_word), false), (make(1), true)];
                        let before = values;
                        $module::copy_fields(&mut values, source, destination);
                        for i in 0..2 {
                            let copied = source < 2 && destination < 2 && i == destination;
                            let expected = snapshot(before[if copied { source } else { i }].0);
                            assert_eq!(snapshot(values[i].0), expected);
                            assert_eq!(values[i].1, before[i].1);
                        }
                        let mut values = [(make(source_word), false), (make(1), true)];
                        let before = values;
                        $module::whole_product(&mut values, source, destination);
                        for i in 0..2 {
                            let copied = source < 2 && destination < 2 && i == destination;
                            let original = before[if copied { source } else { i }];
                            assert_eq!(snapshot(values[i].0), snapshot(original.0));
                            assert_eq!(values[i].1, original.1);
                        }
                        let mut values = [(make(source_word), false), (make(1), true)];
                        let before = values;
                        $module::via_helper(&mut values, source, destination);
                        for i in 0..2 {
                            let copied = source < 2 && destination < 2 && i == destination;
                            let expected = snapshot(before[if copied { source } else { i }].0);
                            assert_eq!(snapshot(values[i].0), expected);
                            assert_eq!(values[i].1, before[i].1);
                        }
                        let mut values = [(make(source_word), false), (make(1), true)];
                        let before = values;
                        $module::replace(&mut values, destination, replacement);
                        for i in 0..2 {
                            let expected = if i == destination {
                                (replacement != 0, replacement)
                            } else {
                                snapshot(before[i].0)
                            };
                            assert_eq!(snapshot(values[i].0), expected);
                            assert_eq!(values[i].1, before[i].1);
                        }
                        let mut values = [(make(source_word), false), (make(1), true)];
                        let before = values;
                        $module::outer_preservation(&mut values, replacement);
                        assert_eq!(snapshot(values[0].0), (replacement != 0, replacement));
                        assert_eq!(snapshot(values[1].0), snapshot(before[1].0));
                        assert_eq!(values[0].1, before[0].1);
                        assert_eq!(values[1].1, before[1].1);
                        let before = values;
                        $module::partial_payload(&mut values, destination, replacement);
                        for i in 0..2 {
                            let old = snapshot(before[i].0);
                            let expected = if i == destination && old.0 && replacement != 0 {
                                (true, replacement)
                            } else {
                                old
                            };
                            assert_eq!(snapshot(values[i].0), expected);
                            assert_eq!(values[i].1, before[i].1);
                        }
                        let mut bare = [make(source_word), make(1)];
                        let before = bare;
                        $module::bare_owner(&mut bare, destination);
                        for i in 0..2 {
                            let expected = if i == destination {
                                (false, 0)
                            } else {
                                snapshot(before[i])
                            };
                            assert_eq!(snapshot(bare[i]), expected);
                        }
                    }
                }
            }
        }
        let mut empty: [($module::Niche, bool); 0] = [];
        $module::copy_fields(&mut empty, 0, 0);
        $module::whole_product(&mut empty, 0, 0);
        $module::via_helper(&mut empty, 0, 0);
        $module::replace(&mut empty, 0, 1);
        $module::outer_preservation(&mut empty, 1);
        $module::partial_payload(&mut empty, 0, 1);
        let mut wrong = [(make(1), true)];
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            $module::wrong_sibling(&mut wrong, 0);
        }));
        assert!(panic.is_err());
    }};
}

#[cfg(test)]
#[test]
fn native_u8() {
    native_family!(option_u8, u8);
    native_family!(empty_u8, u8);
    native_family!(payload_u8, u8);
}

#[cfg(test)]
#[test]
fn native_u16() {
    native_family!(option_u16, u16);
    native_family!(empty_u16, u16);
    native_family!(payload_u16, u16);
}

#[cfg(test)]
#[test]
fn native_u32() {
    native_family!(option_u32, u32);
    native_family!(empty_u32, u32);
    native_family!(payload_u32, u32);
}

#[cfg(test)]
#[test]
fn native_u64() {
    native_family!(option_u64, u64);
    native_family!(empty_u64, u64);
    native_family!(payload_u64, u64);
}

#[cfg(test)]
#[test]
fn native_u128() {
    native_family!(option_u128, u128);
    native_family!(empty_u128, u128);
    native_family!(payload_u128, u128);
}

#[cfg(test)]
#[test]
fn native_usize() {
    native_family!(option_usize, usize);
    native_family!(empty_usize, usize);
    native_family!(payload_usize, usize);
}

#[cfg(test)]
#[test]
fn native_i8() {
    native_family!(option_i8, i8);
    native_family!(empty_i8, i8);
    native_family!(payload_i8, i8);
}

#[cfg(test)]
#[test]
fn native_i16() {
    native_family!(option_i16, i16);
    native_family!(empty_i16, i16);
    native_family!(payload_i16, i16);
}

#[cfg(test)]
#[test]
fn native_i32() {
    native_family!(option_i32, i32);
    native_family!(empty_i32, i32);
    native_family!(payload_i32, i32);
}

#[cfg(test)]
#[test]
fn native_i64() {
    native_family!(option_i64, i64);
    native_family!(empty_i64, i64);
    native_family!(payload_i64, i64);
}

#[cfg(test)]
#[test]
fn native_i128() {
    native_family!(option_i128, i128);
    native_family!(empty_i128, i128);
    native_family!(payload_i128, i128);
}

#[cfg(test)]
#[test]
fn native_isize() {
    native_family!(option_isize, isize);
    native_family!(empty_isize, isize);
    native_family!(payload_isize, isize);
}
