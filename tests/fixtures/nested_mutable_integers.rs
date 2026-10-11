#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

macro_rules! integer_roots {
    ($module:ident, $integer:ty) => {
        pub mod $module {
            #[inline(never)]
            fn scalar(word: $integer) -> $integer {
                word ^ 0
            }
            #[inline(never)]
            fn leaf(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    values[0] = scalar(word);
                }
            }
            #[inline(never)]
            fn outer(values: &mut [$integer], word: $integer) -> $integer {
                leaf(&mut *(&mut *values), word);
                scalar(word)
            }
            #[inline(never)]
            fn deeper_outer(values: &mut [$integer], word: $integer) {
                outer(values, word);
            }
            pub fn selected(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    outer(values, word);
                    assert!(values[0] == word);
                }
            }
            pub fn sibling(values: &mut [$integer], word: $integer) {
                if values.len() > 1 {
                    let sibling = values[1];
                    outer(values, word);
                    assert!(values[0] == word);
                    assert!(values[1] == sibling);
                }
            }
            pub fn sequential(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    outer(values, word);
                    assert!(values[0] == word);
                    let next = word.wrapping_add(1);
                    outer(values, next);
                    assert!(values[0] == next);
                }
            }
            pub fn scalar_return(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    let returned = outer(values, word);
                    assert!(returned == word);
                    assert!(values[0] == returned);
                }
            }
            pub fn cast(values: &mut [$integer], word: i128) {
                if values.len() > 0 {
                    let converted = word as $integer;
                    outer(values, converted);
                    assert!(values[0] == converted);
                }
            }
            pub fn wrong(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    outer(values, word);
                    assert!(values[0] == (word ^ 1));
                }
            }
            pub fn bounds(values: &mut [$integer], word: $integer) {
                outer(values, word);
                assert!(values[0] == word);
            }
            pub fn deeper(values: &mut [$integer], word: $integer) {
                if values.len() > 0 {
                    deeper_outer(values, word);
                    assert!(values[0] == word);
                }
            }
            #[cfg(test)]
            pub fn native() {
                for length in 0..=129 {
                    for word in [<$integer>::MIN, 0, 17, <$integer>::MAX] {
                        let mut values = std::vec![0; length];
                        selected(&mut values, word);
                        sibling(&mut values, word);
                        sequential(&mut values, word);
                        scalar_return(&mut values, word);
                        cast(&mut values, -1);
                    }
                }
            }
        }
    };
}
integer_roots!(signed8, i8);
integer_roots!(signed16, i16);
integer_roots!(signed32, i32);
integer_roots!(signed64, i64);
integer_roots!(signed128, i128);
integer_roots!(signed_size, isize);
integer_roots!(unsigned16, u16);
integer_roots!(unsigned32, u32);
integer_roots!(unsigned64, u64);
integer_roots!(unsigned128, u128);
integer_roots!(unsigned_size, usize);

#[cfg(test)]
mod native_tests {
    #[test]
    fn mutation_guard() {
        super::signed32::selected(&mut [0; 129], -17);
    }
    #[test]
    fn all_original_types() {
        super::signed8::native();
        super::signed16::native();
        super::signed32::native();
        super::signed64::native();
        super::signed128::native();
        super::signed_size::native();
        super::unsigned16::native();
        super::unsigned32::native();
        super::unsigned64::native();
        super::unsigned128::native();
        super::unsigned_size::native();
    }
}
