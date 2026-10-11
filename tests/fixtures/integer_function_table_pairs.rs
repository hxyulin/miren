#![no_std]
#![forbid(unsafe_code)]

macro_rules! integer_pair_table {
    ($module:ident, $argument:ty, $result:ty) => {
        pub mod $module {
            #[inline(never)]
            pub fn first(word: $argument) -> $result {
                word as $result
            }
            #[inline(never)]
            pub fn second(word: $argument) -> $result {
                (word ^ 1) as $result
            }
            pub fn selected(index: usize, word: $argument) {
                let table: [fn($argument) -> $result; 2] = [first, second];
                if index < 2 {
                    let actual = table[index](word);
                    let expected = if index == 0 {
                        word as $result
                    } else {
                        (word ^ 1) as $result
                    };
                    assert!(actual == expected);
                }
            }
            pub fn wrong(index: usize, word: $argument) {
                let table: [fn($argument) -> $result; 2] = [first, second];
                if index < 2 {
                    assert!(table[index](word) == word as $result);
                }
            }
            pub fn opaque(index: usize, word: $argument, other: fn($argument) -> $result) {
                let table: [fn($argument) -> $result; 2] = [first, other];
                if index < 2 {
                    assert!(table[index](word) == word as $result);
                }
            }
            #[cfg(test)]
            mod tests {
                #[test]
                fn native_boundaries() {
                    for word in [<$argument>::MIN, <$argument>::MAX, 0, 1] {
                        for index in 0..2 {
                            super::selected(index, word);
                        }
                    }
                }
            }
        }
    };
}
integer_pair_table!(u8_to_u8, u8, u8);
integer_pair_table!(u8_to_u16, u8, u16);
integer_pair_table!(u8_to_u32, u8, u32);
integer_pair_table!(u8_to_u64, u8, u64);
integer_pair_table!(u8_to_u128, u8, u128);
integer_pair_table!(u8_to_usize, u8, usize);
integer_pair_table!(u8_to_i8, u8, i8);
integer_pair_table!(u8_to_i16, u8, i16);
integer_pair_table!(u8_to_i32, u8, i32);
integer_pair_table!(u8_to_i64, u8, i64);
integer_pair_table!(u8_to_i128, u8, i128);
integer_pair_table!(u8_to_isize, u8, isize);
integer_pair_table!(u16_to_u8, u16, u8);
integer_pair_table!(u16_to_u16, u16, u16);
integer_pair_table!(u16_to_u32, u16, u32);
integer_pair_table!(u16_to_u64, u16, u64);
integer_pair_table!(u16_to_u128, u16, u128);
integer_pair_table!(u16_to_usize, u16, usize);
integer_pair_table!(u16_to_i8, u16, i8);
integer_pair_table!(u16_to_i16, u16, i16);
integer_pair_table!(u16_to_i32, u16, i32);
integer_pair_table!(u16_to_i64, u16, i64);
integer_pair_table!(u16_to_i128, u16, i128);
integer_pair_table!(u16_to_isize, u16, isize);
integer_pair_table!(u32_to_u8, u32, u8);
integer_pair_table!(u32_to_u16, u32, u16);
integer_pair_table!(u32_to_u32, u32, u32);
integer_pair_table!(u32_to_u64, u32, u64);
integer_pair_table!(u32_to_u128, u32, u128);
integer_pair_table!(u32_to_usize, u32, usize);
integer_pair_table!(u32_to_i8, u32, i8);
integer_pair_table!(u32_to_i16, u32, i16);
integer_pair_table!(u32_to_i32, u32, i32);
integer_pair_table!(u32_to_i64, u32, i64);
integer_pair_table!(u32_to_i128, u32, i128);
integer_pair_table!(u32_to_isize, u32, isize);
integer_pair_table!(u64_to_u8, u64, u8);
integer_pair_table!(u64_to_u16, u64, u16);
integer_pair_table!(u64_to_u32, u64, u32);
integer_pair_table!(u64_to_u64, u64, u64);
integer_pair_table!(u64_to_u128, u64, u128);
integer_pair_table!(u64_to_usize, u64, usize);
integer_pair_table!(u64_to_i8, u64, i8);
integer_pair_table!(u64_to_i16, u64, i16);
integer_pair_table!(u64_to_i32, u64, i32);
integer_pair_table!(u64_to_i64, u64, i64);
integer_pair_table!(u64_to_i128, u64, i128);
integer_pair_table!(u64_to_isize, u64, isize);
integer_pair_table!(u128_to_u8, u128, u8);
integer_pair_table!(u128_to_u16, u128, u16);
integer_pair_table!(u128_to_u32, u128, u32);
integer_pair_table!(u128_to_u64, u128, u64);
integer_pair_table!(u128_to_u128, u128, u128);
integer_pair_table!(u128_to_usize, u128, usize);
integer_pair_table!(u128_to_i8, u128, i8);
integer_pair_table!(u128_to_i16, u128, i16);
integer_pair_table!(u128_to_i32, u128, i32);
integer_pair_table!(u128_to_i64, u128, i64);
integer_pair_table!(u128_to_i128, u128, i128);
integer_pair_table!(u128_to_isize, u128, isize);
integer_pair_table!(usize_to_u8, usize, u8);
integer_pair_table!(usize_to_u16, usize, u16);
integer_pair_table!(usize_to_u32, usize, u32);
integer_pair_table!(usize_to_u64, usize, u64);
integer_pair_table!(usize_to_u128, usize, u128);
integer_pair_table!(usize_to_usize, usize, usize);
integer_pair_table!(usize_to_i8, usize, i8);
integer_pair_table!(usize_to_i16, usize, i16);
integer_pair_table!(usize_to_i32, usize, i32);
integer_pair_table!(usize_to_i64, usize, i64);
integer_pair_table!(usize_to_i128, usize, i128);
integer_pair_table!(usize_to_isize, usize, isize);
integer_pair_table!(i8_to_u8, i8, u8);
integer_pair_table!(i8_to_u16, i8, u16);
integer_pair_table!(i8_to_u32, i8, u32);
integer_pair_table!(i8_to_u64, i8, u64);
integer_pair_table!(i8_to_u128, i8, u128);
integer_pair_table!(i8_to_usize, i8, usize);
integer_pair_table!(i8_to_i8, i8, i8);
integer_pair_table!(i8_to_i16, i8, i16);
integer_pair_table!(i8_to_i32, i8, i32);
integer_pair_table!(i8_to_i64, i8, i64);
integer_pair_table!(i8_to_i128, i8, i128);
integer_pair_table!(i8_to_isize, i8, isize);
integer_pair_table!(i16_to_u8, i16, u8);
integer_pair_table!(i16_to_u16, i16, u16);
integer_pair_table!(i16_to_u32, i16, u32);
integer_pair_table!(i16_to_u64, i16, u64);
integer_pair_table!(i16_to_u128, i16, u128);
integer_pair_table!(i16_to_usize, i16, usize);
integer_pair_table!(i16_to_i8, i16, i8);
integer_pair_table!(i16_to_i16, i16, i16);
integer_pair_table!(i16_to_i32, i16, i32);
integer_pair_table!(i16_to_i64, i16, i64);
integer_pair_table!(i16_to_i128, i16, i128);
integer_pair_table!(i16_to_isize, i16, isize);
integer_pair_table!(i32_to_u8, i32, u8);
integer_pair_table!(i32_to_u16, i32, u16);
integer_pair_table!(i32_to_u32, i32, u32);
integer_pair_table!(i32_to_u64, i32, u64);
integer_pair_table!(i32_to_u128, i32, u128);
integer_pair_table!(i32_to_usize, i32, usize);
integer_pair_table!(i32_to_i8, i32, i8);
integer_pair_table!(i32_to_i16, i32, i16);
integer_pair_table!(i32_to_i32, i32, i32);
integer_pair_table!(i32_to_i64, i32, i64);
integer_pair_table!(i32_to_i128, i32, i128);
integer_pair_table!(i32_to_isize, i32, isize);
integer_pair_table!(i64_to_u8, i64, u8);
integer_pair_table!(i64_to_u16, i64, u16);
integer_pair_table!(i64_to_u32, i64, u32);
integer_pair_table!(i64_to_u64, i64, u64);
integer_pair_table!(i64_to_u128, i64, u128);
integer_pair_table!(i64_to_usize, i64, usize);
integer_pair_table!(i64_to_i8, i64, i8);
integer_pair_table!(i64_to_i16, i64, i16);
integer_pair_table!(i64_to_i32, i64, i32);
integer_pair_table!(i64_to_i64, i64, i64);
integer_pair_table!(i64_to_i128, i64, i128);
integer_pair_table!(i64_to_isize, i64, isize);
integer_pair_table!(i128_to_u8, i128, u8);
integer_pair_table!(i128_to_u16, i128, u16);
integer_pair_table!(i128_to_u32, i128, u32);
integer_pair_table!(i128_to_u64, i128, u64);
integer_pair_table!(i128_to_u128, i128, u128);
integer_pair_table!(i128_to_usize, i128, usize);
integer_pair_table!(i128_to_i8, i128, i8);
integer_pair_table!(i128_to_i16, i128, i16);
integer_pair_table!(i128_to_i32, i128, i32);
integer_pair_table!(i128_to_i64, i128, i64);
integer_pair_table!(i128_to_i128, i128, i128);
integer_pair_table!(i128_to_isize, i128, isize);
integer_pair_table!(isize_to_u8, isize, u8);
integer_pair_table!(isize_to_u16, isize, u16);
integer_pair_table!(isize_to_u32, isize, u32);
integer_pair_table!(isize_to_u64, isize, u64);
integer_pair_table!(isize_to_u128, isize, u128);
integer_pair_table!(isize_to_usize, isize, usize);
integer_pair_table!(isize_to_i8, isize, i8);
integer_pair_table!(isize_to_i16, isize, i16);
integer_pair_table!(isize_to_i32, isize, i32);
integer_pair_table!(isize_to_i64, isize, i64);
integer_pair_table!(isize_to_i128, isize, i128);
integer_pair_table!(isize_to_isize, isize, isize);
