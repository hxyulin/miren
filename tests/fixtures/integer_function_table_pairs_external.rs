#![no_std]
#![forbid(unsafe_code)]
extern crate integer_pair_external;
macro_rules! pair {
    ($module:ident, $argument:ty, $result:ty) => {
        pub mod $module {
            #[inline(never)]
            pub fn local(word: $argument) -> $result {
                word as $result
            }
            pub fn external(index: usize, word: $argument) {
                let table: [fn($argument) -> $result; 2] = [
                    integer_pair_external::$module::first,
                    integer_pair_external::$module::second,
                ];
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
            pub fn infeasible(word: $argument) {
                let table: [fn($argument) -> $result; 2] =
                    [local, integer_pair_external::$module::second];
                let index = 0;
                assert!(table[index](word) == word as $result);
            }
            #[cfg(test)]
            mod tests {
                #[test]
                fn native_boundaries() {
                    for word in [<$argument>::MIN, <$argument>::MAX, 0, 1] {
                        for index in 0..2 {
                            super::external(index, word);
                        }
                        super::infeasible(word);
                    }
                }
            }
        }
    };
}
pair!(u8_to_u8, u8, u8);
pair!(u8_to_u16, u8, u16);
pair!(u8_to_u32, u8, u32);
pair!(u8_to_u64, u8, u64);
pair!(u8_to_u128, u8, u128);
pair!(u8_to_usize, u8, usize);
pair!(u8_to_i8, u8, i8);
pair!(u8_to_i16, u8, i16);
pair!(u8_to_i32, u8, i32);
pair!(u8_to_i64, u8, i64);
pair!(u8_to_i128, u8, i128);
pair!(u8_to_isize, u8, isize);
pair!(u16_to_u8, u16, u8);
pair!(u16_to_u16, u16, u16);
pair!(u16_to_u32, u16, u32);
pair!(u16_to_u64, u16, u64);
pair!(u16_to_u128, u16, u128);
pair!(u16_to_usize, u16, usize);
pair!(u16_to_i8, u16, i8);
pair!(u16_to_i16, u16, i16);
pair!(u16_to_i32, u16, i32);
pair!(u16_to_i64, u16, i64);
pair!(u16_to_i128, u16, i128);
pair!(u16_to_isize, u16, isize);
pair!(u32_to_u8, u32, u8);
pair!(u32_to_u16, u32, u16);
pair!(u32_to_u32, u32, u32);
pair!(u32_to_u64, u32, u64);
pair!(u32_to_u128, u32, u128);
pair!(u32_to_usize, u32, usize);
pair!(u32_to_i8, u32, i8);
pair!(u32_to_i16, u32, i16);
pair!(u32_to_i32, u32, i32);
pair!(u32_to_i64, u32, i64);
pair!(u32_to_i128, u32, i128);
pair!(u32_to_isize, u32, isize);
pair!(u64_to_u8, u64, u8);
pair!(u64_to_u16, u64, u16);
pair!(u64_to_u32, u64, u32);
pair!(u64_to_u64, u64, u64);
pair!(u64_to_u128, u64, u128);
pair!(u64_to_usize, u64, usize);
pair!(u64_to_i8, u64, i8);
pair!(u64_to_i16, u64, i16);
pair!(u64_to_i32, u64, i32);
pair!(u64_to_i64, u64, i64);
pair!(u64_to_i128, u64, i128);
pair!(u64_to_isize, u64, isize);
pair!(u128_to_u8, u128, u8);
pair!(u128_to_u16, u128, u16);
pair!(u128_to_u32, u128, u32);
pair!(u128_to_u64, u128, u64);
pair!(u128_to_u128, u128, u128);
pair!(u128_to_usize, u128, usize);
pair!(u128_to_i8, u128, i8);
pair!(u128_to_i16, u128, i16);
pair!(u128_to_i32, u128, i32);
pair!(u128_to_i64, u128, i64);
pair!(u128_to_i128, u128, i128);
pair!(u128_to_isize, u128, isize);
pair!(usize_to_u8, usize, u8);
pair!(usize_to_u16, usize, u16);
pair!(usize_to_u32, usize, u32);
pair!(usize_to_u64, usize, u64);
pair!(usize_to_u128, usize, u128);
pair!(usize_to_usize, usize, usize);
pair!(usize_to_i8, usize, i8);
pair!(usize_to_i16, usize, i16);
pair!(usize_to_i32, usize, i32);
pair!(usize_to_i64, usize, i64);
pair!(usize_to_i128, usize, i128);
pair!(usize_to_isize, usize, isize);
pair!(i8_to_u8, i8, u8);
pair!(i8_to_u16, i8, u16);
pair!(i8_to_u32, i8, u32);
pair!(i8_to_u64, i8, u64);
pair!(i8_to_u128, i8, u128);
pair!(i8_to_usize, i8, usize);
pair!(i8_to_i8, i8, i8);
pair!(i8_to_i16, i8, i16);
pair!(i8_to_i32, i8, i32);
pair!(i8_to_i64, i8, i64);
pair!(i8_to_i128, i8, i128);
pair!(i8_to_isize, i8, isize);
pair!(i16_to_u8, i16, u8);
pair!(i16_to_u16, i16, u16);
pair!(i16_to_u32, i16, u32);
pair!(i16_to_u64, i16, u64);
pair!(i16_to_u128, i16, u128);
pair!(i16_to_usize, i16, usize);
pair!(i16_to_i8, i16, i8);
pair!(i16_to_i16, i16, i16);
pair!(i16_to_i32, i16, i32);
pair!(i16_to_i64, i16, i64);
pair!(i16_to_i128, i16, i128);
pair!(i16_to_isize, i16, isize);
pair!(i32_to_u8, i32, u8);
pair!(i32_to_u16, i32, u16);
pair!(i32_to_u32, i32, u32);
pair!(i32_to_u64, i32, u64);
pair!(i32_to_u128, i32, u128);
pair!(i32_to_usize, i32, usize);
pair!(i32_to_i8, i32, i8);
pair!(i32_to_i16, i32, i16);
pair!(i32_to_i32, i32, i32);
pair!(i32_to_i64, i32, i64);
pair!(i32_to_i128, i32, i128);
pair!(i32_to_isize, i32, isize);
pair!(i64_to_u8, i64, u8);
pair!(i64_to_u16, i64, u16);
pair!(i64_to_u32, i64, u32);
pair!(i64_to_u64, i64, u64);
pair!(i64_to_u128, i64, u128);
pair!(i64_to_usize, i64, usize);
pair!(i64_to_i8, i64, i8);
pair!(i64_to_i16, i64, i16);
pair!(i64_to_i32, i64, i32);
pair!(i64_to_i64, i64, i64);
pair!(i64_to_i128, i64, i128);
pair!(i64_to_isize, i64, isize);
pair!(i128_to_u8, i128, u8);
pair!(i128_to_u16, i128, u16);
pair!(i128_to_u32, i128, u32);
pair!(i128_to_u64, i128, u64);
pair!(i128_to_u128, i128, u128);
pair!(i128_to_usize, i128, usize);
pair!(i128_to_i8, i128, i8);
pair!(i128_to_i16, i128, i16);
pair!(i128_to_i32, i128, i32);
pair!(i128_to_i64, i128, i64);
pair!(i128_to_i128, i128, i128);
pair!(i128_to_isize, i128, isize);
pair!(isize_to_u8, isize, u8);
pair!(isize_to_u16, isize, u16);
pair!(isize_to_u32, isize, u32);
pair!(isize_to_u64, isize, u64);
pair!(isize_to_u128, isize, u128);
pair!(isize_to_usize, isize, usize);
pair!(isize_to_i8, isize, i8);
pair!(isize_to_i16, isize, i16);
pair!(isize_to_i32, isize, i32);
pair!(isize_to_i64, isize, i64);
pair!(isize_to_i128, isize, i128);
pair!(isize_to_isize, isize, isize);
