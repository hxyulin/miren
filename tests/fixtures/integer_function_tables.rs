#![no_std]
#![forbid(unsafe_code)]

macro_rules! integer_table {
    ($module:ident, $integer:ty) => {
        pub mod $module {
            #[inline(never)]
            pub fn first(word: $integer) -> $integer {
                word
            }
            #[inline(never)]
            pub fn second(word: $integer) -> $integer {
                word ^ 1
            }
            #[inline(never)]
            pub fn increment(word: $integer) -> $integer {
                word.wrapping_add(1)
            }
            #[inline(never)]
            pub fn decrement(word: $integer) -> $integer {
                word.wrapping_sub(1)
            }
            #[inline(never)]
            pub fn checked(word: $integer) -> $integer {
                word + 1
            }
            pub fn selected(index: usize, word: $integer) {
                let table: [fn($integer) -> $integer; 2] = [first, second];
                if index < 2 {
                    assert!(table[index](word) == if index == 0 { word } else { word ^ 1 });
                }
            }
            pub fn wrong(index: usize, word: $integer) {
                let table: [fn($integer) -> $integer; 2] = [first, second];
                if index < 2 {
                    assert!(table[index](word) == word);
                }
            }
            pub fn wrapping(index: usize, word: $integer) {
                let table: [fn($integer) -> $integer; 2] = [increment, decrement];
                if index < 2 {
                    assert!(
                        table[index](word)
                            == if index == 0 {
                                word.wrapping_add(1)
                            } else {
                                word.wrapping_sub(1)
                            }
                    );
                }
            }
            pub fn overflow(index: usize) {
                let table: [fn($integer) -> $integer; 2] = [first, checked];
                if index < 2 {
                    let _ = table[index](<$integer>::MAX);
                }
            }
            pub fn opaque(index: usize, word: $integer, other: fn($integer) -> $integer) {
                let table: [fn($integer) -> $integer; 2] = [first, other];
                if index < 2 {
                    assert!(table[index](word) == word);
                }
            }
            #[cfg(test)]
            mod tests {
                #[test]
                fn native_boundaries() {
                    for word in [<$integer>::MIN, <$integer>::MAX, 0, 1] {
                        for index in 0..2 {
                            super::selected(index, word);
                            super::wrapping(index, word);
                        }
                    }
                }
            }
        }
    };
}
integer_table!(u8_table, u8);
integer_table!(u16_table, u16);
integer_table!(u32_table, u32);
integer_table!(u64_table, u64);
integer_table!(u128_table, u128);
integer_table!(usize_table, usize);
integer_table!(i8_table, i8);
integer_table!(i16_table, i16);
integer_table!(i32_table, i32);
integer_table!(i64_table, i64);
integer_table!(i128_table, i128);
integer_table!(isize_table, isize);

#[inline(never)]
pub fn bool_first(word: bool) -> bool {
    word
}
#[inline(never)]
pub fn bool_second(word: bool) -> bool {
    !word
}
#[inline(never)]
pub fn char_first(word: char) -> char {
    word
}
#[inline(never)]
pub fn char_second(_: char) -> char {
    'x'
}
#[inline(never)]
pub fn float_first(word: f32) -> f32 {
    word
}
#[inline(never)]
pub fn float_second(word: f32) -> f32 {
    word + 1.0
}
#[inline(never)]
pub fn nz_first(word: core::num::NonZeroU16) -> core::num::NonZeroU16 {
    word
}
#[inline(never)]
pub fn nz_second(word: core::num::NonZeroU16) -> core::num::NonZeroU16 {
    word
}
#[inline(never)]
pub fn widened_first(word: u32) -> u64 {
    word as u64
}
#[inline(never)]
pub fn widened_second(word: u32) -> u64 {
    word as u64 ^ 1
}
#[inline(never)]
pub fn pair_first(word: u32, other: u32) -> u32 {
    word ^ other
}
#[inline(never)]
pub fn pair_second(word: u32, other: u32) -> u32 {
    word ^ other ^ 1
}
#[inline(never)]
pub extern "C" fn c_first(word: u32) -> u32 {
    word
}
#[inline(never)]
pub extern "C" fn c_second(word: u32) -> u32 {
    word ^ 1
}
pub fn bool_unknown(index: usize, word: bool) {
    let table: [fn(bool) -> bool; 2] = [bool_first, bool_second];
    if index < 2 {
        assert!(table[index](word) == word);
    }
}
pub fn char_unknown(index: usize, word: char) {
    let table: [fn(char) -> char; 2] = [char_first, char_second];
    if index < 2 {
        assert!(table[index](word) == word);
    }
}
pub fn float_unknown(index: usize, word: f32) {
    let table: [fn(f32) -> f32; 2] = [float_first, float_second];
    if index < 2 {
        assert!(table[index](word) == word);
    }
}
pub fn nz_unknown(index: usize, word: core::num::NonZeroU16) {
    let table: [fn(core::num::NonZeroU16) -> core::num::NonZeroU16; 2] = [nz_first, nz_second];
    if index < 2 {
        assert!(table[index](word).get() == word.get());
    }
}
pub fn result_unknown(index: usize, word: u32) {
    let table: [fn(u32) -> u64; 2] = [widened_first, widened_second];
    if index < 2 {
        assert!(table[index](word) == word as u64);
    }
}
pub fn arity_unknown(index: usize, word: u32, other: u32) {
    let table: [fn(u32, u32) -> u32; 2] = [pair_first, pair_second];
    if index < 2 {
        assert!(table[index](word, other) == word ^ other);
    }
}
pub fn abi_unknown(index: usize, word: u32) {
    let table: [extern "C" fn(u32) -> u32; 2] = [c_first, c_second];
    if index < 2 {
        assert!(table[index](word) == word);
    }
}

#[inline(never)]
pub fn identity<T>(word: T) -> T {
    word
}
pub struct Operations;
impl Operations {
    #[inline(never)]
    pub fn flip(word: i32) -> i32 {
        word ^ 1
    }
}
pub fn associated(index: usize, word: i32) {
    let table: [fn(i32) -> i32; 2] = [identity::<i32>, Operations::flip];
    if index < 2 {
        assert!(table[index](word) == if index == 0 { word } else { word ^ 1 });
    }
}
pub fn wrong_associated(index: usize, word: i32) {
    let table: [fn(i32) -> i32; 2] = [identity::<i32>, Operations::flip];
    if index < 2 {
        assert!(table[index](word) == word);
    }
}
