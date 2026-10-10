#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn operation_i32(word: i32) -> i32 {
    word ^ 0
}

macro_rules! integer_module {
    ($module:ident, $integer:ty, $operation:expr) => {
        pub mod $module {
            #[inline(never)]
            pub fn child(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    values[index] = $operation(word);
                }
            }
            #[inline(never)]
            pub fn returning_child(
                values: &mut [$integer],
                index: usize,
                word: $integer,
            ) -> $integer {
                values[index] = $operation(word);
                values[index]
            }
            pub fn selected(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    child(values, index, word);
                    assert!(values[index] == word);
                }
            }
            pub fn direct(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    values[index] = word;
                    assert!(values[index] == word);
                }
            }
            pub fn bounds(values: &mut [$integer], index: usize) {
                values[index] = 0;
            }
            pub fn wrong(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    child(values, index, word);
                    assert!(values[index] != word);
                }
            }
            pub fn untouched(values: &mut [$integer], index: usize, other: usize, word: $integer) {
                if index < values.len() && other < values.len() && index != other {
                    let previous = values[other];
                    child(values, index, word);
                    assert!(values[other] == previous);
                }
            }
            pub fn sequential(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    child(values, index, word);
                    child(values, index, word ^ 1);
                    assert!(values[index] == word ^ 1);
                }
            }
            pub fn branches(values: &mut [$integer], index: usize, word: $integer, flag: bool) {
                if index < values.len() {
                    let replacement = if flag { word } else { word ^ 1 };
                    child(values, index, replacement);
                    assert!(values[index] == replacement);
                }
            }
            pub fn scalar_return(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    let result = returning_child(values, index, word);
                    assert!(result == word && values[index] == word);
                }
            }
            #[inline(never)]
            pub fn nested_child(values: &mut [$integer], index: usize, word: $integer) {
                child(values, index, word);
            }
            pub fn nested(values: &mut [$integer], index: usize, word: $integer) {
                if index < values.len() {
                    nested_child(values, index, word);
                    assert!(values[index] == word);
                }
            }
            pub fn shared(values: &mut [$integer]) -> usize {
                shared_len(&*values)
            }
            #[inline(never)]
            pub fn shared_len(values: &[$integer]) -> usize {
                values.len()
            }
        }
    };
}
integer_module!(signed8, i8, core::convert::identity);
integer_module!(signed16, i16, core::convert::identity);
integer_module!(signed32, i32, crate::operation_i32);
integer_module!(signed64, i64, core::convert::identity);
integer_module!(signed128, i128, core::convert::identity);
integer_module!(signed_size, isize, core::convert::identity);
integer_module!(unsigned16, u16, core::convert::identity);
integer_module!(unsigned32, u32, core::convert::identity);
integer_module!(unsigned64, u64, core::convert::identity);
integer_module!(unsigned128, u128, core::convert::identity);
integer_module!(unsigned_size, usize, core::convert::identity);

#[cfg(external_control)]
pub fn external_i32(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        stage191_dependency::selected(values, index, word);
        assert!(values[index] == word);
    }
}

pub fn bool_unknown(values: &mut [bool], index: usize) {
    if index < values.len() {
        values[index] = true;
    }
}
pub fn char_unknown(values: &mut [char], index: usize) {
    if index < values.len() {
        values[index] = 'x';
    }
}
pub fn float_unknown(values: &mut [f32], index: usize) {
    if index < values.len() {
        values[index] = 1.0;
    }
}

#[cfg(test)]
extern crate std;
#[cfg(test)]
mod native {
    #[test]
    fn finite_129_all_integer_types() {
        macro_rules! exercise {
            ($module:ident, $integer:ty) => {{
                let mut values = [0 as $integer; 129];
                for index in 0..129 {
                    let word = index as $integer;
                    super::$module::direct(&mut values, index, word);
                    super::$module::selected(&mut values, index, word);
                    super::$module::sequential(&mut values, index, word);
                    super::$module::scalar_return(&mut values, index, word);
                    super::$module::branches(&mut values, index, word, index % 2 == 0);
                }
                super::$module::selected(&mut [], 0, 0);
                super::$module::direct(&mut values, 128, <$integer>::MIN);
                super::$module::selected(&mut values, 128, <$integer>::MAX);
            }};
        }
        exercise!(signed8, i8);
        exercise!(signed16, i16);
        exercise!(signed32, i32);
        exercise!(signed64, i64);
        exercise!(signed128, i128);
        exercise!(signed_size, isize);
        exercise!(unsigned16, u16);
        exercise!(unsigned32, u32);
        exercise!(unsigned64, u64);
        exercise!(unsigned128, u128);
        exercise!(unsigned_size, usize);
    }
    #[test]
    fn mutation_guard() {
        let mut values = [0_i32; 129];
        super::signed32::selected(&mut values, 128, -7);
        assert!(values[128] == -7);
    }
}
