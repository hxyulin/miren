#![no_std]
#![forbid(unsafe_code)]

macro_rules! table {
    ($name:ident, $a:ty, $b:ty, $r:ty) => {
        pub mod $name {
            #[inline(never)]
            pub fn first(a: $a, b: $b) -> $r {
                (a as $r).wrapping_add(b as $r)
            }
            #[inline(never)]
            pub fn second(a: $a, b: $b) -> $r {
                (a as $r).wrapping_add(b as $r) ^ 1
            }
            pub fn selected(index: usize, a: $a, b: $b) {
                let table: [fn($a, $b) -> $r; 2] = [first, second];
                if index < 2 {
                    let actual = table[index](a, b);
                    let expected = (a as $r).wrapping_add(b as $r);
                    assert!(actual == if index == 0 { expected } else { expected ^ 1 });
                }
            }
            pub fn wrong(index: usize, a: $a, b: $b) {
                let table: [fn($a, $b) -> $r; 2] = [first, second];
                if index < 2 {
                    let actual = table[index](a, b);
                    let expected = (a as $r).wrapping_add(b as $r);
                    assert!(actual != if index == 0 { expected } else { expected ^ 1 });
                }
            }
            pub fn opaque(callback: fn($a, $b) -> $r, a: $a, b: $b) {
                let table = [first as fn($a, $b) -> $r, callback];
                let actual = table[1](a, b);
                assert!(actual == (a as $r).wrapping_add(b as $r));
            }
        }
    };
}

table!(unsigned8, u8, u8, u8);
table!(unsigned16, u16, u16, u16);
table!(unsigned32, u32, u32, u32);
table!(unsigned64, u64, u64, u64);
table!(unsigned128, u128, u128, u128);
table!(unsigned_pointer, usize, usize, usize);
table!(signed8, i8, i8, i8);
table!(signed16, i16, i16, i16);
table!(signed32, i32, i32, i32);
table!(signed64, i64, i64, i64);
table!(signed128, i128, i128, i128);
table!(signed_pointer, isize, isize, isize);
table!(cross_width, u16, i32, i64);
table!(cross_sign, i32, u32, u64);
table!(pointer_first, usize, u64, u32);
table!(pointer_second, u64, usize, i64);
table!(signed_pointer_first, isize, i64, i32);
table!(signed_pointer_second, i64, isize, u64);

#[inline(never)]
pub fn add(a: u16, b: u16) -> u16 {
    a + b
}
#[inline(never)]
pub fn multiply(a: u16, b: u16) -> u16 {
    a * b
}
pub fn checked_overflow(index: usize, a: u16, b: u16) {
    let table: [fn(u16, u16) -> u16; 2] = [add, multiply];
    if index < 2 {
        let _ = table[index](a, b);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn mutation_guard() {
        macro_rules! exercise {
            ($name:ident) => {
                for index in [0, 1] {
                    super::$name::selected(index, 129 as _, 7 as _);
                    super::$name::selected(index, 0 as _, 0 as _);
                    super::$name::selected(index, -1_i128 as _, 1 as _);
                }
            };
        }
        exercise!(unsigned8);
        exercise!(unsigned16);
        exercise!(unsigned32);
        exercise!(unsigned64);
        exercise!(unsigned128);
        exercise!(unsigned_pointer);
        exercise!(signed8);
        exercise!(signed16);
        exercise!(signed32);
        exercise!(signed64);
        exercise!(signed128);
        exercise!(signed_pointer);
        exercise!(cross_width);
        exercise!(cross_sign);
        exercise!(pointer_first);
        exercise!(pointer_second);
        exercise!(signed_pointer_first);
        exercise!(signed_pointer_second);
    }
}
