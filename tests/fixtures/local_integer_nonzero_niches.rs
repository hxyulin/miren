#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
pub enum WordU8 {
    Empty,
    Word(core::num::NonZeroU8),
}
#[derive(Clone, Copy)]
pub enum ReverseU8 {
    Word(core::num::NonZeroU8),
    Empty,
}
#[inline(never)]
pub fn get_u8(value: core::num::NonZeroU8) -> u8 {
    value.get()
}
pub fn read_u8(values: &[WordU8], index: usize) {
    if index < values.len()
        && let WordU8::Word(value) = values[index]
    {
        assert!(get_u8(value) == value.get());
        assert!(get_u8(value) != 0);
    }
}
pub fn reverse_u8(values: &[ReverseU8], index: usize) {
    if index < values.len()
        && let ReverseU8::Word(value) = values[index]
    {
        assert!(get_u8(value) == value.get());
        assert!(get_u8(value) != 0);
    }
}
pub fn wrong_u8(values: &[WordU8], index: usize) {
    if index < values.len()
        && let WordU8::Word(value) = values[index]
    {
        assert!(get_u8(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordU16 {
    Empty,
    Word(core::num::NonZeroU16),
}
#[derive(Clone, Copy)]
pub enum ReverseU16 {
    Word(core::num::NonZeroU16),
    Empty,
}
#[inline(never)]
pub fn get_u16(value: core::num::NonZeroU16) -> u16 {
    value.get()
}
pub fn read_u16(values: &[WordU16], index: usize) {
    if index < values.len()
        && let WordU16::Word(value) = values[index]
    {
        assert!(get_u16(value) == value.get());
        assert!(get_u16(value) != 0);
    }
}
pub fn reverse_u16(values: &[ReverseU16], index: usize) {
    if index < values.len()
        && let ReverseU16::Word(value) = values[index]
    {
        assert!(get_u16(value) == value.get());
        assert!(get_u16(value) != 0);
    }
}
pub fn wrong_u16(values: &[WordU16], index: usize) {
    if index < values.len()
        && let WordU16::Word(value) = values[index]
    {
        assert!(get_u16(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordU32 {
    Empty,
    Word(core::num::NonZeroU32),
}
#[derive(Clone, Copy)]
pub enum ReverseU32 {
    Word(core::num::NonZeroU32),
    Empty,
}
#[inline(never)]
pub fn get_u32(value: core::num::NonZeroU32) -> u32 {
    value.get()
}
pub fn read_u32(values: &[WordU32], index: usize) {
    if index < values.len()
        && let WordU32::Word(value) = values[index]
    {
        assert!(get_u32(value) == value.get());
        assert!(get_u32(value) != 0);
    }
}
pub fn reverse_u32(values: &[ReverseU32], index: usize) {
    if index < values.len()
        && let ReverseU32::Word(value) = values[index]
    {
        assert!(get_u32(value) == value.get());
        assert!(get_u32(value) != 0);
    }
}
pub fn wrong_u32(values: &[WordU32], index: usize) {
    if index < values.len()
        && let WordU32::Word(value) = values[index]
    {
        assert!(get_u32(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordU64 {
    Empty,
    Word(core::num::NonZeroU64),
}
#[derive(Clone, Copy)]
pub enum ReverseU64 {
    Word(core::num::NonZeroU64),
    Empty,
}
#[inline(never)]
pub fn get_u64(value: core::num::NonZeroU64) -> u64 {
    value.get()
}
pub fn read_u64(values: &[WordU64], index: usize) {
    if index < values.len()
        && let WordU64::Word(value) = values[index]
    {
        assert!(get_u64(value) == value.get());
        assert!(get_u64(value) != 0);
    }
}
pub fn reverse_u64(values: &[ReverseU64], index: usize) {
    if index < values.len()
        && let ReverseU64::Word(value) = values[index]
    {
        assert!(get_u64(value) == value.get());
        assert!(get_u64(value) != 0);
    }
}
pub fn wrong_u64(values: &[WordU64], index: usize) {
    if index < values.len()
        && let WordU64::Word(value) = values[index]
    {
        assert!(get_u64(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordU128 {
    Empty,
    Word(core::num::NonZeroU128),
}
#[derive(Clone, Copy)]
pub enum ReverseU128 {
    Word(core::num::NonZeroU128),
    Empty,
}
#[inline(never)]
pub fn get_u128(value: core::num::NonZeroU128) -> u128 {
    value.get()
}
pub fn read_u128(values: &[WordU128], index: usize) {
    if index < values.len()
        && let WordU128::Word(value) = values[index]
    {
        assert!(get_u128(value) == value.get());
        assert!(get_u128(value) != 0);
    }
}
pub fn reverse_u128(values: &[ReverseU128], index: usize) {
    if index < values.len()
        && let ReverseU128::Word(value) = values[index]
    {
        assert!(get_u128(value) == value.get());
        assert!(get_u128(value) != 0);
    }
}
pub fn wrong_u128(values: &[WordU128], index: usize) {
    if index < values.len()
        && let WordU128::Word(value) = values[index]
    {
        assert!(get_u128(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordUsize {
    Empty,
    Word(core::num::NonZeroUsize),
}
#[derive(Clone, Copy)]
pub enum ReverseUsize {
    Word(core::num::NonZeroUsize),
    Empty,
}
#[inline(never)]
pub fn get_usize(value: core::num::NonZeroUsize) -> usize {
    value.get()
}
pub fn read_usize(values: &[WordUsize], index: usize) {
    if index < values.len()
        && let WordUsize::Word(value) = values[index]
    {
        assert!(get_usize(value) == value.get());
        assert!(get_usize(value) != 0);
    }
}
pub fn reverse_usize(values: &[ReverseUsize], index: usize) {
    if index < values.len()
        && let ReverseUsize::Word(value) = values[index]
    {
        assert!(get_usize(value) == value.get());
        assert!(get_usize(value) != 0);
    }
}
pub fn wrong_usize(values: &[WordUsize], index: usize) {
    if index < values.len()
        && let WordUsize::Word(value) = values[index]
    {
        assert!(get_usize(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordI8 {
    Empty,
    Word(core::num::NonZeroI8),
}
#[derive(Clone, Copy)]
pub enum ReverseI8 {
    Word(core::num::NonZeroI8),
    Empty,
}
#[inline(never)]
pub fn get_i8(value: core::num::NonZeroI8) -> i8 {
    value.get()
}
pub fn read_i8(values: &[WordI8], index: usize) {
    if index < values.len()
        && let WordI8::Word(value) = values[index]
    {
        assert!(get_i8(value) == value.get());
        assert!(get_i8(value) != 0);
    }
}
pub fn reverse_i8(values: &[ReverseI8], index: usize) {
    if index < values.len()
        && let ReverseI8::Word(value) = values[index]
    {
        assert!(get_i8(value) == value.get());
        assert!(get_i8(value) != 0);
    }
}
pub fn wrong_i8(values: &[WordI8], index: usize) {
    if index < values.len()
        && let WordI8::Word(value) = values[index]
    {
        assert!(get_i8(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordI16 {
    Empty,
    Word(core::num::NonZeroI16),
}
#[derive(Clone, Copy)]
pub enum ReverseI16 {
    Word(core::num::NonZeroI16),
    Empty,
}
#[inline(never)]
pub fn get_i16(value: core::num::NonZeroI16) -> i16 {
    value.get()
}
pub fn read_i16(values: &[WordI16], index: usize) {
    if index < values.len()
        && let WordI16::Word(value) = values[index]
    {
        assert!(get_i16(value) == value.get());
        assert!(get_i16(value) != 0);
    }
}
pub fn reverse_i16(values: &[ReverseI16], index: usize) {
    if index < values.len()
        && let ReverseI16::Word(value) = values[index]
    {
        assert!(get_i16(value) == value.get());
        assert!(get_i16(value) != 0);
    }
}
pub fn wrong_i16(values: &[WordI16], index: usize) {
    if index < values.len()
        && let WordI16::Word(value) = values[index]
    {
        assert!(get_i16(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordI32 {
    Empty,
    Word(core::num::NonZeroI32),
}
#[derive(Clone, Copy)]
pub enum ReverseI32 {
    Word(core::num::NonZeroI32),
    Empty,
}
#[inline(never)]
pub fn get_i32(value: core::num::NonZeroI32) -> i32 {
    value.get()
}
pub fn read_i32(values: &[WordI32], index: usize) {
    if index < values.len()
        && let WordI32::Word(value) = values[index]
    {
        assert!(get_i32(value) == value.get());
        assert!(get_i32(value) != 0);
    }
}
pub fn reverse_i32(values: &[ReverseI32], index: usize) {
    if index < values.len()
        && let ReverseI32::Word(value) = values[index]
    {
        assert!(get_i32(value) == value.get());
        assert!(get_i32(value) != 0);
    }
}
pub fn wrong_i32(values: &[WordI32], index: usize) {
    if index < values.len()
        && let WordI32::Word(value) = values[index]
    {
        assert!(get_i32(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordI64 {
    Empty,
    Word(core::num::NonZeroI64),
}
#[derive(Clone, Copy)]
pub enum ReverseI64 {
    Word(core::num::NonZeroI64),
    Empty,
}
#[inline(never)]
pub fn get_i64(value: core::num::NonZeroI64) -> i64 {
    value.get()
}
pub fn read_i64(values: &[WordI64], index: usize) {
    if index < values.len()
        && let WordI64::Word(value) = values[index]
    {
        assert!(get_i64(value) == value.get());
        assert!(get_i64(value) != 0);
    }
}
pub fn reverse_i64(values: &[ReverseI64], index: usize) {
    if index < values.len()
        && let ReverseI64::Word(value) = values[index]
    {
        assert!(get_i64(value) == value.get());
        assert!(get_i64(value) != 0);
    }
}
pub fn wrong_i64(values: &[WordI64], index: usize) {
    if index < values.len()
        && let WordI64::Word(value) = values[index]
    {
        assert!(get_i64(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordI128 {
    Empty,
    Word(core::num::NonZeroI128),
}
#[derive(Clone, Copy)]
pub enum ReverseI128 {
    Word(core::num::NonZeroI128),
    Empty,
}
#[inline(never)]
pub fn get_i128(value: core::num::NonZeroI128) -> i128 {
    value.get()
}
pub fn read_i128(values: &[WordI128], index: usize) {
    if index < values.len()
        && let WordI128::Word(value) = values[index]
    {
        assert!(get_i128(value) == value.get());
        assert!(get_i128(value) != 0);
    }
}
pub fn reverse_i128(values: &[ReverseI128], index: usize) {
    if index < values.len()
        && let ReverseI128::Word(value) = values[index]
    {
        assert!(get_i128(value) == value.get());
        assert!(get_i128(value) != 0);
    }
}
pub fn wrong_i128(values: &[WordI128], index: usize) {
    if index < values.len()
        && let WordI128::Word(value) = values[index]
    {
        assert!(get_i128(value) == 0);
    }
}

#[derive(Clone, Copy)]
pub enum WordIsize {
    Empty,
    Word(core::num::NonZeroIsize),
}
#[derive(Clone, Copy)]
pub enum ReverseIsize {
    Word(core::num::NonZeroIsize),
    Empty,
}
#[inline(never)]
pub fn get_isize(value: core::num::NonZeroIsize) -> isize {
    value.get()
}
pub fn read_isize(values: &[WordIsize], index: usize) {
    if index < values.len()
        && let WordIsize::Word(value) = values[index]
    {
        assert!(get_isize(value) == value.get());
        assert!(get_isize(value) != 0);
    }
}
pub fn reverse_isize(values: &[ReverseIsize], index: usize) {
    if index < values.len()
        && let ReverseIsize::Word(value) = values[index]
    {
        assert!(get_isize(value) == value.get());
        assert!(get_isize(value) != 0);
    }
}
pub fn wrong_isize(values: &[WordIsize], index: usize) {
    if index < values.len()
        && let WordIsize::Word(value) = values[index]
    {
        assert!(get_isize(value) == 0);
    }
}

pub fn mutable_unknown(values: &mut [WordU32], index: usize) {
    if index < values.len() {
        let _ = values[index];
    }
}
#[derive(Clone, Copy)]
pub enum ReferenceNiche<'a> {
    Empty,
    Word(&'a u32),
}
pub fn reference_unknown(values: &[ReferenceNiche<'_>], index: usize) {
    if index < values.len()
        && let ReferenceNiche::Word(value) = values[index]
    {
        assert!(*value == *value);
    }
}
#[derive(Clone, Copy)]
pub enum Extra {
    Empty,
    Word(core::num::NonZeroU32, u32),
}
pub fn extra_unknown(values: &[Extra], index: usize) {
    if index < values.len()
        && let Extra::Word(value, _) = values[index]
    {
        assert!(value.get() != 0);
    }
}
pub enum Dropping {
    Empty,
    Word(core::num::NonZeroI32),
}
impl Drop for Dropping {
    fn drop(&mut self) {}
}
pub fn drop_unknown(values: &[Dropping], index: usize) {
    if index < values.len()
        && let Dropping::Word(value) = &values[index]
    {
        assert!(value.get() != 0);
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn original_local_integer_rows() {
        for raw in [1, u8::MAX, 1 << (u8::BITS - 1)] {
            let value = core::num::NonZeroU8::new(raw).unwrap();
            let values = [super::WordU8::Empty, super::WordU8::Word(value)];
            let reversed = [super::ReverseU8::Empty, super::ReverseU8::Word(value)];
            for index in 0..2 {
                super::read_u8(&values, index);
                super::reverse_u8(&reversed, index);
            }
        }

        for raw in [1, u16::MAX, 1 << (u16::BITS - 1)] {
            let value = core::num::NonZeroU16::new(raw).unwrap();
            let values = [super::WordU16::Empty, super::WordU16::Word(value)];
            let reversed = [super::ReverseU16::Empty, super::ReverseU16::Word(value)];
            for index in 0..2 {
                super::read_u16(&values, index);
                super::reverse_u16(&reversed, index);
            }
        }

        for raw in [1, u32::MAX, 1 << (u32::BITS - 1)] {
            let value = core::num::NonZeroU32::new(raw).unwrap();
            let values = [super::WordU32::Empty, super::WordU32::Word(value)];
            let reversed = [super::ReverseU32::Empty, super::ReverseU32::Word(value)];
            for index in 0..2 {
                super::read_u32(&values, index);
                super::reverse_u32(&reversed, index);
            }
        }

        for raw in [1, u64::MAX, 1 << (u64::BITS - 1)] {
            let value = core::num::NonZeroU64::new(raw).unwrap();
            let values = [super::WordU64::Empty, super::WordU64::Word(value)];
            let reversed = [super::ReverseU64::Empty, super::ReverseU64::Word(value)];
            for index in 0..2 {
                super::read_u64(&values, index);
                super::reverse_u64(&reversed, index);
            }
        }

        for raw in [1, u128::MAX, 1 << (u128::BITS - 1)] {
            let value = core::num::NonZeroU128::new(raw).unwrap();
            let values = [super::WordU128::Empty, super::WordU128::Word(value)];
            let reversed = [super::ReverseU128::Empty, super::ReverseU128::Word(value)];
            for index in 0..2 {
                super::read_u128(&values, index);
                super::reverse_u128(&reversed, index);
            }
        }

        for raw in [1, usize::MAX, 1 << (usize::BITS - 1)] {
            let value = core::num::NonZeroUsize::new(raw).unwrap();
            let values = [super::WordUsize::Empty, super::WordUsize::Word(value)];
            let reversed = [super::ReverseUsize::Empty, super::ReverseUsize::Word(value)];
            for index in 0..2 {
                super::read_usize(&values, index);
                super::reverse_usize(&reversed, index);
            }
        }

        for raw in [1, -1, i8::MIN, i8::MAX] {
            let value = core::num::NonZeroI8::new(raw).unwrap();
            let values = [super::WordI8::Empty, super::WordI8::Word(value)];
            let reversed = [super::ReverseI8::Empty, super::ReverseI8::Word(value)];
            for index in 0..2 {
                super::read_i8(&values, index);
                super::reverse_i8(&reversed, index);
            }
        }

        for raw in [1, -1, i16::MIN, i16::MAX] {
            let value = core::num::NonZeroI16::new(raw).unwrap();
            let values = [super::WordI16::Empty, super::WordI16::Word(value)];
            let reversed = [super::ReverseI16::Empty, super::ReverseI16::Word(value)];
            for index in 0..2 {
                super::read_i16(&values, index);
                super::reverse_i16(&reversed, index);
            }
        }

        for raw in [1, -1, i32::MIN, i32::MAX] {
            let value = core::num::NonZeroI32::new(raw).unwrap();
            let values = [super::WordI32::Empty, super::WordI32::Word(value)];
            let reversed = [super::ReverseI32::Empty, super::ReverseI32::Word(value)];
            for index in 0..2 {
                super::read_i32(&values, index);
                super::reverse_i32(&reversed, index);
            }
        }

        for raw in [1, -1, i64::MIN, i64::MAX] {
            let value = core::num::NonZeroI64::new(raw).unwrap();
            let values = [super::WordI64::Empty, super::WordI64::Word(value)];
            let reversed = [super::ReverseI64::Empty, super::ReverseI64::Word(value)];
            for index in 0..2 {
                super::read_i64(&values, index);
                super::reverse_i64(&reversed, index);
            }
        }

        for raw in [1, -1, i128::MIN, i128::MAX] {
            let value = core::num::NonZeroI128::new(raw).unwrap();
            let values = [super::WordI128::Empty, super::WordI128::Word(value)];
            let reversed = [super::ReverseI128::Empty, super::ReverseI128::Word(value)];
            for index in 0..2 {
                super::read_i128(&values, index);
                super::reverse_i128(&reversed, index);
            }
        }

        for raw in [1, -1, isize::MIN, isize::MAX] {
            let value = core::num::NonZeroIsize::new(raw).unwrap();
            let values = [super::WordIsize::Empty, super::WordIsize::Word(value)];
            let reversed = [super::ReverseIsize::Empty, super::ReverseIsize::Word(value)];
            for index in 0..2 {
                super::read_isize(&values, index);
                super::reverse_isize(&reversed, index);
            }
        }
    }
}
