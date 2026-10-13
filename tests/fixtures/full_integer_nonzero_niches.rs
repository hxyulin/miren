#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn actual_get_u64(value: core::num::NonZeroU64) -> u64 {
    value.get()
}
#[inline(never)]
pub fn actual_equal_u64(
    left: Option<core::num::NonZeroU64>,
    right: Option<core::num::NonZeroU64>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_u64(
    values: &[Option<core::num::NonZeroU64>],
    needle: Option<core::num::NonZeroU64>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_u64(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_u64(value) == 0);
    }
}
pub fn same_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_u64(values[index], values[index]));
    }
}
pub fn member_u64(values: &[Option<core::num::NonZeroU64>], index: usize) {
    if index < values.len() {
        assert!(actual_member_u64(values, values[index]));
    }
}

#[inline(never)]
pub fn actual_get_u128(value: core::num::NonZeroU128) -> u128 {
    value.get()
}
#[inline(never)]
pub fn actual_equal_u128(
    left: Option<core::num::NonZeroU128>,
    right: Option<core::num::NonZeroU128>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_u128(
    values: &[Option<core::num::NonZeroU128>],
    needle: Option<core::num::NonZeroU128>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_u128(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_u128(value) == 0);
    }
}
pub fn same_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_u128(values[index], values[index]));
    }
}
pub fn member_u128(values: &[Option<core::num::NonZeroU128>], index: usize) {
    if index < values.len() {
        assert!(actual_member_u128(values, values[index]));
    }
}

#[inline(never)]
pub fn actual_get_usize(value: core::num::NonZeroUsize) -> usize {
    value.get()
}
#[inline(never)]
pub fn actual_equal_usize(
    left: Option<core::num::NonZeroUsize>,
    right: Option<core::num::NonZeroUsize>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_usize(
    values: &[Option<core::num::NonZeroUsize>],
    needle: Option<core::num::NonZeroUsize>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_usize(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_usize(value) == 0);
    }
}
pub fn same_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_usize(values[index], values[index]));
    }
}
pub fn member_usize(values: &[Option<core::num::NonZeroUsize>], index: usize) {
    if index < values.len() {
        assert!(actual_member_usize(values, values[index]));
    }
}

#[inline(never)]
pub fn actual_get_i64(value: core::num::NonZeroI64) -> i64 {
    value.get()
}
#[inline(never)]
pub fn actual_equal_i64(
    left: Option<core::num::NonZeroI64>,
    right: Option<core::num::NonZeroI64>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_i64(
    values: &[Option<core::num::NonZeroI64>],
    needle: Option<core::num::NonZeroI64>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_i64(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_i64(value) == 0);
    }
}
pub fn same_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_i64(values[index], values[index]));
    }
}
pub fn member_i64(values: &[Option<core::num::NonZeroI64>], index: usize) {
    if index < values.len() {
        assert!(actual_member_i64(values, values[index]));
    }
}

#[inline(never)]
pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {
    value.get()
}
#[inline(never)]
pub fn actual_equal_i128(
    left: Option<core::num::NonZeroI128>,
    right: Option<core::num::NonZeroI128>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_i128(
    values: &[Option<core::num::NonZeroI128>],
    needle: Option<core::num::NonZeroI128>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_i128(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_i128(value) == 0);
    }
}
pub fn same_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_i128(values[index], values[index]));
    }
}
pub fn member_i128(values: &[Option<core::num::NonZeroI128>], index: usize) {
    if index < values.len() {
        assert!(actual_member_i128(values, values[index]));
    }
}

#[inline(never)]
pub fn actual_get_isize(value: core::num::NonZeroIsize) -> isize {
    value.get()
}
#[inline(never)]
pub fn actual_equal_isize(
    left: Option<core::num::NonZeroIsize>,
    right: Option<core::num::NonZeroIsize>,
) -> bool {
    left == right
}
#[inline(never)]
pub fn actual_member_isize(
    values: &[Option<core::num::NonZeroIsize>],
    needle: Option<core::num::NonZeroIsize>,
) -> bool {
    values.contains(&needle)
}
pub fn niche_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
    if index < values.len() {
        let first = values[index];
        if let Some(value) = first {
            assert!(actual_get_isize(value) != 0);
            assert!(values[index].is_some());
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn wrong_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        assert!(actual_get_isize(value) == 0);
    }
}
pub fn same_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
    if index < values.len() {
        assert!(actual_equal_isize(values[index], values[index]));
    }
}
pub fn member_isize(values: &[Option<core::num::NonZeroIsize>], index: usize) {
    if index < values.len() {
        assert!(actual_member_isize(values, values[index]));
    }
}

pub fn extremes(values: &[Option<core::num::NonZeroI128>], index: usize) {
    if index < values.len()
        && let Some(value) = values[index]
    {
        let value = actual_get_i128(value);
        if value == i128::MIN {
            assert!(value as u128 == (1_u128 << 127));
        }
        if value == i128::MAX {
            assert!(value as u128 == (u128::MAX >> 1));
        }
    }
}
#[derive(Clone, Copy)]
pub enum LocalWide {
    Empty,
    Word(core::num::NonZeroU64),
}
pub fn local_unknown(values: &[LocalWide], index: usize) {
    if index < values.len()
        && let LocalWide::Word(value) = values[index]
    {
        assert!(value.get() != 0);
    }
}
pub fn mutable_unknown(values: &mut [Option<core::num::NonZeroU128>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}
pub fn pointer_unknown(values: &[Option<&u128>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_some() || values[index].is_none());
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn actual_integer_helpers_keep_original_claims() {
        let mut values = [None, None];
        for number in [1, u64::MAX] {
            values[1] = core::num::NonZeroU64::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_u64(&values, index);
                super::same_u64(&values, index);
                super::member_u64(&values, index);
            }
        }
        let mut values = [None, None];
        for number in [1, u128::MAX] {
            values[1] = core::num::NonZeroU128::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_u128(&values, index);
                super::same_u128(&values, index);
                super::member_u128(&values, index);
            }
        }
        let mut values = [None, None];
        for number in [1, usize::MAX] {
            values[1] = core::num::NonZeroUsize::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_usize(&values, index);
                super::same_usize(&values, index);
                super::member_usize(&values, index);
            }
        }
        let mut values = [None, None];
        for number in [i64::MIN, -1, 1, i64::MAX] {
            values[1] = core::num::NonZeroI64::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_i64(&values, index);
                super::same_i64(&values, index);
                super::member_i64(&values, index);
            }
        }
        let mut values = [None, None];
        for number in [i128::MIN, -1, 1, i128::MAX] {
            values[1] = core::num::NonZeroI128::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_i128(&values, index);
                super::extremes(&values, index);
                super::same_i128(&values, index);
                super::member_i128(&values, index);
            }
        }
        let mut values = [None, None];
        for number in [isize::MIN, -1, 1, isize::MAX] {
            values[1] = core::num::NonZeroIsize::new(number);
            for index in [0, 1, 2, usize::MAX] {
                super::niche_isize(&values, index);
                super::same_isize(&values, index);
                super::member_isize(&values, index);
            }
        }
    }
}
