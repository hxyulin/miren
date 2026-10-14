#![no_std]

use core::num::NonZeroU8;

#[derive(Clone, Copy)]
pub struct OriginProduct {
    pub payload: Option<NonZeroU8>,
    pub keep: bool,
}

pub fn tuple_plan(values: &mut [(Option<NonZeroU8>, bool)]) -> usize {
    values.len()
}

pub fn array_struct_plan(values: &mut [[OriginProduct; 2]]) -> usize {
    values.len()
}

pub fn oversized_array_plan(values: &mut [[OriginProduct; 129]]) -> usize {
    values.len()
}

pub struct NonCopyProduct {
    pub payload: Option<NonZeroU8>,
    pub keep: bool,
}

pub fn noncopy_array_plan(values: &mut [[NonCopyProduct; 2]]) -> usize {
    values.len()
}
