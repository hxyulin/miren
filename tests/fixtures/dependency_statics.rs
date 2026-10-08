#![no_std]
#![forbid(unsafe_code)]

use core::sync::atomic::AtomicU32;

pub static WORD: AtomicU32 = AtomicU32::new(7);
pub static FROZEN: u32 = 7;
pub static FROZEN_SLICE: [u32; 2] = [7, 9];

#[inline(always)]
pub fn word() -> &'static AtomicU32 {
    &WORD
}

#[inline(always)]
pub fn frozen() -> u32 {
    FROZEN
}

#[inline(always)]
pub fn frozen_slice() -> u32 {
    let values: &[u32] = &FROZEN_SLICE;
    values[0]
}

pub struct Site(pub AtomicU32);

impl Site {
    const fn new() -> Self {
        Self(AtomicU32::new(7))
    }
}

pub static SITE: Site = Site::new();

#[inline(always)]
pub fn site() -> &'static Site {
    &SITE
}
