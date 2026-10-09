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

pub struct ChannelState(pub AtomicU32);

impl ChannelState {
    pub const NEW: Self = Self(AtomicU32::new(7));
}

pub static STATES: [ChannelState; 16] = [ChannelState::NEW; 16];

#[inline(always)]
pub fn channel() -> &'static ChannelState {
    &STATES[11]
}

pub struct AggregateParameter(pub ChannelState);

const fn wrap(value: ChannelState) -> AggregateParameter {
    AggregateParameter(value)
}

pub static AGGREGATE_PARAMETER: AggregateParameter = wrap(ChannelState::NEW);

#[inline(always)]
pub fn aggregate_parameter() -> &'static AggregateParameter {
    &AGGREGATE_PARAMETER
}

#[cfg(test)]
#[test]
fn nested_constructor_native() {
    assert_eq!(channel().0.load(core::sync::atomic::Ordering::Relaxed), 7);
}
