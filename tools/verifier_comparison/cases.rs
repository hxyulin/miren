#![forbid(unsafe_code)]

use std::future::Future;
use std::num::NonZeroU8;
use std::pin::{Pin, pin};
use std::task::{Context, Poll, Waker};

pub fn guarded_index(values: [u8; 4], index: u8) {
    if index < 4 {
        let expected = match index {
            0 => values[0],
            1 => values[1],
            2 => values[2],
            _ => values[3],
        };
        assert_eq!(values[index as usize], expected);
    }
}

pub fn unguarded_index(values: [u8; 4], index: u8) {
    let _ = values[index as usize];
}

pub fn checked_add(left: u8, right: u8) {
    if let Some(sum) = left.checked_add(right) {
        assert_eq!(u16::from(sum), u16::from(left) + u16::from(right));
    }
}

pub fn overflow_add(left: u8, right: u8) {
    assert!(left + right >= left);
}

pub fn nonzero_match(raw: u8) {
    match NonZeroU8::new(raw) {
        Some(value) => assert_eq!(value.get(), raw),
        None => assert_eq!(raw, 0),
    }
}

pub fn nonzero_unwrap(raw: u8) {
    let _ = NonZeroU8::new(raw).unwrap();
}

pub fn mutable_preserve(mut values: [u8; 4], index: u8, value: u8) {
    if index < 4 {
        let before = values;
        values[index as usize] = value;
        for sibling in 0..4 {
            if sibling != index as usize {
                assert_eq!(values[sibling], before[sibling]);
            }
        }
    }
}

pub fn mutable_wrong_claim(mut values: [u8; 4], index: u8, value: u8) {
    if index < 4 {
        let before = values;
        values[index as usize] = value;
        assert_eq!(values[index as usize], before[index as usize]);
    }
}

pub fn bounded_iterator(values: [u8; 4]) {
    let sum: u16 = values.iter().map(|value| u16::from(*value)).sum();
    assert!(sum <= 1020);
}

trait Apply {
    fn apply(&self, value: u8) -> u8;
}

struct Increment;
struct Toggle;

impl Apply for Increment {
    fn apply(&self, value: u8) -> u8 {
        value.wrapping_add(1)
    }
}

impl Apply for Toggle {
    fn apply(&self, value: u8) -> u8 {
        value ^ 1
    }
}

pub fn trait_dispatch(increment: bool, value: u8) {
    let operation: &dyn Apply = if increment { &Increment } else { &Toggle };
    let result = operation.apply(value);
    assert_eq!(
        result,
        if increment {
            value.wrapping_add(1)
        } else {
            value ^ 1
        }
    );
}

pub fn vec_roundtrip(values: [u8; 4]) {
    let mut vector = values.to_vec();
    vector.push(7);
    assert_eq!(vector.pop(), Some(7));
    assert_eq!(vector.len(), 4);
    for index in 0..4 {
        assert_eq!(vector[index], values[index]);
    }
}

pub fn vec_wrong_length(values: [u8; 4]) {
    let mut vector = values.to_vec();
    vector.push(7);
    assert_eq!(vector.len(), 4);
}

struct Pause(bool);

impl Future for Pause {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

async fn after_pause(value: u8) -> u8 {
    Pause(false).await;
    assert!(value < 6);
    value
}

pub fn async_two_polls(value: u8) {
    if value < 6 {
        let mut context = Context::from_waker(Waker::noop());
        let mut future = pin!(after_pause(value));
        assert!(future.as_mut().poll(&mut context).is_pending());
        assert_eq!(future.as_mut().poll(&mut context), Poll::Ready(value));
    }
}

pub fn async_late_panic(value: u8) {
    let mut context = Context::from_waker(Waker::noop());
    let mut future = pin!(after_pause(value));
    assert!(future.as_mut().poll(&mut context).is_pending());
    let _ = future.as_mut().poll(&mut context);
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn positive_controls() {
        for value in 0..=u8::MAX {
            guarded_index([0, 1, 2, 3], value);
            nonzero_match(value);
            mutable_preserve([0, 1, 2, 3], value, 9);
            trait_dispatch(false, value);
            trait_dispatch(true, value);
            async_two_polls(value);
            for right in 0..=u8::MAX {
                checked_add(value, right);
            }
        }
        bounded_iterator([255; 4]);
        vec_roundtrip([0, 1, 254, 255]);
    }

    #[test]
    fn negative_controls_have_real_panics() {
        let controls: [fn(); 6] = [
            || unguarded_index([0; 4], 4),
            || overflow_add(255, 1),
            || nonzero_unwrap(0),
            || mutable_wrong_claim([0; 4], 0, 1),
            || vec_wrong_length([0; 4]),
            || async_late_panic(6),
        ];
        for control in controls {
            assert!(std::panic::catch_unwind(control).is_err());
        }
    }
}
