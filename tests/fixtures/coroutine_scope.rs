#![no_std]
#![forbid(unsafe_code)]

pub async fn delayed_panic() {
    panic!("reached only by polling");
}

pub fn immediate_panic() {
    panic!("ordinary function body");
}

pub fn callback_boundary(callback: fn()) {
    callback();
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::future::Future;

    #[test]
    fn constructing_does_not_poll() {
        let _future = delayed_panic();
    }

    #[test]
    #[should_panic(expected = "reached only by polling")]
    fn polling_reaches_the_delayed_failure() {
        let mut future = core::pin::pin!(delayed_panic());
        let waker = core::task::Waker::noop();
        let mut context = core::task::Context::from_waker(waker);
        let _ = future.as_mut().poll(&mut context);
    }
}
