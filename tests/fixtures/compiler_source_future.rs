#![no_std]
#![forbid(unsafe_code)]

pub async fn future_source() -> u8 {
    7
}

pub fn ordinary_source_with_future_local() -> u8 {
    let future = future_source();
    core::mem::drop(future);
    7
}

pub fn ordinary_source_with_wrapped_future_local() -> u8 {
    let wrapped = (Some(future_source()), 7u8);
    core::mem::drop(wrapped);
    7
}
