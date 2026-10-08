#![no_std]
#![forbid(unsafe_code)]

static INFO: (u32, (u16, u16)) = (7, (3, 4));

pub fn info() -> &'static (u32, (u16, u16)) {
    &INFO
}
