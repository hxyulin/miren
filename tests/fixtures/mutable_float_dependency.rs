#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn selected(value: f32) -> f32 {
    if value == 1.0 { 2.0 } else { 1.0 }
}
