#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn write_float(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        values[index][0] = f32::from_bits(0x7fc0_1234);
    }
}
