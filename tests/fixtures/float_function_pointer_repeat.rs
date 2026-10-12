#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn identity32(value: f32) -> f32 {
    value
}
#[inline(never)]
pub fn identity64(value: f64) -> f64 {
    value
}
#[inline(never)]
pub fn negate32(value: f32) -> f32 {
    -value
}
#[inline(never)]
pub fn negate64(value: f64) -> f64 {
    -value
}
#[inline(never)]
pub fn generic<T: Copy>(value: T) -> T {
    value
}
pub extern "C" fn foreign(value: f32) -> f32 {
    value
}
pub fn mixed(value: f32) -> f64 {
    value as f64
}

pub fn selected32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [identity32; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == value.to_bits());
    }
}
pub fn selected64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [identity64; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == value.to_bits());
    }
}
pub fn sign32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [negate32; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000));
    }
}
pub fn sign64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [negate64; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000_0000_0000));
    }
}
pub fn wrong32(index: usize, value: f32) {
    let table: [fn(f32) -> f32; 2] = [identity32; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000));
    }
}
pub fn wrong64(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 2] = [identity64; 2];
    if index < 2 {
        assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000_0000_0000));
    }
}
pub fn opaque32(value: f32, callback: fn(f32) -> f32) {
    let table = [callback; 2];
    assert!(table[0](value).to_bits() == value.to_bits());
}
pub fn opaque64(value: f64, callback: fn(f64) -> f64) {
    let table = [callback; 2];
    assert!(table[0](value).to_bits() == value.to_bits());
}
pub fn generic32(value: f32) {
    let table: [fn(f32) -> f32; 2] = [generic::<f32>; 2];
    assert!(table[0](value).to_bits() == value.to_bits());
}
pub fn foreign32(value: f32) {
    let table: [extern "C" fn(f32) -> f32; 2] = [foreign; 2];
    assert!(table[0](value).to_bits() == value.to_bits());
}
pub fn mixed_width(value: f32) {
    let table: [fn(f32) -> f64; 2] = [mixed; 2];
    assert!(table[0](value).to_bits() == (value.to_bits() as u64));
}
pub fn last32(value: f32) {
    let table: [fn(f32) -> f32; 128] = [identity32; 128];
    assert!(table[127](value).to_bits() == value.to_bits());
}
pub fn last64(value: f64) {
    let table: [fn(f64) -> f64; 128] = [identity64; 128];
    assert!(table[127](value).to_bits() == value.to_bits());
}
pub fn count_budget(value: f32) {
    let table: [fn(f32) -> f32; 129] = [identity32; 129];
    assert!(table[0](value).to_bits() == value.to_bits());
}
pub fn dispatch_budget(index: usize, value: f64) {
    let table: [fn(f64) -> f64; 128] = [identity64; 128];
    if index < 128 {
        assert!(table[index](value).to_bits() == value.to_bits());
    }
}
pub fn zero() {
    let table32: [fn(f32) -> f32; 0] = [identity32; 0];
    let table64: [fn(f64) -> f64; 0] = [identity64; 0];
    assert!(table32.len() == 0 && table64.len() == 0);
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        for index in 0..2 {
            for bits in [
                0,
                0x8000_0000,
                1,
                0x007f_ffff,
                0x0080_0000,
                0x7f7f_ffff,
                0xff7f_ffff,
                0x7f80_0000,
                0xff80_0000,
                0x7f80_0001,
                0x7fc1_2345,
                0xffc1_2345,
            ] {
                let value = f32::from_bits(bits);
                super::selected32(index, value);
                super::sign32(index, value);
                super::last32(value);
            }
            for bits in [
                0,
                0x8000_0000_0000_0000,
                1,
                0x000f_ffff_ffff_ffff,
                0x0010_0000_0000_0000,
                0x7fef_ffff_ffff_ffff,
                0xffef_ffff_ffff_ffff,
                0x7ff0_0000_0000_0000,
                0xfff0_0000_0000_0000,
                0x7ff0_0000_0000_0001,
                0x7ff8_1234_5678_9abc,
                0xfff8_1234_5678_9abc,
            ] {
                let value = f64::from_bits(bits);
                super::selected64(index, value);
                super::sign64(index, value);
                super::last64(value);
            }
            for sample in 0..129u32 {
                let value = f32::from_bits(sample.wrapping_mul(0x9e37_79b9));
                super::selected32(index, value);
                super::sign32(index, value);
            }
            for sample in 0..129u64 {
                let value = f64::from_bits(sample.wrapping_mul(0x9e37_79b9_7f4a_7c15));
                super::selected64(index, value);
                super::sign64(index, value);
            }
        }
        super::zero();
    }
}
