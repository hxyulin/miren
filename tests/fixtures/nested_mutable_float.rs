#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

pub mod single {
    #[inline(never)]
    pub fn scalar(value: f32) -> f32 { value }
    #[inline(never)]
    fn leaf(values: &mut [f32], value: f32) -> f32 {
        let copied = scalar(value);
        if values.len() > 0 { values[0] = copied; }
        copied
    }
    #[inline(never)]
    fn outer(values: &mut [f32], value: f32) -> f32 {
        leaf(&mut *(&mut *values), value)
    }
    #[inline(never)]
    fn deeper_outer(values: &mut [f32], value: f32) -> f32 { outer(values, value) }
    pub fn selected(values: &mut [f32], value: f32) {
        if values.len() > 0 {
            outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
        }
    }
    pub fn sibling(values: &mut [f32], value: f32) {
        if values.len() > 1 {
            let old = values[1].to_bits();
            outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
            assert!(values[1].to_bits() == old);
        }
    }
    pub fn scalar_return(values: &mut [f32], value: f32) {
        let copied = outer(values, value);
        assert!(copied.to_bits() == value.to_bits());
    }
    pub fn sequential(values: &mut [f32], value: f32) {
        if values.len() > 0 {
            outer(values, value);
            outer(values, -value);
            assert!(values[0].to_bits() == (-value).to_bits());
        }
    }
    pub fn wrong(values: &mut [f32], value: f32) {
        if values.len() > 0 {
            outer(values, value);
            assert!(values[0].to_bits() != value.to_bits());
        }
    }
    pub fn deeper(values: &mut [f32], value: f32) {
        if values.len() > 0 {
            deeper_outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
        }
    }
}
pub mod double {
    #[inline(never)]
    pub fn scalar(value: f64) -> f64 { value }
    #[inline(never)]
    fn leaf(values: &mut [f64], value: f64) -> f64 {
        let copied = scalar(value);
        if values.len() > 0 { values[0] = copied; }
        copied
    }
    #[inline(never)]
    fn outer(values: &mut [f64], value: f64) -> f64 {
        leaf(&mut *(&mut *values), value)
    }
    #[inline(never)]
    fn deeper_outer(values: &mut [f64], value: f64) -> f64 { outer(values, value) }
    pub fn selected(values: &mut [f64], value: f64) {
        if values.len() > 0 {
            outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
        }
    }
    pub fn sibling(values: &mut [f64], value: f64) {
        if values.len() > 1 {
            let old = values[1].to_bits();
            outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
            assert!(values[1].to_bits() == old);
        }
    }
    pub fn scalar_return(values: &mut [f64], value: f64) {
        let copied = outer(values, value);
        assert!(copied.to_bits() == value.to_bits());
    }
    pub fn sequential(values: &mut [f64], value: f64) {
        if values.len() > 0 {
            outer(values, value);
            outer(values, -value);
            assert!(values[0].to_bits() == (-value).to_bits());
        }
    }
    pub fn wrong(values: &mut [f64], value: f64) {
        if values.len() > 0 {
            outer(values, value);
            assert!(values[0].to_bits() != value.to_bits());
        }
    }
    pub fn deeper(values: &mut [f64], value: f64) {
        if values.len() > 0 {
            deeper_outer(values, value);
            assert!(values[0].to_bits() == value.to_bits());
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn float_native_guard() {
        let single = [0.0_f32, -0.0, 1.0, -1.0, f32::INFINITY, f32::NEG_INFINITY,
            f32::from_bits(0x7fc0_0123), f32::from_bits(0xffc0_0456)];
        let double = [0.0_f64, -0.0, 1.0, -1.0, f64::INFINITY, f64::NEG_INFINITY,
            f64::from_bits(0x7ff8_0000_0000_0123), f64::from_bits(0xfff8_0000_0000_0456)];
        for length in 0..=129 {
            for value in single {
                let mut values = vec![value; length];
                super::single::selected(&mut values, value);
                super::single::sibling(&mut values, value);
                super::single::scalar_return(&mut values, value);
                super::single::sequential(&mut values, value);
            }
            for value in double {
                let mut values = vec![value; length];
                super::double::selected(&mut values, value);
                super::double::sibling(&mut values, value);
                super::double::scalar_return(&mut values, value);
                super::double::sequential(&mut values, value);
            }
        }
    }
}
