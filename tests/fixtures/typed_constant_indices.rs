#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

#[inline(never)]
pub fn word(value: u16) -> u16 {
    value ^ 0
}

pub fn first(values: &mut [u16]) {
    if values.len() > 0 {
        let before = values[0];
        values[0] = word(before);
        assert!(values[0] == before);
    }
}

pub fn last(values: &mut [u16]) {
    if values.len() > 0 {
        let index = values.len() - 1;
        let before = values[index];
        values[index] = word(before);
        assert!(values[index] == before);
    }
}

pub fn wrong(values: &mut [u16]) {
    if values.len() > 0 {
        values[0] = 17;
        assert!(values[0] == 18);
    }
}

pub fn bool_first(values: &mut [bool]) {
    if values.len() > 0 {
        values[0] = true;
        assert!(values[0]);
    }
}

pub fn char_first(values: &mut [char]) {
    if values.len() > 0 {
        values[0] = '\u{10ffff}';
        assert!(values[0] == '\u{10ffff}');
    }
}

pub fn i32_first(values: &mut [i32]) {
    if values.len() > 0 {
        values[0] = i32::MIN;
        assert!(values[0] == i32::MIN);
    }
}

pub fn float_first(values: &mut [f32]) {
    if values.len() > 0 {
        values[0] = -0.0;
        assert!(values[0].to_bits() == 0x8000_0000);
    }
}

#[inline(never)]
pub fn child(values: &mut [u16]) {
    first(values);
}

pub fn parent(values: &mut [u16]) {
    child(values);
    if values.len() > 0 {
        values[0] = 31;
        assert!(values[0] == 31);
    }
}

pub fn proper(values: &mut [u16], start: usize, end: usize) {
    if start <= end && end <= values.len() {
        child(&mut values[start..end]);
    }
}

pub fn unguarded(values: &mut [u16]) {
    let _ = values[0];
}

pub fn extra_field(values: &mut [(u16, u16)]) {
    if values.len() > 0 {
        values[0].0 = 17;
        assert!(values[0].0 == 17);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_guard() {
        for length in 0..=129 {
            let mut values = vec![u16::MAX; length];
            first(&mut values);
            last(&mut values);
            parent(&mut values);
            proper(&mut values, 0, length);
            bool_first(&mut vec![false; length]);
            char_first(&mut vec!['\0'; length]);
            i32_first(&mut vec![0; length]);
            float_first(&mut vec![f32::from_bits(0x7fc0_0017); length]);
        }
        for value in [0, 1, 17, u16::MAX] {
            first(&mut [value]);
            last(&mut [value]);
        }
    }
}
