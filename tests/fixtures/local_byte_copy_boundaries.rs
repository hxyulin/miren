#![no_std]
#![forbid(unsafe_code)]

pub fn empty_retains_first(values: &mut [u8]) {
    if !values.is_empty() {
        let old = values[0];
        let bytes: [u8; 0] = [];
        values[..0].copy_from_slice(&bytes);
        assert!(values[0] == old);
    }
}

pub fn empty_wrong(values: &mut [u8]) {
    if !values.is_empty() {
        let old = values[0];
        let bytes: [u8; 0] = [];
        values[..0].copy_from_slice(&bytes);
        assert!(values[0] != old);
    }
}

#[inline(never)]
pub fn boundary_source() -> [u8; 128] {
    [17; 128]
}

pub fn boundary_positive(values: &mut [u8]) {
    if values.len() >= 129 {
        let old_tail = values[128];
        let bytes = boundary_source();
        values[..128].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[127] == 17 && values[128] == old_tail);
    }
}

pub fn boundary_wrong(values: &mut [u8]) {
    if values.len() >= 128 {
        let bytes = boundary_source();
        values[..128].copy_from_slice(&bytes);
        assert!(values[127] == 19);
    }
}

#[inline(never)]
pub fn oversized_source() -> [u8; 129] {
    [17; 129]
}

pub fn oversized(values: &mut [u8]) {
    if values.len() >= 129 {
        let bytes = oversized_source();
        values[..129].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[128] == 17);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        let mut values = [0xa5; 129];
        super::empty_retains_first(&mut values);
        assert!(values.iter().all(|value| *value == 0xa5));
        super::empty_retains_first(&mut []);
        super::boundary_positive(&mut values);
        assert!(values[..128].iter().all(|value| *value == 17));
        assert_eq!(values[128], 0xa5);
        super::boundary_positive(&mut []);
        super::oversized(&mut values);
        assert!(values.iter().all(|value| *value == 17));
    }
}
