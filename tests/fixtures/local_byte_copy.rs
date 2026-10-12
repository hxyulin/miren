#![no_std]

#[inline(never)]
pub fn source() -> [u8; 2] {
    [17, 19]
}

pub fn positive(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = source();
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 19);
    }
}

pub fn wrong(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = source();
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 17);
    }
}

pub fn symbolic(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 2 {
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == second);
    }
}

pub fn symbolic_wrong(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 2 {
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == first);
    }
}

pub fn tail(values: &mut [u8], first: u8, second: u8) {
    if values.len() >= 3 {
        let old = values[2];
        let bytes = [first, second];
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == first && values[1] == second && values[2] == old);
    }
}

pub fn empty(values: &mut [u8]) {
    let bytes: [u8; 0] = [];
    values[..0].copy_from_slice(&bytes);
    assert!(values.len() == values.len());
}

#[inline(never)]
unsafe fn unsafe_source() -> [u8; 2] {
    [17, 19]
}

pub fn unsafe_transport(values: &mut [u8]) {
    if values.len() >= 2 {
        let bytes = unsafe { unsafe_source() };
        values[..2].copy_from_slice(&bytes);
        assert!(values[0] == 17 && values[1] == 19);
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn genuine_claims() {
        let mut values = [0xa5; 129];
        super::positive(&mut values);
        assert!(values[2..].iter().all(|value| *value == 0xa5));
        super::positive(&mut []);
        super::symbolic(&mut values, 0, 255);
        super::tail(&mut values, 13, 23);
        super::empty(&mut values);
    }
}
