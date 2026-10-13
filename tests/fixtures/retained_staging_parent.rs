#![no_std]
#![forbid(unsafe_code)]
pub fn earlier_staging_parent(values: &mut [u16]) {
    let original_len = values.len();
    if original_len >= 2 {
        let borrowed = &mut *values;
        let child = &mut borrowed[0..1];
        assert!(child.len() == 1);
        assert!(borrowed.len() == original_len);
    }
}
