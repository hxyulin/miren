#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]
extern crate local_associated_dependency;
struct Local;
impl Local {
    #[inline(never)]
    fn outer(values: &mut [u16], word: u16) {
        local_associated_dependency::leaf(&mut *values, word);
    }
}
pub fn selected(values: &mut [u16], word: u16) {
    if values.len() > 0 {
        Local::outer(values, word);
        assert!(values[0] == word);
    }
}
pub fn empty(values: &mut [u16], word: u16) {
    if values.len() == 0 {
        Local::outer(values, word);
        assert!(values.len() == 0);
    }
}
#[cfg(test)]
mod tests {
    #[test]
    fn actual_foreign_controls() {
        for length in [0, 1, 2, 129] {
            for word in [0, 1, 17, u16::MAX] {
                let mut values = std::vec![0; length];
                super::selected(&mut values, word);
                super::empty(&mut values, word);
            }
        }
    }
}
