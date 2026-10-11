#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]
extern crate nested_bool_dependency;
pub fn selected(values: &mut [bool], word: bool) {
    if values.len() > 0 {
        let returned = nested_bool_dependency::outer(values, word);
        assert!(values[0] == word && returned == word);
    }
}
pub fn empty(values: &mut [bool], word: bool) {
    if values.len() == 0 {
        nested_bool_dependency::outer(values, word);
        assert!(values.len() == 0);
    }
}
#[cfg(test)] mod tests {
    #[test] fn valid_controls() {
        for length in 0..=129 {
            for word in [false, true] {
                let mut values = std::vec![false; length];
                super::selected(&mut values, word);
                super::empty(&mut values, word);
            }
        }
    }
}
