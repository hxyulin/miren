#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

pub mod character {
    #[inline(never)]
    fn scalar(word: char) -> char {
        if word == '\0' { '\0' } else { word }
    }
    #[inline(never)]
    fn leaf(values: &mut [char], word: char) {
        if values.len() > 0 {
            values[0] = scalar(word);
        }
    }
    #[inline(never)]
    fn outer(values: &mut [char], word: char) -> char {
        leaf(&mut *(&mut *values), word);
        scalar(word)
    }
    #[inline(never)]
    fn deeper_outer(values: &mut [char], word: char) {
        outer(values, word);
    }
    pub fn selected(values: &mut [char], word: char) {
        if values.len() > 0 {
            outer(values, word);
            assert!(values[0] == word);
        }
    }
    pub fn sibling(values: &mut [char], word: char) {
        if values.len() > 1 {
            let old = values[1];
            outer(values, word);
            assert!(values[0] == word);
            assert!(values[1] == old);
        }
    }
    pub fn scalar_return(values: &mut [char], word: char) {
        if values.len() > 0 {
            let returned = outer(values, word);
            assert!(returned == word);
            assert!(values[0] == returned);
        }
    }
    pub fn wrong(values: &mut [char], word: char) {
        if values.len() > 0 {
            outer(values, word);
            assert!(values[0] != word);
        }
    }
    pub fn bounds(values: &mut [char], word: char) {
        outer(values, word);
        assert!(values[0] == word);
    }
    pub fn deeper(values: &mut [char], word: char) {
        if values.len() > 0 {
            deeper_outer(values, word);
            assert!(values[0] == word);
        }
    }
}
#[cfg(test)]
mod native_tests {
    #[test]
    fn characters() {
        for len in 0..=129 {
            for word in ['\0', 'a', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
                let mut values = std::vec!['x'; len];
                super::character::selected(&mut values, word);
                super::character::sibling(&mut values, word);
                super::character::scalar_return(&mut values, word);
            }
        }
    }
}
