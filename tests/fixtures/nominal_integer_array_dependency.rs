#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
pub struct External {
    pub words: [u16; 2],
    pub marker: bool,
}
impl PartialEq for External {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words && self.marker == other.marker
    }
}

#[derive(Clone, Copy)]
pub struct ExternalZero {
    pub words: [u16; 0],
}
impl PartialEq for ExternalZero {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words
    }
}
