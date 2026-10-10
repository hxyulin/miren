#![no_std]
#![forbid(unsafe_code)]
#[derive(Clone, Copy)]
pub struct External {
    pub flags: [bool; 2],
    pub characters: [char; 2],
    pub values: [f32; 2],
}
impl PartialEq for External {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.flags == other.flags
            && self.characters == other.characters
            && self.values == other.values
    }
}
#[derive(Clone, Copy)]
pub struct ExternalZero {
    pub flags: [bool; 0],
    pub characters: [char; 0],
    pub values: [f64; 0],
}
impl PartialEq for ExternalZero {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.flags == other.flags
            && self.characters == other.characters
            && self.values == other.values
    }
}
