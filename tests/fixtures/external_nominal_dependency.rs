#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}

impl PartialEq for Record {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.right
    }
}

#[derive(Clone, Copy)]
pub struct Zero;

impl PartialEq for Zero {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
