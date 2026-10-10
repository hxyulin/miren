#![no_std]
#![feature(pattern_types, pattern_type_macro)]

#[derive(Clone, Copy, PartialEq)]
pub struct Pair {
    pub left: u16,
    pub right: u16,
    pub padding: u8,
}
impl Pair {
    #[inline(never)]
    pub fn selected(&self) -> u16 {
        self.left
    }
    #[inline(never)]
    pub fn borrowed(&self) -> &u16 {
        &self.right
    }
    #[inline(never)]
    pub fn checked_next(&self) -> u16 {
        self.left + 1
    }
}
#[derive(Clone, Copy)]
pub struct Tuple(pub u16, pub bool);
#[derive(Clone, Copy)]
pub struct Generic<T> {
    pub payload: T,
    pub flag: bool,
}
#[derive(Clone, Copy)]
pub struct Rich {
    pub pair: Pair,
    pub bytes: [u8; 2],
    pub floating: f32,
    pub wide: f64,
    pub character: char,
}
#[derive(Clone, Copy)]
pub struct Private(u16);
impl Private {
    pub fn new() -> Self {
        Self(3)
    }
    #[inline(never)]
    pub fn get(&self) -> u16 {
        self.0
    }
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct Zero<const N: usize>;
impl<const N: usize> Zero<N> {
    #[inline(never)]
    pub fn marker(&self) -> usize {
        N
    }
}
#[derive(Clone, Copy)]
pub struct RefField<'a> {
    pub reference: [&'a u16; 0],
    pub value: u16,
}
#[derive(Clone, Copy)]
pub struct RawField {
    pub pointer: [*const u16; 0],
    pub value: u16,
}
#[derive(Clone, Copy)]
pub struct PatField {
    pub restricted: [core::pattern_type!(u32 is 1..); 0],
    pub value: u16,
}
#[derive(Clone, Copy)]
pub struct CoreField {
    pub marker: [core::marker::PhantomData<&'static u16>; 0],
    pub value: u16,
}
#[derive(Clone, Copy)]
#[repr(packed)]
pub struct Packed(pub u16);
pub struct Dropped(pub u16);
impl Drop for Dropped {
    fn drop(&mut self) {}
}
#[derive(Clone, Copy)]
pub struct NonZeroField(pub [core::num::NonZeroU16; 0]);
#[derive(Clone, Copy)]
pub struct Huge(pub [u16; 129]);
