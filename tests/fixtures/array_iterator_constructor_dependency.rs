#![no_std]
#![forbid(unsafe_code)]
pub struct Stamp(pub u16);
impl Drop for Stamp {
    fn drop(&mut self) {}
}
pub fn build(input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
    input.into_iter()
}
