#![no_std]
#![forbid(unsafe_code)]
extern crate array_iterator_dependency;
pub fn unavailable(input: [array_iterator_dependency::Stamp; 2])
    -> core::array::IntoIter<array_iterator_dependency::Stamp, 2>
{
    array_iterator_dependency::build(input)
}
