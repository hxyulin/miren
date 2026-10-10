#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn first(value: u16) -> u16 { value }
#[inline(never)] pub fn second(value: u16) -> u16 { value ^ 1 }
pub fn selected(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [first,second];
    if index < 2 { assert!(table[index](value) == if index == 0 {value} else {value ^ 1}); }
}
pub fn wrong(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [first,second];
    if index < 2 { assert!(table[index](value) == value); }
}
pub fn duplicates(index: usize, value: u16) {
    let table: [fn(u16)->u16;3] = [first,second,first];
    if index < 3 { assert!(table[index](value) == if index == 1 {value ^ 1} else {value}); }
}
pub fn field(index: usize, value: u16) {
    let record: ([fn(u16)->u16;2],bool) = ([first,second],true);
    if index < 2 { assert!(record.0[index](value) == if index == 0 {value} else {value ^ 1}); }
}
pub fn second_call(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [first,second];
    if index < 2 { let f = table[index]; assert!(f(f(value)) == value); }
}
pub fn opaque(index: usize, value: u16, unknown: fn(u16)->u16) {
    let table: [fn(u16)->u16;2] = [first,unknown];
    if index < 2 { assert!(table[index](value) == value); }
}
#[inline(never)] pub fn wide_first(value: u32) -> u32 { value }
#[inline(never)] pub fn wide_second(value: u32) -> u32 { value ^ 1 }
pub fn wide(index: usize, value: u32) {
    let table: [fn(u32)->u32;2] = [wide_first,wide_second];
    if index < 2 { assert!(table[index](value) == if index == 0 {value} else {value ^ 1}); }
}
pub fn shared(index: usize, value: u16, table: &[fn(u16)->u16;2]) {
    if index < 2 { assert!(table[index](value) == value); }
}
pub fn excessive(index: usize, value: u16) {
    let table: [fn(u16)->u16;17] = [first;17];
    if index < 17 { assert!(table[index](value) == value); }
}
#[cfg(test)] mod tests {
    #[test] fn selected_body_guard() { super::selected(1,129); }
    #[test] fn selected_order_guard() { super::selected(1,129); }
}
