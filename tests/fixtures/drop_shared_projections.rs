#![no_std]
#![forbid(unsafe_code)]

pub struct Dropped {
    pub word: u16,
    pub guard: u16,
    pub flag: bool,
    pub character: char,
    pub number: i32,
    pub floating: f32,
}
impl Drop for Dropped {
    fn drop(&mut self) {
        assert!(self.guard == 7);
    }
}
fn item(word: u16, flag: bool, character: char, number: i32, floating: f32) -> Dropped {
    Dropped {
        word,
        guard: 7,
        flag,
        character,
        number,
        floating,
    }
}
#[inline(never)]
pub fn actual_word(value: &u16) -> u16 {
    *value
}
#[inline(never)]
pub fn borrowed(index: usize) {
    let values = [
        item(3, false, 'a', -7, -0.0),
        item(7, true, '\u{10ffff}', i32::MIN, 0.0),
    ];
    if index < 2 {
        let selected = &values[index];
        assert!(actual_word(&selected.word) == if index == 0 { 3 } else { 7 });
    }
}
pub fn direct(index: usize) {
    let values = [
        item(3, false, 'a', -7, -0.0),
        item(7, true, '\u{10ffff}', i32::MIN, 0.0),
    ];
    if index < 2 {
        assert!(values[index].word == if index == 0 { 3 } else { 7 });
    }
}
pub fn nested(index: usize) {
    let values = [
        [item(3, false, 'a', -7, -0.0)],
        [item(7, true, 'z', -9, 0.0)],
    ];
    if index < 2 {
        let selected = &values[index];
        assert!(actual_word(&selected[0].word) == if index == 0 { 3 } else { 7 });
    }
}
pub fn scalar_codecs(index: usize) {
    let values = [
        item(3, false, 'a', -7, -0.0),
        item(7, true, '\u{10ffff}', i32::MIN, 0.0),
    ];
    if index < 2 {
        let selected = &values[index];
        assert!(selected.flag == (index == 1));
        assert!(selected.character == if index == 0 { 'a' } else { '\u{10ffff}' });
        assert!(selected.number == if index == 0 { -7 } else { i32::MIN });
        assert!(selected.floating.to_bits() == if index == 0 { 0x8000_0000 } else { 0 });
    }
}
pub fn wrong(index: usize) {
    let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    if index < 2 {
        let selected = &values[index];
        assert!(actual_word(&selected.word) == if index == 0 { 7 } else { 3 });
    }
}
pub fn unguarded(index: usize) {
    let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    assert!(values[index].word != 0);
}
#[inline(never)]
pub fn whole_accessor(value: &Dropped) -> u16 {
    value.word
}
pub fn whole_receiver_unknown(index: usize) {
    let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    if index < 2 {
        assert!(whole_accessor(&values[index]) != 0);
    }
}
#[inline(never)]
pub fn actual_store(value: &mut u16) {
    *value = 19;
}
pub fn mutable_unknown(index: usize) {
    let mut values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    if index < 2 {
        actual_store(&mut values[index].word);
        assert!(values[index].word == 19);
    }
}
#[inline(never)]
pub fn pointer_observer(value: *const u16) -> bool {
    value.is_null()
}
pub fn raw_unknown(index: usize) {
    let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    if index < 2 {
        let selected = &raw const values[index].word;
        assert!(!pointer_observer(selected));
    }
}
pub struct Probe {
    pub word: u16,
    pub guard: u16,
}
impl Drop for Probe {
    fn drop(&mut self) {
        assert!(self.guard == 7);
    }
}
#[inline(never)]
pub fn probe_borrow(values: [Probe; 2], index: usize) {
    if index < 2 {
        let selected = &values[index];
        assert!(actual_word(&selected.word) != 0);
    }
}
#[cfg(external_control)]
pub fn missing_accessor(index: usize) {
    let values = [item(3, false, 'a', -7, -0.0), item(7, true, 'z', -9, 0.0)];
    if index < 2 {
        assert!(drop_observer_dependency::observe(&values[index].word) != 0);
    }
}
#[cfg(test)]
mod native {
    #[test]
    fn genuine_borrows_observe_fields_and_execute_destructors() {
        for index in [0, 1, 2, usize::MAX] {
            super::borrowed(index);
            super::direct(index);
            super::nested(index);
            super::scalar_codecs(index);
        }
    }
}

#[inline(never)]
pub fn activation_seed(word: u16) -> u16 {
    word
}

pub mod fieldless_drop {
    pub struct Fieldless;
    #[cfg(not(fieldless_missing))]
    #[inline(never)]
    pub fn fieldless_tag() -> u16 {
        7
    }
    #[cfg(fieldless_missing)]
    #[inline(never)]
    pub fn fieldless_tag() -> u16 {
        drop_observer_dependency::observe(&7)
    }
    impl Drop for Fieldless {
        fn drop(&mut self) {
            assert!(fieldless_tag() == 7);
        }
    }
    pub fn incoming(values: [Fieldless; 2], index: usize) {
        if index < 2 {
            let _selected = &values[index];
            assert!(index < 2);
        }
    }
    pub fn local(index: usize) {
        let values = [Fieldless, Fieldless];
        if index < 2 {
            let _selected = &values[index];
            assert!(index < 2);
        }
    }
    pub fn wrong(values: [Fieldless; 2], index: usize) {
        if index < 2 {
            let _selected = &values[index];
            assert!(index >= 2);
        }
    }
    pub fn unguarded(values: [Fieldless; 2], index: usize) {
        let _selected = &values[index];
        assert!(index < 2);
    }
    #[inline(never)]
    pub fn whole(_value: &Fieldless) -> u16 {
        7
    }
    pub fn whole_unknown(values: [Fieldless; 2], index: usize) {
        if index < 2 {
            assert!(whole(&values[index]) == 7);
        }
    }
    #[cfg(test)]
    mod native {
        #[test]
        fn fieldless_borrows_execute_nonempty_destructors() {
            for index in [0, 1, 2, usize::MAX] {
                super::local(index);
                super::incoming([super::Fieldless, super::Fieldless], index);
            }
        }
    }
}
