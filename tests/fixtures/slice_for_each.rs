#![no_std]
#![forbid(unsafe_code)]

pub struct Controller {
    pub slot: u8,
    pub total: u16,
    pub previous: Option<u16>,
}

impl Controller {
    pub fn reset(&mut self) {
        self.total = 0;
        self.previous = None;
    }
}

pub struct Bank {
    pub controllers: [Controller; 4],
    pub untouched: u16,
}

pub fn reset_bank(bank: &mut Bank) {
    let untouched = bank.untouched;
    bank.controllers.iter_mut().for_each(Controller::reset);
    for controller in &bank.controllers {
        assert!(controller.total == 0 && controller.previous.is_none());
    }
    assert!(bank.untouched == untouched);
}

pub fn captured_order() {
    let mut values = [9_u16; 4];
    let mut next = 0_u16;
    values.iter_mut().for_each(|value| {
        *value = next;
        next += 1;
    });
    assert!(values == [0, 1, 2, 3] && next == 4);
}

pub fn borrowed_cursor() {
    let mut values = [1_u16, 2, 3];
    let mut iterator = values.iter_mut();
    *iterator.next().unwrap() = 7;
    iterator.by_ref().for_each(|value| *value = 9);
    assert!(iterator.next().is_none());
    assert!(values == [7, 9, 9]);
}

pub fn shared_order() {
    let values = [2_u16, 3, 5];
    let mut total = 0_u16;
    values.iter().for_each(|value| total = total * 10 + *value);
    assert!(total == 235);
}

pub fn empty() {
    let mut values: [u16; 0] = [];
    values.iter_mut().for_each(|_| panic!("empty callback"));
}

pub fn last_callback_panics() {
    let mut values = [1_u16, 2, 3];
    values.iter_mut().for_each(|value| assert!(*value != 3));
}

pub fn callback_overflows(values: &mut [u8; 4]) {
    values.iter_mut().for_each(|value| *value += 1);
}

pub fn wrong_effect() {
    let mut values = [1_u16, 2, 3];
    values.iter_mut().for_each(|value| *value = 7);
    assert!(values[2] == 9);
}

pub fn function_pointer() {
    let mut controller = [Controller {
        slot: 0,
        total: 7,
        previous: Some(4),
    }];
    let callback: fn(&mut Controller) = Controller::reset;
    controller.iter_mut().for_each(callback);
}

pub fn unbounded(values: &mut [u16]) {
    values.iter_mut().for_each(|value| *value = 0);
}

pub fn ambiguous(values: &mut [[u16; 4]; 2], index: usize) {
    if index < 4 {
        values.iter_mut().for_each(|row| row[index] = 7);
    }
}

struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {}
}

pub fn callback_destructor() {
    let guard = Guard;
    let mut values = [1_u16, 2];
    values.iter_mut().for_each(move |value| {
        let _guard = &guard;
        *value = 0;
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traversal_matches_direct_updates() {
        for seed in 0..16_u16 {
            let mut bank = Bank {
                controllers: core::array::from_fn(|index| Controller {
                    slot: index as u8,
                    total: seed + index as u16,
                    previous: Some(seed),
                }),
                untouched: seed,
            };
            reset_bank(&mut bank);
            assert!(
                bank.controllers
                    .iter()
                    .all(|controller| controller.total == 0)
            );
        }
        captured_order();
        borrowed_cursor();
        shared_order();
        empty();
    }
}
