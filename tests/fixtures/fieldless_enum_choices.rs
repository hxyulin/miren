#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
#[repr(i8)]
pub enum Press {
    Idle = -7,
    Long = -1,
    Short = 0,
    Double = 9,
    Released = 31,
    Pressing = 100,
}

#[derive(Clone, Copy)]
pub enum Key {
    W,
    S,
    A,
    D,
    Shift,
    Ctrl,
    Q,
    E,
    R,
    F,
    G,
    Z,
    X,
    C,
    V,
    B,
    MouseLeft,
    MouseRight,
}

pub fn state(states: &[Press; 18], key: Key) -> Press {
    states[key as usize]
}

pub fn selected_state_retains_exact_signed_discriminant(states: [Press; 18], key: Key) {
    let chosen = state(&states, key);
    if key as usize == 0 {
        assert!(chosen as i8 == states[0] as i8);
    }
    assert!(matches!(
        chosen,
        Press::Idle
            | Press::Long
            | Press::Short
            | Press::Double
            | Press::Released
            | Press::Pressing
    ));
}

pub fn wrong_selected_state_is_refuted(states: [Press; 18], key: Key) {
    let chosen = state(&states, key);
    if key as usize == 0 {
        assert!(chosen as i8 != states[0] as i8);
    }
}

pub fn unbounded_index_is_refuted(states: [Press; 18], index: usize) -> Press {
    states[index]
}

#[derive(Clone, Copy)]
pub enum Payload {
    Empty,
    Data(u8),
}

pub fn payload_choice_is_unknown(states: [Payload; 3], index: usize) -> Payload {
    if index < 3 {
        states[index]
    } else {
        Payload::Empty
    }
}

pub fn mixed_symbolic_and_constructed_choices_stay_unknown(
    mut states: [Press; 3],
    index: usize,
) -> Press {
    states[1] = Press::Short;
    if index < 3 {
        states[index]
    } else {
        Press::Idle
    }
}

#[cfg(test)]
#[test]
fn native_selected_states() {
    let mut states = [Press::Idle; 18];
    states[1] = Press::Short;
    for key in [Key::W, Key::S, Key::MouseRight] {
        selected_state_retains_exact_signed_discriminant(states, key);
    }
}
