#![no_std]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]

#[inline(never)]
fn ordinary_identity(value: Token) -> Token { value }

pub fn ordinary_reassignment(word: u16) {
    let mut value = Token { word };
    value = ordinary_identity(value);
    assert!(value.word == word);
}

pub struct Token {
    word: u16,
}

pub struct Counted<'a>(&'a core::cell::Cell<u16>);

impl Drop for Counted<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get().wrapping_add(1));
    }
}

pub struct DropPair<'a> {
    left: Counted<'a>,
    right: Counted<'a>,
}

pub enum Tagged {
    Word(Token),
    Empty,
}

pub fn noncopy_result_payload(word: u16) {
    let value = Ok::<Token, ()>(Token { word }).ok();
    match value {
        Some(value) => assert!(value.word == word),
        None => panic!(),
    }
}

pub struct Pair {
    left: Token,
    right: Token,
}

// Deliberately unsupported initialization sequences are analyzer-only controls.
// Never execute stale-load, duplicate-move or repeated-drop controls natively.
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn consumed_unit_return() {
        mir! {
            let moved: ();
            {
                RET = ();
                moved = Move(RET);
                Return()
            }
        }
    }

    #[inline(never)]
    fn identity(value: Token) -> Token { value }

    // The compiler explicitly leaves Move-input/return-place aliasing unresolved (#71117).
    // This is a translator refusal control, never a native execution or a UB claim.
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn overlapping_call(mut value: Token) -> Token {
        mir! {
            {
                Call(value = identity(Move(value)), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = Move(value); Return() }
        }
    }

    pub fn overlapping_call_claim(word: u16) {
        assert!(overlapping_call(Token { word }).word == word);
    }

    #[inline(never)]
    fn scalar_identity(value: u16) -> u16 { value }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn inductive_live_move(word: u16, limit: u16) -> u16 {
        mir! {
            let index: u16;
            let again: bool;
            let ignored: u16;
            { index = 0; Goto(head) }
            head = {
                again = index < limit;
                match again { true => body, _ => done }
            }
            body = {
                Call(ignored = scalar_identity(Move(word)), ReturnTo(step), UnwindUnreachable())
            }
            step = { index = index + 1; Goto(head) }
            done = { RET = word; Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn terminal_owned_argument(word: u16, limit: u16) -> u16 {
        mir! {
            let index: u16;
            let again: bool;
            { index = 0; Goto(head) }
            head = { again = index < limit; match again { true => step, _ => done } }
            step = { index = index + 1; Goto(head) }
            done = { RET = Move(word); Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn terminal_reference_argument(value: &u16, limit: u16) -> &u16 {
        mir! {
            let index: u16;
            let again: bool;
            { index = 0; Goto(head) }
            head = { again = index < limit; match again { true => step, _ => done } }
            step = { index = index + 1; Goto(head) }
            done = { RET = Move(value); Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn terminal_addressed_argument(word: u16, limit: u16) -> u16 {
        mir! {
            let index: u16;
            let again: bool;
            let alias: &u16;
            { alias = &word; index = 0; Goto(head) }
            head = { again = index < limit; match again { true => step, _ => done } }
            step = { index = index + 1; Goto(head) }
            done = { RET = Move(word); Return() }
        }
    }

    #[doc = "<!-- miren:v1:ensures:result == result -->"]
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn terminal_current_argument(word: u16, limit: u16) -> u16 {
        mir! {
            let index: u16;
            let again: bool;
            { index = 0; Goto(head) }
            head = { again = index < limit; match again { true => step, _ => done } }
            step = { index = index + 1; Goto(head) }
            done = { RET = Move(word); Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn tag_after_payload(value: Tagged) -> isize {
        mir! {
            let moved: Token;
            {
                moved = Move(Field(Variant(value, 0), 0));
                RET = Discriminant(value);
                Return()
            }
        }
    }

    pub fn retained_tag_claim(word: u16) {
        assert!(tag_after_payload(Tagged::Word(Token { word })) == 0);
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn whole_consumed_tag(value: Tagged) -> isize {
        mir! {
            let moved: Tagged;
            { moved = Move(value); RET = Discriminant(value); Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn ancestor_consumed_tag(value: (Tagged, ())) -> isize {
        mir! {
            let moved: (Tagged, ());
            { moved = Move(value); RET = Discriminant(value.0); Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn payload_after_move(value: Tagged) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(Field(Variant(value, 0), 0));
                RET = Field::<Token>(Variant(value, 0), 0).word;
                Return()
            }
        }
    }

    pub fn payload_after_move_claim(word: u16) {
        assert!(payload_after_move(Tagged::Word(Token { word })) == word);
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn no_drop_payload_nop(value: (Token, ())) {
        mir! {
            let moved: Token;
            {
                moved = Move(value.0);
                Drop(value.0, ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn no_drop_cannot_repair(value: (Token, ())) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(value.0);
                Drop(value.0, ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = value.0.word; Return() }
        }
    }

    static mut BYTE: u16 = 0;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn moved_static_store(handle: *mut u16) {
        mir! {
            let moved: *mut u16;
            {
                moved = Move(handle);
                *handle = 19;
                Return()
            }
        }
    }

    pub fn moved_static_handle_store() {
        moved_static_store(&raw mut BYTE);
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn indexed_move(values: [Token; 2], index: usize) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(values[index]);
                RET = moved.word;
                Return()
            }
        }
    }

    #[inline(never)]
    fn consume(value: Token) -> u16 {
        value.word
    }

    #[inline(never)]
    fn consume_pair(first: Token, second: Token) -> u16 {
        first.word.wrapping_add(second.word)
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale_after_call(value: Token) -> u16 {
        mir! {
            let ignored: u16;
            {
                Call(ignored = consume(Move(value)), ReturnTo(done), UnwindUnreachable())
            }
            done = {
                RET = value.word;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn duplicate_call_move(value: Token) -> u16 {
        mir! {
            {
                Call(RET = consume_pair(Move(value), Move(value)),
                    ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    pub fn stale_after_call_claim(word: u16) {
        assert!(stale_after_call(Token { word }) == word);
    }

    pub fn duplicate_call_move_claim(word: u16) {
        assert!(duplicate_call_move(Token { word }) == word.wrapping_add(word));
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale_alias(value: Token) -> u16 {
        mir! {
            let alias: &u16;
            let ignored: u16;
            {
                alias = &value.word;
                Call(ignored = consume(Move(value)), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = *alias; Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn live_sibling_alias(value: Pair) -> u16 {
        mir! {
            let alias: &u16;
            let moved: Token;
            {
                alias = &value.right.word;
                moved = Move(value.left);
                RET = *alias;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale_whole(value: Token) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(value);
                RET = value.word;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale_field(value: Pair) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(value.left);
                RET = value.left.word;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn moved_destination(value: Token) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(value);
                RET = moved.word;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn unaffected_sibling(value: Pair) -> u16 {
        mir! {
            let moved: Token;
            {
                moved = Move(value.left);
                RET = value.right.word;
                Return()
            }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn double_field_drop(value: DropPair<'_>) {
        mir! {
            {
                Drop(value.left, ReturnTo(again), UnwindUnreachable())
            }
            again = {
                Drop(value.left, ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    pub fn stale_whole_claim(word: u16) {
        let got = stale_whole(Token { word });
        assert!(got == word);
    }

    pub fn stale_field_claim(first: u16, second: u16) {
        let got = stale_field(Pair {
            left: Token { word: first },
            right: Token { word: second },
        });
        assert!(got == first);
    }

    pub fn double_field_drop_claim() {
        let count = core::cell::Cell::new(0);
        double_field_drop(DropPair {
            left: Counted(&count),
            right: Counted(&count),
        });
        assert!(count.get() == 2);
    }
}

pub fn safe_whole(word: u16) {
    let value = Token { word };
    let moved = value;
    assert!(moved.word == word);
}

pub fn safe_partial(first: u16, second: u16) {
    let value = Pair {
        left: Token { word: first },
        right: Token { word: second },
    };
    let moved = value.left;
    assert!(moved.word == first);
    assert!(value.right.word == second);
}

#[inline(never)]
fn chosen(value: Token) -> u16 {
    value.word
}

pub fn transferred(word: u16) {
    let value = Token { word };
    assert!(chosen(value) == word);
}

pub fn reinitialize(first: u16, second: u16) {
    let mut value = Pair {
        left: Token { word: first },
        right: Token { word: second },
    };
    let moved = value.left;
    value.left = Token { word: second };
    assert!(moved.word == first);
    assert!(value.left.word == second && value.right.word == second);
}

pub fn moved_handle(target: &mut u16) {
    let moved = target;
    *moved = 19;
    assert!(*moved == 19);
}

pub fn wrong_transfer(word: u16) {
    assert!(chosen(Token { word }) == word.wrapping_add(1));
}

pub fn safe_drop() {
    let count = core::cell::Cell::new(0);
    {
        let value = DropPair {
            left: Counted(&count),
            right: Counted(&count),
        };
        drop(value.left);
        assert!(count.get() == 1);
    }
    assert!(count.get() == 2);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_moves_keep_destination_and_siblings() {
        safe_whole(19);
        ordinary_reassignment(19);
        noncopy_result_payload(19);
        safe_partial(19, 41);
        safe_drop();
        transferred(19);
        reinitialize(19, 41);
        let mut target = 0;
        moved_handle(&mut target);
    }
}
