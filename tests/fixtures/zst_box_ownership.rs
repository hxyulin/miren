#![no_std]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![cfg_attr(not(test), allow(internal_features))]

extern crate alloc;
use alloc::boxed::Box;

#[inline(never)]
pub fn selected(owner: Box<()>) -> u16 {
    let () = *owner;
    core::mem::drop(owner);
    19
}
#[inline(never)]
pub fn borrowed(value: &()) -> u16 {
    let () = *value;
    19
}
#[inline(never)]
pub fn borrowed_unit(owner: &Box<()>) -> &() {
    &**owner
}
#[inline(never)]
pub fn transfer(owner: Box<()>) -> Box<()> {
    owner
}
pub fn construct_drop() {
    let owner = Box::new(());
    let () = *owner;
    core::mem::drop(owner);
}
pub fn selected_claim() {
    assert!(selected(Box::new(())) == 19);
}
pub fn selected_wrong() {
    assert!(selected(Box::new(())) == 20);
}
pub fn borrowed_claim() {
    let owner = Box::new(());
    assert!(borrowed(&owner) == 19);
    core::mem::drop(owner);
}
pub fn readonly_owner_claim() {
    let owner = Box::new(());
    assert!(borrowed(borrowed_unit(&owner)) == 19);
    core::mem::drop(owner);
}
pub fn borrowed_wrong() {
    let owner = Box::new(());
    assert!(borrowed(&owner) == 20);
    core::mem::drop(owner);
}
#[inline(never)]
pub fn rejected(owner: Box<()>) {
    core::mem::drop(owner);
    panic!();
}
pub fn reached_panic() {
    rejected(Box::new(()));
}
pub fn return_transfer() {
    let owner = transfer(Box::new(()));
    let () = *owner;
    core::mem::drop(owner);
}
pub fn independent(choice: bool) {
    if choice {
        assert!(selected(Box::new(())) == 19);
    } else {
        let owner = Box::new(());
        assert!(borrowed(&owner) == 19);
        core::mem::drop(owner);
    }
}
pub fn automatic_drop() {
    let owner = Box::new(());
    let () = *owner;
}
pub fn nonzero() {
    let owner = Box::new(19_u16);
    assert!(*owner == 19);
}
#[repr(align(8))]
pub struct Aligned;
pub fn aligned_zero() {
    let owner = Box::new(Aligned);
    core::mem::drop(owner);
}
pub fn pointer_equality() {
    let left = Box::new(());
    let right = Box::new(());
    assert!(core::ptr::eq(&*left, &*right));
}
pub fn exposed_address() {
    let owner = Box::new(());
    assert!((&*owner as *const () as usize) != 0);
}
pub fn mutable_access() {
    let mut owner = Box::new(());
    let target = &mut *owner;
    *target = ();
}
pub fn leaked() {
    let owner = Box::new(());
    let value = Box::leak(owner);
    let () = *value;
}
pub fn forgotten() {
    core::mem::forget(Box::new(()));
}
pub fn incoming(owner: Box<()>) {
    core::mem::drop(owner);
}

#[cfg(not(test))]
pub mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_owner() {
        mir! {
            let owner: Box<()>;
            let unit: ();
            let duplicate: Box<()>;
            let result: ();
            {
                unit = ();
                Call(owner = Box::<()>::new(unit), ReturnTo(copy_owner), UnwindUnreachable())
            }
            copy_owner = {
                duplicate = owner;
                Call(result = core::mem::drop(Move(owner)), ReturnTo(done), UnwindUnreachable())
            }
            done = {
                RET = ();
                Return()
            }
        }
    }
    pub fn escaping_shared() {
        let mut slot = &();
        store_dangling(&mut slot);
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn store_dangling(destination: &mut &()) {
        mir! {
            let owner: Box<()>;
            let unit: ();
            let value: &();
            let owner_ref: &Box<()>;
            let result: ();
            {
                unit = ();
                Call(owner = Box::<()>::new(unit), ReturnTo(escape), UnwindUnreachable())
            }
            escape = {
                owner_ref = &owner;
                Call(value = borrowed_unit(owner_ref), ReturnTo(store), UnwindUnreachable())
            }
            store = {
                *destination = value;
                Call(result = core::mem::drop(owner), ReturnTo(done), UnwindUnreachable())
            }
            done = {
                RET = ();
                Return()
            }
        }
    }
    pub fn mutable_virtual_owner() {
        let owner = Box::new(());
        virtual_mutation(&owner);
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn virtual_mutation(source: &Box<()>) {
        mir! {
            let temporary: Box<()>;
            let writable: &mut Box<()>;
            {
                temporary = *source;
                writable = &mut temporary;
                RET = ();
                Return()
            }
        }
    }
    pub fn raw_virtual_owner() {
        let owner = Box::new(());
        virtual_raw(&owner);
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn virtual_raw(source: &Box<()>) {
        mir! {
            let temporary: Box<()>;
            let writable: *mut Box<()>;
            {
                temporary = *source;
                writable = &raw mut temporary;
                RET = ();
                Return()
            }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn double_drop() {
        mir! {
            let owner: Box<()>;
            let unit: ();
            let result: ();
            {
                unit = ();
                Call(owner = Box::<()>::new(unit), ReturnTo(first), UnwindUnreachable())
            }
            first = {
                Call(result = core::mem::drop(owner), ReturnTo(second), UnwindUnreachable())
            }
            second = {
                Call(result = core::mem::drop(owner), ReturnTo(done), UnwindUnreachable())
            }
            done = {
                RET = ();
                Return()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn construction() {
        construct_drop();
    }
    #[test]
    fn selected_body() {
        selected_claim();
    }
    #[test]
    fn shared_body() {
        borrowed_claim();
        readonly_owner_claim();
    }
    #[test]
    fn owner_return() {
        return_transfer();
    }
    #[test]
    fn branches() {
        independent(false);
        independent(true);
    }
    #[test]
    fn automatic_destructor() {
        automatic_drop();
    }
    #[test]
    fn mutation_guard() {
        selected_claim();
    }
}
