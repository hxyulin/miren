//! Destruction progress is separate from the unchanged compiler alive range.
//! This representation grants no call, element access, raw pointer or retirement permission.
use super::*;
use rustc_middle::mir::{BorrowKind, Location, RawPtrKind};

mod protocol;
#[cfg(test)]
pub(super) use protocol::controls as protocol_controls;
pub(in crate::proof) use protocol::{ElementWitness, Invocation, View};

/// Branch-local progress through the original remaining interval, in ascending order.
#[derive(Clone, Debug)]
pub(in crate::proof) struct Progress {
    pub(super) next: usize,
    pub(super) entry: Rc<()>,
    /// A leased slot is absent from the iterator; its typed child storage must be authenticated
    /// separately by the actual destructor invocation before that invocation can execute.
    pub(super) leased: Option<Lease>,
}

#[derive(Clone, Debug)]
pub(in crate::proof) struct Lease {
    pub(super) index: usize,
    pub(super) allocation: usize,
}

impl Progress {
    pub(super) fn validate(&self, payload: &Payload) -> Result<(), String> {
        if payload.retired
            || payload.pending.is_some()
            || payload.front > payload.back
            || payload.back > payload.slots.len()
            || !(payload.front..=payload.back).contains(&self.next)
            || self
                .leased
                .as_ref()
                .is_some_and(|lease| lease.index != self.next || lease.index >= payload.back)
        {
            return Err("IntoIter active destruction cursor or lease differs".into());
        }
        for (index, slot) in payload.slots.iter().enumerate() {
            let remaining = (self.next..payload.back).contains(&index)
                && self.leased.as_ref().map(|lease| lease.index) != Some(index);
            if slot.is_some() != remaining {
                return Err("IntoIter active destruction initialized slots differ".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
pub(super) fn core_evidence_controls<'tcx>(engine: &mut Engine<'tcx>, iterator: Ty<'tcx>) {
    // Follow actual compiler Call occurrences. This authenticates bodies only; it executes no
    // destructor, issues no raw view and consumes no element. The larger budget is diagnostic.
    fn children<'tcx>(engine: &mut Engine<'tcx>, body: &Body<'tcx>) -> Vec<ty::Instance<'tcx>> {
        let mut children = Vec::new();
        for block in body.basic_blocks.iter() {
            if let TerminatorKind::Call {
                func: Operand::Constant(function),
                ..
            } = &block.terminator().kind
            {
                let ty::FnDef(id, args) = function.const_.ty().kind() else {
                    panic!("real destructor chain function item")
                };
                children.push(
                    engine
                        .resolve_function_item(*id, args.skip_binder())
                        .unwrap(),
                );
            }
        }
        children
    }
    let mut instance = ty::Instance::resolve_drop_glue(engine.tcx, iterator);
    let arm = engine.tcx.sess.target.llvm_target == "thumbv7em-none-eabihf";
    for (locals, statements) in [
        (4, vec![1, 0]),
        (5, vec![0, 2, 0, 1]),
        (4, vec![1, 0]),
        (5, vec![4, 2]),
        (4, vec![2, 1]),
        if arm {
            (22, vec![4, 4, 2, 17, 7, 1, 4, 2, 1])
        } else {
            (20, vec![4, 4, 2, 18, 5, 2, 2])
        },
    ] {
        let evidence = match instance.def {
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_))) => {
                compiler_evidence::load_drop(engine, instance).unwrap()
            }
            ty::InstanceKind::Item(_) => compiler_evidence::load_item(engine, instance).unwrap(),
            _ => panic!("destruction chain is actual available Item or typed DropGlue"),
        };
        assert!(evidence.current.return_ty().is_unit());
        assert_eq!(evidence.current.local_decls.len(), locals);
        assert_eq!(
            evidence
                .current
                .basic_blocks
                .iter()
                .map(|block| block.statements.len())
                .collect::<Vec<_>>(),
            statements
        );
        let calls = children(engine, &evidence.current);
        if locals == 20 || locals == 22 {
            assert_eq!(calls.len(), if arm { 1 } else { 2 });
            let bounds = compiler_evidence::load_item(engine, calls[0]).unwrap();
            assert_eq!(bounds.current.arg_count, 2);
            let (loop_body, drop_block) = if arm {
                (evidence.current.clone(), 7)
            } else {
                let slice = compiler_evidence::load_drop(engine, calls[1]).unwrap();
                assert_eq!(slice.current.arg_count, 1);
                assert_eq!(slice.current.local_decls.len(), 8);
                assert_eq!(
                    slice
                        .current
                        .basic_blocks
                        .iter()
                        .map(|block| block.statements.len())
                        .collect::<Vec<_>>(),
                    vec![2, 0, 2, 1]
                );
                (slice.current, 2)
            };
            let TerminatorKind::Drop { place, .. } = &loop_body.basic_blocks
                [BasicBlock::from_usize(drop_block)]
            .terminator()
            .kind
            else {
                panic!("actual remaining slice element Drop")
            };
            let original = place.ty(&loop_body.local_decls, engine.tcx).ty;
            if arm {
                assert_eq!(place.local.as_usize(), 20);
                assert_eq!(place.projection.as_ref(), [ProjectionElem::Deref]);
                let scope = loop_body.basic_blocks[BasicBlock::from_usize(drop_block)]
                    .terminator()
                    .source_info
                    .scope;
                let inline = loop_body.source_scopes[scope].inlined.as_ref().unwrap();
                assert_eq!(
                    inline.0,
                    ty::Instance::resolve_drop_glue(
                        engine.tcx,
                        Ty::new_slice(engine.tcx, original)
                    )
                );
            }
            let child = ty::Instance::resolve_drop_glue(engine.tcx, original);
            let child = compiler_evidence::load_drop(engine, child).unwrap();
            assert!(child.current.return_ty().is_unit());
        } else {
            assert_eq!(calls.len(), 1);
            instance = calls[0];
        }
    }
    println!(
        "actual remaining Drop compiler evidence only, diagnostic steps={}",
        engine.steps
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn payload(front: usize, back: usize, next: usize, leased: Option<usize>) -> Payload {
        Payload {
            slots: Rc::new(
                (0..5)
                    .map(|index| {
                        ((next..back).contains(&index) && leased != Some(index))
                            .then_some(Value::Unit)
                    })
                    .collect(),
            ),
            front,
            back,
            pending: None,
            dropping: Some(Progress {
                next,
                leased: leased.map(|index| Lease {
                    index,
                    allocation: 42,
                }),
                entry: Rc::new(()),
            }),
            retired: false,
        }
    }

    #[test]
    fn destruction_slots_follow_progress_without_changing_alive() {
        for (front, back) in [(0, 0), (0, 5), (1, 4), (5, 5)] {
            for next in front..=back {
                let mut value = payload(front, back, next, None);
                value.dropping.as_ref().unwrap().validate(&value).unwrap();
                assert!(value.validate(5, false).is_err());
                assert!(value.validate(5, true).is_err());
                assert_eq!((value.front, value.back), (front, back));
                if next < back {
                    value.dropping.as_mut().unwrap().leased = Some(Lease {
                        index: next,
                        allocation: 42,
                    });
                    Rc::make_mut(&mut value.slots)[next] = None;
                    value.dropping.as_ref().unwrap().validate(&value).unwrap();
                    assert!(value.validate(5, true).is_err());
                }
            }
        }
    }

    #[test]
    fn malformed_progress_or_slots_cannot_authorize_destruction() {
        let valid = payload(1, 4, 2, Some(2));
        for index in 0..5 {
            let mut changed = valid.clone();
            let slot = &mut Rc::make_mut(&mut changed.slots)[index];
            *slot = if slot.is_some() {
                None
            } else {
                Some(Value::Unit)
            };
            assert!(
                changed
                    .dropping
                    .as_ref()
                    .unwrap()
                    .validate(&changed)
                    .is_err()
            );
            valid.dropping.as_ref().unwrap().validate(&valid).unwrap();
        }
        for (next, leased) in [(0, None), (5, None), (2, Some(1)), (4, Some(4))] {
            let mut changed = valid.clone();
            changed.dropping = Some(Progress {
                next,
                leased: leased.map(|index| Lease {
                    index,
                    allocation: 42,
                }),
                entry: Rc::new(()),
            });
            assert!(
                changed
                    .dropping
                    .as_ref()
                    .unwrap()
                    .validate(&changed)
                    .is_err()
            );
        }
        let mut retired = valid.clone();
        retired.retired = true;
        assert!(
            retired
                .dropping
                .as_ref()
                .unwrap()
                .validate(&retired)
                .is_err()
        );
    }
}
