//! Actual typed route source controls; no storage, branch exclusion or search result is claimed.
use super::*;
use rustc_middle::mir::{BasicBlock, Local, Place, UnwindAction};

#[derive(Clone, Copy)]
enum Mutation {
    LocalType,
    SharedMutability,
    Predicate,
    Branch,
    NeedleOperand,
    SliceMove,
    RawArguments,
    TupleField,
    SearchArguments,
    Result,
    ClosureCapture,
    NormalEdge,
    Unwind,
    Helper,
}

fn change<'tcx>(engine: &Engine<'tcx>, body: &mut Body<'tcx>, mutation: Mutation) {
    match mutation {
        Mutation::LocalType => body.local_decls[Local::from_usize(8)].ty = engine.tcx.types.u16,
        Mutation::SharedMutability => {
            let ty::Ref(region, child, rustc_hir::Mutability::Not) =
                body.local_decls[Local::from_usize(2)].ty.kind()
            else {
                panic!("actual shared slice type")
            };
            body.local_decls[Local::from_usize(2)].ty =
                Ty::new_ref(engine.tcx, *region, *child, rustc_hir::Mutability::Mut);
        }
        Mutation::Predicate => {
            let StatementKind::Assign(value) =
                &mut body.basic_blocks.as_mut()[BasicBlock::from_usize(1)].statements[0].kind
            else {
                panic!("actual size comparison")
            };
            let Rvalue::BinaryOp(operation, _) = &mut value.1 else {
                panic!("actual Eq")
            };
            *operation = rustc_middle::mir::BinOp::Ne;
        }
        Mutation::Branch => {
            let TerminatorKind::SwitchInt { targets, .. } = &mut body.basic_blocks.as_mut()
                [BasicBlock::from_usize(1)]
            .terminator_mut()
            .kind
            else {
                panic!("actual size branch")
            };
            *targets = rustc_middle::mir::SwitchTargets::new(
                [(0, BasicBlock::from_usize(2))].into_iter(),
                BasicBlock::from_usize(8),
            );
        }
        Mutation::TupleField => {
            let StatementKind::Assign(value) =
                &mut body.basic_blocks.as_mut()[BasicBlock::from_usize(6)].statements[1].kind
            else {
                panic!("actual tuple field")
            };
            value.1 = Rvalue::Use(
                Operand::Copy(Place::from(Local::from_usize(8))),
                rustc_middle::mir::WithRetag::Yes,
            );
        }
        Mutation::ClosureCapture => {
            let StatementKind::Assign(value) =
                &mut body.basic_blocks.as_mut()[BasicBlock::from_usize(9)].statements[1].kind
            else {
                panic!("actual closure construction")
            };
            let Rvalue::Aggregate(_, fields) = &mut value.1 else {
                panic!("actual aggregate")
            };
            fields[rustc_abi::FieldIdx::from_usize(0)] =
                Operand::Copy(Place::from(Local::from_usize(2)));
        }
        Mutation::NeedleOperand
        | Mutation::SliceMove
        | Mutation::RawArguments
        | Mutation::SearchArguments
        | Mutation::Result
        | Mutation::NormalEdge
        | Mutation::Unwind
        | Mutation::Helper => {
            let index = match mutation {
                Mutation::NeedleOperand => 2,
                Mutation::SliceMove => 3,
                Mutation::RawArguments => 5,
                Mutation::SearchArguments
                | Mutation::Result
                | Mutation::NormalEdge
                | Mutation::Unwind
                | Mutation::Helper => 6,
                Mutation::LocalType
                | Mutation::SharedMutability
                | Mutation::Predicate
                | Mutation::Branch
                | Mutation::TupleField
                | Mutation::ClosureCapture => unreachable!(),
            };
            let replacement = if matches!(mutation, Mutation::Helper) {
                let TerminatorKind::Call { func, .. } = &body.basic_blocks
                    [BasicBlock::from_usize(7)]
                .terminator()
                .kind
                else {
                    panic!("actual is_some Call")
                };
                Some(func.clone())
            } else {
                None
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } = &mut body.basic_blocks.as_mut()[BasicBlock::from_usize(index)]
                .terminator_mut()
                .kind
            else {
                panic!("actual helper Call")
            };
            match mutation {
                Mutation::NeedleOperand => {
                    args[0].node = Operand::Copy(Place::from(Local::from_usize(2)))
                }
                Mutation::SliceMove => {
                    args[0].node = Operand::Move(Place::from(Local::from_usize(2)))
                }
                Mutation::RawArguments | Mutation::SearchArguments => args.swap(0, 1),
                Mutation::Result => *destination = Place::from(Local::from_usize(0)),
                Mutation::NormalEdge => *target = Some(BasicBlock::from_usize(10)),
                Mutation::Unwind => *unwind = UnwindAction::Continue,
                Mutation::Helper => *func = replacement.unwrap(),
                Mutation::LocalType
                | Mutation::SharedMutability
                | Mutation::Predicate
                | Mutation::Branch
                | Mutation::TupleField
                | Mutation::ClosureCapture => unreachable!(),
            }
        }
    }
}

pub(super) fn compiler_controls<'tcx>(engine: &Engine<'tcx>, root: ty::Instance<'tcx>) {
    let root_body = engine.instantiated_body(root).unwrap();
    let outer = root_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return None;
            };
            let ty::FnDef(id, args) = func.ty(&root_body.local_decls, engine.tcx).kind() else {
                return None;
            };
            Some(
                engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap(),
            )
        })
        .unwrap();
    let raw_outer = engine.tcx.instance_mir(outer.def);
    let TerminatorKind::Call { func, .. } = &raw_outer.basic_blocks[rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        panic!("actual raw outer helper")
    };
    let ty::FnDef(helper_id, parameters) = func.ty(&raw_outer.local_decls, engine.tcx).kind()
    else {
        panic!("actual raw helper declaration")
    };
    GraphBudget::new(0)
        .unwrap()
        .arguments_in_caller(engine.tcx, parameters.skip_binder(), outer)
        .unwrap();
    let mut paid = GraphBudget::new(0).unwrap();
    let inventory = paid.inventory(engine.tcx, outer, raw_outer).unwrap();
    paid.phase(GraphPhase::BodyClone, inventory).unwrap();
    paid.charge(32).unwrap();
    let mut missing_param = raw_outer.clone();
    let unknown = Ty::new_param(engine.tcx, 1, rustc_span::Symbol::intern("Foreign"));
    let parameters = engine.tcx.mk_args(&[unknown.into()]);
    let TerminatorKind::Call { func, .. } = &mut missing_param.basic_blocks.as_mut()
        [rustc_middle::mir::START_BLOCK]
        .terminator_mut()
        .kind
    else {
        panic!("actual copied raw helper")
    };
    let Operand::Constant(constant) = func else {
        panic!("actual FnDef constant")
    };
    constant.const_ = rustc_middle::mir::Const::Val(
        rustc_middle::mir::ConstValue::ZeroSized,
        Ty::new_fn_def(engine.tcx, *helper_id, ty::Binder::dummy(parameters)),
    );
    let error = match byte_transport::source(
        engine,
        outer,
        &missing_param,
        byte_transport::SourcePhase::Raw,
        &mut paid,
    ) {
        Ok(_) => panic!("unknown caller Param index was accepted"),
        Err(error) => error,
    };
    assert_eq!(error, "raw Param mapping unavailable");
    let outer_body = engine
        .capture_niche_comparison_body(
            outer,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        )
        .unwrap()
        .body;
    let wrong_outer = ty::Instance::new_raw(
        outer.def_id(),
        engine.tcx.mk_args(&[engine.tcx.types.bool.into()]),
    );
    let error = match byte_transport::source(
        engine,
        wrong_outer,
        &outer_body,
        byte_transport::SourcePhase::Current,
        &mut GraphBudget::new(0).unwrap(),
    ) {
        Ok(_) => panic!("wrong concrete caller environment was accepted"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        "typed byte current source differs from actual caller argument"
    );
    let error = match byte_transport::source(
        engine,
        outer,
        &outer_body,
        byte_transport::SourcePhase::Raw,
        &mut GraphBudget::new(0).unwrap(),
    ) {
        Ok(_) => panic!("normalized source was treated as raw formal source"),
        Err(error) => error,
    };
    assert_eq!(error, "typed byte raw source lacks exact caller Param0");
    eprintln!("TYPED BYTE actual caller-environment and unknown Param-index controls");
    let TerminatorKind::Call { func, .. } = &outer_body.basic_blocks
        [rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        panic!("actual outer")
    };
    let ty::FnDef(id, args) = func.ty(&outer_body.local_decls, engine.tcx).kind() else {
        panic!("actual dispatcher FnDef")
    };
    let dispatcher = engine
        .resolve_function_item(*id, args.skip_binder())
        .unwrap();
    let malformed_outer = ty::Instance::new_raw(
        outer.def_id(),
        engine.tcx.mk_args(&[engine.tcx.lifetimes.re_erased.into()]),
    );
    let error = match byte_transport::source(
        engine,
        malformed_outer,
        &outer_body,
        byte_transport::SourcePhase::Current,
        &mut GraphBudget::new(0).unwrap(),
    ) {
        Ok(_) => panic!("non-type caller argument was accepted"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        "typed byte source caller argument is not an original Rust type"
    );
    let raw_dispatcher = engine.tcx.instance_mir(dispatcher.def);
    for (block, arity) in [(6, 0), (5, 2)] {
        let TerminatorKind::Call { func, .. } = &raw_dispatcher.basic_blocks
            [BasicBlock::from_usize(block)]
        .terminator()
        .kind
        else {
            panic!("actual unrelated helper Call")
        };
        let ty::FnDef(id, _) = func.ty(&raw_dispatcher.local_decls, engine.tcx).kind() else {
            panic!("actual unrelated helper FnDef")
        };
        let parameters = if arity == 0 {
            engine.tcx.mk_args(&[])
        } else {
            engine
                .tcx
                .mk_args(&[engine.tcx.types.u8.into(), engine.tcx.types.bool.into()])
        };
        let unrelated = ty::Instance::new_raw(*id, parameters);
        // Deliberately foreign body: an unselected key must not inspect its environment.
        assert!(
            byte_transport::source(
                engine,
                unrelated,
                &outer_body,
                byte_transport::SourcePhase::Current,
                &mut GraphBudget::new(0).unwrap(),
            )
            .unwrap()
            .is_none()
        );
    }
    eprintln!("TYPED BYTE unrelated zero/two-argument keys and non-type caller refusal");
    let TerminatorKind::Call { func, .. } = &raw_dispatcher.basic_blocks
        [rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        panic!("actual sizeof wrapper Call")
    };
    let ty::FnDef(size_id, _) = func.ty(&raw_dispatcher.local_decls, engine.tcx).kind() else {
        panic!("actual sizeof wrapper FnDef")
    };
    let size_instance = engine
        .resolve_function_item(*size_id, dispatcher.args)
        .unwrap();
    let size_current = engine
        .capture_niche_comparison_body(
            size_instance,
            &mut GraphBudget::new(0).unwrap(),
            false,
            GraphGoal::ByteRoute,
        )
        .unwrap()
        .body;
    let size_raw = engine.tcx.instance_mir(size_instance.def);
    let formal = Ty::new_param(engine.tcx, 0, rustc_span::Symbol::intern("T"));
    for (body, expected) in [
        (size_raw, formal),
        (size_current.as_ref(), outer.args.type_at(0)),
    ] {
        byte_transport::size_body(
            engine,
            size_instance,
            body,
            expected,
            &mut GraphBudget::new(0).unwrap(),
        )
        .unwrap();
        for mutation in 0..7 {
            let mut budget = GraphBudget::new(0).unwrap();
            let inventory = budget.inventory(engine.tcx, size_instance, body).unwrap();
            budget.phase(GraphPhase::BodyClone, inventory).unwrap();
            // Actual owned constant/type/terminator mutation and dispatch.
            budget.charge(32).unwrap();
            let mut changed = body.clone();
            if mutation == 0 {
                changed.local_decls[Local::from_usize(0)].ty = engine.tcx.types.bool;
            } else if mutation == 1 {
                changed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
                    .terminator_mut()
                    .kind = TerminatorKind::Unreachable;
            } else if mutation == 6 {
                budget.phase(GraphPhase::BodyClone, inventory).unwrap();
                budget.charge(4).unwrap(); // Actual extra statement copy and vector publication.
                let extra =
                    changed.basic_blocks[rustc_middle::mir::START_BLOCK].statements[0].clone();
                changed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
                    .statements
                    .push(extra);
            } else {
                let StatementKind::Assign(value) = &mut changed.basic_blocks.as_mut()
                    [rustc_middle::mir::START_BLOCK]
                    .statements[0]
                    .kind
                else {
                    panic!("actual sizeof assignment")
                };
                let Rvalue::Use(Operand::Constant(constant), _) = &mut value.1 else {
                    panic!("actual sizeof constant")
                };
                let rustc_middle::mir::Const::Unevaluated(original, ty) = constant.const_ else {
                    panic!("actual associated SIZE")
                };
                let mut altered = original;
                let mut altered_ty = ty;
                match mutation {
                    2 => altered.def = *size_id,
                    3 => altered.args = engine.tcx.mk_args(&[engine.tcx.types.bool.into()]),
                    4 => altered.promoted = Some(rustc_middle::mir::Promoted::from_usize(0)),
                    5 => altered_ty = engine.tcx.types.bool,
                    _ => unreachable!(),
                }
                constant.const_ = rustc_middle::mir::Const::Unevaluated(altered, altered_ty);
            }
            let error =
                byte_transport::size_body(engine, size_instance, &changed, expected, &mut budget)
                    .unwrap_err();
            assert!(error.starts_with("typed byte sizeof "), "{error}");
            if std::ptr::eq(body, size_current.as_ref()) {
                engine
                    .bodies
                    .borrow_mut()
                    .insert(size_instance, std::rc::Rc::new(changed));
                let error = match engine.capture_niche_comparison_body(
                    size_instance,
                    &mut GraphBudget::new(0).unwrap(),
                    false,
                    GraphGoal::ByteRoute,
                ) {
                    Ok(_) => panic!("changed current sizeof wrapper was accepted"),
                    Err(error) => error,
                };
                let expected_error = if mutation == 4 {
                    "comparison template has uncertified embedded compiler identities"
                } else if mutation == 6 {
                    "typed byte current block/source attributes differ from original"
                } else {
                    "niche cached body differs from actual compiler body"
                };
                assert_eq!(error, expected_error);
                engine
                    .bodies
                    .borrow_mut()
                    .insert(size_instance, size_current.clone());
            }
        }
    }
    let wrong_trait = engine.tcx.lang_items().sized_trait().unwrap();
    let error = byte_transport::size_trait(engine, wrong_trait, &mut GraphBudget::new(0).unwrap())
        .unwrap_err();
    assert_eq!(
        error,
        "typed byte sizeof associated constant original trait differs"
    );
    eprintln!(
        "TYPED BYTE sizeof seven raw/current mutants and standalone trait gate, no layout fact"
    );
    let captured = engine
        .capture_niche_comparison_body(
            dispatcher,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        )
        .unwrap();
    let raw = engine.tcx.instance_mir(dispatcher.def);
    let current = captured.body;
    for (body, phase) in [
        (raw, byte_transport::SourcePhase::Raw),
        (current.as_ref(), byte_transport::SourcePhase::Current),
    ] {
        let shape = byte_transport::source(
            engine,
            dispatcher,
            body,
            phase,
            &mut GraphBudget::new(0).unwrap(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            shape.family(),
            super::super::pure_comparison_templates::PureTemplateFamily::ContainsBytes
        );
    }
    let original = outer.args.type_at(0);
    let mut budget = GraphBudget::new(0).unwrap();
    budget.charge(8).unwrap(); // Actual two Rc copies and temporary record construction.
    let records = [(outer, outer_body.clone()), (dispatcher, current.clone())];
    let mapping =
        byte_transport::bind_current(engine, original, outer, dispatcher, &records, &mut budget)
            .unwrap()
            .unwrap();
    assert_eq!(mapping.helpers.len(), 9);
    assert_eq!(
        mapping.outer_transfers,
        [byte_transport::SharedTransfer::Copy; 2]
    );
    assert_eq!(
        mapping.dispatcher_transfers,
        [byte_transport::SharedTransfer::Copy; 2]
    );
    mapping.check_held_modes(&engine.bodies.borrow()).unwrap();
    for mutation in [
        Mutation::LocalType,
        Mutation::SharedMutability,
        Mutation::Predicate,
        Mutation::Branch,
        Mutation::NeedleOperand,
        Mutation::SliceMove,
        Mutation::RawArguments,
        Mutation::TupleField,
        Mutation::SearchArguments,
        Mutation::Result,
        Mutation::ClosureCapture,
        Mutation::NormalEdge,
        Mutation::Unwind,
        Mutation::Helper,
    ] {
        let mut budget = GraphBudget::new(0).unwrap();
        let inventory = budget.inventory(engine.tcx, dispatcher, raw).unwrap();
        budget.phase(GraphPhase::BodyClone, inventory).unwrap();
        budget.charge(64).unwrap(); // Actual bounded source mutation and gate dispatch.
        let mut changed = raw.clone();
        change(engine, &mut changed, mutation);
        let error = match byte_transport::source(
            engine,
            dispatcher,
            &changed,
            byte_transport::SourcePhase::Raw,
            &mut budget,
        ) {
            Ok(_) => panic!("changed typed raw dispatcher was accepted"),
            Err(error) => error,
        };
        assert!(error.starts_with("typed byte "), "{error}");
        let inventory = budget.inventory(engine.tcx, dispatcher, &current).unwrap();
        budget.phase(GraphPhase::BodyClone, inventory).unwrap();
        budget.charge(64).unwrap();
        let mut changed = current.as_ref().clone();
        change(engine, &mut changed, mutation);
        engine
            .bodies
            .borrow_mut()
            .insert(dispatcher, std::rc::Rc::new(changed));
        let error = match engine.capture_niche_comparison_body(
            dispatcher,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        ) {
            Ok(_) => panic!("changed typed current dispatcher was accepted"),
            Err(error) => error,
        };
        let expected_error =
            if matches!(mutation, Mutation::RawArguments | Mutation::SearchArguments) {
                "typed byte current Call occurrence spans differ from original"
            } else {
                "niche cached body differs from actual compiler body"
            };
        assert_eq!(error, expected_error);
        engine
            .bodies
            .borrow_mut()
            .insert(dispatcher, current.clone());
    }
    engine
        .capture_niche_comparison_body(
            dispatcher,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        )
        .unwrap();
    mapping.check_held_modes(&engine.bodies.borrow()).unwrap();
    eprintln!(
        "TYPED BYTE actual full original/current dispatcher and fourteen raw/current mutations"
    );
}

pub(super) fn compiler_precondition_controls<'tcx>(
    engine: &Engine<'tcx>,
    root: ty::Instance<'tcx>,
) {
    let root_body = engine.instantiated_body(root).unwrap();
    let outer = root_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return None;
            };
            let ty::FnDef(id, args) = func.ty(&root_body.local_decls, engine.tcx).kind() else {
                return None;
            };
            Some(
                engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap(),
            )
        })
        .unwrap();
    let mut budget = GraphBudget::new(0).unwrap();
    let outer_body = engine
        .capture_niche_comparison_body(outer, &mut budget, true, GraphGoal::ByteRoute)
        .unwrap()
        .body;
    let TerminatorKind::Call { func, .. } = &outer_body.basic_blocks
        [rustc_middle::mir::START_BLOCK]
        .terminator()
        .kind
    else {
        panic!("actual dispatcher")
    };
    let ty::FnDef(id, args) = func.ty(&outer_body.local_decls, engine.tcx).kind() else {
        panic!("actual dispatcher item")
    };
    let dispatcher = engine
        .resolve_function_item(*id, args.skip_binder())
        .unwrap();
    let dispatcher_body = engine
        .capture_niche_comparison_body(dispatcher, &mut budget, true, GraphGoal::ByteRoute)
        .unwrap()
        .body;
    let original = outer.args.type_at(0);
    budget.charge(8).unwrap();
    let records = [
        (outer, outer_body.clone()),
        (dispatcher, dispatcher_body.clone()),
    ];
    let mapping =
        byte_transport::bind_current(engine, original, outer, dispatcher, &records, &mut budget)
            .unwrap()
            .unwrap();
    let fact =
        byte_transport::compiler_byte_layout(engine, &mapping, original, &mut budget).unwrap();
    assert!(fact.matches(original));
    assert!(!fact.matches(engine.tcx.types.bool));
    let error = match byte_transport::compiler_byte_layout(
        engine,
        &mapping,
        engine.tcx.types.bool,
        &mut GraphBudget::new(0).unwrap(),
    ) {
        Ok(_) => panic!("foreign original item produced a byte layout fact"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        "byte layout fact has a different original caller item"
    );
    let held = engine.bodies.borrow_mut();
    let error = match byte_transport::compiler_byte_layout(
        engine,
        &mapping,
        original,
        &mut GraphBudget::new(0).unwrap(),
    ) {
        Ok(_) => panic!("conflicting registry produced a layout fact"),
        Err(error) => error,
    };
    assert_eq!(error, "byte layout Body registry is borrowed");
    drop(held);
    eprintln!("BYTE LAYOUT actual SIZE equals original size1 align1; no branch/storage rights");
    super::byte_search_source::pending::compiler_controls(
        engine,
        mapping.helpers[5].instance,
        budget.work,
    );
}
