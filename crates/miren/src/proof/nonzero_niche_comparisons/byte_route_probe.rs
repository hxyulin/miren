//! Actual compiler Copy transport schema controls; this grants no search or storage rights.
use super::*;

#[derive(Clone, Copy)]
enum Mutation {
    Operands,
    Move,
    Type,
    Mutability,
    Destination,
    Target,
    Unwind,
}

fn mutate<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>, mutation: Mutation) {
    use rustc_middle::mir::{Local, Place, UnwindAction};
    match mutation {
        Mutation::Type => body.local_decls[Local::from_usize(2)].ty = tcx.types.u8,
        Mutation::Mutability => {
            let ty::Ref(region, item, rustc_hir::Mutability::Not) =
                body.local_decls[Local::from_usize(2)].ty.kind()
            else {
                panic!("actual immutable needle reference")
            };
            body.local_decls[Local::from_usize(2)].ty =
                Ty::new_ref(tcx, *region, *item, rustc_hir::Mutability::Mut);
        }
        Mutation::Operands
        | Mutation::Move
        | Mutation::Destination
        | Mutation::Target
        | Mutation::Unwind => {
            let TerminatorKind::Call {
                args,
                destination,
                target,
                unwind,
                ..
            } = &mut body.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
                .terminator_mut()
                .kind
            else {
                panic!("actual Contains forwarding Call")
            };
            match mutation {
                Mutation::Operands => args.swap(0, 1),
                Mutation::Move => {
                    let Operand::Copy(place) = args[0].node else {
                        panic!("actual shared Copy operand")
                    };
                    args[0].node = Operand::Move(place);
                }
                Mutation::Destination => *destination = Place::from(Local::from_usize(1)),
                Mutation::Target => *target = Some(rustc_middle::mir::START_BLOCK),
                Mutation::Unwind => *unwind = UnwindAction::Continue,
                Mutation::Type | Mutation::Mutability => unreachable!(),
            }
        }
    }
}

pub(super) fn compiler_controls<'tcx>(engine: &Engine<'tcx>, root: ty::Instance<'tcx>) {
    use super::super::super::pure_comparison_templates as templates;
    let root_body = engine.instantiated_body(root).unwrap();
    let selected = root_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return None;
            };
            let ty::FnDef(id, args) = func.ty(&root_body.local_decls, engine.tcx).kind() else {
                return None;
            };
            (templates::definition_key(*id) == "DefId(core::slice::{impl#0}::contains)").then(
                || {
                    engine
                        .resolve_function_item(*id, args.skip_binder())
                        .unwrap()
                },
            )
        })
        .expect("actual membership outer Contains Call");
    let raw = engine.tcx.instance_mir(selected.def);
    let core = engine.tcx.lang_items().sized_trait().unwrap().krate;
    let key = templates::definition_key(selected.def_id());
    let encoded = templates::encode_template(engine.tcx, raw, core).unwrap();
    assert!(templates::reference_family(&key, &encoded).is_none());
    assert_eq!(
        super::byte_route::copy_contains_reference(
            &key,
            &encoded,
            &mut GraphBudget::new(0).unwrap()
        )
        .unwrap(),
        Some(templates::PureTemplateFamily::Contains)
    );
    let captured = engine
        .capture_niche_comparison_body(
            selected,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        )
        .unwrap();
    assert_eq!(
        captured.family,
        Some(templates::PureTemplateFamily::Contains)
    );
    let current = engine.bodies.borrow().get(&selected).unwrap().clone();
    for mutation in [
        Mutation::Operands,
        Mutation::Move,
        Mutation::Type,
        Mutation::Mutability,
        Mutation::Destination,
        Mutation::Target,
        Mutation::Unwind,
    ] {
        let mut paid = GraphBudget::new(0).unwrap();
        let raw_work = paid.inventory(engine.tcx, selected, raw).unwrap();
        paid.phase(GraphPhase::BodyClone, raw_work).unwrap();
        paid.charge(32).unwrap(); // Actual bounded clone mutation and standalone gate dispatch.
        let mut changed_raw = raw.clone();
        mutate(engine.tcx, &mut changed_raw, mutation);
        let changed = templates::encode_template(engine.tcx, &changed_raw, core).unwrap();
        assert!(
            super::byte_route::copy_contains_reference(&key, &changed, &mut paid)
                .unwrap()
                .is_none()
        );
        let current_work = paid.inventory(engine.tcx, selected, &current).unwrap();
        paid.phase(GraphPhase::BodyClone, current_work).unwrap();
        paid.charge(32).unwrap();
        let mut changed_current = current.as_ref().clone();
        mutate(engine.tcx, &mut changed_current, mutation);
        engine
            .bodies
            .borrow_mut()
            .insert(selected, std::rc::Rc::new(changed_current));
        let error = match engine.capture_niche_comparison_body(
            selected,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        ) {
            Ok(_) => panic!("changed current Contains Body was accepted"),
            Err(error) => error,
        };
        let expected = if matches!(mutation, Mutation::Operands) {
            "typed byte current Call occurrence spans differ from original"
        } else {
            "niche cached body differs from actual compiler body"
        };
        assert_eq!(error, expected);
        engine.bodies.borrow_mut().insert(selected, current.clone());
    }
    engine
        .capture_niche_comparison_body(
            selected,
            &mut GraphBudget::new(0).unwrap(),
            true,
            GraphGoal::ByteRoute,
        )
        .unwrap();
    eprintln!("BYTE COPY actual original/current source and seven hostile transport controls");
}
