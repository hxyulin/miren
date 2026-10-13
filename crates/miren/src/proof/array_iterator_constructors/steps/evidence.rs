//! Immutable original/current MIR evidence; no execution or ownership facts are cached.
use super::*;

pub(super) fn schema<'tcx>(
    engine: &mut Engine<'tcx>,
    evidence: &BodyEvidence<'tcx>,
    kind: FrameKind,
    direction: Direction,
    element: Ty<'tcx>,
) -> Result<(), String> {
    let body = &evidence.current;
    pay(engine, body.local_decls.len() + body.basic_blocks.len() + 1)?;
    let counts: &[usize] = match kind {
        FrameKind::Public => &[5, 1],
        FrameKind::Inner => &[11, 4, 7, 0, 17, 2, 2, 1, 8, 10],
        FrameKind::BoundsHelper => return Err("bounds helper has no iterator schema".into()),
    };
    if body.arg_count != 1
        || body.basic_blocks.len() != counts.len()
        || body.local_decls.len() != if kind == FrameKind::Public { 4 } else { 25 }
        || body
            .basic_blocks
            .iter()
            .zip(counts)
            .any(|(block, count)| block.is_cleanup || block.statements.len() != *count)
        || engine.tcx.lang_items().get(LangItem::Option)
            != body.return_ty().ty_adt_def().map(|def| def.did())
    {
        return Err("IntoIter step exact original local/block/output schema differs".into());
    }
    let ty::Adt(_, args) = body.return_ty().kind() else {
        unreachable!()
    };
    if args.type_at(0) != element {
        return Err("IntoIter step Option original element type differs".into());
    }
    if kind == FrameKind::Public {
        if !matches!(assignment(body,0,2,3)?,Rvalue::Ref(_,BorrowKind::Mut{..},place)
            if field_path(*place,1,&[0,0]))
            || !matches!(assignment(body,0,3,2)?,Rvalue::Cast(
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize,_),operand,_)
                if copied(operand,3))
        {
            return Err("IntoIter step exact public forwarding projection/Unsize differs".into());
        }
    } else {
        for (index, field) in [(4, 1), (6, 0)] {
            if !matches!(assignment(body,0,index,if field==1{9}else{10})?,
                Rvalue::Use(Operand::Copy(place),_) if field_path(*place,1,&[0,field]))
            {
                return Err("IntoIter step exact range read differs".into());
            }
        }
        let cursor = if direction == Direction::Front { 1 } else { 2 };
        let StatementKind::Assign(pair) =
            &body.basic_blocks[BasicBlock::from_usize(4)].statements[cursor].kind
        else {
            return Err("IntoIter step cursor store absent".into());
        };
        if !field_path(
            pair.0,
            1,
            &[0, if direction == Direction::Front { 0 } else { 1 }],
        ) || !matches!(&pair.1,Rvalue::Use(operand,_) if
                matches!(
                    operand,
                    Operand::Move(place) if direction == Direction::Front && local(*place, 11)
                )
                || copied(operand,8)&&direction==Direction::Back)
            || !matches!(assignment(body,9,2,14)?,Rvalue::Use(Operand::Copy(place),_)
                if place.local.as_usize()==22&&place.projection.as_ref()==[ProjectionElem::Deref])
        {
            return Err("IntoIter step exact cursor store/owning read differs".into());
        }
    }
    Ok(())
}
pub(super) fn load_evidence<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<BodyEvidence<'tcx>, String> {
    compiler_evidence::load_item(engine, instance)
}
