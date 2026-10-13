//! Bounded prepaid clone planning for constructor and iterator-step evidence.
//! Interned compiler handles clone shallowly; opaque compiler queries are not instruction-counted.
use super::*;
use rustc_middle::mir::{AssertKind, ClearCrossCrate, ConstOperand, Terminator};

struct Plan {
    nodes: usize,
    owned: usize,
}

impl Plan {
    fn node(&mut self, engine: &mut Engine<'_>, clone_fields: usize) -> Result<(), String> {
        pay(engine, 1)?; // This distinct borrowed planning visit occurs even if allocation refuses.
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter clone plan exceeds the existing 512-node limit".into(),
            ));
        }
        self.owned = self
            .owned
            .checked_add(clone_fields)
            .ok_or("IntoIter owned clone work overflow")?;
        Ok(())
    }

    fn vector(&mut self, engine: &mut Engine<'_>, length: usize) -> Result<(), String> {
        self.node(engine, 1 + length)?; // Allocation/header and shallow element copies.
        if length > MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter clone vector exceeds the existing 512-node limit".into(),
            ));
        }
        Ok(())
    }

    fn constant(&mut self, engine: &mut Engine<'_>, _: &ConstOperand<'_>) -> Result<(), String> {
        // span, optional user annotation index and Const are inline/interned handles.
        self.node(engine, 3)
    }

    fn operand(&mut self, engine: &mut Engine<'_>, operand: &Operand<'_>) -> Result<(), String> {
        self.node(engine, 1)?;
        match operand {
            Operand::Constant(value) => {
                self.node(engine, 1)?; // Owned ConstOperand Box.
                self.constant(engine, value)
            }
            Operand::Copy(_) | Operand::Move(_) | Operand::RuntimeChecks(_) => Ok(()),
        }
    }

    fn rvalue(&mut self, engine: &mut Engine<'_>, value: &Rvalue<'_>) -> Result<(), String> {
        self.node(engine, 1)?;
        match value {
            Rvalue::Use(operand, _)
            | Rvalue::Repeat(operand, _)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::WrapUnsafeBinder(operand, _) => self.operand(engine, operand),
            Rvalue::BinaryOp(_, operands) => {
                self.node(engine, 3)?; // Owned pair Box and two inline operand fields.
                self.operand(engine, &operands.0)?;
                self.operand(engine, &operands.1)
            }
            Rvalue::Aggregate(_, operands) => {
                self.node(engine, 2)?; // AggregateKind Box; its Ty/Args/DefId fields are interned.
                self.vector(engine, operands.len())?;
                for operand in operands {
                    self.operand(engine, operand)?;
                }
                Ok(())
            }
            Rvalue::Ref(..)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::RawPtr(..)
            | Rvalue::Discriminant(_)
            | Rvalue::CopyForDeref(_)
            | Rvalue::Reborrow(..) => Ok(()),
        }
    }

    fn debug_infos(
        &mut self,
        engine: &mut Engine<'_>,
        infos: &rustc_middle::mir::StmtDebugInfos<'_>,
    ) -> Result<(), String> {
        self.vector(engine, infos.len())?;
        for info in infos.as_slice() {
            match info {
                rustc_middle::mir::StmtDebugInfo::AssignRef(_, _) => self.node(engine, 2)?,
                rustc_middle::mir::StmtDebugInfo::InvalidAssign(_) => self.node(engine, 1)?,
            }
        }
        Ok(())
    }
    fn statement(
        &mut self,
        engine: &mut Engine<'_>,
        statement: &StatementKind<'_>,
    ) -> Result<(), String> {
        self.node(engine, 3)?; // SourceInfo, StatementKind and empty StmtDebugInfos fields.
        match statement {
            StatementKind::Assign(assignment) => {
                self.node(engine, 3)?; // Pair Box, Place handle and Rvalue field.
                self.rvalue(engine, &assignment.1)
            }
            StatementKind::SetDiscriminant { .. }
            | StatementKind::PlaceMention(_)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::FakeRead(_) => {
                self.node(engine, 2) // Owned place/pair Box; Place projections are interned.
            }
            StatementKind::Intrinsic(intrinsic) => {
                self.node(engine, 2)?;
                match intrinsic.as_ref() {
                    rustc_middle::mir::NonDivergingIntrinsic::Assume(operand) => {
                        self.operand(engine, operand)
                    }
                    rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                        self.operand(engine, &copy.src)?;
                        self.operand(engine, &copy.dst)?;
                        self.operand(engine, &copy.count)
                    }
                }
            }
            StatementKind::AscribeUserType(..) | StatementKind::Coverage(_) => {
                Err("IntoIter clone plan auxiliary statement payload is unsupported".into())
            }
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter => Ok(()),
        }
    }

    fn terminator(
        &mut self,
        engine: &mut Engine<'_>,
        terminator: &Terminator<'_>,
    ) -> Result<(), String> {
        self.node(engine, 3)?;
        if !terminator.attributes.is_empty() {
            return Err("IntoIter clone plan terminator attributes are unsupported".into());
        }
        match &terminator.kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                self.operand(engine, func)?;
                self.node(engine, 1)?; // Owned argument slice Box.
                self.vector(engine, args.len())?;
                for arg in args {
                    self.node(engine, 1)?;
                    self.operand(engine, &arg.node)?;
                }
                Ok(())
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.operand(engine, discr)?;
                // SwitchTargets owns its values SmallVec and targets SmallVec. Their exposed
                // lengths bound inline copies and any spilled allocation, without reading caches.
                self.vector(engine, targets.all_targets().len())?;
                self.vector(engine, targets.all_targets().len())
            }
            TerminatorKind::Assert { cond, msg, .. } => {
                self.operand(engine, cond)?;
                self.node(engine, 2)?; // AssertMessage Box and its enum payload.
                match msg.as_ref() {
                    AssertKind::BoundsCheck { len, index }
                    | AssertKind::MisalignedPointerDereference {
                        required: len,
                        found: index,
                    }
                    | AssertKind::Overflow(_, len, index) => {
                        self.operand(engine, len)?;
                        self.operand(engine, index)
                    }
                    AssertKind::OverflowNeg(value)
                    | AssertKind::DivisionByZero(value)
                    | AssertKind::RemainderByZero(value)
                    | AssertKind::InvalidEnumConstruction(value) => self.operand(engine, value),
                    AssertKind::ResumedAfterReturn(_)
                    | AssertKind::ResumedAfterPanic(_)
                    | AssertKind::ResumedAfterDrop(_)
                    | AssertKind::NullPointerDereference
                    | AssertKind::NullReferenceConstructed => Ok(()),
                }
            }
            TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => {
                Err("IntoIter clone plan coroutine/assembly is unsupported".into())
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => Ok(()),
        }
    }
}

pub(super) fn step_statement(
    engine: &mut Engine<'_>,
    statement: &rustc_middle::mir::Statement<'_>,
) -> Result<usize, String> {
    let mut plan = Plan { nodes: 0, owned: 0 };
    plan.statement(engine, &statement.kind)?;
    plan.debug_infos(engine, &statement.debuginfos)?;
    Ok(plan.owned)
}
pub(super) fn step_terminator(
    engine: &mut Engine<'_>,
    terminator: &Terminator<'_>,
) -> Result<usize, String> {
    let mut plan = Plan { nodes: 0, owned: 0 };
    plan.terminator(engine, terminator)?;
    Ok(plan.owned)
}
pub(super) fn step_variable(
    engine: &mut Engine<'_>,
    info: &rustc_middle::mir::VarDebugInfo<'_>,
) -> Result<usize, String> {
    let mut plan = Plan { nodes: 0, owned: 0 };
    plan.node(engine, 5)?;
    if let Some(fragment) = &info.composite {
        plan.node(engine, 3)?;
        plan.vector(engine, fragment.projection.len())?;
    }
    if let VarDebugInfoContents::Const(value) = &info.value {
        plan.constant(engine, value)?;
    }
    Ok(plan.owned)
}
pub(super) fn body(engine: &mut Engine<'_>, body: &Body<'_>) -> Result<usize, String> {
    body_inner(engine, body, false, false)
}
pub(super) fn step_body(engine: &mut Engine<'_>, body: &Body<'_>) -> Result<usize, String> {
    body_inner(engine, body, true, false)
}
pub(super) fn drop_body(engine: &mut Engine<'_>, body: &Body<'_>) -> Result<usize, String> {
    if !matches!(
        body.source.instance,
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_)))
    ) {
        return Err("IntoIter destruction clone plan requires actual typed DropGlue".into());
    }
    body_inner(engine, body, true, true)
}
fn body_inner(
    engine: &mut Engine<'_>,
    body: &Body<'_>,
    step_debug: bool,
    boring_locals: bool,
) -> Result<usize, String> {
    let mut plan = Plan { nodes: 0, owned: 0 };
    plan.node(engine, 20)?; // Pinned Body fields plus shallow BasicBlocks cache Arc clone.
    if body.coroutine.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
    {
        return Err("IntoIter clone plan coroutine/coverage metadata is unsupported".into());
    }
    if !body.user_type_annotations.is_empty() {
        return Err("IntoIter clone plan canonical user annotation table is unsupported".into());
    }
    plan.vector(engine, body.user_type_annotations.len())?;
    plan.vector(engine, body.source_scopes.len())?;
    for _ in &body.source_scopes {
        plan.node(engine, 5)?;
    } // All scope fields are inline handles.
    plan.vector(engine, body.local_decls.len())?;
    for local in &body.local_decls {
        plan.node(engine, 5)?;
        match &local.local_info {
            ClearCrossCrate::Clear => {}
            ClearCrossCrate::Set(info)
                if boring_locals
                    && matches!(info.as_ref(), rustc_middle::mir::LocalInfo::Boring) =>
            {
                plan.node(engine, 2)?; // A real LocalInfo Box allocation and its Boring enum.
            }
            ClearCrossCrate::Set(_) => {
                return Err(
                    "IntoIter clone plan owned local auxiliary metadata is unsupported".into(),
                );
            }
        }
        if local.user_ty.is_some() {
            return Err("IntoIter clone plan owned local auxiliary metadata is unsupported".into());
        }
    }
    plan.vector(engine, body.var_debug_info.len())?;
    for info in &body.var_debug_info {
        plan.node(engine, 5)?;
        if let Some(fragment) = &info.composite {
            plan.node(engine, 3)?; // Fragment Box plus Ty/projection fields.
            plan.vector(engine, fragment.projection.len())?;
        }
        match &info.value {
            VarDebugInfoContents::Place(_) => {}
            VarDebugInfoContents::Const(value) => plan.constant(engine, value)?,
        }
    }
    if let Some(constants) = &body.required_consts {
        plan.vector(engine, constants.len())?;
        for constant in constants {
            plan.constant(engine, constant)?;
        }
    }
    if let Some(items) = &body.mentioned_items {
        plan.vector(engine, items.len())?;
    }
    plan.vector(engine, body.basic_blocks.len())?;
    for block in body.basic_blocks.iter() {
        plan.node(engine, 4)?;
        if !step_debug && !block.after_last_stmt_debuginfos.is_empty() {
            return Err("IntoIter clone plan block debug payload is unsupported".into());
        }
        if step_debug {
            plan.debug_infos(engine, &block.after_last_stmt_debuginfos)?;
        }
        plan.vector(engine, block.statements.len())?;
        for statement in &block.statements {
            if !step_debug && !statement.debuginfos.is_empty() {
                return Err("IntoIter clone plan statement debug payload is unsupported".into());
            }
            if step_debug {
                plan.debug_infos(engine, &statement.debuginfos)?;
            }
            plan.statement(engine, &statement.kind)?;
        }
        let terminator = block
            .terminator
            .as_ref()
            .ok_or("IntoIter clone plan terminator is missing")?;
        plan.terminator(engine, terminator)?;
    }
    Ok(plan.owned)
}

pub(super) fn masks(
    engine: &mut Engine<'_>,
    masks: &initialized_places::MissingPlaces,
) -> Result<initialized_places::MissingPlaces, String> {
    let work = mask_clone_work(engine, masks)?;
    pay(engine, work)?;
    Ok(masks.clone())
}

pub(super) fn mask_clone_work(
    engine: &mut Engine<'_>,
    masks: &initialized_places::MissingPlaces,
) -> Result<usize, String> {
    pay(engine, 1)?; // Distinct borrowed ledger planning pass.
    let mut nodes = 0_usize;
    let mut clone_work = 1_usize; // Owned entries vector header/allocation.
    for (_, path) in masks.entries() {
        pay(engine, 1)?;
        nodes = nodes
            .checked_add(1 + path.len())
            .ok_or("IntoIter mask node count overflow")?;
        if path.len() > MAX_INPUT_DEPTH || nodes > MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter mask clone exceeds existing 512-node/depth16 bounds".into(),
            ));
        }
        clone_work = clone_work
            .checked_add(3 + path.len())
            .ok_or("IntoIter initialization ledger clone work overflow")?;
    }
    Ok(clone_work)
}
