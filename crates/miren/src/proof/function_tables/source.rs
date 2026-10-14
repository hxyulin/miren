//! No-substitution original/current comparison. No owned Body is cloned or folded here.
use super::*;
use rustc_middle::mir::Statement;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
use std::ops::ControlFlow;

struct Work<'a, 'tcx> {
    engine: &'a mut Engine<'tcx>,
    nodes: usize,
    depth: usize,
    error: Option<String>,
}
impl Work<'_, '_> {
    fn node(&mut self, count: usize) -> bool {
        self.nodes = self.nodes.saturating_add(1);
        self.pay(count)
    }
    fn pay(&mut self, count: usize) -> bool {
        if self.error.is_some() {
            return false;
        }
        if let Err(error) = super::nested::pay(self.engine, count) {
            self.error = Some(error);
            return false;
        }
        if self.nodes > MAX_INPUT_VALUES
            || count > MAX_INPUT_VALUES
            || self.depth >= MAX_INPUT_DEPTH
        {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                format!(
                    "nested choice borrowed source exceeds existing512/depth16 bounds: \
                     nodes={} depth={} width={count}",
                    self.nodes, self.depth,
                ),
            ));
            return false;
        }
        true
    }
}
impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for Work<'_, 'tcx> {
    type Result = ControlFlow<()>;
    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        if !self.node(1) {
            return ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Never
            | ty::Str
            | ty::Tuple(_)
            | ty::Array(..)
            | ty::Slice(_)
            | ty::Ref(..)
            | ty::RawPtr(..)
            | ty::Adt(..) => original.super_visit_with(self),
            ty::FnDef(_, arguments) => {
                if !self.node(arguments.bound_vars().len()) {
                    ControlFlow::Break(())
                } else {
                    original.super_visit_with(self)
                }
            }
            ty::FnPtr(signature, _) => {
                if !self.node(signature.bound_vars().len()) {
                    ControlFlow::Break(())
                } else {
                    original.super_visit_with(self)
                }
            }
            ty::Param(_)
            | ty::Bound(..)
            | ty::Alias(..)
            | ty::Foreign(_)
            | ty::Pat(..)
            | ty::UnsafeBinder(_)
            | ty::Dynamic(..)
            | ty::Closure(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => {
                self.error =
                    Some("nested choice borrowed source needs streamed type normalization".into());
                ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }
    fn visit_region(&mut self, _: ty::Region<'tcx>) -> Self::Result {
        if self.node(1) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }
    fn visit_const(&mut self, original: ty::Const<'tcx>) -> Self::Result {
        if !self.node(1) {
            return ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::ConstKind::Value(_) => original.super_visit_with(self),
            ty::ConstKind::Param(_)
            | ty::ConstKind::Bound(..)
            | ty::ConstKind::Alias(..)
            | ty::ConstKind::Expr(_)
            | ty::ConstKind::Infer(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Error(_) => {
                self.error =
                    Some("nested choice borrowed constant needs streamed normalization".into());
                ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }
}
impl<'tcx> Visitor<'tcx> for Work<'_, 'tcx> {
    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        let _ = TypeVisitable::visit_with(&original, self);
    }
    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: rustc_middle::mir::Location,
    ) {
        if place.projection.len() > MAX_INPUT_DEPTH || !self.node(1 + place.projection.len()) {
            self.error
                .get_or_insert_with(|| "nested choice source Place exceeds depth16".into());
            return;
        }
        self.super_place(place, context, location);
    }
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        if self.node(1) {
            self.super_operand(operand, location);
        }
    }
    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: rustc_middle::mir::Location) {
        let size = match value {
            Rvalue::Aggregate(_, operands) => operands.len(),
            Rvalue::BinaryOp(_, _) => 2,
            Rvalue::Use(..)
            | Rvalue::Repeat(..)
            | Rvalue::Cast(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::WrapUnsafeBinder(..)
            | Rvalue::Ref(..)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::RawPtr(..)
            | Rvalue::Discriminant(_)
            | Rvalue::CopyForDeref(_)
            | Rvalue::Reborrow(..) => 0,
        };
        if self.node(1 + size) {
            self.super_rvalue(value, location);
        }
    }
    fn visit_statement(
        &mut self,
        statement: &Statement<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if !self.node(2) {
            return;
        }
        if !statement.debuginfos.is_empty()
            || matches!(
                statement.kind,
                StatementKind::Coverage(_) | StatementKind::AscribeUserType(..)
            )
        {
            self.error =
                Some("nested choice borrowed statement auxiliary payload unsupported".into());
            return;
        }
        self.super_statement(statement, location);
    }
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if !self.node(2) {
            return;
        }
        let size = match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args.len(),
            TerminatorKind::SwitchInt { targets, .. } => 2 * targets.all_targets().len(),
            TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => {
                self.error = Some("nested choice borrowed assembly/coroutine unsupported".into());
                return;
            }
            TerminatorKind::Assert { .. } => 3,
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => 0,
        };
        if self.node(size) {
            self.super_terminator(terminator, location);
        }
    }
}

fn inventory<'tcx>(
    work: &mut Work<'_, 'tcx>,
    body: &Body<'tcx>,
    types: bool,
) -> Result<(), String> {
    if !(if types { work.node(24) } else { work.pay(24) }) {
        return Err(work.error.take().unwrap());
    }
    if body.arg_count >= body.local_decls.len()
        || body.local_decls.len() > MAX_INPUT_VALUES
        || body.basic_blocks.len() > 128
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.tainted_by_errors.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
        || !body.user_type_annotations.is_empty()
    {
        return Err("nested choice borrowed source auxiliary metadata unsupported".into());
    }
    if !work.pay(body.local_decls.len() + body.source_scopes.len() + body.var_debug_info.len()) {
        return Err(work.error.take().unwrap());
    }
    for local in &body.local_decls {
        if local.user_ty.is_some()
            || matches!(local.local_info, rustc_middle::mir::ClearCrossCrate::Set(_))
        {
            return Err(
                "nested choice borrowed source local auxiliary metadata unsupported".into(),
            );
        }
    }
    for variable in &body.var_debug_info {
        if variable.composite.is_some() {
            return Err("nested choice borrowed composite debug metadata unsupported".into());
        }
    }
    for data in body.basic_blocks.iter() {
        if !work.pay(3 + data.statements.len()) {
            return Err(work.error.take().unwrap());
        }
        let Some(term) = &data.terminator else {
            return Err("nested source terminator absent".into());
        };
        if !term.attributes.is_empty() || !data.after_last_stmt_debuginfos.is_empty() {
            return Err("nested choice borrowed source debug/attribute payload unsupported".into());
        }
        // Each owned vector is bounded before a later borrowed equality can inspect it.
        let payload = match &term.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args.len(),
            TerminatorKind::SwitchInt { targets, .. } => 2 * targets.all_targets().len(),
            TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => {
                return Err("nested choice borrowed assembly/coroutine unsupported".into());
            }
            TerminatorKind::Assert { .. } => 3,
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => 0,
        };
        if !work.pay(1 + payload) {
            return Err(work.error.take().unwrap());
        }
        for statement in &data.statements {
            if !statement.debuginfos.is_empty()
                || matches!(
                    statement.kind,
                    StatementKind::Coverage(_) | StatementKind::AscribeUserType(..)
                )
            {
                return Err(
                    "nested choice borrowed statement auxiliary payload unsupported".into(),
                );
            }
            if let StatementKind::Assign(pair) = &statement.kind
                && let Rvalue::Aggregate(_, operands) = &pair.1
                && !work.pay(1 + operands.len())
            {
                return Err(work.error.take().unwrap());
            }
        }
        for target in term.successors() {
            if !work.pay(2) {
                return Err(work.error.take().unwrap());
            }
            if target.as_usize() >= body.basic_blocks.len() {
                return Err("nested choice borrowed source CFG edge outside Body".into());
            }
        }
    }
    if let Some(constants) = &body.required_consts {
        if !work.pay(constants.len()) {
            return Err(work.error.take().unwrap());
        }
        if types {
            for constant in constants {
                work.visit_const_operand(constant, rustc_middle::mir::Location::START);
            }
        }
    }
    if types {
        work.visit_body(body);
    }
    for scope in &body.source_scopes {
        if let Some((instance, _)) = scope.inlined {
            if !work.pay(1 + instance.args.len()) {
                return Err(work.error.take().unwrap());
            }
            if types {
                let _ = instance.args.visit_with(work);
            }
        }
    }
    if let Some(items) = &body.mentioned_items {
        if !work.pay(items.len()) {
            return Err(work.error.take().unwrap());
        }
        for item in items {
            if !types {
                continue;
            }
            match item.node {
                rustc_middle::mir::MentionedItem::Fn(ty)
                | rustc_middle::mir::MentionedItem::Drop(ty)
                | rustc_middle::mir::MentionedItem::Closure(ty) => {
                    let _ = ty.visit_with(work);
                }
                rustc_middle::mir::MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty,
                } => {
                    let _ = source_ty.visit_with(work);
                    let _ = target_ty.visit_with(work);
                }
            }
        }
    }
    work.error.take().map_or(Ok(()), Err)
}

pub(in crate::proof) fn borrowed<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<Option<std::rc::Rc<Body<'tcx>>>, String> {
    super::nested::pay(engine, 12 + instance.args.len())?;
    // This means no generic Instance arguments, not zero callable input arity.
    if !instance.args.is_empty() {
        return Ok(None);
    }
    if !matches!(instance.def, ty::InstanceKind::Item(id)
        if matches!(engine.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
    {
        return Err("nested choice borrowed source requires actual Item".into());
    }
    if !engine.tcx.is_mir_available(instance.def_id()) {
        return Err(engine.categorized_error(
            UnknownCategory::MissingCompilerEvidence,
            engine.missing_body_reason(instance.def_id()),
        ));
    }
    super::nested::pay(engine, 4)?;
    let Some(current) = engine.bodies.borrow().get(&instance).cloned() else {
        return Ok(None);
    };
    let raw = engine.tcx.instance_mir(instance.def);
    if raw.source.instance != instance.def
        || current.source.instance != instance.def
        || raw.source.promoted.is_some()
        || current.source.promoted.is_some()
    {
        return Err("nested choice borrowed original/current source identity differs".into());
    }
    let mut work = Work {
        engine,
        nodes: 0,
        depth: 0,
        error: None,
    };
    inventory(&mut work, raw, false)?;
    inventory(&mut work, &current, true)?;
    // Types are visited once on the current side. The ensuing complete paired MIR equality
    // admits only identical raw types/regions/constants; any normalization difference streams.
    // Complete borrowed inventories bounded every dynamic equality field before any comparison.
    let auxiliary = raw
        .required_consts
        .as_ref()
        .map_or(0, |items| items.len() * 3)
        + raw
            .mentioned_items
            .as_ref()
            .map_or(0, |items| items.len() * 5);
    if !work.pay(24 + auxiliary) {
        return Err(work.error.take().unwrap());
    }
    if raw.source != current.source
        || raw.phase != current.phase
        || raw.pass_count != current.pass_count
        || raw.arg_count != current.arg_count
        || raw.span != current.span
        || raw.is_polymorphic != current.is_polymorphic
        || raw.injection_phase != current.injection_phase
        || raw.required_consts != current.required_consts
        || raw.mentioned_items != current.mentioned_items
        || raw.local_decls.len() != current.local_decls.len()
        || raw.source_scopes.len() != current.source_scopes.len()
        || raw.var_debug_info.len() != current.var_debug_info.len()
        || raw.basic_blocks.len() != current.basic_blocks.len()
    {
        return Ok(None);
    }
    for (left, right) in raw.local_decls.iter().zip(&current.local_decls) {
        if !work.pay(4) {
            return Err(work.error.take().unwrap());
        }
        if left.ty != right.ty
            || left.mutability != right.mutability
            || left.source_info != right.source_info
        {
            return Ok(None);
        }
    }
    for (left, right) in raw.source_scopes.iter().zip(&current.source_scopes) {
        if !work.pay(6) {
            return Err(work.error.take().unwrap());
        }
        let local_same = match (&left.local_data, &right.local_data) {
            (
                rustc_middle::mir::ClearCrossCrate::Clear,
                rustc_middle::mir::ClearCrossCrate::Clear,
            ) => true,
            (
                rustc_middle::mir::ClearCrossCrate::Set(a),
                rustc_middle::mir::ClearCrossCrate::Set(b),
            ) => a.lint_root == b.lint_root,
            _ => false,
        };
        if left.span != right.span
            || left.parent_scope != right.parent_scope
            || left.inlined != right.inlined
            || left.inlined_parent_scope != right.inlined_parent_scope
            || !local_same
        {
            return Ok(None);
        }
    }
    for (left, right) in raw.var_debug_info.iter().zip(&current.var_debug_info) {
        if !work.pay(5) {
            return Err(work.error.take().unwrap());
        }
        let value_same = match (&left.value, &right.value) {
            (
                rustc_middle::mir::VarDebugInfoContents::Place(a),
                rustc_middle::mir::VarDebugInfoContents::Place(b),
            ) => a == b,
            (
                rustc_middle::mir::VarDebugInfoContents::Const(a),
                rustc_middle::mir::VarDebugInfoContents::Const(b),
            ) => a == b,
            _ => false,
        };
        if left.name != right.name
            || left.source_info != right.source_info
            || left.argument_index != right.argument_index
            || !value_same
        {
            return Ok(None);
        }
    }
    for (left, right) in raw.basic_blocks.iter().zip(current.basic_blocks.iter()) {
        let fields =
            array_iterator_constructors::terminator_fields_work(work.engine, left.terminator())?;
        if !work.pay(4 + fields) {
            return Err(work.error.take().unwrap());
        }
        if left.is_cleanup != right.is_cleanup
            || left.statements.len() != right.statements.len()
            || left.terminator().source_info != right.terminator().source_info
            || left.terminator().kind != right.terminator().kind
        {
            return Ok(None);
        }
        for (left, right) in left.statements.iter().zip(&right.statements) {
            let fields = array_iterator_constructors::statement_fields_work(work.engine, left)?;
            if !work.pay(2 + fields) {
                return Err(work.error.take().unwrap());
            }
            if left.source_info != right.source_info || left.kind != right.kind {
                return Ok(None);
            }
        }
    }
    Ok(Some(current))
}
