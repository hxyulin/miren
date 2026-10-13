//! Authenticated source observation only: there is no verified search constructor here.
use super::*;

#[path = "byte_search_source/population.rs"]
mod population;
#[path = "byte_search_source/word.rs"]
mod word;
use std::cell::Ref;
use std::collections::HashMap;
use std::rc::Rc;

// New source-operation record policy; the comparison graph's nine-body policy is unchanged.
const SOURCE_HELPERS: usize = 512;
const SOURCE_DEPTH: usize = 16;

#[derive(Clone, Debug)]
pub(in crate::proof) struct Failure {
    pub(in crate::proof) category: UnknownCategory,
    pub(in crate::proof) reason: String,
}

impl From<String> for Failure {
    fn from(reason: String) -> Self {
        Self {
            category: UnknownCategory::Semantics,
            reason,
        }
    }
}

impl From<&str> for Failure {
    fn from(reason: &str) -> Self {
        reason.to_owned().into()
    }
}

pub(in crate::proof) struct Work {
    used: usize,
    body: usize,
    failed: Option<Failure>,
}

impl Work {
    pub(in crate::proof) fn new(prior_work: usize) -> Result<Self, Failure> {
        let mut work = Self {
            used: prior_work,
            body: 0,
            failed: None,
        };
        work.charge(3)?;
        Ok(work)
    }

    pub(in crate::proof) fn charge(&mut self, amount: usize) -> Result<(), Failure> {
        if let Some(error) = &self.failed {
            return Err(error.clone());
        }
        self.used = self.used.saturating_add(amount);
        if self.used > NICHE_GRAPH_WORK {
            let error = Failure {
                category: UnknownCategory::ResourceLimit,
                reason: format!(
                    "byte source exceeds cumulative work: limit={NICHE_GRAPH_WORK} used={}",
                    self.used
                ),
            };
            self.failed = Some(error.clone());
            return Err(error);
        }
        Ok(())
    }

    pub(in crate::proof) fn used(&self) -> usize {
        self.used
    }

    fn node(&mut self, amount: usize) -> Result<(), Failure> {
        self.charge(amount)?;
        self.body = self.body.saturating_add(amount);
        if self.body > NICHE_BODY_WORK {
            let error = Failure {
                category: UnknownCategory::ResourceLimit,
                reason: format!(
                    "byte source exceeds inventory-pass work: limit={NICHE_BODY_WORK} used={}",
                    self.body
                ),
            };
            self.failed = Some(error.clone());
            return Err(error);
        }
        Ok(())
    }

    fn depth(&mut self, depth: usize) -> Result<(), Failure> {
        self.charge(1)?;
        if depth >= SOURCE_DEPTH {
            let error = Failure {
                category: UnknownCategory::ResourceLimit,
                reason: "byte source helper edge exceeds depth16".to_owned(),
            };
            self.failed = Some(error.clone());
            return Err(error);
        }
        Ok(())
    }
}

// Original inventory may contain authenticated core projections; normalized inventory may not.
#[derive(Clone, Copy)]
enum SourcePhase {
    Raw,
    Normalized,
}

struct Types<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    phase: SourcePhase,
    work: &'a mut Work,
    core: rustc_span::def_id::CrateNum,
    arguments: ty::GenericArgsRef<'tcx>,
    depth: usize,
    error: Option<Failure>,
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for Types<'_, 'tcx> {
    type Result = std::ops::ControlFlow<()>;

    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if let Err(error) = self.work.node(1) {
            self.error = Some(error);
            return std::ops::ControlFlow::Break(());
        }
        if self.depth >= SOURCE_DEPTH {
            let failure = Failure {
                category: UnknownCategory::ResourceLimit,
                reason: "byte source type exceeds depth16".into(),
            };
            self.work.failed = Some(failure.clone());
            self.error = Some(failure);
            return std::ops::ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Type(original) => self.visit_ty(original),
                    _ => {
                        self.error = Some("byte source Param is not an original type".into());
                        std::ops::ControlFlow::Break(())
                    }
                },
                None => {
                    self.error = Some("byte source Param lacks its full Instance argument".into());
                    std::ops::ControlFlow::Break(())
                }
            },
            ty::Adt(definition, _) if definition.did().krate != self.core => {
                self.error = Some("byte source contains a non-core original type".into());
                std::ops::ControlFlow::Break(())
            }
            ty::FnDef(id, _) if id.krate != self.core => {
                self.error = Some("byte source contains a non-core callable".into());
                std::ops::ControlFlow::Break(())
            }
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Tuple(_)
            | ty::Array(..)
            | ty::Slice(_)
            | ty::Ref(..)
            | ty::RawPtr(..)
            | ty::FnPtr(..)
            | ty::Bound(..)
            | ty::Adt(..)
            | ty::FnDef(..) => original.super_visit_with(self),
            ty::Alias(_, alias) if matches!(self.phase, SourcePhase::Raw) => {
                if let Err(error) = self.work.node(6 + alias.args.len()) {
                    self.error = Some(error);
                    return std::ops::ControlFlow::Break(());
                }
                let ty::AliasTyKind::Projection { def_id } = alias.kind else {
                    self.error =
                        Some("byte source raw alias is not a core associated projection".into());
                    return std::ops::ControlFlow::Break(());
                };
                if def_id.krate != self.core
                    || self.tcx.def_kind(def_id) != DefKind::AssocTy
                    || !self
                        .tcx
                        .trait_of_assoc(def_id)
                        .is_some_and(|parent| parent.krate == self.core)
                    || self.tcx.generics_of(def_id).count() != alias.args.len()
                {
                    self.error = Some(
                        "byte source raw projection identity/argument inventory differs".into(),
                    );
                    return std::ops::ControlFlow::Break(());
                }
                original.super_visit_with(self)
            }
            ty::Alias(..)
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
                self.error = Some("byte source has an unsupported original type".into());
                std::ops::ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }

    fn visit_region(&mut self, _: ty::Region<'tcx>) -> Self::Result {
        // A FnDef/FnPtr can carry many region arguments without additional type nodes. Count
        // every actual region visit independently; type-only counts cannot bound its erasure.
        match self.work.node(1) {
            Ok(()) => std::ops::ControlFlow::Continue(()),
            Err(error) => {
                self.error = Some(error);
                std::ops::ControlFlow::Break(())
            }
        }
    }

    fn visit_const(&mut self, original: ty::Const<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if let Err(error) = self.work.node(1) {
            self.error = Some(error);
            return std::ops::ControlFlow::Break(());
        }
        if self.depth >= SOURCE_DEPTH {
            let failure = Failure {
                category: UnknownCategory::ResourceLimit,
                reason: "byte source constant exceeds depth16".into(),
            };
            self.work.failed = Some(failure.clone());
            self.error = Some(failure);
            return std::ops::ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::ConstKind::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Const(original) => self.visit_const(original),
                    _ => {
                        self.error = Some("byte source Const Param is not a constant".into());
                        std::ops::ControlFlow::Break(())
                    }
                },
                None => {
                    self.error = Some("byte source Const Param lacks its Instance argument".into());
                    std::ops::ControlFlow::Break(())
                }
            },
            ty::ConstKind::Value(_) | ty::ConstKind::Bound(..) => original.super_visit_with(self),
            ty::ConstKind::Alias(..)
            | ty::ConstKind::Expr(_)
            | ty::ConstKind::Infer(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Error(_) => {
                self.error = Some("byte source constant requires separate normalization".into());
                std::ops::ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }
}

struct Inventory<'a, 'tcx> {
    types: Types<'a, 'tcx>,
    locals: usize,
}

impl Inventory<'_, '_> {
    fn pay(&mut self, amount: usize) -> bool {
        if self.types.error.is_some() {
            return false;
        }
        if let Err(error) = self.types.work.node(amount) {
            self.types.error = Some(error);
            return false;
        }
        true
    }
}

impl<'tcx> Visitor<'tcx> for Inventory<'_, 'tcx> {
    fn visit_local(
        &mut self,
        local: Local,
        _: rustc_middle::mir::visit::PlaceContext,
        _: Location,
    ) {
        if self.pay(1) && local.as_usize() >= self.locals {
            self.types.error = Some("byte source local is outside its original Body".into());
        }
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        location: Location,
    ) {
        use ty::TypeVisitable;
        if !self.pay(3) {
            return;
        }
        // This optimized-MIR hint is a Copy scalar UserTypeAnnotationIndex, not an owned user
        // annotation payload. Preserve it in full operand equality; never interpret it as type
        // or runtime authority. Nonempty Body annotation vectors remain separately refused.
        if constant.user_ty.is_some() && !self.pay(1) {
            return;
        }
        if let rustc_middle::mir::Const::Unevaluated(value, _) = constant.const_ {
            if !self.pay(value.args.len()) {
                return;
            }
            let _ = value.args.visit_with(&mut self.types);
        }
        if self.types.error.is_none() {
            self.super_const_operand(constant, location);
        }
    }

    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        use ty::TypeVisitable;
        if self.types.error.is_none() {
            let _ = original.visit_with(&mut self.types);
        }
    }

    fn visit_args(&mut self, args: &ty::GenericArgsRef<'tcx>, _: Location) {
        use ty::TypeVisitable;
        if self.pay(args.len()) {
            let _ = args.visit_with(&mut self.types);
        }
    }

    fn visit_ty_const(&mut self, value: ty::Const<'tcx>, _: Location) {
        use ty::TypeVisitable;
        if self.types.error.is_none() {
            let _ = value.visit_with(&mut self.types);
        }
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: Location,
    ) {
        if !self.pay(1 + place.projection.len()) {
            return;
        }
        if place.local.as_usize() >= self.locals || place.projection.iter().any(|part| {
            matches!(part, ProjectionElem::Index(index) if index.as_usize() >= self.locals)
        }) {
            self.types.error = Some("byte source place local is outside its original Body".into());
            return;
        }
        self.super_place(place, context, location);
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        if self.pay(1) {
            self.super_operand(operand, location);
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: Location) {
        let extra = match value {
            Rvalue::Aggregate(_, operands) => operands.len(),
            _ => 0,
        };
        if self.pay(1 + extra) {
            self.super_rvalue(value, location);
        }
    }

    fn visit_statement(
        &mut self,
        statement: &rustc_middle::mir::Statement<'tcx>,
        location: Location,
    ) {
        if !self.pay(2 + statement.debuginfos.len()) {
            return;
        }
        if !statement.debuginfos.is_empty() {
            self.types.error = Some("byte source statement debug payload is unsupported".into());
            return;
        }
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        let extra = match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args.len(),
            TerminatorKind::SwitchInt { targets, .. } => 2 * targets.all_targets().len(),
            _ => 0,
        };
        if self.pay(2 + extra) {
            self.super_terminator(terminator, location);
        }
    }
}

fn inventory<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    phase: SourcePhase,
    work: &mut Work,
) -> Result<usize, Failure> {
    use ty::TypeVisitable;
    work.body = 0;
    work.node(24)?;
    if body.local_decls.is_empty()
        || body.arg_count >= body.local_decls.len()
        || body.basic_blocks.len() > 128
        || body.local_decls.len() > 512
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.tainted_by_errors.is_some()
        || body.injection_phase.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
        || !body.user_type_annotations.is_empty()
    {
        return Err("byte source Body metadata is unsupported".into());
    }
    work.node(
        body.local_decls.len() * 5
            + body.source_scopes.len() * 5
            + body.var_debug_info.len() * 5
            + body.required_consts.as_ref().map_or(0, Vec::len)
            + body.mentioned_items.as_ref().map_or(0, Vec::len),
    )?;
    for local in &body.local_decls {
        if local.user_ty.is_some()
            || matches!(local.local_info, rustc_middle::mir::ClearCrossCrate::Set(_))
        {
            return Err("byte source local auxiliary metadata is unsupported".into());
        }
    }
    for variable in &body.var_debug_info {
        if variable.composite.is_some() {
            return Err("byte source composite debug payload is unsupported".into());
        }
    }
    let mut operations = 0usize;
    for block in body.basic_blocks.iter() {
        work.node(3)?;
        operations = operations.saturating_add(block.statements.len() + 1);
        if operations > 512 || !block.after_last_stmt_debuginfos.is_empty() {
            return Err("byte source CFG/auxiliary operation domain is unsupported".into());
        }
        let terminator = block
            .terminator
            .as_ref()
            .ok_or("byte source terminator is unavailable")?;
        work.node(1)?;
        if !terminator.attributes.is_empty() {
            return Err("byte source terminator attributes require separate clone planning".into());
        }
        // Reject opaque owned payload BEFORE any raw Body clone/normalization is performed.
        let edges = match &terminator.kind {
            TerminatorKind::Goto { .. } => 1,
            TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().len(),
            TerminatorKind::Call { target, unwind, .. } => {
                usize::from(target.is_some())
                    + usize::from(matches!(
                        unwind,
                        rustc_middle::mir::UnwindAction::Cleanup(_)
                    ))
            }
            TerminatorKind::Assert { unwind, .. } => {
                1 + usize::from(matches!(
                    unwind,
                    rustc_middle::mir::UnwindAction::Cleanup(_)
                ))
            }
            TerminatorKind::TailCall { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_) => 0,
            TerminatorKind::Drop { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {
                return Err(
                    "byte source opaque terminator requires separate clone planning".into(),
                );
            }
        };
        // Target read and bounds comparison are prepaid for EVERY possible yielded edge.
        work.node(2 * edges)?;
        for target in terminator.successors() {
            if target.as_usize() >= body.basic_blocks.len() {
                return Err("byte source CFG target is outside its original Body".into());
            }
        }
        for statement in &block.statements {
            work.node(2)?;
            match &statement.kind {
                StatementKind::Assign(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::Intrinsic(_) => {}
                StatementKind::FakeRead(_)
                | StatementKind::SetDiscriminant { .. }
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::BackwardIncompatibleDropHint { .. } => {
                    return Err(
                        "byte source opaque statement requires separate clone planning".into(),
                    );
                }
            }
        }
    }
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("byte source core unavailable")?
        .krate;
    work.node(2)?; // Actual Context and raw-projection phase fields.
    let mut visitor = Inventory {
        types: Types {
            tcx: engine.tcx,
            phase,
            work,
            core,
            arguments: instance.args,
            depth: 0,
            error: None,
        },
        locals: body.local_decls.len(),
    };
    let _ = instance.args.visit_with(&mut visitor.types);
    visitor.visit_body(body);
    if let Some(items) = &body.mentioned_items {
        for item in items {
            if !visitor.pay(2) {
                break;
            }
            match item.node {
                rustc_middle::mir::MentionedItem::Fn(original)
                | rustc_middle::mir::MentionedItem::Drop(original)
                | rustc_middle::mir::MentionedItem::Closure(original) => {
                    let _ = original.visit_with(&mut visitor.types);
                }
                rustc_middle::mir::MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty,
                } => {
                    let _ = source_ty.visit_with(&mut visitor.types);
                    if visitor.types.error.is_none() {
                        let _ = target_ty.visit_with(&mut visitor.types);
                    }
                }
            }
        }
    }
    if let Some(error) = visitor.types.error {
        return Err(error);
    }
    Ok(visitor.types.work.body)
}

fn same_debug_value<'tcx>(a: &VarDebugInfoContents<'tcx>, b: &VarDebugInfoContents<'tcx>) -> bool {
    match (a, b) {
        (VarDebugInfoContents::Place(a), VarDebugInfoContents::Place(b)) => a == b,
        (VarDebugInfoContents::Const(a), VarDebugInfoContents::Const(b)) => a == b,
        _ => false,
    }
}

fn mirror<'tcx>(
    actual: &Body<'tcx>,
    expected: &Body<'tcx>,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(24)?;
    if actual.phase != expected.phase
        || actual.pass_count != expected.pass_count
        || actual.source != expected.source
        || actual.arg_count != expected.arg_count
        || actual.span != expected.span
        || actual.is_polymorphic != expected.is_polymorphic
        || actual.required_consts != expected.required_consts
        || actual.mentioned_items != expected.mentioned_items
        || actual.local_decls.len() != expected.local_decls.len()
        || actual.source_scopes.len() != expected.source_scopes.len()
        || actual.var_debug_info.len() != expected.var_debug_info.len()
        || actual.basic_blocks.len() != expected.basic_blocks.len()
    {
        return Err("byte source current Body differs from original compiler metadata".into());
    }
    for (a, b) in actual.local_decls.iter().zip(&expected.local_decls) {
        work.charge(5)?;
        if a.ty != b.ty || a.mutability != b.mutability || a.source_info != b.source_info {
            return Err("byte source current local differs from original compiler local".into());
        }
    }
    for (a, b) in actual.source_scopes.iter().zip(&expected.source_scopes) {
        work.charge(5)?;
        let local_same = match (&a.local_data, &b.local_data) {
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
        if a.span != b.span
            || a.parent_scope != b.parent_scope
            || a.inlined != b.inlined
            || a.inlined_parent_scope != b.inlined_parent_scope
            || !local_same
        {
            return Err("byte source current scope differs from original compiler scope".into());
        }
    }
    for (a, b) in actual.var_debug_info.iter().zip(&expected.var_debug_info) {
        work.charge(5)?;
        if a.name != b.name
            || a.source_info != b.source_info
            || !same_debug_value(&a.value, &b.value)
            || a.argument_index != b.argument_index
        {
            return Err(
                "byte source current debug carrier differs from original compiler carrier".into(),
            );
        }
    }
    for (a, b) in actual.basic_blocks.iter().zip(expected.basic_blocks.iter()) {
        work.charge(3)?;
        if a.is_cleanup != b.is_cleanup
            || a.statements.len() != b.statements.len()
            || a.terminator().source_info != b.terminator().source_info
            || a.terminator().kind != b.terminator().kind
        {
            return Err("byte source current CFG differs from original compiler CFG".into());
        }
        for (a, b) in a.statements.iter().zip(&b.statements) {
            work.charge(2)?;
            if a.source_info != b.source_info || a.kind != b.kind {
                return Err(
                    "byte source current statement differs from original compiler statement".into(),
                );
            }
        }
    }
    Ok(())
}

fn checked_signature<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    work: &mut Work,
) -> Result<ty::PolyFnSig<'tcx>, Failure> {
    use ty::TypeVisitable;
    work.charge(5 + instance.args.len())?;
    if !matches!(
        engine.tcx.def_kind(instance.def_id()),
        DefKind::Fn | DefKind::AssocFn
    ) || instance.args.len() != engine.tcx.generics_of(instance.def_id()).count()
    {
        return Err("byte source helper full signature identity differs".into());
    }
    let raw = engine
        .tcx
        .fn_sig(instance.def_id())
        .instantiate_identity()
        .skip_norm_wip();
    work.body = 0;
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("byte source core unavailable")?
        .krate;
    work.node(5 + raw.bound_vars().len() + raw.skip_binder().inputs().len())?;
    let before = work.used;
    work.node(2)?; // Actual Context and raw-projection phase fields.
    let mut types = Types {
        tcx: engine.tcx,
        phase: SourcePhase::Raw,
        work,
        core,
        arguments: instance.args,
        depth: 0,
        error: None,
    };
    let _ = raw.visit_with(&mut types);
    if types.error.is_none() {
        let _ = instance.args.visit_with(&mut types);
    }
    if let Some(error) = types.error {
        return Err(error);
    }
    let cost = types.work.used - before + 5;
    types.work.charge(3 * cost)?;
    let expected = engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            engine
                .tcx
                .fn_sig(instance.def_id())
                .instantiate(engine.tcx, instance.args),
        )
        .map_err(|_| "byte source helper signature normalization failed")?;
    // Raw projection inventory grants no normalized-type permission. Independently require the
    // compiler's actual normalized signature to fit the existing closed source domain.
    types.work.body = 0;
    types
        .work
        .node(5 + expected.bound_vars().len() + expected.skip_binder().inputs().len())?;
    types.work.node(1)?;
    types.phase = SourcePhase::Normalized;
    let _ = expected.visit_with(&mut types);
    if let Some(error) = types.error {
        return Err(error);
    }
    types.work.charge(3 + instance.args.len())?;
    let prior = engine
        .call_signatures
        .try_borrow()
        .map_err(|_| "byte source signature registry is borrowed")?
        .get(&instance)
        .copied();
    if let Some(prior) = prior {
        if prior != expected {
            return Err(
                "byte source current signature differs from original compiler signature".into(),
            );
        }
    } else {
        let mut signatures = engine
            .call_signatures
            .try_borrow_mut()
            .map_err(|_| "byte source signature registry cannot publish")?;
        if signatures.len() >= 256 {
            return Err("byte source signature cache reached existing256 limit".into());
        }
        types.work.charge(3 + 3 * signatures.len())?;
        signatures
            .try_reserve(1)
            .map_err(|_| "byte source signature allocation failed")?;
        signatures.insert(instance, expected);
    }
    Ok(expected)
}

#[derive(Clone, Copy)]
enum HelperKind {
    RustBody(bool),
    PopulationCount,
}

struct Helper<'tcx> {
    selected: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    kind: HelperKind,
}

#[cfg(test)]
impl Helper<'_> {
    fn body_available(&self) -> bool {
        match self.kind {
            HelperKind::RustBody(available) => available,
            HelperKind::PopulationCount => false,
        }
    }
}

// Holding both actual registry guards freezes source authority only. No Memory/raw rights exist.
pub(super) struct SourceObservation<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    depth: usize,
    bodies: Ref<'a, HashMap<ty::Instance<'tcx>, Rc<Body<'tcx>>>>,
    signatures: Ref<'a, HashMap<ty::Instance<'tcx>, ty::PolyFnSig<'tcx>>>,
    helpers: Vec<Helper<'tcx>>,
    work: Work,
}

impl SourceObservation<'_, '_> {
    pub(super) fn reject_unverified_search(self) -> Result<(), String> {
        population::reject(self)
    }

    fn reject_without_word(self) -> Result<(), String> {
        // All validation and this consumption traversal were prepaid while constructing the
        // observation. Read guards remain live; this result can only refuse unproved semantics.
        let _used = self.work.used;
        if !self.bodies.contains_key(&self.instance)
            || !self.signatures.contains_key(&self.instance)
        {
            return Err("byte source observation lost its current source registries".into());
        }
        for helper in &self.helpers {
            if self.signatures.get(&helper.selected) != Some(&helper.signature) {
                return Err("byte source helper signature changed during observation".into());
            }
            if matches!(helper.kind, HelperKind::RustBody(false)) {
                return Err(self.engine.missing_body_reason(helper.selected.def_id()));
            }
        }
        Err(self.engine.categorized_error(
            UnknownCategory::Semantics,
            "niche byte-sized transport needs a separate available-body certificate".into(),
        ))
    }
}

fn erasure_types<'a, 'tcx>(
    engine: &Engine<'tcx>,
    work: &'a mut Work,
) -> Result<Types<'a, 'tcx>, Failure> {
    // Original core queries, seven actual visitor fields and dispatch/counter/error accesses.
    work.node(12)?;
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("byte source core unavailable")?
        .krate;
    Ok(Types {
        tcx: engine.tcx,
        phase: SourcePhase::Normalized,
        work,
        core,
        arguments: ty::GenericArgs::empty(),
        depth: 0,
        error: None,
    })
}

fn erase_type<'tcx>(
    engine: &Engine<'tcx>,
    original: Ty<'tcx>,
    work: &mut Work,
) -> Result<Ty<'tcx>, Failure> {
    use ty::TypeVisitable;
    let mut types = erasure_types(engine, work)?;
    let before = types.work.used;
    let _ = original.visit_with(&mut types);
    if let Some(error) = types.error {
        return Err(error);
    }
    let visited = types.work.used - before;
    // Actual Context/typeflag reads and erase operation. Each type/const node additionally covers
    // every region argument, so normalization is bounded by twice all actual graph visits.
    types.work.charge(3 + 2 * visited)?;
    Ok(engine.tcx.erase_and_anonymize_regions(original))
}

fn bind_signature<'tcx>(
    engine: &Engine<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    work: &mut Work,
) -> Result<ty::FnSig<'tcx>, Failure> {
    use ty::TypeVisitable;
    work.node(2)?;
    let bound_variables = signature.bound_vars().len();
    let inputs = signature.skip_binder().inputs().len();
    work.node(bound_variables + inputs)?;
    let mut types = erasure_types(engine, work)?;
    let before = types.work.used;
    let _ = signature.visit_with(&mut types);
    if let Some(error) = types.error {
        return Err(error);
    }
    let visited = types.work.used - before;
    types
        .work
        .charge(3 + 2 * visited + signature.bound_vars().len())?;
    Ok(engine.tcx.instantiate_bound_regions_with_erased(signature))
}

fn operand_type<'tcx>(
    engine: &Engine<'tcx>,
    current: &Body<'tcx>,
    operand: &Operand<'tcx>,
    work: &mut Work,
) -> Result<Ty<'tcx>, Failure> {
    work.node(2)?;
    let projections = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.projection.len(),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => 0,
    };
    // Actual operand discriminant/type access and every original Place projection step.
    work.node(3 * projections)?;
    Ok(operand.ty(&current.local_decls, engine.tcx))
}

fn destination_type<'tcx>(
    engine: &Engine<'tcx>,
    current: &Body<'tcx>,
    place: Place<'tcx>,
    work: &mut Work,
) -> Result<Ty<'tcx>, Failure> {
    work.node(2)?;
    work.node(3 * place.projection.len())?;
    Ok(place.ty(&current.local_decls, engine.tcx).ty)
}

fn check_occurrence<'tcx>(
    engine: &Engine<'tcx>,
    current: &Body<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: Option<Place<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    work: &mut Work,
) -> Result<(), Failure> {
    // Original fixed occurrence services remain. Whole-Body allowances are replaced only for
    // actual type erasures; no Body/source/clone/mirror or edge/depth validation is removed.
    work.charge(2 + args.len())?;
    let erased = bind_signature(engine, signature, work)?;
    if args.len() != erased.inputs().len() {
        return Err(
            "byte source helper Call argument types differ from its original signature".into(),
        );
    }
    for (argument, formal) in args.iter().zip(erased.inputs()) {
        let actual = operand_type(engine, current, &argument.node, work)?;
        let actual = erase_type(engine, actual, work)?;
        let formal = erase_type(engine, *formal, work)?;
        work.charge(1)?;
        if actual != formal {
            return Err(
                "byte source helper Call argument types differ from its original signature".into(),
            );
        }
    }
    if let Some(destination) = destination {
        work.charge(2)?;
        let actual = destination_type(engine, current, destination, work)?;
        let actual = erase_type(engine, actual, work)?;
        let original = erase_type(engine, erased.output(), work)?;
        work.charge(1)?;
        if actual != original {
            return Err(
                "byte source helper Call return type differs from its original signature".into(),
            );
        }
    }
    Ok(())
}

fn observe_inner<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    work_depth: usize,
    prior_work: usize,
) -> Result<SourceObservation<'a, 'tcx>, Failure> {
    let mut work = Work::new(prior_work)?;
    work.depth(work_depth)?;
    work.charge(6 + instance.args.len())?;
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(
            engine.tcx.def_kind(instance.def_id()),
            DefKind::Fn | DefKind::AssocFn
        )
        || engine.tcx.intrinsic(instance.def_id()).is_some()
    {
        return Err("byte source requires an ordinary original function Instance".into());
    }
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("byte source core unavailable")?
        .krate;
    if instance.def_id().krate != core
        || instance.args.len() != engine.tcx.generics_of(instance.def_id()).count()
    {
        return Err("byte source original core/full Instance identity differs".into());
    }
    if !engine.tcx.is_mir_available(instance.def_id()) {
        return Err(Failure {
            category: UnknownCategory::MissingCompilerEvidence,
            reason: engine.missing_body_reason(instance.def_id()),
        });
    }
    let raw = engine.tcx.instance_mir(instance.def);
    if raw.source.instance != instance.def
        || raw.source.promoted.is_some()
        || raw.phase
            != rustc_middle::mir::MirPhase::Runtime(rustc_middle::mir::RuntimePhase::Optimized)
    {
        return Err("byte source original Body identity/phase differs".into());
    }
    let raw_work = inventory(engine, instance, raw, SourcePhase::Raw, &mut work)?;
    // Raw owned clone, instantiate/normalize, container construction.
    work.charge(3 * raw_work + 4)?;
    let expected = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            engine.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(engine.tcx, raw.clone()),
        )
        .map_err(|_| "byte source original MIR normalization failed")?;
    let expected_clone_work = inventory(
        engine,
        instance,
        &expected,
        SourcePhase::Normalized,
        &mut work,
    )?;
    let signature = checked_signature(engine, instance, &mut work)?;
    let has_body = engine
        .bodies
        .try_borrow()
        .map_err(|_| "byte source Body registry is borrowed")?
        .contains_key(&instance);
    if !has_body
        && engine
            .bodies
            .try_borrow()
            .map_err(|_| "byte source Body registry is borrowed")?
            .len()
            >= 128
    {
        return Err("byte source miss would clear unrelated Engine bodies".into());
    }
    let current = if has_body {
        work.charge(3)?;
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "byte source Body registry is borrowed")?;
        bodies
            .get(&instance)
            .ok_or("byte source current Body disappeared")?
            .clone()
    } else {
        work.charge(expected_clone_work + 8)?;
        let mut bodies = engine
            .bodies
            .try_borrow_mut()
            .map_err(|_| "byte source Body registry cannot publish")?;
        // Reserve/possible rehash is actual new work, prepaid before allocation.
        work.charge(2 + 3 * bodies.len())?;
        bodies
            .try_reserve(1)
            .map_err(|_| "byte source Body allocation failed")?;
        let current = Rc::new(expected.clone());
        bodies.insert(instance, current.clone());
        current
    };
    let current_work = inventory(
        engine,
        instance,
        &current,
        SourcePhase::Normalized,
        &mut work,
    )?;
    let expected_work = inventory(
        engine,
        instance,
        &expected,
        SourcePhase::Normalized,
        &mut work,
    )?;
    work.charge(2 * (current_work + expected_work))?;
    mirror(&current, &expected, &mut work)?;
    work.charge(3 + 2 * current_work)?;
    let erased = engine.tcx.instantiate_bound_regions_with_erased(signature);
    if current.arg_count != erased.inputs().len()
        || current.return_ty() != erased.output()
        || current
            .args_iter()
            .zip(erased.inputs())
            .any(|(local, original)| current.local_decls[local].ty != *original)
    {
        return Err("byte source actual Body locals disagree with its full signature".into());
    }
    let mut helpers: Vec<Helper<'tcx>> = Vec::new();
    for block in current.basic_blocks.iter() {
        work.charge(1)?;
        let (func, args, destination) = match &block.terminator().kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => (func, args, Some(destination)),
            TerminatorKind::TailCall { func, args, .. } => (func, args, None),
            TerminatorKind::Drop { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => {
                return Err("byte source implicit/opaque helper edge is unsupported".into());
            }
            _ => continue,
        };
        // Every edge is charged/depth checked BEFORE looking for a previously selected Instance.
        work.depth(work_depth + 1)?;
        work.charge(2)?;
        let ty::FnDef(id, arguments) = func.ty(&current.local_decls, engine.tcx).kind() else {
            return Err("byte source helper call has no exact original function item".into());
        };
        work.charge(4 + arguments.skip_binder().len())?;
        let selected = engine.resolve_function_item(*id, arguments.skip_binder())?;
        work.charge(2)?; // Added primitive classification and ordinary-route branch.
        let primitive = matches!(selected.def, ty::InstanceKind::Intrinsic(_));
        if !primitive {
            if selected.def_id().krate != core
                || !matches!(selected.def, ty::InstanceKind::Item(_))
                || !matches!(
                    engine.tcx.def_kind(selected.def_id()),
                    DefKind::Fn | DefKind::AssocFn
                )
                || engine.tcx.intrinsic(selected.def_id()).is_some()
            {
                return Err(
                    "byte source helper needs a separate intrinsic/foreign/callable rule".into(),
                );
            }
        } else {
            work.charge(16 + selected.args.len())?;
            if selected.def_id().krate != core
                || selected.args.len() != 1
                || !selected
                    .args
                    .first()
                    .is_some_and(|argument| match argument.kind() {
                        ty::GenericArgKind::Type(original) => original == engine.tcx.types.usize,
                        ty::GenericArgKind::Lifetime(_) | ty::GenericArgKind::Const(_) => false,
                    })
                || !engine
                    .tcx
                    .is_intrinsic(selected.def_id(), rustc_span::Symbol::intern("ctpop"))
            {
                return Err(
                    "byte source primitive is not exact original target-usize ctpop".into(),
                );
            }
        }
        work.charge(helpers.len())?;
        let mut duplicate = false;
        for helper in &helpers {
            work.charge(2 + selected.args.len().max(helper.selected.args.len()))?;
            if helper.selected == selected {
                duplicate = true;
                break;
            }
        }
        let signature = checked_signature(engine, selected, &mut work)?;
        if primitive {
            work.charge(18)?;
            let concrete = signature.skip_binder();
            if engine.population_count_type(selected.def_id(), concrete)
                != Some((u32::from(engine.tcx.sess.target.pointer_width), false))
                || concrete.inputs() != [engine.tcx.types.usize]
                || concrete.output() != engine.tcx.types.u32
                || concrete.safety() != rustc_hir::Safety::Safe
                || concrete.abi() != rustc_abi::ExternAbi::Rust
                || concrete.c_variadic()
            {
                return Err("byte source population primitive signature differs".into());
            }
        }
        check_occurrence(
            engine,
            &current,
            args,
            destination.copied(),
            signature,
            &mut work,
        )?;
        if duplicate {
            continue;
        }
        if helpers.len() >= SOURCE_HELPERS {
            return Err("byte source distinct helper records exceed new512 policy".into());
        }
        work.charge(5 + 5 * helpers.len() + selected.args.len())?;
        work.charge(1)?; // Actual Body/primitive record construction dispatch.
        helpers
            .try_reserve_exact(1)
            .map_err(|_| "byte source helper allocation failed")?;
        helpers.push(Helper {
            selected,
            signature,
            kind: if primitive {
                HelperKind::PopulationCount
            } else {
                HelperKind::RustBody(engine.tcx.is_mir_available(selected.def_id()))
            },
        });
    }
    work.charge(6 + helpers.len())?;
    work.charge(helpers.len())?; // Additional Body/primitive consumption dispatch.
    work.charge(1)?; // Preserve the actual issuing edge depth in operation-local evidence.
    for helper in &helpers {
        work.charge(3 + helper.selected.args.len())?;
    }
    let bodies = engine
        .bodies
        .try_borrow()
        .map_err(|_| "byte source Body registry is borrowed")?;
    let signatures = engine
        .call_signatures
        .try_borrow()
        .map_err(|_| "byte source signature registry is borrowed")?;
    if !bodies
        .get(&instance)
        .is_some_and(|body| Rc::ptr_eq(body, &current))
    {
        return Err("byte source current Body identity changed during observation".into());
    }
    Ok(SourceObservation {
        engine,
        instance,
        depth: work_depth,
        bodies,
        signatures,
        helpers,
        work,
    })
}

pub(super) fn observe<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    work_depth: usize,
    prior_work: usize,
) -> Result<SourceObservation<'a, 'tcx>, String> {
    observe_inner(engine, instance, work_depth, prior_work)
        .map_err(|failure| engine.categorized_error(failure.category, failure.reason))
}

// Standalone actual shared gate control, not a whole SourceObservation or search proof.
#[cfg(test)]
pub(super) fn duplicate_occurrence_control<'tcx>(engine: &Engine<'tcx>, body: &Body<'tcx>) {
    let mut work = Work::new(0).unwrap();
    work.charge(3 + 4 * body.basic_blocks.len()).unwrap();
    let calls = body
        .basic_blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &block.terminator().kind
            else {
                return None;
            };
            let ty::FnDef(id, arguments) = func.ty(&body.local_decls, engine.tcx).kind() else {
                return None;
            };
            Some((
                engine
                    .resolve_function_item(*id, arguments.skip_binder())
                    .unwrap(),
                args.as_ref(),
                *destination,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].0, calls[1].0);
    let signature = checked_signature(engine, calls[0].0, &mut work).unwrap();
    // The private control's original fixture is bounded. These calls exercise the production gate,
    // not a raw-source permit or a successful application outcome.
    check_occurrence(
        engine,
        body,
        calls[0].1,
        Some(calls[0].2),
        signature,
        &mut work,
    )
    .unwrap();
    check_occurrence(
        engine,
        body,
        calls[1].1,
        Some(calls[1].2),
        signature,
        &mut work,
    )
    .unwrap();
    let wrong = Place::from(Local::from_usize(3));
    assert_eq!(body.local_decls[wrong.local].ty, engine.tcx.types.bool);
    work.charge(1 + 3 * calls[1].1.len()).unwrap();
    let mut args = calls[1].1.to_vec();
    args[0].node = Operand::Copy(wrong);
    assert_eq!(
        check_occurrence(engine, body, &args, Some(calls[1].2), signature, &mut work)
            .unwrap_err()
            .reason,
        "byte source helper Call argument types differ from its original signature"
    );
    assert_eq!(
        check_occurrence(engine, body, calls[1].1, Some(wrong), signature, &mut work)
            .unwrap_err()
            .reason,
        "byte source helper Call return type differs from its original signature"
    );
    check_occurrence(
        engine,
        body,
        calls[1].1,
        Some(calls[1].2),
        signature,
        &mut work,
    )
    .unwrap();
    eprintln!("SOURCE duplicate-actual-call-occurrences-both-validated");
    eprintln!("SOURCE duplicate-later-argument-gate-refused");
    eprintln!("SOURCE duplicate-later-destination-gate-refused");
}

// Standalone genuine compiler type-gate controls, not a complete search/body proof.
#[cfg(test)]
pub(super) fn raw_projection_control<'tcx>(engine: &Engine<'tcx>, instance: ty::Instance<'tcx>) {
    use ty::TypeVisitable;
    let mut work = Work::new(0).unwrap();
    let signature = checked_signature(engine, instance, &mut work).unwrap();
    let signature = engine.tcx.instantiate_bound_regions_with_erased(signature);
    let ty::Ref(_, output, rustc_hir::Mutability::Not) = signature.output().kind() else {
        panic!("actual index signature did not retain a shared result")
    };
    assert_eq!(output.kind(), &ty::Slice(engine.tcx.types.u8));
    eprintln!("SEARCH actual-core-projection-normalizes-to-shared-u8-slice");
    let core = engine.tcx.lang_items().sized_trait().unwrap().krate;
    let raw = engine
        .tcx
        .fn_sig(instance.def_id())
        .instantiate_identity()
        .skip_norm_wip();
    let mut work = Work::new(0).unwrap();
    work.node(2).unwrap();
    let mut types = Types {
        tcx: engine.tcx,
        phase: SourcePhase::Normalized,
        work: &mut work,
        core,
        arguments: instance.args,
        depth: 0,
        error: None,
    };
    let _ = raw.visit_with(&mut types);
    assert_eq!(
        types.error.unwrap().reason,
        "byte source has an unsupported original type"
    );
    eprintln!("SEARCH same-raw-projection-refused-in-normalized-phase");
    let foreign = engine
        .tcx
        .mir_keys(())
        .iter()
        .copied()
        .find(|id| {
            engine.tcx.def_kind(*id) == DefKind::Fn
                && engine.tcx.item_name(id.to_def_id()).as_str() == "foreign_projection"
        })
        .unwrap();
    let raw = engine
        .tcx
        .fn_sig(foreign)
        .instantiate_identity()
        .skip_norm_wip();
    let mut work = Work::new(0).unwrap();
    work.node(2).unwrap();
    let mut types = Types {
        tcx: engine.tcx,
        phase: SourcePhase::Raw,
        work: &mut work,
        core,
        arguments: instance.args,
        depth: 0,
        error: None,
    };
    let _ = raw.visit_with(&mut types);
    assert_eq!(
        types.error.unwrap().reason,
        "byte source raw projection identity/argument inventory differs"
    );
    eprintln!("SEARCH actual-foreign-associated-type-refused");
    let mut work = Work::new(0).unwrap();
    work.node(2).unwrap();
    let mut types = Types {
        tcx: engine.tcx,
        phase: SourcePhase::Raw,
        work: &mut work,
        core,
        arguments: instance.args,
        depth: SOURCE_DEPTH,
        error: None,
    };
    let _ = engine
        .tcx
        .fn_sig(instance.def_id())
        .instantiate_identity()
        .skip_norm_wip()
        .visit_with(&mut types);
    let failure = types.error.take().unwrap();
    assert_eq!(failure.category, UnknownCategory::ResourceLimit);
    assert_eq!(types.work.node(0).unwrap_err().reason, failure.reason);
    eprintln!("SEARCH actual-type-depth-exhaustion-sticky-resource");
}

// Standalone actual borrowed inventory/mirror controls, not raw construction or search proof.
#[cfg(test)]
pub(super) fn constant_hint_control<'tcx>(engine: &Engine<'tcx>, instance: ty::Instance<'tcx>) {
    let raw = engine.tcx.instance_mir(instance.def);
    assert!(raw.user_type_annotations.is_empty());
    let mut work = Work::new(0).unwrap();
    let raw_work = inventory(engine, instance, raw, SourcePhase::Raw, &mut work).unwrap();
    work.charge(2 + 3 * raw_work).unwrap();
    let mut wrong = raw.clone();
    let mut changed = false;
    for block in wrong.basic_blocks.as_mut() {
        if let TerminatorKind::Call {
            func: Operand::Constant(constant),
            ..
        } = &mut block.terminator_mut().kind
            && constant.user_ty.is_some()
        {
            constant.user_ty = None;
            changed = true;
            break;
        }
    }
    assert!(changed, "actual function-item user hint was not found");
    let wrong_work = inventory(engine, instance, &wrong, SourcePhase::Raw, &mut work).unwrap();
    work.charge(2 * (raw_work + wrong_work)).unwrap();
    assert_eq!(
        mirror(&wrong, raw, &mut work).unwrap_err().reason,
        "byte source current CFG differs from original compiler CFG"
    );
    eprintln!("SEARCH actual-scalar-user-hint-inventory-preserved");
    eprintln!("SEARCH actual-user-hint-erasure-mirror-refused");
}

// Actual source inventory controls; neither a pointer permission nor complete search proof.
#[cfg(test)]
pub(super) fn metadata_projection_control<'tcx>(engine: &Engine<'tcx>, slice: ty::Instance<'tcx>) {
    let mut source = observe_inner(engine, slice, 0, 0).unwrap();
    source.work.charge(2 + 8 * source.helpers.len()).unwrap();
    let pointer = source
        .helpers
        .iter()
        .find(|helper| {
            engine
                .tcx
                .def_path_str(helper.selected.def_id())
                .ends_with("::slice_from_raw_parts")
        })
        .expect("actual slice raw builder Call disappeared")
        .selected;
    let used = source.work.used;
    drop(source);
    let mut source = observe_inner(engine, pointer, 1, used).unwrap();
    source.work.charge(2 + 8 * source.helpers.len()).unwrap();
    let metadata = source
        .helpers
        .iter()
        .find(|helper| {
            engine
                .tcx
                .def_path_str(helper.selected.def_id())
                .ends_with("::from_raw_parts")
        })
        .expect("actual pointer metadata builder Call disappeared")
        .selected;
    let used = source.work.used;
    drop(source);
    let mut source = observe_inner(engine, metadata, 2, used).unwrap();
    source.work.charge(4).unwrap();
    let current = source.bodies.get(&metadata).unwrap().clone();
    let used = source.work.used;
    drop(source);
    let raw = engine.tcx.instance_mir(metadata.def);
    assert_eq!(raw.arg_count, 2);
    assert_eq!(raw.local_decls.len(), 3);
    let ty::Alias(_, alias) = raw.local_decls[Local::from_usize(2)].ty.kind() else {
        panic!("actual raw metadata projection disappeared")
    };
    let ty::AliasTyKind::Projection { def_id } = alias.kind else {
        panic!("actual raw metadata is not an associated projection")
    };
    assert_eq!(engine.tcx.item_name(def_id).as_str(), "Metadata");
    assert_eq!(
        current.local_decls[Local::from_usize(2)].ty,
        engine.tcx.types.usize
    );
    let mut work = Work::new(used).unwrap();
    let raw_work = inventory(engine, metadata, raw, SourcePhase::Raw, &mut work).unwrap();
    let error = inventory(engine, metadata, raw, SourcePhase::Normalized, &mut work).unwrap_err();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(error.reason, "byte source has an unsupported original type");
    let current_work = inventory(
        engine,
        metadata,
        &current,
        SourcePhase::Normalized,
        &mut work,
    )
    .unwrap();
    // Complete borrowed inventories precede the owned diagnostic clone and mirror traversal.
    work.charge(3 * current_work + 4).unwrap();
    let mut wrong = current.as_ref().clone();
    wrong.local_decls[Local::from_usize(2)].ty =
        if engine.tcx.data_layout.pointer_size().bits() == 64 {
            engine.tcx.types.u64
        } else {
            engine.tcx.types.u32
        };
    let wrong_work =
        inventory(engine, metadata, &wrong, SourcePhase::Normalized, &mut work).unwrap();
    work.charge(2 * (current_work + wrong_work)).unwrap();
    let error = mirror(&wrong, &current, &mut work).unwrap_err();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source current local differs from original compiler local"
    );
    engine.bodies.borrow_mut().insert(metadata, Rc::new(wrong));
    let error = observe_inner(engine, metadata, 2, work.used).err().unwrap();
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source current local differs from original compiler local"
    );
    engine.bodies.borrow_mut().insert(metadata, current);
    let restored = observe_inner(engine, metadata, 2, work.used).unwrap();
    eprintln!("SEARCH raw-original-metadata-projection-inventory-positive visits={raw_work}");
    eprintln!("SEARCH raw-metadata-alias-normalized-phase-refused");
    eprintln!("SEARCH normalized-metadata-target-sized-type-mutation-refused");
    eprintln!(
        "SEARCH metadata-original-current-source-restored used={}",
        restored.work.used
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cumulative_work_failure_is_sticky_across_inventory_passes() {
        let mut work = Work::new(0).unwrap();
        for _ in 0..10 {
            work.depth(0).unwrap();
            work.body = 0;
            work.node(NICHE_BODY_WORK).unwrap();
        }
        let remaining = NICHE_GRAPH_WORK - work.used;
        work.charge(remaining).unwrap();
        let failure = work.charge(1).unwrap_err();
        assert_eq!(failure.category, UnknownCategory::ResourceLimit);
        assert_eq!(work.charge(0).unwrap_err().reason, failure.reason);
        work.body = 0;
        assert_eq!(work.node(1).unwrap_err().reason, failure.reason);
    }

    #[test]
    fn inventory_and_every_edge_have_independent_bounds() {
        let mut work = Work::new(0).unwrap();
        work.node(NICHE_BODY_WORK).unwrap();
        assert_eq!(
            work.node(1).unwrap_err().category,
            UnknownCategory::ResourceLimit
        );
        let mut repeated = Work::new(0).unwrap();
        repeated.depth(SOURCE_DEPTH - 1).unwrap();
        assert_eq!(
            repeated.depth(SOURCE_DEPTH).unwrap_err().reason,
            "byte source helper edge exceeds depth16"
        );
    }
}
