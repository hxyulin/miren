//! Exact admission-local core niche comparison law and readonly membership application.
use super::*;

#[path = "nonzero_niche_comparisons/byte_route.rs"]
mod byte_route;
pub(in crate::proof) use byte_route::PreparedByteRoute;
#[path = "nonzero_niche_comparisons/byte_search_source.rs"]
mod byte_search_source;
#[cfg(test)]
#[path = "nonzero_niche_comparisons/byte_search_source_probe.rs"]
mod byte_search_source_probe;

use rustc_abi::VariantIdx;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Location, Terminator};

struct ExpandedTypes<'tcx> {
    core: rustc_span::def_id::CrateNum,
    limit: usize,
    arguments: ty::GenericArgsRef<'tcx>,
    work: usize,
    depth: usize,
    error: Option<&'static str>,
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for ExpandedTypes<'tcx> {
    type Result = std::ops::ControlFlow<()>;

    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if self.depth >= 16 || self.work >= self.limit {
            self.error = Some("research expansion bound exceeded");
            return std::ops::ControlFlow::Break(());
        }
        self.work = self.work.saturating_add(1);
        self.depth += 1;
        let result = match original.kind() {
            ty::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Type(original) => self.visit_ty(original),
                    _ => {
                        self.error = Some("raw Param mapping is not a type");
                        std::ops::ControlFlow::Break(())
                    }
                },
                None => {
                    self.error = Some("raw Param mapping unavailable");
                    std::ops::ControlFlow::Break(())
                }
            },
            ty::Alias(..) => {
                self.error = Some("unbounded raw alias normalization is refused");
                std::ops::ControlFlow::Break(())
            }
            ty::Adt(definition, _) if definition.did().krate != self.core => {
                self.error
                    .get_or_insert("niche raw type has non-core original identity");
                std::ops::ControlFlow::Break(())
            }
            ty::FnDef(id, _) | ty::Closure(id, _) if id.krate != self.core => {
                self.error
                    .get_or_insert("niche raw callable has non-core original identity");
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
            | ty::FnDef(..)
            | ty::Closure(..) => original.super_visit_with(self),
            ty::Foreign(_)
            | ty::Pat(..)
            | ty::UnsafeBinder(_)
            | ty::Dynamic(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => {
                self.error
                    .get_or_insert("niche raw type grammar is unsupported");
                std::ops::ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }

    fn visit_const(&mut self, original: ty::Const<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if self.depth >= 16 || self.work >= self.limit {
            self.error = Some("research constant expansion bound exceeded");
            return std::ops::ControlFlow::Break(());
        }
        self.work = self.work.saturating_add(1);
        self.depth += 1;
        let result = match original.kind() {
            ty::ConstKind::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Const(original) => self.visit_const(original),
                    _ => {
                        self.error = Some("raw Const Param mapping is not a constant");
                        std::ops::ControlFlow::Break(())
                    }
                },
                None => {
                    self.error = Some("raw Const Param mapping unavailable");
                    std::ops::ControlFlow::Break(())
                }
            },
            ty::ConstKind::Alias(..) | ty::ConstKind::Expr(_) => {
                self.error = Some("raw constant normalization is refused");
                std::ops::ControlFlow::Break(())
            }
            ty::ConstKind::Value(_) | ty::ConstKind::Bound(..) => original.super_visit_with(self),
            ty::ConstKind::Infer(_) | ty::ConstKind::Placeholder(_) | ty::ConstKind::Error(_) => {
                self.error
                    .get_or_insert("niche raw constant grammar is unsupported");
                std::ops::ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }
}

struct FullInventory<'tcx> {
    locals: usize,
    limit: usize,
    types: ExpandedTypes<'tcx>,
    work: usize,
}

impl FullInventory<'_> {
    fn bound(&mut self) -> bool {
        if self.work.saturating_add(self.types.work) > self.limit {
            self.types
                .error
                .get_or_insert("niche graph inventory exceeds cumulative 8192 work limit");
            return false;
        }
        self.types.limit = self.limit.saturating_sub(self.work);
        self.types.error.is_none()
    }
}

impl<'tcx> Visitor<'tcx> for FullInventory<'tcx> {
    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        use ty::TypeVisitable;
        if !self.bound() {
            return;
        }
        let _ = original.visit_with(&mut self.types);
    }

    fn visit_args(&mut self, args: &ty::GenericArgsRef<'tcx>, _: Location) {
        use ty::TypeVisitable;
        self.work = self.work.saturating_add(args.len());
        if !self.bound() {
            return;
        }
        let _ = args.visit_with(&mut self.types);
    }

    fn visit_ty_const(&mut self, constant: ty::Const<'tcx>, _: Location) {
        use ty::TypeVisitable;
        if !self.bound() {
            return;
        }
        let _ = constant.visit_with(&mut self.types);
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        location: Location,
    ) {
        if let rustc_middle::mir::Const::Unevaluated(value, _) = constant.const_ {
            use ty::TypeVisitable;
            self.work = self.work.saturating_add(value.args.len());
            if !self.bound() {
                return;
            }
            let _ = value.args.visit_with(&mut self.types);
        }
        if !self.bound() {
            return;
        }
        self.super_const_operand(constant, location);
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: Location,
    ) {
        self.work = self.work.saturating_add(1 + place.projection.len());
        if !self.bound() {
            return;
        }
        if place.local.as_usize() >= self.locals
            || place.projection.iter().any(|projection| {
                matches!(projection,
                ProjectionElem::Index(local) if local.as_usize() >= self.locals)
            })
        {
            self.types
                .error
                .get_or_insert("niche place local is out of bounds");
            return;
        }
        if !self.bound() {
            return;
        }
        self.super_place(place, context, location);
    }

    fn visit_local(
        &mut self,
        local: Local,
        _: rustc_middle::mir::visit::PlaceContext,
        _: Location,
    ) {
        if local.as_usize() >= self.locals {
            self.types
                .error
                .get_or_insert("niche MIR local is out of bounds");
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.work = self.work.saturating_add(1);
        if !self.bound() {
            return;
        }
        self.super_operand(operand, location);
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Aggregate(_, operands) = value {
            self.work = self.work.saturating_add(operands.len());
        }
        if !self.bound() {
            return;
        }
        self.super_rvalue(value, location);
    }

    fn visit_user_type_projection(&mut self, projection: &rustc_middle::mir::UserTypeProjection) {
        self.work = self.work.saturating_add(projection.projs.len());
        if !self.bound() {
            return;
        }
        if projection.projs.len() > 16 {
            self.types
                .error
                .get_or_insert("niche user projection exceeds depth16");
            return;
        }
        self.super_user_type_projection(projection);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                self.work = self.work.saturating_add(args.len());
            }
            TerminatorKind::SwitchInt { targets, .. } => {
                self.work = self
                    .work
                    .saturating_add(targets.all_targets().len().saturating_mul(2));
            }
            _ => {}
        }
        if !self.bound() {
            return;
        }
        self.super_terminator(terminator, location);
    }
}

#[cfg(test)]
fn full_inventory<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
) -> (usize, Option<&'static str>) {
    full_inventory_limit(tcx, instance, body, 16384)
}

fn full_inventory_limit<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    limit: usize,
) -> (usize, Option<&'static str>) {
    use ty::TypeVisitable;
    let Some(core) = tcx.lang_items().sized_trait().map(|id| id.krate) else {
        return (0, Some("niche core type authority unavailable"));
    };
    let mut inventory = FullInventory {
        locals: body.local_decls.len(),
        limit,
        types: ExpandedTypes {
            core,
            limit,
            arguments: instance.args,
            work: 0,
            depth: 0,
            error: None,
        },
        work: body.local_decls.len()
            + body.basic_blocks.len()
            + body.source_scopes.len()
            + body.var_debug_info.len()
            + instance.args.len(),
    };
    if !inventory.bound() {
        return (inventory.work, inventory.types.error);
    }
    let _ = instance.args.visit_with(&mut inventory.types);
    if matches!(
        tcx.def_kind(instance.def_id()),
        DefKind::Fn | DefKind::AssocFn
    ) {
        let signature = tcx
            .fn_sig(instance.def_id())
            .instantiate_identity()
            .skip_norm_wip();
        let _ = signature.visit_with(&mut inventory.types);
    }
    if body.coroutine.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
        || !body.user_type_annotations.is_empty()
        || body.local_decls.iter().any(|local| {
            local.user_ty.is_some()
                || matches!(local.local_info, rustc_middle::mir::ClearCrossCrate::Set(_))
        })
        || body
            .var_debug_info
            .iter()
            .any(|info| info.composite.is_some())
    {
        inventory
            .types
            .error
            .get_or_insert("niche raw auxiliary grammar requires separate treatment");
    }
    for block in body.basic_blocks.iter() {
        inventory.work = inventory
            .work
            .saturating_add(block.statements.len() + 1 + block.after_last_stmt_debuginfos.len());
        if !inventory.bound() {
            return (inventory.work + inventory.types.work, inventory.types.error);
        }
        for statement in &block.statements {
            inventory.work = inventory.work.saturating_add(statement.debuginfos.len());
            if !inventory.bound() {
                return (inventory.work + inventory.types.work, inventory.types.error);
            }
        }
        if !inventory.bound() {
            return (inventory.work + inventory.types.work, inventory.types.error);
        }
        for information in block.after_last_stmt_debuginfos.iter().chain(
            block
                .statements
                .iter()
                .flat_map(|statement| statement.debuginfos.iter()),
        ) {
            match information {
                rustc_middle::mir::StmtDebugInfo::AssignRef(local, place) => {
                    if local.as_usize() >= body.local_decls.len()
                        || place.local.as_usize() >= body.local_decls.len()
                    {
                        inventory
                            .types
                            .error
                            .get_or_insert("niche debug local is out of bounds");
                        break;
                    }
                    inventory.visit_place(
                        place,
                        rustc_middle::mir::visit::PlaceContext::NonMutatingUse(
                            rustc_middle::mir::visit::NonMutatingUseContext::Inspect,
                        ),
                        Location {
                            block: START_BLOCK,
                            statement_index: 0,
                        },
                    );
                }
                rustc_middle::mir::StmtDebugInfo::InvalidAssign(local) => {
                    if local.as_usize() >= body.local_decls.len() {
                        inventory
                            .types
                            .error
                            .get_or_insert("niche debug local is out of bounds");
                        break;
                    }
                }
            }
            if !inventory.bound() {
                break;
            }
        }
    }
    for scope in &body.source_scopes {
        if matches!(scope.local_data, rustc_middle::mir::ClearCrossCrate::Set(_)) {
            inventory
                .types
                .error
                .get_or_insert("niche source scope local metadata is unsupported");
        }
        if let Some((instance, _)) = scope.inlined {
            inventory.work = inventory.work.saturating_add(instance.args.len());
            if !inventory.bound() {
                return (inventory.work, inventory.types.error);
            }
            let _ = instance.args.visit_with(&mut inventory.types);
        }
    }
    if let Some(constants) = &body.required_consts {
        inventory.work = inventory.work.saturating_add(constants.len());
    }
    if let Some(items) = &body.mentioned_items {
        inventory.work = inventory.work.saturating_add(items.len());
        if !inventory.bound() {
            return (inventory.work + inventory.types.work, inventory.types.error);
        }
        for item in items {
            if !inventory.bound() {
                return (inventory.work + inventory.types.work, inventory.types.error);
            }
            match item.node {
                rustc_middle::mir::MentionedItem::Fn(original)
                | rustc_middle::mir::MentionedItem::Drop(original)
                | rustc_middle::mir::MentionedItem::Closure(original) => {
                    let _ = original.visit_with(&mut inventory.types);
                }
                rustc_middle::mir::MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty,
                } => {
                    let _ = source_ty.visit_with(&mut inventory.types);
                    let _ = target_ty.visit_with(&mut inventory.types);
                }
            }
        }
    }
    if !inventory.bound() {
        return (inventory.work + inventory.types.work, inventory.types.error);
    }
    inventory.visit_body(body);
    (inventory.work + inventory.types.work, inventory.types.error)
}

// Research observations preserve original types and side provenance. This is not an issued law.
#[derive(Clone, Copy, Debug)]
enum TraceValue<'tcx> {
    Origin {
        original: Ty<'tcx>,
        side: usize,
        refs: usize,
        variant: Option<VariantIdx>,
    },
    Tag(Ty<'tcx>, u128),
    Boolean(u8),
}

struct CompletedTrace<'tcx> {
    instance: ty::Instance<'tcx>,
    original: Ty<'tcx>,
    relation: u8,
    body: std::rc::Weak<Body<'tcx>>,
}

#[derive(Clone, Copy, Debug, Default)]
struct LawWork {
    semantic: usize,
    live_engine: usize,
    materialization: usize,
}

fn mark_niche_block(seen: &mut u128, blocks: usize, index: usize) -> Result<(), String> {
    if blocks == 0 || blocks > 128 || index >= blocks || index >= 128 {
        return Err("trace selected block index is outside fixed128 domain".into());
    }
    let bit = 1_u128
        .checked_shl(index as u32)
        .ok_or("trace checked block shift failed")?;
    if *seen & bit != 0 {
        return Err("trace cyclic selected path".into());
    }
    *seen |= bit;
    Ok(())
}

struct LawTrace<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    engine: Option<&'a Engine<'tcx>>,
    graph: Option<&'a mut GraphBudget<'tcx>>,
    original: Ty<'tcx>,
    payload: Ty<'tcx>,
    primitive: Ty<'tcx>,
    tags: Option<[usize; 2]>,
    equality: u8,
    completed: Vec<CompletedTrace<'tcx>>,
    bodies: &'a [(ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>)],
    work: usize,
    limit: usize,
    observed: LawWork,
    active: [Option<ty::Instance<'tcx>>; 16],
}

impl<'tcx> LawTrace<'_, 'tcx> {
    fn charge(&mut self, work: usize) -> Result<(), String> {
        self.observed.semantic = self
            .observed
            .semantic
            .checked_add(work)
            .ok_or("trace semantic observation overflow")?;
        self.charge_total(work)
    }

    fn charge_live_engine(&mut self, work: usize) -> Result<(), String> {
        self.observed.live_engine = self
            .observed
            .live_engine
            .checked_add(work)
            .ok_or("trace provenance observation overflow")?;
        let graph = self
            .graph
            .as_deref_mut()
            .ok_or("trace live Engine requires the same admission graph")?;
        graph.phase(GraphPhase::LawLiveEngine, work)
    }

    fn failure(&self, error: String) -> String {
        match self.graph.as_deref() {
            Some(graph) => format!(
                "{error}; law={} observed={:?}; graph={} phases={:?}",
                self.work, self.observed, graph.work, graph.phases,
            ),
            None => format!(
                "{error}; law={} observed={:?}; graph unavailable",
                self.work, self.observed
            ),
        }
    }

    fn charge_materialization(&mut self, work: usize) -> Result<(), String> {
        self.observed.materialization = self
            .observed
            .materialization
            .checked_add(work)
            .ok_or("trace materialization observation overflow")?;
        self.charge_total(work)
    }

    fn charge_total(&mut self, work: usize) -> Result<(), String> {
        self.work = self.work.checked_add(work).ok_or("trace work overflow")?;
        if self.work > self.limit {
            return Err(format!(
                "trace cumulative work limit exceeded: limit={} attempted={} \
                observed={:?}",
                self.limit, self.work, self.observed
            ));
        }
        Ok(())
    }

    fn typed(&mut self, original: Ty<'tcx>, value: TraceValue<'tcx>) -> Result<(), String> {
        self.charge(1)?;
        let mut expected = original;
        let actual = match value {
            TraceValue::Origin { original, refs, .. } => {
                if refs > 16 {
                    return Err("niche receiver depth exceeds16".into());
                }
                for _ in 0..refs {
                    self.charge(1)?;
                    let ty::Ref(_, child, rustc_hir::Mutability::Not) = expected.kind() else {
                        return Err("trace reference original type mismatch".into());
                    };
                    expected = *child;
                }
                original
            }
            TraceValue::Tag(original, _) => original,
            TraceValue::Boolean(_) => self.tcx.types.bool,
        };
        if actual != expected {
            return Err("trace original type mismatch".into());
        }
        Ok(())
    }

    fn place(
        &mut self,
        body: &Body<'tcx>,
        locals: &[Option<TraceValue<'tcx>>],
        place: Place<'tcx>,
    ) -> Result<TraceValue<'tcx>, String> {
        if place.projection.len() > 16 {
            return Err("trace projection depth exceeded".into());
        }
        self.charge(1 + place.projection.len())?;
        let mut value = *locals
            .get(place.local.as_usize())
            .and_then(Option::as_ref)
            .ok_or("trace uninitialized or consumed local")?;
        self.typed(body.local_decls[place.local].ty, value)?;
        for projection in place.projection {
            match (projection, &mut value) {
                (ProjectionElem::Deref, TraceValue::Origin { refs, .. }) if *refs > 0 => {
                    *refs -= 1;
                }
                (
                    ProjectionElem::Downcast(name, selected),
                    TraceValue::Origin {
                        original,
                        side,
                        refs: 0,
                        variant,
                    },
                ) if *original == self.original
                    && variant.is_none()
                    && self
                        .tags
                        .is_some_and(|tags| selected.as_usize() == tags[*side]) =>
                {
                    let ty::Adt(definition, _) = original.kind() else {
                        return Err("niche downcast lacks original enum".into());
                    };
                    if name.is_some_and(|name| name != definition.variant(selected).name) {
                        return Err("niche downcast has wrong original variant name".into());
                    }
                    *variant = Some(selected);
                }
                (
                    ProjectionElem::Field(field, field_ty),
                    TraceValue::Origin {
                        original,
                        refs: 0,
                        variant: Some(selected),
                        ..
                    },
                ) if *original == self.original
                    && selected.as_usize() == 1
                    && field.as_usize() == 0
                    && field_ty == self.payload =>
                {
                    *original = field_ty;
                    if let TraceValue::Origin { variant, .. } = &mut value {
                        *variant = None;
                    }
                }
                _ => return Err("trace unsupported or inactive projection".into()),
            }
        }
        self.typed(place.ty(&body.local_decls, self.tcx).ty, value)?;
        Ok(value)
    }

    fn operand(
        &mut self,
        body: &Body<'tcx>,
        locals: &mut [Option<TraceValue<'tcx>>],
        operand: &Operand<'tcx>,
    ) -> Result<TraceValue<'tcx>, String> {
        self.charge(1)?;
        let value = match operand {
            Operand::Copy(place) => self.place(body, locals, *place)?,
            Operand::Move(place) if place.projection.is_empty() => {
                let value = self.place(body, locals, *place)?;
                locals[place.local.as_usize()] = None;
                value
            }
            Operand::Constant(constant) => {
                let original = constant.const_.ty();
                let bits = constant
                    .const_
                    .try_eval_bits(self.tcx, ty::TypingEnv::fully_monomorphized())
                    .ok_or("trace nonliteral constant")?;
                if original == self.tcx.types.bool && bits <= 1 {
                    TraceValue::Boolean(if bits == 0 { 0 } else { u8::MAX })
                } else if original == self.original.discriminant_ty(self.tcx) {
                    TraceValue::Tag(original, bits)
                } else {
                    return Err("trace unsupported scalar constant".into());
                }
            }
            _ => return Err("trace unsupported Move projection".into()),
        };
        self.typed(operand.ty(&body.local_decls, self.tcx), value)?;
        Ok(value)
    }

    fn call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: [TraceValue<'tcx>; 2],
        depth: usize,
    ) -> Result<u8, String> {
        if depth >= 16 {
            return Err("trace call depth exceeded".into());
        }
        self.charge(depth)?;
        if self.active[..depth].contains(&Some(instance)) {
            return Err("niche law selected full Instance cycle".into());
        }
        self.active[depth] = Some(instance);
        let result = self.interpret(instance, values, depth);
        self.active[depth] = None;
        result
    }

    fn interpret(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: [TraceValue<'tcx>; 2],
        depth: usize,
    ) -> Result<u8, String> {
        if depth >= 16 {
            return Err("trace call depth exceeded".into());
        }
        self.charge(1)?;
        if self.engine.is_some() {
            self.charge_live_engine(3)?;
        }
        let body = self
            .graph
            .as_deref_mut()
            .ok_or("trace record lookup requires the same admission graph")?
            .lookup_body(self.bodies, instance)?
            .ok_or("trace selected body unavailable")?;
        if let Some(engine) = self.engine
            && !engine
                .bodies
                .borrow()
                .get(&instance)
                .is_some_and(|current| std::rc::Rc::ptr_eq(current, body))
        {
            return Err("trace live Engine dependency was replaced or evicted".into());
        }
        if body.source.instance != instance.def
            || body.source.promoted.is_some()
            || body.coroutine.is_some()
            || body.arg_count != 2
            || body.local_decls.len() < 3
            || body.spread_arg.is_some()
            || body.tainted_by_errors.is_some()
        {
            return Err("trace selected body metadata mismatch".into());
        }
        self.charge(self.completed.len())?;
        if let Some(proof) = self
            .completed
            .iter()
            .find(|proof| proof.instance == instance)
        {
            let witness = proof
                .body
                .upgrade()
                .ok_or("trace completed body witness expired")?;
            if !std::rc::Rc::ptr_eq(&witness, body) {
                return Err("trace completed selected body was replaced".into());
            }
            let original = proof.original;
            let relation = proof.relation;
            self.charge(1)?;
            for (side, value) in values.iter().enumerate() {
                self.charge(1)?;
                if !matches!(value, TraceValue::Origin { original: actual, side: actual_side,
                    refs: 1, variant: None } if *actual == original && *actual_side == side)
                {
                    return Err("trace completed relation receiver mapping mismatch".into());
                }
                self.typed(body.local_decls[Local::from_usize(side + 1)].ty, *value)?;
            }
            return Ok(relation);
        }
        self.charge_materialization(body.local_decls.len())?;
        let mut locals = Vec::new();
        locals
            .try_reserve_exact(body.local_decls.len())
            .map_err(|_| "trace locals allocation resource failure")?;
        locals.resize(body.local_decls.len(), None);
        for (index, value) in values.into_iter().enumerate() {
            self.typed(body.local_decls[Local::from_usize(index + 1)].ty, value)?;
            locals[index + 1] = Some(value);
        }
        self.charge(1)?;
        if body.basic_blocks.is_empty() || body.basic_blocks.len() > 128 {
            return Err("trace selected block extent exceeds fixed128 domain".into());
        }
        self.charge_materialization(1)?;
        let mut block = START_BLOCK;
        let mut seen = 0_u128;
        loop {
            self.charge(1)?;
            // Range, checked shift, bit test and update form a fixed structural service.
            self.charge(4)?;
            mark_niche_block(&mut seen, body.basic_blocks.len(), block.as_usize())?;
            let data = body
                .basic_blocks
                .get(block)
                .ok_or("trace selected block unavailable")?;
            for statement in &data.statements {
                self.charge(1)?;
                match &statement.kind {
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                        locals[local.as_usize()] = None;
                    }
                    StatementKind::Assign(assignment) if assignment.0.projection.is_empty() => {
                        let value = match &assignment.1 {
                            Rvalue::Use(operand, _) => self.operand(body, &mut locals, operand)?,
                            Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place) => {
                                let mut value = self.place(body, &locals, *place)?;
                                let TraceValue::Origin { refs, .. } = &mut value else {
                                    return Err("trace reference lacks original origin".into());
                                };
                                *refs += 1;
                                value
                            }
                            Rvalue::Discriminant(place) => {
                                let TraceValue::Origin {
                                    original,
                                    side,
                                    refs: 0,
                                    variant: None,
                                } = self.place(body, &locals, *place)?
                                else {
                                    return Err("trace discriminant lacks whole original".into());
                                };
                                if original != self.original {
                                    return Err("trace wrong discriminant original".into());
                                }
                                TraceValue::Tag(
                                    original.discriminant_ty(self.tcx),
                                    self.tags.ok_or(
                                        "trace symbolic tag observation requires full branch proof",
                                    )?[side] as u128,
                                )
                            }
                            Rvalue::Cast(
                                rustc_middle::mir::CastKind::Transmute,
                                operand,
                                target,
                            ) if *target == self.primitive => {
                                let TraceValue::Origin {
                                    original,
                                    side,
                                    refs: 0,
                                    variant: None,
                                } = self.operand(body, &mut locals, operand)?
                                else {
                                    return Err("trace transmute lacks original payload".into());
                                };
                                if original != self.payload {
                                    return Err("trace transmute wrong payload type".into());
                                }
                                TraceValue::Origin {
                                    original: *target,
                                    side,
                                    refs: 0,
                                    variant: None,
                                }
                            }
                            Rvalue::UnaryOp(rustc_middle::mir::UnOp::Not, operand) => {
                                let TraceValue::Boolean(value) =
                                    self.operand(body, &mut locals, operand)?
                                else {
                                    return Err("trace Not wrong type".into());
                                };
                                TraceValue::Boolean(!value)
                            }
                            Rvalue::BinaryOp(BinOp::Eq, operands) => {
                                let left = self.operand(body, &mut locals, &operands.0)?;
                                let right = self.operand(body, &mut locals, &operands.1)?;
                                let equal = match (left, right) {
                                    (TraceValue::Tag(a, x), TraceValue::Tag(b, y)) if a == b => {
                                        if x == y { u8::MAX } else { 0 }
                                    }
                                    (
                                        TraceValue::Origin {
                                            original: a,
                                            side: x,
                                            refs: 0,
                                            ..
                                        },
                                        TraceValue::Origin {
                                            original: b,
                                            side: y,
                                            refs: 0,
                                            ..
                                        },
                                    ) if a == self.primitive && a == b => {
                                        if x == y {
                                            u8::MAX
                                        } else {
                                            self.equality
                                        }
                                    }
                                    _ => return Err("trace Eq lacks typed relation".into()),
                                };
                                TraceValue::Boolean(equal)
                            }
                            _ => return Err("trace unsupported rvalue".into()),
                        };
                        self.typed(body.local_decls[assignment.0.local].ty, value)?;
                        locals[assignment.0.local.as_usize()] = Some(value);
                    }
                    _ => return Err("trace unsupported statement".into()),
                }
            }
            self.charge(1)?;
            match &data.terminator().kind {
                TerminatorKind::Return => {
                    let TraceValue::Boolean(value) =
                        self.place(body, &locals, Place::from(Local::from_usize(0)))?
                    else {
                        return Err("trace return wrong type".into());
                    };
                    return Ok(value);
                }
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::SwitchInt { discr, targets } => {
                    let bits = match self.operand(body, &mut locals, discr)? {
                        TraceValue::Tag(_, bits) => bits,
                        TraceValue::Boolean(0) => 0,
                        TraceValue::Boolean(u8::MAX) => 1,
                        TraceValue::Boolean(_) => {
                            return Err("trace symbolic branch needs split".into());
                        }
                        _ => return Err("trace switch lacks concrete tag".into()),
                    };
                    block = targets.target_for_value(bits);
                }
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target: Some(target),
                    ..
                } if args.len() == 2 && destination.projection.is_empty() => {
                    self.charge(1 + args.len())?;
                    let ty::FnDef(id, arguments) = func.ty(&body.local_decls, self.tcx).kind()
                    else {
                        return Err("trace non-FnDef delegate".into());
                    };
                    let selected = ty::Instance::try_resolve(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        *id,
                        arguments.skip_binder(),
                    )
                    .map_err(|_| "trace delegate resolution failed")?
                    .ok_or("trace delegate unavailable")?;
                    let left = self.operand(body, &mut locals, &args[0].node)?;
                    let right = self.operand(body, &mut locals, &args[1].node)?;
                    let value =
                        TraceValue::Boolean(self.call(selected, [left, right], depth + 1)?);
                    self.typed(body.local_decls[destination.local].ty, value)?;
                    locals[destination.local.as_usize()] = Some(value);
                    block = *target;
                }
                _ => return Err("trace unsupported terminator".into()),
            }
        }
    }
}

const NICHE_GRAPH_WORK: usize = 131072;
const NICHE_BODY_WORK: usize = 8192;
const NICHE_BODIES: usize = 9;
const NICHE_PENDING: usize = 32;
// Exact table facts from the immutable committed222 reference source association.
const NICHE_REFERENCE_ENTRIES: usize = 110;
const NICHE_REFERENCE_BYTES: usize = 340003;
const NICHE_ADMISSION_LAW_WORK: usize = 1024;
#[cfg(test)]
const NICHE_LEGACY_LAW_WORK: usize = 512;

#[derive(Clone, Copy, Debug)]
#[repr(usize)]
enum GraphPhase {
    InventoryPrelude,
    InventoryAuxiliary,
    InventoryVisitor,
    BodyClone,
    BodyInstantiate,
    BodyNormalize,
    CoroutineScan,
    SignatureInstantiate,
    SignatureNormalize,
    SignatureValidate,
    EncoderBudget,
    EncoderIdentity,
    EncoderRender,
    Cleanup,
    Layout,
    Edges,
    Schema,
    Records,
    Text,
    LawLiveEngine,
}

#[derive(Debug)]
struct GraphBudget<'tcx> {
    work: usize,
    phases: [usize; 20],
    text_reservations: usize,
    text_bounds: [usize; 6],
    bodies: [Option<ty::Instance<'tcx>>; NICHE_BODIES],
    body_count: usize,
}

impl<'tcx> GraphBudget<'tcx> {
    fn new(work: usize) -> Result<Self, String> {
        // Fixed counter/key initialization is recorded, not an uncharged tail allowance.
        let initialization = 20 + 6 + NICHE_BODIES;
        let total = work
            .checked_add(initialization)
            .ok_or("niche budget initialization overflow")?;
        if total > NICHE_GRAPH_WORK {
            return Err(format!(
                "niche graph initialization exceeds NICHE_GRAPH_WORK policy: \
                 limit={NICHE_GRAPH_WORK} attempted={total} before record construction"
            ));
        }
        let mut phases = [0; 20];
        phases[GraphPhase::Records as usize] = initialization;
        Ok(Self {
            work: total,
            phases,
            text_reservations: 0,
            text_bounds: [0; 6],
            bodies: [None; NICHE_BODIES],
            body_count: 0,
        })
    }

    fn charge(&mut self, work: usize) -> Result<(), String> {
        self.phase(GraphPhase::Records, work)
    }

    fn phase(&mut self, phase: GraphPhase, work: usize) -> Result<(), String> {
        self.work = self
            .work
            .checked_add(work)
            .ok_or("niche graph work overflow")?;
        self.phases[phase as usize] = self.phases[phase as usize]
            .checked_add(work)
            .ok_or("niche graph phase overflow")?;
        if self.work > NICHE_GRAPH_WORK {
            return Err(format!(
                "niche graph exceeds cumulative NICHE_GRAPH_WORK policy: \
                limit={NICHE_GRAPH_WORK} phase={phase:?} attempted={} phases={:?}",
                self.work, self.phases
            ));
        }
        Ok(())
    }

    fn record(&mut self, instance: ty::Instance<'tcx>) -> Result<(), String> {
        self.charge(1 + instance.args.len())
    }

    fn lookup_body<'a>(
        &mut self,
        bodies: &'a [(ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>)],
        instance: ty::Instance<'tcx>,
    ) -> Result<Option<&'a std::rc::Rc<Body<'tcx>>>, String> {
        if bodies.len() > NICHE_BODIES {
            return Err("niche body records exceed nine before lookup".into());
        }
        self.charge(bodies.len().saturating_mul(1 + instance.args.len()))?;
        Ok(bodies
            .iter()
            .find(|(key, _)| *key == instance)
            .map(|(_, body)| body))
    }

    fn insert_body(
        &mut self,
        bodies: &mut Vec<(ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>)>,
        instance: ty::Instance<'tcx>,
        body: std::rc::Rc<Body<'tcx>>,
    ) -> Result<(), String> {
        if let Some(previous) = self.lookup_body(bodies, instance)? {
            self.charge(1)?;
            if !std::rc::Rc::ptr_eq(previous, &body) {
                return Err("niche same full Instance body record changed".into());
            }
            return Ok(());
        }
        if bodies.len() == NICHE_BODIES || bodies.capacity() < NICHE_BODIES {
            return Err("niche body records lack prepaid capacity before append".into());
        }
        self.record(instance)?;
        self.charge(2)?; // Rc move and append, within the prepaid nine slots.
        bodies.push((instance, body));
        Ok(())
    }

    fn body(&mut self, instance: ty::Instance<'tcx>) -> Result<(), String> {
        self.charge(
            self.body_count
                .saturating_mul(1usize.saturating_add(instance.args.len())),
        )?;
        if self.bodies[..self.body_count].contains(&Some(instance)) {
            return Ok(());
        }
        if self.body_count == NICHE_BODIES {
            return Err("niche selected bodies exceed nine before construction".into());
        }
        self.record(instance)?;
        self.bodies[self.body_count] = Some(instance);
        self.body_count += 1;
        Ok(())
    }

    fn pending(
        &mut self,
        pending: &mut Vec<(
            ty::Instance<'tcx>,
            Option<super::super::pure_comparisons::CursorArithmetic>,
        )>,
        instance: ty::Instance<'tcx>,
        arithmetic: Option<super::super::pure_comparisons::CursorArithmetic>,
    ) -> Result<(), String> {
        if pending.len() == NICHE_PENDING {
            return Err("niche pending records exceed32 before append".into());
        }
        self.record(instance)?;
        self.charge(1)?;
        pending.push((instance, arithmetic));
        Ok(())
    }

    fn text(&mut self, phase: usize, upper: usize) -> Result<(), String> {
        self.phase(GraphPhase::Text, 1)?;
        self.text_bounds[phase] = self.text_bounds[phase]
            .checked_add(upper)
            .ok_or("niche bounded text service overflow")?;
        Ok(())
    }

    // Legacy exact-text source controls remain test-only after typed production replacement.
    #[cfg(test)]
    fn byte_route_reference_text(&mut self, upper: usize) -> Result<(), String> {
        self.charge(1)?; // Actual additional concrete service dispatch.
        self.text(5, upper)
    }

    fn key(&mut self, id: DefId) -> Result<String, String> {
        self.text(4, 2 * 65536)?;
        let key = super::super::pure_comparison_templates::definition_key(id);
        if key.len() > 65536 {
            return Err("niche core name exceeds bounded text domain".into());
        }
        Ok(key)
    }

    fn reference(
        &mut self,
        key: &str,
        encoded: &str,
    ) -> Result<Option<super::super::pure_comparison_templates::PureTemplateFamily>, String> {
        self.phase(GraphPhase::Text, NICHE_REFERENCE_ENTRIES)?;
        self.text(
            5,
            NICHE_REFERENCE_BYTES + NICHE_REFERENCE_ENTRIES * (65536 + key.len()),
        )?;
        Ok(super::super::pure_comparison_templates::reference_family(
            key, encoded,
        ))
    }

    fn arguments(
        &mut self,
        tcx: TyCtxt<'tcx>,
        arguments: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), String> {
        use ty::TypeVisitable;
        self.charge(arguments.len())?;
        let core = tcx
            .lang_items()
            .sized_trait()
            .ok_or("niche core unavailable")?
            .krate;
        let mut visitor = ExpandedTypes {
            core,
            limit: NICHE_BODY_WORK.min(NICHE_GRAPH_WORK.saturating_sub(self.work)),
            arguments,
            work: 0,
            depth: 0,
            error: None,
        };
        let _ = arguments.visit_with(&mut visitor);
        self.phase(GraphPhase::InventoryVisitor, visitor.work)?;
        if let Some(error) = visitor.error {
            return Err(error.into());
        }
        Ok(())
    }

    fn arguments_in_caller(
        &mut self,
        tcx: TyCtxt<'tcx>,
        arguments: ty::GenericArgsRef<'tcx>,
        caller: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        use ty::TypeVisitable;
        self.charge(6 + caller.args.len())?; // Actual new scoped-context setup and validation.
        if !matches!(caller.def, ty::InstanceKind::Item(_))
            || caller.args.len() != tcx.generics_of(caller.def_id()).count()
        {
            return Err(
                "typed byte raw arguments lack the complete original caller environment".into(),
            );
        }
        // The existing concrete caller argument service refuses unresolved recursive Params.
        // Raw helper Params are still visited, now against that authenticated caller environment.
        self.arguments(tcx, caller.args)?;
        self.charge(arguments.len())?;
        let core = tcx
            .lang_items()
            .sized_trait()
            .ok_or("niche core unavailable")?
            .krate;
        let mut visitor = ExpandedTypes {
            core,
            limit: NICHE_BODY_WORK.min(NICHE_GRAPH_WORK.saturating_sub(self.work)),
            arguments: caller.args,
            work: 0,
            depth: 0,
            error: None,
        };
        let _ = arguments.visit_with(&mut visitor);
        self.phase(GraphPhase::InventoryVisitor, visitor.work)?;
        if let Some(error) = visitor.error {
            return Err(error.into());
        }
        Ok(())
    }

    fn encoding(&mut self, inventory: usize) -> Result<(), String> {
        if self.text_reservations == 32 {
            return Err("niche encoders exceed 32 operations before invocation".into());
        }
        self.charge(1)?;
        self.text_reservations += 1;
        self.phase(GraphPhase::EncoderBudget, inventory)?;
        self.phase(GraphPhase::EncoderIdentity, inventory)?;
        self.phase(GraphPhase::EncoderRender, inventory)?;
        // Post-render byte count is a slot traversal; join/normalize/wrap follow its64KiB check.
        // These are traversal reservations, NOT a peak transient allocation theorem.
        self.phase(GraphPhase::Text, inventory)?;
        self.text(0, 65536)?;
        self.text(1, 65536)?;
        self.text(2, 16 * 65536)?;
        self.text(3, 1)?;
        Ok(())
    }

    fn inventory(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<usize, String> {
        self.charge(6)?;
        let initial = [
            body.local_decls.len(),
            body.basic_blocks.len(),
            body.source_scopes.len(),
            body.var_debug_info.len(),
            body.required_consts.as_ref().map_or(0, Vec::len),
            body.mentioned_items.as_ref().map_or(0, Vec::len),
        ]
        .into_iter()
        .try_fold(0usize, |total, count| total.checked_add(count))
        .ok_or("niche inventory header overflow")?;
        self.phase(GraphPhase::InventoryPrelude, initial)?;
        let mut auxiliary = initial;
        let mut operations = 0usize;
        for block in body.basic_blocks.iter() {
            self.phase(GraphPhase::InventoryPrelude, block.statements.len() + 1)?;
            operations = operations.saturating_add(block.statements.len() + 1);
            if operations > 512 || body.basic_blocks.len() > 128 {
                return Err("niche body exceeds512 operations or128 blocks".into());
            }
            auxiliary = auxiliary.saturating_add(
                block.statements.len() + 1 + block.after_last_stmt_debuginfos.len(),
            );
            for statement in &block.statements {
                self.phase(GraphPhase::InventoryPrelude, statement.debuginfos.len())?;
                auxiliary = auxiliary.saturating_add(statement.debuginfos.len());
            }
        }
        self.phase(GraphPhase::InventoryAuxiliary, auxiliary)?;
        let remaining = NICHE_GRAPH_WORK
            .saturating_sub(self.work)
            .min(NICHE_BODY_WORK);
        let (work, error) = full_inventory_limit(tcx, instance, body, remaining);
        self.phase(GraphPhase::InventoryVisitor, work)?;
        if let Some(error) = error {
            return Err(error.into());
        }
        Ok(work)
    }
}

#[derive(Debug)]
struct CapturedNicheBody<'tcx> {
    body: std::rc::Rc<Body<'tcx>>,
    family: Option<super::super::pure_comparison_templates::PureTemplateFamily>,
    inventory: usize,
}

#[derive(Clone, Copy)]
enum GraphGoal {
    Law,
    ByteRoute,
}

enum GraphOutcome<'a, 'tcx> {
    Law(Box<CheckedNicheLaw<'a, 'tcx>>),
    Byte(byte_route::ByteBoundary<'a, 'tcx>),
}

struct CheckedNicheLaw<'engine, 'tcx> {
    engine: &'engine Engine<'tcx>,
    original: Ty<'tcx>,
    relation: u8,
    bodies: Vec<(ty::Instance<'tcx>, std::rc::Weak<Body<'tcx>>)>,
    graph_work: usize,
    law_work: usize,
    law_limit: usize,
    observed: LawWork,
    application: Option<GraphBudget<'tcx>>,
    membership_schema: Schema,
}

impl<'tcx> CheckedNicheLaw<'_, 'tcx> {
    fn validate(&self, engine: &Engine<'tcx>) -> Result<(), String> {
        if self.law_limit != NICHE_ADMISSION_LAW_WORK
            || self.law_work > self.law_limit
            || self.graph_work > NICHE_GRAPH_WORK
            || self
                .observed
                .semantic
                .checked_add(self.observed.materialization)
                != Some(self.law_work)
        {
            return Err("niche law resource policy metadata differs".into());
        }
        if !std::ptr::eq(self.engine, engine) {
            return Err("niche law belongs to a different live Engine".into());
        }
        for (instance, witness) in &self.bodies {
            let body = witness.upgrade().ok_or("niche law body witness expired")?;
            if !engine
                .bodies
                .borrow()
                .get(instance)
                .is_some_and(|current| std::rc::Rc::ptr_eq(current, &body))
            {
                return Err("niche law selected Engine body was replaced or evicted".into());
            }
        }
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    fn capture_niche_comparison_body(
        &self,
        instance: ty::Instance<'tcx>,
        budget: &mut GraphBudget<'tcx>,
        transport: bool,
        goal: GraphGoal,
    ) -> Result<CapturedNicheBody<'tcx>, String> {
        use super::super::pure_comparison_templates as templates;
        budget.arguments(self.tcx, instance.args)?;
        budget.record(instance)?;
        budget.body(instance)?;
        if matches!(
            self.tcx.def_kind(instance.def_id()),
            DefKind::Fn | DefKind::AssocFn
        ) && instance.args.len() != self.tcx.generics_of(instance.def_id()).count()
        {
            return Err("niche comparison full Instance argument count mismatch".into());
        }
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.intrinsic(instance.def_id()).is_some()
            || !self.tcx.is_mir_available(instance.def_id())
        {
            return Err(self.missing_body_reason(instance.def_id()));
        }
        let raw = self.tcx.instance_mir(instance.def);
        let raw_work = budget.inventory(self.tcx, instance, raw)?;
        budget.phase(GraphPhase::Cleanup, raw.basic_blocks.len())?;
        if raw.source.instance != instance.def
            || raw.source.promoted.is_some()
            || raw.coroutine.is_some()
            || raw.spread_arg.is_some()
            || raw.tainted_by_errors.is_some()
            || raw.injection_phase.is_some()
            || raw.phase
                != rustc_middle::mir::MirPhase::Runtime(rustc_middle::mir::RuntimePhase::Optimized)
            || (!transport && raw.basic_blocks.iter().any(|block| block.is_cleanup))
        {
            return Err(format!(
                "niche comparison raw body metadata mismatch: {instance:?}, \
                phase={:?}, injection={:?}, cleanup={}",
                raw.phase,
                raw.injection_phase,
                raw.basic_blocks.iter().any(|block| block.is_cleanup)
            ));
        }
        let mut family = None;
        if transport {
            budget.charge(2)?;
            budget.encoding(raw_work)?;
            let core = self
                .tcx
                .lang_items()
                .sized_trait()
                .ok_or("niche transport core unavailable")?
                .krate;
            let encoded = templates::encode_template(self.tcx, raw, core)?;
            let key = budget.key(instance.def_id())?;
            family = budget.reference(&key, &encoded)?;
            if family.is_none() {
                budget.charge(2)?; // Actual new failed-reference goal dispatch.
                if matches!(goal, GraphGoal::ByteRoute) {
                    family = byte_transport::source(
                        self,
                        instance,
                        raw,
                        byte_transport::SourcePhase::Raw,
                        budget,
                    )?
                    .map(|shape| shape.family());
                }
            }
            if family.is_none() {
                return Err("niche transport raw body has no complete reference".into());
            }
        }
        // This charge bounds the expanded clone before the Engine constructs it.
        budget.phase(GraphPhase::BodyClone, raw_work)?;
        budget.phase(GraphPhase::BodyInstantiate, raw_work)?;
        budget.phase(GraphPhase::BodyNormalize, raw_work)?;
        if matches!(
            self.tcx.def_kind(instance.def_id()),
            DefKind::Fn | DefKind::AssocFn
        ) {
            budget.phase(GraphPhase::SignatureInstantiate, raw_work)?;
            budget.phase(GraphPhase::SignatureNormalize, raw_work)?;
            budget.phase(GraphPhase::SignatureValidate, raw_work)?;
            budget.record(instance)?;
            let prior = self.call_signatures.borrow().get(&instance).copied();
            if let Some(selected) = prior {
                let expected = self
                    .tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        self.tcx
                            .fn_sig(instance.def_id())
                            .instantiate(self.tcx, instance.args),
                    )
                    .map_err(|_| "niche comparison signature normalization failed")?;
                if selected != expected {
                    return Err(
                        "niche cached full signature differs from actual compiler signature".into(),
                    );
                }
            } else {
                budget.record(instance)?;
                budget.record(instance)?; // Optional signature cache publication.
                self.call_poly_signature(instance)?;
            }
        }
        budget.record(instance)?;
        budget.charge(1)?;
        let prior = self.bodies.borrow().get(&instance).cloned();
        let mut body_work = 0;
        if let Some(cached) = &prior {
            let cached_work = budget.inventory(self.tcx, instance, cached)?;
            body_work = cached_work;
            budget.phase(GraphPhase::Cleanup, cached.basic_blocks.len())?;
            if cached.source.instance != instance.def
                || cached.source.promoted.is_some()
                || cached.coroutine.is_some()
                || cached.spread_arg.is_some()
                || cached.tainted_by_errors.is_some()
                || cached.injection_phase.is_some()
                || cached.phase
                    != rustc_middle::mir::MirPhase::Runtime(
                        rustc_middle::mir::RuntimePhase::Optimized,
                    )
                || (!transport && cached.basic_blocks.iter().any(|block| block.is_cleanup))
            {
                return Err("niche comparison cached body metadata mismatch".into());
            }
        }
        let body = if let Some(cached) = &prior {
            budget.charge(1)?;
            cached.clone()
        } else {
            if self.bodies.borrow().len() >= 128 {
                return Err("niche miss would clear unrelated Engine body cache".into());
            }
            budget.phase(GraphPhase::CoroutineScan, raw_work)?;
            budget.record(instance)?;
            budget.charge(3)?; // Body/Rc allocation, cache insertion and returned Rc copy.
            let body = self.instantiated_body(instance)?;
            let selected_work = budget.inventory(self.tcx, instance, &body)?;
            body_work = selected_work;
            budget.phase(GraphPhase::Cleanup, body.basic_blocks.len())?;
            if body.source.instance != instance.def
                || body.source.promoted.is_some()
                || body.coroutine.is_some()
                || body.spread_arg.is_some()
                || body.tainted_by_errors.is_some()
                || body.injection_phase.is_some()
                || body.phase
                    != rustc_middle::mir::MirPhase::Runtime(
                        rustc_middle::mir::RuntimePhase::Optimized,
                    )
                || (!transport && body.basic_blocks.iter().any(|block| block.is_cleanup))
            {
                return Err("niche comparison selected body metadata mismatch".into());
            }
            body
        };
        if let Some(cached) = prior {
            // Both clone containers and expanded types were charged before fresh construction.
            let expected = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(self.tcx, raw.clone()),
                )
                .map_err(|_| "niche cached body mirror normalization failed")?;
            let expected_work = budget.inventory(self.tcx, instance, &expected)?;
            let core = self
                .tcx
                .lang_items()
                .sized_trait()
                .ok_or("niche comparison core unavailable")?
                .krate;
            budget.charge(2)?;
            budget.phase(
                GraphPhase::Cleanup,
                expected.basic_blocks.len() + cached.basic_blocks.len(),
            )?;
            if expected
                .basic_blocks
                .iter()
                .map(|block| block.is_cleanup)
                .ne(cached.basic_blocks.iter().map(|block| block.is_cleanup))
            {
                return Err("niche cached cleanup graph differs from actual compiler body".into());
            }
            if matches!(goal, GraphGoal::ByteRoute) {
                byte_transport::mirrored_metadata(&expected, &cached, budget)?;
            }
            budget.encoding(expected_work)?;
            budget.encoding(body_work)?;
            if templates::encode_template(self.tcx, &expected, core)?
                != templates::encode_template(self.tcx, &cached, core)?
            {
                return Err("niche cached body differs from actual compiler body".into());
            }
        }
        budget.charge(2)?;
        Ok(CapturedNicheBody {
            body,
            family,
            inventory: body_work,
        })
    }

    fn check_niche_comparison_law<'engine>(
        &'engine self,
        original: Ty<'tcx>,
        outer: ty::Instance<'tcx>,
    ) -> Result<CheckedNicheLaw<'engine, 'tcx>, String> {
        self.check_niche_comparison_law_with_work(original, outer, 0)
    }

    fn check_niche_comparison_law_with_work<'engine>(
        &'engine self,
        original: Ty<'tcx>,
        outer: ty::Instance<'tcx>,
        prior_work: usize,
    ) -> Result<CheckedNicheLaw<'engine, 'tcx>, String> {
        match self.capture_niche_graph_with_goal(original, outer, prior_work, GraphGoal::Law)? {
            GraphOutcome::Law(law) => Ok(*law),
            GraphOutcome::Byte(_) => {
                Err("ordinary niche law unexpectedly returned byte metadata".into())
            }
        }
    }

    pub(in crate::proof) fn prepare_niche_byte_route<'engine>(
        &'engine self,
        scope: super::super::readonly_byte_origins::RouteScope<'engine, 'tcx>,
    ) -> Result<PreparedByteRoute<'engine, 'tcx>, String> {
        let (original, outer, prior_work) = scope.request(self)?;
        let boundary = match self.capture_niche_graph_with_goal(
            original,
            outer,
            prior_work,
            GraphGoal::ByteRoute,
        )? {
            GraphOutcome::Byte(boundary) => boundary,
            GraphOutcome::Law(_) => return Err("byte route reached a non-byte law result".into()),
        };
        boundary.prepare(scope)
    }

    fn capture_niche_graph_with_goal<'engine>(
        &'engine self,
        original: Ty<'tcx>,
        outer: ty::Instance<'tcx>,
        prior_work: usize,
        goal: GraphGoal,
    ) -> Result<GraphOutcome<'engine, 'tcx>, String> {
        use super::super::pure_comparison_templates as templates;
        use super::super::pure_comparisons::CursorArithmetic;
        let mut budget = GraphBudget::new(prior_work)?;
        // New goal/result dispatch; every old phase fee remains literal.
        budget.charge(2)?;
        budget.phase(GraphPhase::Schema, 16)?;
        let ty::Adt(definition, _) = original.kind() else {
            return Err("niche membership original is not Option".into());
        };
        if Some(definition.did()) != self.tcx.lang_items().get(LangItem::Option) {
            return Err("niche membership admits only original core Option".into());
        }
        let ty::Adt(_, arguments) = original.kind() else {
            unreachable!()
        };
        if arguments.len() != 1 {
            return Err("niche Option argument count mismatch".into());
        }
        let Some(ty::GenericArgKind::Type(payload)) = arguments.first().map(|arg| arg.kind())
        else {
            return Err("niche Option argument is not an original type".into());
        };
        let ty::Adt(payload_definition, payload_arguments) = payload.kind() else {
            return Err("niche Option payload is not original NonZero".into());
        };
        let nonzero = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("NonZero"));
        // Additional original target-sized primitive dispatch is performed, not discounted.
        budget.phase(GraphPhase::Schema, 1)?;
        if matches!(payload_arguments.first().map(|arg| arg.kind()),
            Some(ty::GenericArgKind::Type(original))
                if matches!(original.kind(), ty::Int(ty::IntTy::Isize)
                    | ty::Uint(ty::UintTy::Usize)))
        {
            budget.phase(GraphPhase::Schema, 2)?;
        }
        if Some(payload_definition.did()) != nonzero
            || payload_arguments.len() != 1
            || !matches!(payload_arguments.first().map(|arg| arg.kind()),
                Some(ty::GenericArgKind::Type(original))
                    if super::super::nonzero_options::readonly_niche_integer_type(
                        self.tcx, original)
                        .is_some())
        {
            return Err("niche Option payload is not an admitted original integer NonZero".into());
        }
        if outer.def_id().krate != definition.did().krate {
            return Err("niche outer is not original core".into());
        }
        budget.arguments(self.tcx, outer.args)?;
        let outer_key = budget.key(outer.def_id())?;
        if !matches!(
            outer_key.as_str(),
            "DefId(core::slice::{impl#0}::contains)"
                | "DefId(core::slice::cmp::{impl#18}::slice_contains)"
        ) {
            return Err("niche outer is not an eligible actual core contains candidate".into());
        }
        if outer.args.len() != 1
            || !matches!(outer.args.first().map(|arg| arg.kind()),
            Some(ty::GenericArgKind::Type(element)) if element == original)
        {
            return Err("niche membership outer original element mismatch".into());
        }
        // Caller-visible bounded schema services: six purity queries, five layouts,
        // three field instantiations, anchored inner normalization, two variant scans,
        // and the fixed NicheFacts field copy. Compiler-internal complexity is not claimed.
        // Old schema fees remain; extra copies4 and two bounded width/range services48.
        budget.phase(GraphPhase::Schema, 6 + 5 + 3 + 1 + 2 + 32 + 4 + 48)?;
        // Additional actual primitive sign/range and derived-sign metadata services.
        budget.phase(GraphPhase::Schema, 6)?;
        let schema = certify(self.tcx, original)?;
        if schema.payload_variant != 1 || schema.tags != [0, 1] || !facts_match(&schema.facts) {
            return Err("niche membership exact original schema mismatch".into());
        }
        let core = definition.did().krate;
        let eq = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
            .filter(|id| id.krate == core)
            .ok_or("niche equality identity unavailable")?;
        budget.phase(
            GraphPhase::Schema,
            self.tcx.associated_items(self.tcx.parent(eq)).len(),
        )?;
        let ne = self
            .tcx
            .associated_items(self.tcx.parent(eq))
            .in_definition_order()
            .find(|item| item.opt_name() == Some(rustc_span::Symbol::intern("ne")))
            .ok_or("niche inequality identity unavailable")?
            .def_id;
        budget.charge(2)?;
        let args = self.tcx.mk_args(&[original.into(), original.into()]);
        budget.arguments(self.tcx, args)?;
        budget.charge(2)?;
        let eq_instance = self.resolve_function_item(eq, args)?;
        budget.arguments(self.tcx, args)?;
        budget.charge(2)?;
        let ne_instance = self.resolve_function_item(ne, args)?;
        budget.charge(2)?;
        let primitive_args = self
            .tcx
            .mk_args(&[schema.primitive.into(), schema.primitive.into()]);
        budget.arguments(self.tcx, primitive_args)?;
        budget.charge(2)?;
        let primitive = self.resolve_function_item(eq, primitive_args)?;
        budget.charge(2)?;
        let payload_args = self
            .tcx
            .mk_args(&[schema.nonzero.into(), schema.nonzero.into()]);
        budget.arguments(self.tcx, payload_args)?;
        budget.charge(2)?;
        let payload_eq = self.resolve_function_item(eq, payload_args)?;
        let laws = [primitive, payload_eq, eq_instance, ne_instance];
        budget.charge(laws.len())?;
        budget.charge(NICHE_BODIES + 1)?;
        let mut bodies = Vec::new();
        bodies
            .try_reserve_exact(NICHE_BODIES)
            .map_err(|_| "niche body records allocation failed")?;
        for instance in laws {
            let captured =
                self.capture_niche_comparison_body(instance, &mut budget, false, goal)?;
            budget.phase(GraphPhase::SignatureValidate, captured.inventory)?;
            let body = captured.body;
            budget.record(instance)?;
            if !self.call_signatures.borrow().contains_key(&instance) {
                budget.phase(GraphPhase::SignatureInstantiate, captured.inventory)?;
                budget.phase(GraphPhase::SignatureNormalize, captured.inventory)?;
            }
            let signature = self.call_signature(instance)?;
            let receiver = if instance == primitive {
                schema.primitive
            } else if instance == payload_eq {
                schema.nonzero
            } else {
                original
            };
            if signature.abi() != rustc_abi::ExternAbi::Rust
                || signature.c_variadic()
                || signature.safety() != rustc_hir::Safety::Safe
                || signature.inputs().len() != 2
                || !signature.output().is_bool()
                || !signature.inputs().iter().all(|input| {
                    matches!(input.kind(),
                    ty::Ref(_, child, rustc_hir::Mutability::Not) if *child == receiver)
                })
            {
                return Err("niche law selected full safe Rust signature mismatch".into());
            }
            budget.record(instance)?;
            budget.charge(1)?;
            budget.insert_body(&mut bodies, instance, body)?;
        }
        let types = [original, schema.nonzero, schema.primitive];
        budget.charge(types.len() + 1)?;
        budget.charge(NICHE_PENDING * 2)?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(NICHE_PENDING)
            .map_err(|_| "niche pending allocation failed")?;
        budget.pending(&mut pending, outer, None)?;
        let mut seen = Vec::new();
        seen.try_reserve_exact(NICHE_PENDING)
            .map_err(|_| "niche visited contexts allocation failed")?;
        while !pending.is_empty() {
            budget.charge(1)?;
            let (instance, arithmetic) = pending.pop().unwrap();
            budget.record(instance)?;
            budget.charge(
                laws.len()
                    .saturating_mul(1usize.saturating_add(instance.args.len())),
            )?;
            if laws.contains(&instance) {
                continue;
            }
            budget.charge(
                seen.len()
                    .saturating_mul(2usize.saturating_add(instance.args.len())),
            )?;
            if seen.contains(&(instance, arithmetic)) {
                continue;
            }
            if seen.len() == NICHE_PENDING {
                return Err("niche visited contexts exceed32 records".into());
            }
            budget.record(instance)?;
            seen.push((instance, arithmetic));
            if instance.def_id().krate != core {
                return Err("niche membership transport has non-core selected body".into());
            }
            let captured = self.capture_niche_comparison_body(instance, &mut budget, true, goal)?;
            let family = captured
                .family
                .ok_or("niche transport lacks captured raw family")?;
            let inventory = captured.inventory;
            let body = captured.body;
            if !matches!(
                family,
                templates::PureTemplateFamily::Contains
                    | templates::PureTemplateFamily::ContainsDefault
                    | templates::PureTemplateFamily::ContainsBytes
                    | templates::PureTemplateFamily::IterAny
                    | templates::PureTemplateFamily::ClosureDefault
                    | templates::PureTemplateFamily::ClosureBytes
                    | templates::PureTemplateFamily::SubPrecondition
            ) {
                return Err("niche membership transport reached unsupported family".into());
            }
            budget.phase(GraphPhase::Layout, inventory)?;
            budget.phase(
                GraphPhase::Layout,
                inventory
                    .checked_mul(3)
                    .ok_or("niche layout service bound overflow")?,
            )?;
            self.certify_comparison_layout_constants(&body, &types)?;
            match (family, arithmetic) {
                (
                    templates::PureTemplateFamily::SubPrecondition,
                    Some(CursorArithmetic::SubAfterNonzero),
                ) => {}
                (templates::PureTemplateFamily::SubPrecondition, _) | (_, Some(_)) => {
                    return Err("niche cursor lacks authenticated caller premise".into());
                }
                (_, None) => {}
            }
            budget.phase(GraphPhase::SignatureValidate, inventory)?;
            budget.record(instance)?;
            if matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            ) && !self.call_signatures.borrow().contains_key(&instance)
            {
                budget.phase(GraphPhase::SignatureInstantiate, inventory)?;
                budget.phase(GraphPhase::SignatureNormalize, inventory)?;
            }
            let element =
                self.validate_pure_comparison_instance(instance, family, &body, &types)?;
            if instance == outer && element != Some(original) {
                return Err("niche membership outer original element mismatch".into());
            }
            if family == templates::PureTemplateFamily::ContainsBytes && schema.facts.size == 1 {
                budget.charge(2)?; // New byte-boundary goal branch, independent of old source work.
                match goal {
                    GraphGoal::Law => {
                        return byte_search_source::observe(self, instance, 0, budget.work)?
                            .reject_unverified_search()
                            .and_then(|()| {
                                Err("byte search semantic certificate is unavailable".into())
                            });
                    }
                    GraphGoal::ByteRoute => {
                        budget.record(instance)?;
                        budget.charge(1)?;
                        budget.insert_body(&mut bodies, instance, body)?;
                        return byte_route::boundary(
                            self, original, outer, instance, bodies, budget,
                        )
                        .map(GraphOutcome::Byte);
                    }
                }
            }
            budget.phase(GraphPhase::Edges, inventory)?;
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    if let StatementKind::Assign(assignment) = &statement.kind
                        && let Rvalue::Aggregate(kind, _) = &assignment.1
                        && let AggregateKind::Closure(id, args) = kind.as_ref()
                    {
                        budget.charge(1 + args.len())?;
                        budget.pending(&mut pending, ty::Instance::new_raw(*id, args), None)?;
                    }
                }
                let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                    continue;
                };
                budget.charge(1)?;
                let ty::FnDef(id, args) = func.ty(&body.local_decls, self.tcx).kind() else {
                    return Err("niche transport has non-FnDef selected call".into());
                };
                if id.krate != core {
                    return Err("niche transport has non-core call".into());
                }
                budget.arguments(self.tcx, args.skip_binder())?;
                budget.charge(2)?;
                let selected = self.resolve_function_item(*id, args.skip_binder())?;
                if selected.def_id().krate != core {
                    return Err("niche selected transport call is not original core".into());
                }
                let key = budget.key(selected.def_id())?;
                if family == templates::PureTemplateFamily::SubPrecondition
                    && key == "DefId(core::panicking::panic_nounwind_fmt)"
                {
                    // The complete reference and exact caller cursor guard exclude this edge.
                    continue;
                }
                if family == templates::PureTemplateFamily::ContainsBytes
                    && matches!(
                        key.as_str(),
                        "DefId(core::mem::transmute_copy::precondition_check)"
                            | "DefId(core::slice::raw::from_raw_parts::precondition_check)"
                            | "DefId(core::slice::memchr::memchr)"
                    )
                {
                    // Full matched caller + certified non-byte size prove SIZE == 1 unreachable.
                    continue;
                }
                let arithmetic = if family == templates::PureTemplateFamily::IterAny
                    && key == "DefId(core::num::{impl#11}::unchecked_sub::precondition_check)"
                {
                    budget.phase(GraphPhase::Edges, 16)?;
                    self.certify_cursor_arithmetic(CursorArithmetic::SubAfterNonzero)?;
                    Some(CursorArithmetic::SubAfterNonzero)
                } else {
                    None
                };
                budget.pending(&mut pending, selected, arithmetic)?;
            }
            budget.record(instance)?;
            budget.charge(1)?;
            budget.insert_body(&mut bodies, instance, body)?;
        }
        budget.charge(bodies.len() * 4)?;
        for (instance, body) in &bodies {
            budget.record(*instance)?;
            if !self
                .bodies
                .borrow()
                .get(instance)
                .is_some_and(|current| std::rc::Rc::ptr_eq(current, body))
            {
                return Err("niche dependency was replaced before law evaluation".into());
            }
        }
        budget.charge(2)?;
        let roots = |original| {
            [0, 1].map(|side| TraceValue::Origin {
                original,
                side,
                refs: 1,
                variant: None,
            })
        };
        budget.charge(3 + 1)?;
        let (relation, law_work, observed) = {
            let mut law = LawTrace {
                tcx: self.tcx,
                engine: Some(self),
                graph: Some(&mut budget),
                original,
                payload: schema.nonzero,
                primitive: schema.primitive,
                tags: None,
                equality: 0xaa,
                completed: Vec::new(),
                bodies: &bodies,
                work: 0,
                limit: NICHE_ADMISSION_LAW_WORK,
                observed: LawWork::default(),
                active: [None; 16],
            };
            for (instance, receiver) in
                [(primitive, schema.primitive), (payload_eq, schema.nonzero)]
            {
                let called = law.call(instance, roots(receiver), 0);
                let relation = called.map_err(|error| law.failure(error))?;
                if relation != 0xaa {
                    return Err("niche payload law does not preserve equality".into());
                }
                law.charge_materialization(4)?;
                law.completed
                    .try_reserve_exact(1)
                    .map_err(|_| "niche completed law allocation resource failure")?;
                law.completed.push(CompletedTrace {
                    instance,
                    original: receiver,
                    relation,
                    body: std::rc::Rc::downgrade(
                        law.graph
                            .as_deref_mut()
                            .unwrap()
                            .lookup_body(&bodies, instance)?
                            .ok_or("niche completed body missing")?,
                    ),
                });
            }
            let mut relation = 0;
            for left in 0..2 {
                for right in 0..2 {
                    law.tags = Some([left, right]);
                    let called = law.call(eq_instance, roots(original), 0);
                    let value = called.map_err(|error| law.failure(error))?;
                    let expected = if left != right {
                        0
                    } else if left == 0 {
                        0xff
                    } else {
                        0xaa
                    };
                    if value != expected {
                        return Err("niche tag/payload equality law differs".into());
                    }
                    relation |= value & (3 << (2 * (2 * left + right)));
                }
            }
            law.charge_materialization(4)?;
            law.completed
                .try_reserve_exact(1)
                .map_err(|_| "niche completed law allocation resource failure")?;
            law.completed.push(CompletedTrace {
                instance: eq_instance,
                original,
                relation,
                body: std::rc::Rc::downgrade(
                    law.graph
                        .as_deref_mut()
                        .unwrap()
                        .lookup_body(&bodies, eq_instance)?
                        .ok_or("niche completed Eq body missing")?,
                ),
            });
            law.tags = None;
            let called = law.call(ne_instance, roots(original), 0);
            if called.map_err(|error| law.failure(error))? != !relation {
                return Err("niche actual Ne does not negate actual Eq".into());
            }
            law.charge(1)?;
            (relation, law.work, law.observed)
        };
        budget.charge(bodies.len())?;
        let mut witnesses = Vec::new();
        witnesses
            .try_reserve_exact(bodies.len())
            .map_err(|_| "niche weak witness allocation failed")?;
        budget.charge(bodies.len())?;
        for (instance, body) in &bodies {
            budget.record(*instance)?;
            budget.charge(2)?;
            witnesses.push((*instance, std::rc::Rc::downgrade(body)));
        }
        budget.charge(bodies.len() * 4)?;
        // Limit1 and actual observation3 field copies are publication work.
        budget.charge(4)?;
        // Distinct validation: limit read/compare2, total reads/bounds4, and
        // semantic/materialization reads, checked sum and equality4.
        budget.charge(10)?;
        // Schema construction performs two identity renders, one Option-name render and
        // two variant-name services. Each has a prepaid128-byte returned-name bound.
        // Certificate String fields move, rather than clone, into the retained schema.
        budget.charge(5 * (128 + 1) + 24)?;
        let membership_schema = super::schema(self.tcx, schema)?;
        budget.charge(48)?; // Separate sixteen name length/bound/add validation visits.
        membership_schema.membership_match_work(&membership_schema)?;
        // Move the actual admission-local meter and schema into one-shot application.
        budget.charge(44 + 1)?;
        budget.charge(5)?; // Actual new boxed outcome allocation/move/release services.
        let result = CheckedNicheLaw {
            engine: self,
            original,
            relation,
            bodies: witnesses,
            graph_work: budget.work,
            law_work,
            law_limit: NICHE_ADMISSION_LAW_WORK,
            observed,
            application: Some(budget),
            membership_schema,
        };
        result.validate(self)?;
        Ok(GraphOutcome::Law(Box::new(result)))
    }
}

#[cfg(test)]
#[path = "nonzero_niche_comparisons_probe.rs"]
mod probe;

const NICHE_APPLICATION_WORK: usize = 2048;

struct MembershipApplication<'tcx> {
    graph: GraphBudget<'tcx>,
    work: usize,
}

impl MembershipApplication<'_> {
    fn charge(&mut self, count: usize) -> Result<(), String> {
        let next = self
            .work
            .checked_add(count)
            .ok_or("niche application work overflow")?;
        if next > NICHE_APPLICATION_WORK {
            #[cfg(test)]
            eprintln!(
                "public niche application cutoff: work={} charge={count} attempted={next} \
                 graph={} limit={NICHE_APPLICATION_WORK}",
                self.work, self.graph.work
            );
            return Err(format!(
                "niche application exceeds NICHE_APPLICATION_WORK policy: \
                 limit={NICHE_APPLICATION_WORK} attempted={next} previous={} charge={count}",
                self.work
            ));
        }
        self.graph.charge(count)?;
        self.work = next;
        Ok(())
    }
}

// Work backends are counters only, never original-body, source or Memory authority.
pub(in crate::proof) use byte_search_source::{CallerSource, Work as ByteWork, caller_source};

enum EncodingWork<'a, 'tcx> {
    Application(&'a mut MembershipApplication<'tcx>),
    Source(&'a Engine<'tcx>, &'a mut ByteWork),
}

impl EncodingWork<'_, '_> {
    fn charge(&mut self, count: usize) -> Result<(), String> {
        match self {
            Self::Application(application) => {
                application.charge(2)?; // Actual new dispatch and separate payment call.
                application.charge(count)
            }
            Self::Source(engine, work) => {
                work.charge(2)
                    .map_err(|error| engine.categorized_error(error.category, error.reason))?;
                work.charge(count)
                    .map_err(|error| engine.categorized_error(error.category, error.reason))
            }
        }
    }

    fn condition_copy(&mut self, count: usize) -> Result<(), String> {
        self.charge(
            count
                .checked_add(2)
                .ok_or("niche condition copy overflow")?,
        )
    }
}

enum MembershipNeedle<'a> {
    None,
    Some(&'a Term),
    Symbolic { tag: &'a Term, raw: &'a Term },
}

impl<'tcx> Engine<'tcx> {
    // Original compiler descriptor plus exact codec; no law/source/Memory permit is issued.
    pub(in crate::proof) fn readonly_byte_encoding(
        &self,
        original: Ty<'tcx>,
        slice: &Value,
        needle: &Value,
        conditions: &[Term],
        work: &mut ByteWork,
    ) -> Result<Term, String> {
        work.charge(16)
            .map_err(|error| self.categorized_error(error.category, error.reason))?;
        let schema = self.niche_membership_descriptor(original, slice)?;
        if schema.payload_bits() != 8 || schema.item_bytes() != 1 || schema.payload_signed() {
            return Err("byte relation requires its exact unsigned byte encoding".into());
        }
        work.charge(3)
            .map_err(|error| self.categorized_error(error.category, error.reason))?;
        let mut meter = EncodingWork::Source(self, work);
        let parsed = self.parse_niche_needle(&mut meter, schema, needle)?;
        self.encode_niche_needle(&mut meter, schema, parsed, conditions)
    }

    pub(super) fn checked_niche_membership(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
    ) -> Result<Term, String> {
        state.flow.require_unarmed()?;
        let mut law = self.check_niche_comparison_law(original, instance)?;
        self.apply_niche_membership(&mut law, slice, needle, state)
    }

    pub(super) fn checked_prepared_byte_membership(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
        prior: usize,
    ) -> Result<Term, String> {
        state.flow.require_unarmed()?;
        let mut law = self.check_niche_comparison_law_with_work(original, instance, prior)?;
        self.apply_niche_membership(&mut law, slice, needle, state)
    }

    fn apply_niche_membership(
        &self,
        law: &mut CheckedNicheLaw<'_, 'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
    ) -> Result<Term, String> {
        state.flow.require_unarmed()?;
        let graph = law
            .application
            .take()
            .ok_or("niche law application already consumed")?;
        if graph.work != law.graph_work || law.relation != 0x83 {
            return Err("niche one-shot handoff total/relation differs".into());
        }
        let mut application = MembershipApplication { graph, work: 0 };
        // Distinct policy and witness-validation passes; their existing fees are not credit.
        application.charge(10 + law.bodies.len())?;
        for (instance, _) in &law.bodies {
            application.charge(1 + instance.args.len() + 4)?;
        }
        law.validate(self)?;
        application.charge(12 + 3)?;
        let current_schema = self.niche_membership_descriptor(law.original, slice)?;
        // Pay the separate sixteen name length/bound/add planning visits before evaluation.
        application.charge(48)?;
        application.charge(current_schema.membership_match_work(&law.membership_schema)?)?;
        if !current_schema.membership_matches(&law.membership_schema) {
            return Err("niche current descriptor schema differs from issued law".into());
        }
        let schema = &law.membership_schema;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        application.charge(12)?;
        let Value::CompositeSlice { length, leaves, .. } = slice else {
            unreachable!()
        };
        let Value::Int {
            expression: length,
            bits: width,
            signed: false,
        } = length.as_ref()
        else {
            return Err("niche current length shape differs".into());
        };
        let [column] = leaves.as_slice() else {
            return Err("niche current descriptor must have one column".into());
        };
        if *width != bits
            || length.sort() != &Sort::BitVec(bits)
            || !length.belongs_to(&self.terms)
            || column.sort()
                != &Sort::Array(
                    Box::new(Sort::BitVec(bits)),
                    Box::new(Sort::BitVec(schema.payload_bits())),
                )
            || !column.belongs_to(&self.terms)
            || !matches!(bits, 32 | 64)
        {
            return Err("niche current length/column context differs".into());
        }
        self.niche_memory_clone_service(&mut application, state)?;
        application.charge(2)?; // Actual temporary encoding meter construction.
        let parsed = self.parse_niche_needle(
            &mut EncodingWork::Application(&mut application),
            schema,
            needle,
        )?;
        // Actual canonical descriptor is checked; selecting its raw column removes the old
        // nested Value/name reconstruction, and the retained schema removes recertification.
        application.charge(6)?;
        application.charge(3)?;
        let item_bytes = schema.item_bytes();
        let denominator = item_bytes.checked_mul(2).ok_or("niche extent overflow")?;
        let maximum = (u128::MAX >> (128 - bits)) / u128::from(denominator);
        let safe = self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(maximum, bits)?],
        )?;
        application.charge(2)?;
        let outside = self.terms.apply(Op::Not, &[safe])?;
        application.charge(2)?;
        self.niche_application_refuse_if(
            &mut EncodingWork::Application(&mut application),
            &state.conditions,
            outside,
            "niche current length lacks original allocation extent",
        )?;
        application.charge(2)?; // Actual separate encoding meter construction.
        let encoded = self.encode_niche_needle(
            &mut EncodingWork::Application(&mut application),
            schema,
            parsed,
            &state.conditions,
        )?;
        // Index, Select, equality, in-range, conjunction and existential service; argument
        // copies are included in their fixed small caller-visible node services.
        application.charge(21)?;
        let index = self.fresh(Sort::BitVec(bits));
        let raw = self
            .terms
            .apply(Op::Select, &[column.clone(), index.clone()])?;
        let equal = self.terms.apply(Op::Equal, &[raw, encoded])?;
        let inside = self
            .terms
            .apply(Op::BvUnsignedLt, &[index.clone(), length.clone()])?;
        let predicate = self.terms.apply(Op::And, &[inside, equal])?;
        #[cfg(test)]
        eprintln!(
            "public niche application completed: work={} graph={} limit={NICHE_APPLICATION_WORK}",
            application.work, application.graph.work
        );
        self.terms
            .quantify(miren::smt::Quantifier::Exists, &index, &predicate)
    }

    fn niche_application_refuse_if(
        &self,
        application: &mut EncodingWork<'_, 'tcx>,
        conditions: &[Term],
        invalid: Term,
        reason: &str,
    ) -> Result<(), String> {
        application.condition_copy(conditions.len())?;
        let mut query = Vec::with_capacity(conditions.len() + 1);
        query.extend_from_slice(conditions);
        query.push(invalid);
        if self.feasible(&query)? {
            return Err(reason.into());
        }
        Ok(())
    }

    fn niche_memory_clone_service(
        &self,
        application: &mut MembershipApplication<'tcx>,
        state: &State,
    ) -> Result<(), String> {
        application.charge(12)?; // Actual Memory header/Rc/empty collection copies.
        if !state.memory.startup_values.is_empty() || !state.memory.incoming_byte_roots.is_empty() {
            return Err("niche startup/byte snapshot clone is unsupported".into());
        }
        let entries = state.memory.missing_places.entries();
        application.charge(entries.len())?; // Extent validation pass, distinct from clone.
        for (_, path) in entries {
            if path.len() > 16 {
                return Err("niche Memory mask path exceeds16".into());
            }
            application.charge(3 + path.len())?; // Owner, path header/allocation and path copies.
        }
        application.charge(state.memory.isolated_static_types.len().saturating_mul(2) + 1)?;
        application.charge(state.memory.startup_overwritten.len() + 1)?;
        application.charge(state.memory.static_uninitialized.len() + 1)?;
        application.charge(state.conditions.len() + 1)?; // Final Return's condition Vec clone.
        Ok(())
    }

    fn niche_name_service(
        &self,
        application: &mut EncodingWork<'_, 'tcx>,
        actual: &str,
        expected: &str,
    ) -> Result<(), String> {
        if actual.len() > 128 || expected.len() > 128 {
            return Err("niche value name exceeds128 bytes".into());
        }
        application.charge(actual.len() + expected.len() + 1)?;
        if actual != expected {
            return Err("niche original storage name differs".into());
        }
        Ok(())
    }

    fn parse_niche_variant<'a>(
        &self,
        application: &mut EncodingWork<'_, 'tcx>,
        schema: &Schema,
        value: &'a Value,
        expected: usize,
    ) -> Result<Option<&'a Term>, String> {
        application.charge(6)?;
        let Value::Adt {
            name,
            variant,
            is_option: true,
            discriminant,
            fields,
        } = value
        else {
            return Err("niche original Option shape differs".into());
        };
        self.niche_name_service(application, name, &schema.name)?;
        if *variant != expected || *discriminant != schema.tags[expected] {
            return Err("niche Option variant/tag differs".into());
        }
        if expected != schema.payload_variant {
            if !fields.is_empty() {
                return Err("niche None carries fields".into());
            }
            return Ok(None);
        }
        application.charge(12)?;
        let [
            (
                name,
                Value::Adt {
                    name: outer,
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields,
                },
            ),
        ] = fields.as_slice()
        else {
            return Err("niche Some outer shape differs".into());
        };
        self.niche_name_service(application, name, &schema.payload_field)?;
        self.niche_name_service(application, outer, &schema.outer_name)?;
        let [
            (
                name,
                Value::Adt {
                    name: inner,
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields,
                },
            ),
        ] = fields.as_slice()
        else {
            return Err("niche Some inner shape differs".into());
        };
        self.niche_name_service(application, name, &schema.outer_field)?;
        self.niche_name_service(application, inner, &schema.inner_name)?;
        let [
            (
                name,
                Value::Int {
                    expression,
                    bits,
                    signed,
                },
            ),
        ] = fields.as_slice()
        else {
            return Err("niche Some scalar shape differs".into());
        };
        self.niche_name_service(application, name, &schema.inner_field)?;
        application.charge(2)?; // Derive authenticated payload sign and compare scalar metadata.
        if *bits != schema.payload_bits()
            || *signed != schema.payload_signed()
            || expression.sort() != &Sort::BitVec(schema.payload_bits())
            || !expression.belongs_to(&self.terms)
        {
            return Err("niche Some scalar context differs".into());
        }
        Ok(Some(expression))
    }

    fn parse_niche_needle<'a>(
        &self,
        application: &mut EncodingWork<'_, 'tcx>,
        schema: &Schema,
        value: &'a Value,
    ) -> Result<MembershipNeedle<'a>, String> {
        application.charge(4)?;
        match value {
            Value::Adt { variant, .. } if *variant < 2 => Ok(
                match self.parse_niche_variant(application, schema, value, *variant)? {
                    Some(raw) => MembershipNeedle::Some(raw),
                    None => MembershipNeedle::None,
                },
            ),
            Value::Enum {
                discriminant,
                variants,
                is_option: true,
            } if variants.len() == 2 => {
                let Value::Int {
                    expression: tag,
                    bits,
                    signed,
                } = discriminant.as_ref()
                else {
                    return Err("niche symbolic tag shape differs".into());
                };
                if *bits != schema.bits
                    || *signed != schema.signed
                    || tag.sort() != &Sort::BitVec(schema.bits)
                    || !tag.belongs_to(&self.terms)
                {
                    return Err("niche symbolic tag context differs".into());
                }
                self.parse_niche_variant(application, schema, &variants[0], 0)?;
                let raw = self
                    .parse_niche_variant(application, schema, &variants[1], 1)?
                    .ok_or("niche symbolic Some payload missing")?;
                Ok(MembershipNeedle::Symbolic { tag, raw })
            }
            _ => Err("niche original needle shape differs".into()),
        }
    }

    fn encode_niche_needle(
        &self,
        application: &mut EncodingWork<'_, 'tcx>,
        schema: &Schema,
        needle: MembershipNeedle<'_>,
        conditions: &[Term],
    ) -> Result<Term, String> {
        match needle {
            MembershipNeedle::None => {
                application.charge(1)?;
                self.terms.bit_vector(0, schema.payload_bits())
            }
            MembershipNeedle::Some(raw) => {
                application.charge(5)?;
                let zero = self.terms.apply(
                    Op::Equal,
                    &[
                        raw.clone(),
                        self.terms.bit_vector(0, schema.payload_bits())?,
                    ],
                )?;
                self.niche_application_refuse_if(
                    application,
                    conditions,
                    zero,
                    "niche Some lacks proved nonzero validity",
                )?;
                application.charge(1)?;
                Ok(raw.clone())
            }
            MembershipNeedle::Symbolic { tag, raw } => {
                application.charge(15)?;
                let none = self.terms.apply(
                    Op::Equal,
                    &[
                        tag.clone(),
                        self.terms.bit_vector(schema.tags[0], schema.bits)?,
                    ],
                )?;
                let some = self.terms.apply(
                    Op::Equal,
                    &[
                        tag.clone(),
                        self.terms.bit_vector(schema.tags[1], schema.bits)?,
                    ],
                )?;
                let valid = self.terms.apply(Op::Or, &[none, some.clone()])?;
                let invalid = self.terms.apply(Op::Not, &[valid])?;
                self.niche_application_refuse_if(
                    application,
                    conditions,
                    invalid,
                    "niche symbolic tag lacks proved validity",
                )?;
                application.charge(8)?;
                let zero = self.terms.apply(
                    Op::Equal,
                    &[
                        raw.clone(),
                        self.terms.bit_vector(0, schema.payload_bits())?,
                    ],
                )?;
                let invalid_payload = self.terms.apply(Op::And, &[some.clone(), zero])?;
                self.niche_application_refuse_if(
                    application,
                    conditions,
                    invalid_payload,
                    "niche active Some lacks proved nonzero validity",
                )?;
                application.charge(5)?;
                self.terms.apply(
                    Op::Ite,
                    &[
                        some,
                        raw.clone(),
                        self.terms.bit_vector(0, schema.payload_bits())?,
                    ],
                )
            }
        }
    }
}

#[cfg(test)]
pub(super) fn signed_current_comparison_control<'tcx>(
    engine: &Engine<'tcx>,
    original: Ty<'tcx>,
    outer: ty::Instance<'tcx>,
) {
    let law = engine.check_niche_comparison_law(original, outer).unwrap();
    law.validate(engine).unwrap();
    let (instance, _) = law.bodies.first().unwrap();
    let instance = *instance;
    let previous = engine.instantiated_body(instance).unwrap();
    let mut changed = previous.as_ref().clone();
    changed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
        .terminator_mut()
        .kind = TerminatorKind::Unreachable;
    engine
        .bodies
        .borrow_mut()
        .insert(instance, std::rc::Rc::new(changed));
    assert_eq!(
        law.validate(engine).unwrap_err(),
        "niche law selected Engine body was replaced or evicted"
    );
    engine.bodies.borrow_mut().insert(instance, previous);
    law.validate(engine).unwrap();
}

#[cfg(test)]
#[path = "nonzero_niche_comparisons/byte_route_probe.rs"]
mod byte_route_probe;

#[path = "nonzero_niche_comparisons/byte_transport.rs"]
mod byte_transport;

#[cfg(test)]
#[path = "nonzero_niche_comparisons/byte_transport_probe.rs"]
mod byte_transport_probe;
