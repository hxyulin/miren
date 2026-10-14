//! Paid general Rust source authentication; metadata grants no storage or execution rights.
use super::*;
use rustc_middle::mir::{MirPhase, RuntimePhase, StmtDebugInfos};
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
use std::ops::ControlFlow;
use std::rc::Rc;

pub(super) struct Evidence<'tcx> {
    instance: ty::Instance<'tcx>,
    raw: &'tcx Body<'tcx>,
    current: Rc<Body<'tcx>>,
    context: Term,
    signature: ty::PolyFnSig<'tcx>,
}
fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    engine.niche_plan_work(count)
}

struct LocalTypes<'a, 'tcx> {
    engine: &'a mut Engine<'tcx>,
    seen: Vec<(Ty<'tcx>, usize)>,
    nodes: usize,
    depth: usize,
    error: Option<String>,
}
impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for LocalTypes<'_, 'tcx> {
    type Result = ControlFlow<()>;
    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        if let Err(error) = pay(self.engine, self.seen.len() + 4) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        if self.depth >= MAX_INPUT_DEPTH {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "Rust source local type depth exceeds16".into(),
            ));
            return ControlFlow::Break(());
        }
        // Only successful subtrees are memoized. Reuse is restricted to the same or a
        // shallower context, so validated descendants cannot bypass the depth16 bound.
        if self
            .seen
            .iter()
            .any(|(ty, depth)| *ty == original && self.depth <= *depth)
        {
            return ControlFlow::Continue(());
        }
        if self.nodes >= MAX_INPUT_VALUES {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "Rust source local type graph exceeds512".into(),
            ));
            return ControlFlow::Break(());
        }
        if matches!(
            original.kind(),
            ty::Coroutine(..) | ty::CoroutineClosure(..) | ty::CoroutineWitness(..)
        ) {
            self.error =
                Some("Rust source coroutine-containing locals need paid flattening".into());
            return ControlFlow::Break(());
        }
        if let Err(error) = pay(self.engine, 8) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        let width = match original.kind() {
            ty::Tuple(fields) => fields.len(),
            ty::Adt(_, args) | ty::Closure(_, args) => args.len(),
            ty::FnDef(_, args) => {
                let count = args.bound_vars().len();
                if count > MAX_INPUT_VALUES {
                    self.error = Some("Rust source function binder exceeds512".into());
                    return ControlFlow::Break(());
                }
                if let Err(error) = pay(self.engine, count + 4) {
                    self.error = Some(error);
                    return ControlFlow::Break(());
                }
                args.skip_binder().len()
            }
            ty::Alias(_, alias) => alias.args.len(),
            ty::FnPtr(signature, _) => {
                let count = signature.bound_vars().len();
                if count > MAX_INPUT_VALUES {
                    self.error = Some("Rust source local signature binder exceeds512".into());
                    return ControlFlow::Break(());
                }
                if let Err(error) = pay(self.engine, count + 4) {
                    self.error = Some(error);
                    return ControlFlow::Break(());
                }
                signature.skip_binder().inputs_and_output.len()
            }
            ty::Dynamic(predicates, ..) => {
                if predicates.len() > MAX_INPUT_VALUES {
                    self.error = Some("Rust source local predicate vector exceeds512".into());
                    return ControlFlow::Break(());
                }
                if let Err(error) = pay(self.engine, predicates.len() + 4) {
                    self.error = Some(error);
                    return ControlFlow::Break(());
                }
                for predicate in predicates.iter() {
                    let count = predicate.bound_vars().len();
                    if count > MAX_INPUT_VALUES {
                        self.error = Some("Rust source predicate binder exceeds512".into());
                        return ControlFlow::Break(());
                    }
                    if let Err(error) = pay(self.engine, count + 4) {
                        self.error = Some(error);
                        return ControlFlow::Break(());
                    }
                    let arguments = match predicate.skip_binder() {
                        ty::ExistentialPredicate::Trait(value) => value.args.len(),
                        ty::ExistentialPredicate::Projection(value) => value.args.len(),
                        ty::ExistentialPredicate::AutoTrait(_) => 0,
                    };
                    if arguments > MAX_INPUT_VALUES {
                        self.error =
                            Some("Rust source existential argument vector exceeds512".into());
                        return ControlFlow::Break(());
                    }
                    if let Err(error) = pay(self.engine, arguments + 4) {
                        self.error = Some(error);
                        return ControlFlow::Break(());
                    }
                }
                predicates.len()
            }
            ty::UnsafeBinder(_) | ty::Pat(..) => {
                self.error =
                    Some("Rust source local binder/pattern type needs bounded policy".into());
                return ControlFlow::Break(());
            }
            _ => 0,
        };
        if width > MAX_INPUT_VALUES {
            self.error = Some("Rust source local generic/type vector exceeds512".into());
            return ControlFlow::Break(());
        }
        if let Err(error) = pay(self.engine, width + 4) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        self.nodes += 1;
        self.depth += 1;
        let result = original.super_visit_with(self);
        self.depth -= 1;
        if result.is_continue() {
            if let Err(error) = pay(self.engine, self.seen.len() + 8) {
                self.error = Some(error);
                return ControlFlow::Break(());
            }
            if let Some((_, depth)) = self.seen.iter_mut().find(|(ty, _)| *ty == original) {
                *depth = (*depth).max(self.depth);
            } else {
                self.seen.push((original, self.depth));
            }
        }
        result
    }
    fn visit_region(&mut self, _: ty::Region<'tcx>) -> Self::Result {
        if let Err(error) = pay(self.engine, 4) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        if self.nodes >= MAX_INPUT_VALUES || self.depth >= MAX_INPUT_DEPTH {
            self.error = Some("Rust source local lifetime graph exceeds512/depth16".into());
            return ControlFlow::Break(());
        }
        self.nodes += 1;
        ControlFlow::Continue(())
    }
    fn visit_const(&mut self, value: ty::Const<'tcx>) -> Self::Result {
        if let Err(error) = pay(self.engine, 4) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        if self.nodes >= MAX_INPUT_VALUES || self.depth >= MAX_INPUT_DEPTH {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "Rust source local const graph exceeds512/depth16".into(),
            ));
            return ControlFlow::Break(());
        }
        let arguments = match value.kind() {
            ty::ConstKind::Alias(_, alias) => alias.args.len(),
            ty::ConstKind::Expr(_) => {
                self.error = Some(
                    "Rust source local const expression needs bounded arguments policy".into(),
                );
                return ControlFlow::Break(());
            }
            _ => 0,
        };
        if arguments > MAX_INPUT_VALUES {
            self.error = Some("Rust source const alias argument vector exceeds512".into());
            return ControlFlow::Break(());
        }
        if let Err(error) = pay(self.engine, arguments + 4) {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        self.nodes += 1;
        self.depth += 1;
        let result = value.super_visit_with(self);
        self.depth -= 1;
        result
    }
}
fn local_types<'tcx>(engine: &mut Engine<'tcx>, body: &Body<'tcx>) -> Result<(), String> {
    if body.local_decls.len() > MAX_INPUT_VALUES {
        return Err("Rust source local type catalogue exceeds512".into());
    }
    pay(engine, body.local_decls.len() + 8)?;
    let mut plan = LocalTypes {
        engine,
        seen: Vec::new(),
        nodes: 0,
        depth: 0,
        error: None,
    };
    for local in &body.local_decls {
        if local.ty.visit_with(&mut plan).is_break() {
            break;
        }
    }
    plan.error.map_or(Ok(()), Err)
}

pub(super) fn authenticated_item<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<Rc<Body<'tcx>>, String> {
    pay(engine, 2)?;
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(
            engine.tcx.def_kind(instance.def_id()),
            DefKind::Fn | DefKind::AssocFn
        )
        || !engine.tcx.is_mir_available(instance.def_id())
    {
        return Err(engine.categorized_error(
            UnknownCategory::MissingCompilerEvidence,
            engine.missing_body_reason(instance.def_id()),
        ));
    }
    let signature_count = engine
        .call_signatures
        .try_borrow()
        .map_err(|_| "Rust source signature registry borrowed")?
        .len();
    if signature_count > 256 {
        return Err("Rust source signature catalogue exceeds ordinary256 cap".into());
    }
    pay(engine, 4)?;
    let raw = engine.tcx.instance_mir(instance.def);
    identity(raw, instance)?;
    let signature = mutable_hierarchy::products::niche_codec_signature(engine, instance)?;
    let body_count = engine
        .bodies
        .try_borrow()
        .map_err(|_| "Rust source Body registry borrowed")?
        .len();
    if body_count > 128 {
        return Err("Rust source Body catalogue exceeds ordinary128 cap".into());
    }
    pay(engine, 3 * 128 + 32)?;
    if engine.compiler_sources.len() > MAX_INPUT_VALUES {
        return Err("Rust source catalogue exceeds512".into());
    }
    pay(engine, engine.compiler_sources.len() + 3)?;
    if let Some(evidence) = engine
        .compiler_sources
        .iter()
        .find(|evidence| evidence.instance == instance)
    {
        let cached = engine
            .bodies
            .try_borrow()
            .map_err(|_| "Rust source Body registry borrowed")?;
        if !std::ptr::eq(raw, evidence.raw)
            || !evidence.context.belongs_to(&engine.terms)
            || evidence.signature != signature
            || cached
                .get(&instance)
                .is_none_or(|current| !Rc::ptr_eq(current, &evidence.current))
        {
            return Err(
                "Rust compiler source authenticated compiler/current Body cache was replaced"
                    .into(),
            );
        }
        identity(&evidence.current, instance)?;
        return Ok(evidence.current.clone());
    }

    let owned = array_iterator_constructors::compiler_source_body_clone_work(engine, raw)?;
    local_types(engine, raw)?;
    let cached = engine
        .bodies
        .try_borrow()
        .map_err(|_| "Rust source Body registry borrowed")?
        .get(&instance)
        .cloned();
    let (current, staged_places) = match cached {
        Some(current) => (current, None),
        None => {
            pay(engine, owned)?; // Actual owned compiler Body clone.
            pay(engine, owned)?; // Distinct normalization/fold allowance.
            let current = Rc::new(engine.normalized_compiler_body(instance)?);
            (current, Some(Vec::new()))
        }
    };
    identity(&current, instance)?;
    // Actual current cache contents are mutable. Establish cardinality before return_ty or
    // parameter-local indexing, even when a corrupted Rc preserves the original source ID.
    if current.local_decls.is_empty()
        || current.local_decls.len() <= current.arg_count
        || raw.local_decls.len() != current.local_decls.len()
        || raw.arg_count != current.arg_count
        || raw.basic_blocks.len() != current.basic_blocks.len()
    {
        return Err("Rust compiler source current local/block cardinality differs".into());
    }
    let current_owned =
        array_iterator_constructors::compiler_source_body_clone_work(engine, &current)?;
    local_types(engine, &current)?;
    pay(engine, current_owned)?; // Full borrowed current equality inventory, not another clone.
    let arguments = signature.skip_binder().inputs_and_output.len();
    pay(engine, arguments * 2 + signature.bound_vars().len() + 16)?;
    let callable = engine.tcx.instantiate_bound_regions_with_erased(signature);
    pay(engine, arguments * 4 + 16)?;
    if current.arg_count != callable.inputs().len()
        || current.return_ty() != callable.output()
        || current
            .args_iter()
            .zip(callable.inputs())
            .any(|(local, expected)| {
                engine
                    .tcx
                    .erase_and_anonymize_regions(current.local_decls[local].ty)
                    != *expected
            })
    {
        return Err("Rust source current Body/full callable signature differs".into());
    }
    if raw.phase != current.phase
        || raw.pass_count != current.pass_count
        || raw.is_polymorphic != current.is_polymorphic
        || raw.injection_phase != current.injection_phase
        || current.coverage_early_info.is_some()
        || current.coverage_mir_info.is_some()
        || raw.arg_count != current.arg_count
        || raw.span != current.span
        || raw.local_decls.len() != current.local_decls.len()
        || raw.basic_blocks.len() != current.basic_blocks.len()
        || raw.source_scopes.len() != current.source_scopes.len()
        || raw.var_debug_info.len() != current.var_debug_info.len()
        || current.coroutine.is_some()
        || current.tainted_by_errors.is_some()
        || current.spread_arg.is_some()
        || !current.user_type_annotations.is_empty()
    {
        return Err("Rust compiler source borrowed original/current header differs".into());
    }
    for (original, actual) in raw.local_decls.iter().zip(&current.local_decls) {
        pay(engine, 3)?;
        let local_info = matches!(
            (&original.local_info, &actual.local_info),
            (
                rustc_middle::mir::ClearCrossCrate::Clear,
                rustc_middle::mir::ClearCrossCrate::Clear
            )
        );
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.ty),
            )
            .map_err(|error| {
                format!("Rust compiler source original local normalization failed: {error:?}")
            })?;
        if normalized != actual.ty
            || original.mutability != actual.mutability
            || original.source_info != actual.source_info
            || actual.user_ty.is_some()
            || !local_info
        {
            return Err("Rust compiler source normalized original/current local differs".into());
        }
    }
    for (original, actual) in raw.source_scopes.iter().zip(&current.source_scopes) {
        pay(engine, 5)?;
        pay(engine, 5)?;
        pay(engine, 5)?; // clone, fold, comparison are separate.
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("Rust compiler source original scope normalization failed: {error:?}")
            })?;
        if normalized.span != actual.span
            || normalized.parent_scope != actual.parent_scope
            || normalized.inlined != actual.inlined
            || normalized.inlined_parent_scope != actual.inlined_parent_scope
            || !match (&normalized.local_data, &actual.local_data) {
                (
                    rustc_middle::mir::ClearCrossCrate::Clear,
                    rustc_middle::mir::ClearCrossCrate::Clear,
                ) => true,
                (
                    rustc_middle::mir::ClearCrossCrate::Set(a),
                    rustc_middle::mir::ClearCrossCrate::Set(b),
                ) => a.lint_root == b.lint_root,
                _ => false,
            }
        {
            return Err("Rust compiler source original/current source scope differs".into());
        }
    }
    for (original, actual) in raw.var_debug_info.iter().zip(&current.var_debug_info) {
        let owned = array_iterator_constructors::compiler_source_variable_work(engine, original)?;
        pay(engine, owned)?;
        pay(engine, owned)?;
        pay(engine, 5)?;
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("Rust compiler source original debug normalization failed: {error:?}")
            })?;
        let composite = match (&normalized.composite, &actual.composite) {
            (None, None) => true,
            (Some(a), Some(b)) => a.ty == b.ty && a.projection == b.projection,
            _ => false,
        };
        let value = match (&normalized.value, &actual.value) {
            (VarDebugInfoContents::Place(a), VarDebugInfoContents::Place(b)) => a == b,
            (VarDebugInfoContents::Const(a), VarDebugInfoContents::Const(b)) => a == b,
            _ => false,
        };
        if normalized.name != actual.name
            || normalized.source_info != actual.source_info
            || normalized.argument_index != actual.argument_index
            || !composite
            || !value
        {
            return Err("Rust compiler source original/current debug variable differs".into());
        }
    }
    if raw.required_consts.as_ref().map(Vec::len) != current.required_consts.as_ref().map(Vec::len)
        || raw.mentioned_items.as_ref().map(Vec::len)
            != current.mentioned_items.as_ref().map(Vec::len)
    {
        return Err("Rust compiler source original/current auxiliary vectors differ".into());
    }
    if let (Some(original), Some(actual)) = (&raw.required_consts, &current.required_consts) {
        for (original, actual) in original.iter().zip(actual) {
            pay(engine, 3)?;
            pay(engine, 3)?;
            pay(engine, 3)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, *original),
                )
                .map_err(|error| {
                    format!(
                        "Rust compiler source required constant normalization failed: {error:?}"
                    )
                })?;
            if normalized != *actual {
                return Err(
                    "Rust compiler source original/current required constant differs".into(),
                );
            }
        }
    }
    if let (Some(original), Some(actual)) = (&raw.mentioned_items, &current.mentioned_items) {
        for (original, actual) in original.iter().zip(actual) {
            pay(engine, 5)?;
            pay(engine, 5)?;
            pay(engine, 3)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, *original),
                )
                .map_err(|error| {
                    format!("Rust compiler source mentioned item normalization failed: {error:?}")
                })?;
            if normalized != *actual {
                return Err("Rust compiler source original/current mentioned item differs".into());
            }
        }
    }
    for (original, actual) in raw.basic_blocks.iter().zip(current.basic_blocks.iter()) {
        pay(engine, 4)?;
        if original.is_cleanup != actual.is_cleanup
            || original.statements.len() != actual.statements.len()
            || !debug_equal(
                engine,
                &original.after_last_stmt_debuginfos,
                &actual.after_last_stmt_debuginfos,
            )?
        {
            return Err("Rust compiler source original/current block differs".into());
        }
        for (original, actual) in original.statements.iter().zip(&actual.statements) {
            let owned =
                array_iterator_constructors::compiler_source_statement_work(engine, original)?;
            pay(engine, owned)?;
            pay(engine, owned)?;
            pay(engine, 4)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, original.clone()),
                )
                .map_err(|error| {
                    format!(
                        "Rust compiler source original statement normalization failed: {error:?}"
                    )
                })?;
            if normalized.kind != actual.kind
                || normalized.source_info != actual.source_info
                || !debug_equal(engine, &normalized.debuginfos, &actual.debuginfos)?
            {
                return Err("Rust compiler source original/current statement differs".into());
            }
        }
        let original = original.terminator();
        let actual = actual.terminator();
        let owned = array_iterator_constructors::compiler_source_terminator_work(engine, original)?;
        pay(engine, owned)?;
        pay(engine, owned)?;
        pay(engine, 4)?;
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("Rust compiler source original terminator normalization failed: {error:?}")
            })?;
        if normalized.kind != actual.kind
            || normalized.source_info != actual.source_info
            || !normalized.attributes.is_empty()
            || !actual.attributes.is_empty()
        {
            return Err("Rust compiler source original/current terminator differs".into());
        }
    }

    if engine.compiler_sources.len() >= MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Rust compiler source compiler evidence exceeds existing 512-node limit".into(),
        ));
    }
    pay(engine, engine.compiler_sources.len() + 6)?;
    // Publish only after every original/current field has been authenticated and paid.
    if let Some(places) = staged_places {
        engine.publish_instantiated_body(instance, current.clone(), places)?;
    }
    engine.compiler_sources.push(Evidence {
        instance,
        raw,
        current: current.clone(),
        context: engine.terms.boolean(true),
        signature,
    });
    Ok(current)
}

fn identity<'tcx>(body: &Body<'tcx>, instance: ty::Instance<'tcx>) -> Result<(), String> {
    if body.source.instance != instance.def
        || body.source.promoted.is_some()
        || !matches!(body.phase, MirPhase::Runtime(RuntimePhase::Optimized))
    {
        return Err("Rust compiler source Instance/promoted/phase differs".into());
    }
    Ok(())
}
fn debug_equal<'tcx>(
    engine: &mut Engine<'_>,
    a: &StmtDebugInfos<'tcx>,
    b: &StmtDebugInfos<'tcx>,
) -> Result<bool, String> {
    if a.len() > MAX_INPUT_VALUES || b.len() > MAX_INPUT_VALUES {
        return Err("Rust compiler source debug inventory exceeds512".into());
    }
    pay(engine, 1 + a.len() + b.len())?;
    Ok(a.len() == b.len()
        && a.as_slice()
            .iter()
            .zip(b.as_slice())
            .all(|(a, b)| match (a, b) {
                (
                    rustc_middle::mir::StmtDebugInfo::AssignRef(a, ap),
                    rustc_middle::mir::StmtDebugInfo::AssignRef(b, bp),
                ) => a == b && ap == bp,
                (
                    rustc_middle::mir::StmtDebugInfo::InvalidAssign(a),
                    rustc_middle::mir::StmtDebugInfo::InvalidAssign(b),
                ) => a == b,
                _ => false,
            }))
}

#[cfg(test)]
#[path = "compiler_sources_probe.rs"]
mod probe;
