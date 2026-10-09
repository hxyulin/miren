//! Produce storage-origin certificates from a deliberately small typed construction language.
use miren::static_origins::{Construction, Evidence, Origin, OriginKind, SCHEMA, digest, sidecar};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::config::OutputType;
use rustc_span::def_id::LOCAL_CRATE;
use std::collections::HashSet;
use std::process::ExitCode;

pub fn run(args: &[String]) -> ExitCode {
    let mut producer = Producer {
        error: None,
        pending: None,
    };
    let result = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(args, &mut producer);
    });
    if result == ExitCode::SUCCESS
        && producer.error.is_none()
        && let Some((artifact, mut evidence)) = producer.pending.take()
    {
        producer.error = write_evidence(&artifact, &mut evidence).err();
    }
    if let Some(error) = producer.error {
        eprintln!("miren static origin producer: {error}");
        return ExitCode::FAILURE;
    }
    result
}

struct Producer {
    error: Option<String>,
    pending: Option<(std::path::PathBuf, Evidence)>,
}

impl Callbacks for Producer {
    fn config(&mut self, config: &mut interface::Config) {
        super::compiler_exports::retain(config);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        match collect(tcx) {
            Ok(pending) => self.pending = pending,
            Err(error) => self.error = Some(error),
        }
        if self.error.is_some() {
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }
}

fn collect(tcx: TyCtxt<'_>) -> Result<Option<(std::path::PathBuf, Evidence)>, String> {
    if !tcx
        .output_filenames(())
        .outputs
        .contains_key(&OutputType::Metadata)
    {
        return Ok(None);
    }
    let artifact = tcx
        .output_filenames(())
        .path(OutputType::Metadata)
        .as_path()
        .to_owned();
    let output = sidecar(&artifact);
    if output.exists() {
        std::fs::remove_file(&output).map_err(|error| error.to_string())?;
    }
    let mut origins = Vec::new();
    for id in tcx.mir_keys(()) {
        let id = id.to_def_id();
        if !matches!(tcx.def_kind(id), DefKind::Static { .. }) {
            continue;
        }
        let instance = ty::Instance::new_raw(id, ty::GenericArgs::identity_for_item(tcx, id));
        let mut construction = Vec::new();
        let mut kind = check_construction(tcx, instance, &mut HashSet::new(), &mut construction);
        if kind.is_none() {
            construction.clear();
            kind = check_closed_construction(
                tcx,
                instance,
                &[],
                &mut HashSet::new(),
                &mut construction,
            );
        }
        if let Some(kind) = kind {
            origins.push(Origin {
                static_id: identity(tcx, instance),
                kind,
                construction,
            });
        }
    }
    let evidence = Evidence {
        schema: SCHEMA,
        payload_sha256: String::new(),
        compiler: env!("MIREN_COMPILER").to_owned(),
        target: tcx.sess.opts.target_triple.to_string(),
        crate_id: format!("{:?}", tcx.stable_crate_id(LOCAL_CRATE)),
        artifact_sha256: String::new(),
        origins,
    };
    Ok(Some((artifact, evidence)))
}

fn write_evidence(artifact: &std::path::Path, evidence: &mut Evidence) -> Result<(), String> {
    evidence.artifact_sha256 = digest(&std::fs::read(artifact).map_err(|error| error.to_string())?);
    evidence.seal()?;
    let output = sidecar(artifact);
    let temporary = output.with_extension(format!("tmp-{}", std::process::id()));
    std::fs::write(
        &temporary,
        serde_json::to_vec(evidence).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    std::fs::rename(temporary, output).map_err(|error| error.to_string())
}

fn identity(tcx: TyCtxt<'_>, instance: ty::Instance<'_>) -> String {
    let mut identity = format!("{:?}", tcx.def_path_hash(instance.def_id()));
    if !instance.args.is_empty() {
        identity.push(':');
        identity.push_str(&digest(format!("{:?}", instance.args).as_bytes()));
    }
    identity
}

fn check_construction<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    active: &mut HashSet<ty::Instance<'tcx>>,
    construction: &mut Vec<Construction>,
) -> Option<OriginKind> {
    let key = identity(tcx, instance);
    if let Some(node) = construction.iter().find(|node| node.definition == key) {
        return Some(node.kind);
    }
    if active.len() + construction.len() >= 64 || !active.insert(instance) {
        return None;
    }
    let id = instance.def_id();
    // Local trait declarations have a DefId but no body. The compiler availability query
    // checks actual local body owners before any mir_for_ctfe request.
    if !tcx.is_mir_available(id) {
        return None;
    }
    if !id.is_local()
        && !matches!(
            tcx.def_kind(id),
            DefKind::Fn
                | DefKind::AssocFn
                | DefKind::Const
                | DefKind::AssocConst
                | DefKind::AnonConst
        )
    {
        return None;
    }
    if tcx.intrinsic(id).is_some() || !matches!(instance.def, ty::InstanceKind::Item(_)) {
        return None;
    }
    let body = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, tcx.mir_for_ctfe(id).clone()),
        )
        .ok()?;
    if body.basic_blocks.len() > 128 || body.local_decls.len() > 512 {
        return None;
    }
    if matches!(
        tcx.def_kind(id),
        DefKind::Const | DefKind::AssocConst | DefKind::AnonConst
    ) && tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            tcx.type_of(id).instantiate(tcx, instance.args),
        )
        .ok()?
        != body.return_ty()
    {
        return None;
    }
    if uninitialized_constructor(tcx, id, &body) || cell_constructor(tcx, id, &body) {
        construction.push(Construction {
            definition: key,
            kind: OriginKind::Declared,
            mir_sha256: digest(format!("{body:?}").as_bytes()),
            calls: Vec::new(),
        });
        active.remove(&instance);
        return Some(OriginKind::Declared);
    }
    // Parameters carry only scalar values; aggregate arguments could hide an earlier origin.
    if body.args_iter().any(|local| {
        !matches!(
            body.local_decls[local].ty.kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)
        )
    }) {
        return None;
    }
    if primitive_transmute(tcx, &body) {
        construction.push(Construction {
            definition: key,
            kind: OriginKind::U32,
            mir_sha256: digest(format!("{body:?}").as_bytes()),
            calls: Vec::new(),
        });
        active.remove(&instance);
        return Some(OriginKind::U32);
    }
    let mut checker = ConstructionChecker {
        tcx,
        body: &body,
        valid: true,
        calls: Vec::new(),
        constants: Vec::new(),
        return_assignments: 0,
    };
    checker.visit_body(&body);
    if !checker.valid {
        return None;
    }
    let mut kind = None;
    let mut calls = Vec::new();
    for (callee, returned) in &checker.calls {
        let origin = check_construction(tcx, *callee, active, construction)?;
        calls.push(identity(tcx, *callee));
        if *returned
            && kind
                .replace(origin)
                .is_some_and(|previous| previous != origin)
        {
            return None;
        }
    }
    for (constant, expected) in &checker.constants {
        if tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                tcx.type_of(constant.def_id())
                    .instantiate(tcx, constant.args),
            )
            .ok()?
            != *expected
        {
            return None;
        }
        check_construction(tcx, *constant, active, construction)?;
        calls.push(identity(tcx, *constant));
    }
    if checker.return_assignments > 0
        && kind
            .replace(OriginKind::Declared)
            .is_some_and(|previous| previous != OriginKind::Declared)
    {
        return None;
    }
    let kind = kind?;
    active.remove(&instance);
    construction.push(Construction {
        definition: key,
        kind,
        mir_sha256: digest(format!("{body:?}").as_bytes()),
        calls,
    });
    Some(kind)
}

fn uninitialized_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    body: &Body<'tcx>,
) -> bool {
    if !tcx.is_diagnostic_item(rustc_span::Symbol::intern("maybe_uninit_uninit"), id)
        || body.arg_count != 0
        || body.basic_blocks.len() != 1
    {
        return false;
    }
    let ty::Adt(def, _) = body.return_ty().kind() else {
        return false;
    };
    if tcx.lang_items().get(rustc_attr_ir::LangItem::MaybeUninit) != Some(def.did())
        || !def.is_union()
    {
        return false;
    }
    let block = &body.basic_blocks[START_BLOCK];
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return false;
    }
    let mut returned = false;
    let mut units = vec![false; body.local_decls.len()];
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter => {}
            StatementKind::Assign(assignment) => {
                let (destination, value) = assignment.as_ref();
                if let Rvalue::Use(Operand::Constant(unit), _) = value
                    && unit.const_.ty().is_unit()
                    && destination.projection.is_empty()
                    && body.local_decls[destination.local].ty.is_unit()
                {
                    units[destination.local.as_usize()] = true;
                    continue;
                }
                let Rvalue::Aggregate(kind, fields) = value else {
                    return false;
                };
                if matches!(kind.as_ref(), AggregateKind::Tuple)
                    && fields.is_empty()
                    && destination.projection.is_empty()
                    && body.local_decls[destination.local].ty.is_unit()
                {
                    units[destination.local.as_usize()] = true;
                    continue;
                }
                let AggregateKind::Adt(aggregate, _, args, _, Some(field)) = kind.as_ref() else {
                    return false;
                };
                let unit_operand = fields.iter().next();
                if destination.local != RETURN_PLACE
                    || !destination.projection.is_empty()
                    || returned
                    || *aggregate != def.did()
                    || ty::Ty::new_adt(tcx, *def, args) != body.return_ty()
                    || fields.len() != 1
                    || def.non_enum_variant().fields[*field].name.as_str() != "uninit"
                    || !fields
                        .iter()
                        .next()
                        .unwrap()
                        .ty(&body.local_decls, tcx)
                        .is_unit()
                    || !matches!(unit_operand, Some(Operand::Move(source) | Operand::Copy(source))
                        if source.projection.is_empty() && units[source.local.as_usize()])
                {
                    return false;
                }
                returned = true;
            }
            _ => return false,
        }
    }
    returned
}

fn cell_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    body: &Body<'tcx>,
) -> bool {
    if body.arg_count != 1 || body.basic_blocks.len() != 1 || tcx.item_name(id).as_str() != "new" {
        return false;
    }
    let ty::Adt(def, args) = body.return_ty().kind() else {
        return false;
    };
    let is_cell = |id| {
        tcx.lang_items().get(rustc_attr_ir::LangItem::UnsafeCell) == Some(id)
            || tcx.is_diagnostic_item(rustc_span::Symbol::intern("SyncUnsafeCell"), id)
    };
    if !is_cell(def.did())
        || id.krate != def.did().krate
        || tcx.def_kind(id) != DefKind::AssocFn
        || args.type_at(0) != body.local_decls[Local::from_usize(1)].ty
    {
        return false;
    }
    let block = &body.basic_blocks[START_BLOCK];
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return false;
    }
    let mut derived = vec![false; body.local_decls.len()];
    derived[1] = true;
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter => {}
            StatementKind::Assign(assignment) => {
                let (destination, value) = assignment.as_ref();
                if let Rvalue::Use(Operand::Move(source) | Operand::Copy(source), _) = value
                    && source.projection.is_empty()
                    && destination.projection.is_empty()
                    && derived[source.local.as_usize()]
                    && body.local_decls[source.local].ty == body.local_decls[destination.local].ty
                {
                    derived[destination.local.as_usize()] = true;
                    continue;
                }
                let Rvalue::Aggregate(kind, fields) = value else {
                    return false;
                };
                let AggregateKind::Adt(aggregate, _, arguments, _, None) = kind.as_ref() else {
                    return false;
                };
                let Some(Operand::Move(source) | Operand::Copy(source)) = fields.iter().next()
                else {
                    return false;
                };
                let aggregate_def = tcx.adt_def(*aggregate);
                let field = aggregate_def.non_enum_variant().fields.iter().next();
                let Some(field) = field else {
                    return false;
                };
                let Ok(field_ty) = tcx.try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    field.ty(tcx, arguments),
                ) else {
                    return false;
                };
                if !destination.projection.is_empty()
                    || !source.projection.is_empty()
                    || fields.len() != 1
                    || !derived[source.local.as_usize()]
                    || !is_cell(*aggregate)
                    || field_ty != body.local_decls[source.local].ty
                    || ty::Ty::new_adt(tcx, aggregate_def, arguments)
                        != body.local_decls[destination.local].ty
                {
                    return false;
                }
                derived[destination.local.as_usize()] = true;
            }
            _ => return false,
        }
    }
    derived[RETURN_PLACE.as_usize()]
}

fn primitive_transmute<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    if body.arg_count != 1
        || body.basic_blocks.len() != 1
        || body.local_decls[Local::from_usize(1)].ty != tcx.types.u32
    {
        return false;
    }
    let block = &body.basic_blocks[START_BLOCK];
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return false;
    }
    let mut derived = vec![false; body.local_decls.len()];
    derived[1] = true;
    let mut target = None;
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter => {}
            StatementKind::Assign(assignment) => {
                let (destination, value) = assignment.as_ref();
                if !destination.projection.is_empty() {
                    return false;
                }
                match value {
                    Rvalue::Use(Operand::Move(source) | Operand::Copy(source), _)
                        if source.projection.is_empty()
                            && derived[source.local.as_usize()]
                            && body.local_decls[destination.local].ty == tcx.types.u32 =>
                    {
                        derived[destination.local.as_usize()] = true;
                    }
                    Rvalue::Cast(
                        CastKind::Transmute,
                        Operand::Move(source) | Operand::Copy(source),
                        ty,
                    ) if destination.local == RETURN_PLACE
                        && source.projection.is_empty()
                        && derived[source.local.as_usize()]
                        && *ty == body.return_ty() =>
                    {
                        if target.replace(*ty).is_some() {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
    let Some(target) = target else {
        return false;
    };
    if matches!(target.kind(), ty::Adt(def, _) if def.is_union()) {
        return false;
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let Ok(source_layout) = tcx.layout_of(env.as_query_input(tcx.types.u32)) else {
        return false;
    };
    let Ok(target_layout) = tcx.layout_of(env.as_query_input(target)) else {
        return false;
    };
    source_layout.size == target_layout.size && source_layout.align.abi <= target_layout.align.abi
}

struct ConstructionChecker<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    valid: bool,
    calls: Vec<(ty::Instance<'tcx>, bool)>,
    constants: Vec<(ty::Instance<'tcx>, ty::Ty<'tcx>)>,
    return_assignments: usize,
}

impl<'tcx> Visitor<'tcx> for ConstructionChecker<'_, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if !matches!(
            statement.kind,
            StatementKind::Assign(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::ConstEvalCounter
        ) {
            self.valid = false;
        }
        if let StatementKind::Assign(assignment) = &statement.kind {
            let (destination, value) = assignment.as_ref();
            if destination.local == RETURN_PLACE && destination.projection.is_empty() {
                self.return_assignments += 1;
                if matches!(value, Rvalue::Use(operand, _) if !matches!(
                    operand.ty(&self.body.local_decls, self.tcx).kind(),
                    ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)
                )) {
                    self.valid = false;
                }
            }
        }
        self.super_statement(statement, location);
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: Location) {
        let supported = match value {
            Rvalue::Use(..) | Rvalue::Repeat(..) => true,
            Rvalue::Cast(CastKind::IntToInt, operand, target)
                if operand.ty(&self.body.local_decls, self.tcx).is_bool()
                    && *target == self.tcx.types.u8 =>
            {
                true
            }
            Rvalue::Aggregate(kind, _) => match kind.as_ref() {
                AggregateKind::Array(_) | AggregateKind::Tuple => true,
                AggregateKind::Adt(id, ..) => !self.tcx.adt_def(*id).is_union(),
                AggregateKind::Closure(..)
                | AggregateKind::Coroutine(..)
                | AggregateKind::CoroutineClosure(..)
                | AggregateKind::RawPtr(..) => false,
            },
            Rvalue::Ref(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::RawPtr(..)
            | Rvalue::Cast(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::Discriminant(..)
            | Rvalue::CopyForDeref(..)
            | Rvalue::WrapUnsafeBinder(..)
            | Rvalue::Reborrow(..) => false,
        };
        self.valid &= supported;
        self.super_rvalue(value, location);
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        // An evaluated aggregate or pointer may have erased construction history. Only a
        // compiler-owned unevaluated constant definition can supply a nested origin DAG.
        if matches!(
            constant.const_.ty().kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::FnDef(..)
        ) || constant.const_.ty().is_unit()
        {
            self.super_const_operand(constant, location);
            return;
        }
        let Const::Unevaluated(value, ty) = constant.const_ else {
            self.valid = false;
            return;
        };
        if value.promoted.is_some()
            || !matches!(
                self.tcx.def_kind(value.def),
                DefKind::Const | DefKind::AssocConst | DefKind::AnonConst
            )
            || !matches!(ty.kind(), ty::Adt(def, _) if !def.is_union())
                && !matches!(ty.kind(), ty::Tuple(_) | ty::Array(_, _))
        {
            self.valid = false;
            return;
        }
        self.constants
            .push((ty::Instance::new_raw(value.def, value.args), ty));
        self.super_const_operand(constant, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        for (base, projection) in place.iter_projections() {
            let ty = base.ty(&self.body.local_decls, self.tcx).ty;
            if matches!(ty.kind(), ty::Adt(def, _) if def.is_union())
                || !matches!(projection, ProjectionElem::Field(..))
            {
                self.valid = false;
            }
        }
        self.super_place(place, context, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Return | TerminatorKind::Goto { .. } => {}
            TerminatorKind::UnwindResume | TerminatorKind::UnwindTerminate(_)
                if self.body.basic_blocks[location.block].is_cleanup => {}
            TerminatorKind::Call {
                func, destination, ..
            } => {
                if let ty::FnDef(id, args) = func.ty(&self.body.local_decls, self.tcx).kind() {
                    match ty::Instance::try_resolve(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        *id,
                        args.skip_binder(),
                    ) {
                        Ok(Some(instance)) => self.calls.push((
                            instance,
                            destination.local == RETURN_PLACE && destination.projection.is_empty(),
                        )),
                        Ok(None) | Err(_) => self.valid = false,
                    }
                } else {
                    self.valid = false;
                }
            }
            TerminatorKind::SwitchInt { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::TailCall { .. } => {
                self.valid = false;
            }
        }
        self.super_terminator(terminator, location);
    }
}

// A second, narrower execution language permits aggregate constructor parameters only when
// their actual operands were certified in the caller. Transmuted U32 storage may be forwarded
// whole; composition admits only the exact compiler Atomic<u32> carrier with matching scalar
// layout. DAG node identities include parameter origin kinds when U32 arguments are admitted,
// so cached bodies cannot erase a different argument's construction history.
fn check_closed_construction<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    arguments: &[OriginKind],
    active: &mut HashSet<ty::Instance<'tcx>>,
    construction: &mut Vec<Construction>,
) -> Option<OriginKind> {
    let id = instance.def_id();
    if !tcx.is_mir_available(id) {
        return None;
    }
    if tcx.intrinsic(id).is_some()
        || !matches!(instance.def, ty::InstanceKind::Item(_))
        || !id.is_local()
            && !matches!(
                tcx.def_kind(id),
                DefKind::Fn
                    | DefKind::AssocFn
                    | DefKind::Const
                    | DefKind::AssocConst
                    | DefKind::AnonConst
            )
    {
        return None;
    }
    let body = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, tcx.mir_for_ctfe(id).clone()),
        )
        .ok()?;
    if body.basic_blocks.len() > 128
        || body.local_decls.len() > 512
        || body.arg_count != arguments.len()
        || body
            .args_iter()
            .any(|local| !constructor_type(body.local_decls[local].ty))
    {
        return None;
    }
    for (local, argument) in body.args_iter().zip(arguments) {
        declared_constructor_origin(tcx, body.local_decls[local].ty, *argument)?;
    }
    if matches!(
        tcx.def_kind(id),
        DefKind::Const | DefKind::AssocConst | DefKind::AnonConst
    ) && normalized_constructor_type(tcx, tcx.type_of(id).instantiate(tcx, instance.args))?
        != body.return_ty()
    {
        return None;
    }
    if matches!(tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) {
        let signature = tcx.fn_sig(id).instantiate(tcx, instance.args).skip_binder();
        if signature.c_variadic()
            || signature.inputs().len() != body.arg_count
            || normalized_constructor_type(tcx, ty::Unnormalized::new_wip(signature.output()))?
                != body.return_ty()
        {
            return None;
        }
        for (local, expected) in body.args_iter().zip(signature.inputs()) {
            if normalized_constructor_type(tcx, ty::Unnormalized::new_wip(*expected))?
                != body.local_decls[local].ty
            {
                return None;
            }
        }
    }
    let key = closed_identity(tcx, instance, arguments);
    if let Some(node) = construction.iter().find(|node| node.definition == key) {
        return Some(node.kind);
    }
    if active.len() + construction.len() >= 64 || !active.insert(instance) {
        return None;
    }
    let mut calls = Vec::new();
    let kind = if uninitialized_constructor(tcx, id, &body)
        || cell_constructor(tcx, id, &body)
        || atomic_usize_constructor(tcx, id, &body)
    {
        OriginKind::Declared
    } else if primitive_transmute(tcx, &body) {
        OriginKind::U32
    } else {
        let mut checker = ClosedConstruction {
            tcx,
            body: &body,
            locals: vec![None; body.local_decls.len()],
            active,
            construction,
            calls: &mut calls,
        };
        for (local, argument) in body.args_iter().zip(arguments) {
            checker.locals[local.as_usize()] = Some(*argument);
        }
        checker.run()?
    };
    active.remove(&instance);
    construction.push(Construction {
        definition: key,
        kind,
        mir_sha256: digest(format!("{body:?}").as_bytes()),
        calls,
    });
    Some(kind)
}

// Unlike the general U32 carrier recognizer, this certifies only core's typed Atomic<usize>
// constructor. Both the source scalar and target diagnostic type are exact compiler identities.
fn atomic_usize_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    body: &Body<'tcx>,
) -> bool {
    let ty::Adt(def, args) = body.return_ty().kind() else {
        return false;
    };
    if tcx.get_diagnostic_item(rustc_span::Symbol::intern("Atomic")) != Some(def.did())
        || args.len() != 1
        || args.types().next() != Some(tcx.types.usize)
        || id.krate != def.did().krate
        || tcx.def_kind(id) != DefKind::AssocFn
        || tcx.item_name(id).as_str() != "new"
        || body.arg_count != 1
        || body.basic_blocks.len() != 1
        || body.local_decls[Local::from_usize(1)].ty != tcx.types.usize
    {
        return false;
    }
    let block = &body.basic_blocks[START_BLOCK];
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return false;
    }
    let mut derived = vec![false; body.local_decls.len()];
    derived[1] = true;
    let mut returned = false;
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter => {}
            StatementKind::Assign(assignment) => {
                let (destination, value) = assignment.as_ref();
                if !destination.projection.is_empty() {
                    return false;
                }
                match value {
                    Rvalue::Use(Operand::Move(source) | Operand::Copy(source), _)
                        if source.projection.is_empty()
                            && derived[source.local.as_usize()]
                            && body.local_decls[destination.local].ty == tcx.types.usize =>
                    {
                        derived[destination.local.as_usize()] = true;
                    }
                    Rvalue::Cast(
                        CastKind::Transmute,
                        Operand::Move(source) | Operand::Copy(source),
                        target,
                    ) if destination.local == RETURN_PLACE
                        && source.projection.is_empty()
                        && derived[source.local.as_usize()]
                        && *target == body.return_ty()
                        && !returned =>
                    {
                        returned = true;
                    }
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let Ok(source) = tcx.layout_of(env.as_query_input(tcx.types.usize)) else {
        return false;
    };
    let Ok(target) = tcx.layout_of(env.as_query_input(body.return_ty())) else {
        return false;
    };
    returned && source.size == target.size && source.align.abi == target.align.abi
}

fn closed_identity(
    tcx: TyCtxt<'_>,
    instance: ty::Instance<'_>,
    arguments: &[OriginKind],
) -> String {
    let mut key = identity(tcx, instance);
    if arguments.contains(&OriginKind::U32) {
        key.push_str(":argument-origins:");
        key.push_str(&digest(format!("{arguments:?}").as_bytes()));
    }
    key
}

fn constructor_type(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Tuple(_)
        | ty::Array(_, _) => true,
        ty::Adt(def, _) => !def.is_union(),
        _ => false,
    }
}

fn declared_constructor_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    origin: OriginKind,
) -> Option<OriginKind> {
    if origin == OriginKind::Declared {
        return Some(origin);
    }
    let ty::Adt(def, args) = ty.kind() else {
        return None;
    };
    if tcx.get_diagnostic_item(rustc_span::Symbol::intern("Atomic")) != Some(def.did())
        || args.types().next() != Some(tcx.types.u32)
    {
        return None;
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let atomic = tcx.layout_of(env.as_query_input(ty)).ok()?;
    let scalar = tcx.layout_of(env.as_query_input(tcx.types.u32)).ok()?;
    (atomic.size == scalar.size && atomic.align.abi == scalar.align.abi)
        .then_some(OriginKind::Declared)
}

fn normalized_constructor_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Unnormalized<'tcx, ty::Ty<'tcx>>,
) -> Option<ty::Ty<'tcx>> {
    tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), ty)
        .ok()
}

struct ClosedConstruction<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    locals: Vec<Option<OriginKind>>,
    active: &'a mut HashSet<ty::Instance<'tcx>>,
    construction: &'a mut Vec<Construction>,
    calls: &'a mut Vec<String>,
}

impl<'tcx> ClosedConstruction<'_, 'tcx> {
    fn run(&mut self) -> Option<OriginKind> {
        let mut block = START_BLOCK;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(block) {
                return None;
            }
            let data = &self.body.basic_blocks[block];
            for statement in &data.statements {
                match &statement.kind {
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                        self.locals[local.as_usize()] = None;
                    }
                    StatementKind::Nop | StatementKind::ConstEvalCounter => {}
                    StatementKind::Assign(assignment) => {
                        let (place, value) = assignment.as_ref();
                        if !place.projection.is_empty() {
                            return None;
                        }
                        let origin = self.rvalue(value, self.body.local_decls[place.local].ty)?;
                        self.locals[place.local.as_usize()] = Some(origin);
                    }
                    _ => return None,
                }
            }
            match &data.terminator().kind {
                TerminatorKind::Return => return self.locals[RETURN_PLACE.as_usize()],
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    if !destination.projection.is_empty() {
                        return None;
                    }
                    let ty::FnDef(id, generic) = func.ty(&self.body.local_decls, self.tcx).kind()
                    else {
                        return None;
                    };
                    let instance = ty::Instance::try_resolve(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        *id,
                        generic.skip_binder(),
                    )
                    .ok()??;
                    let signature = self
                        .tcx
                        .fn_sig(instance.def_id())
                        .instantiate(self.tcx, instance.args)
                        .skip_binder();
                    if signature.c_variadic()
                        || signature.inputs().len() != args.len()
                        || normalized_constructor_type(
                            self.tcx,
                            ty::Unnormalized::new_wip(signature.output()),
                        )? != self.body.local_decls[destination.local].ty
                    {
                        return None;
                    }
                    let mut origins = Vec::new();
                    for (argument, expected) in args.iter().zip(signature.inputs()) {
                        let actual = argument.node.ty(&self.body.local_decls, self.tcx);
                        if normalized_constructor_type(
                            self.tcx,
                            ty::Unnormalized::new_wip(*expected),
                        )? != actual
                        {
                            return None;
                        }
                        let origin = self.operand(&argument.node)?;
                        declared_constructor_origin(self.tcx, actual, origin)?;
                        origins.push(origin);
                    }
                    let origin = check_closed_construction(
                        self.tcx,
                        instance,
                        &origins,
                        self.active,
                        self.construction,
                    )?;
                    self.calls
                        .push(closed_identity(self.tcx, instance, &origins));
                    self.locals[destination.local.as_usize()] = Some(origin);
                    block = (*target)?;
                }
                _ => return None,
            }
        }
    }

    fn rvalue(&mut self, value: &Rvalue<'tcx>, destination: ty::Ty<'tcx>) -> Option<OriginKind> {
        match value {
            Rvalue::Use(operand, _) => {
                if operand.ty(&self.body.local_decls, self.tcx) != destination {
                    return None;
                }
                self.operand(operand)
            }
            Rvalue::Repeat(operand, count) => {
                let ty::Array(element, length) = destination.kind() else {
                    return None;
                };
                if count.try_to_target_usize(self.tcx)? != length.try_to_target_usize(self.tcx)?
                    || *element != operand.ty(&self.body.local_decls, self.tcx)
                    || declared_constructor_origin(self.tcx, *element, self.operand(operand)?)?
                        != OriginKind::Declared
                {
                    return None;
                }
                Some(OriginKind::Declared)
            }
            Rvalue::Aggregate(kind, operands) => {
                let expected = match kind.as_ref() {
                    AggregateKind::Tuple => {
                        let ty::Tuple(fields) = destination.kind() else {
                            return None;
                        };
                        fields.iter().collect::<Vec<_>>()
                    }
                    AggregateKind::Array(element) => {
                        let ty::Array(actual, length) = destination.kind() else {
                            return None;
                        };
                        if actual != element
                            || length.try_to_target_usize(self.tcx)? != operands.len() as u64
                        {
                            return None;
                        }
                        vec![*element; operands.len()]
                    }
                    AggregateKind::Adt(id, variant, args, _, None) => {
                        let def = self.tcx.adt_def(*id);
                        if def.is_union() || ty::Ty::new_adt(self.tcx, def, args) != destination {
                            return None;
                        }
                        let variant = def.variants().get(*variant)?;
                        variant
                            .fields
                            .iter()
                            .map(|field| {
                                normalized_constructor_type(self.tcx, field.ty(self.tcx, args))
                            })
                            .collect::<Option<Vec<_>>>()?
                    }
                    _ => return None,
                };
                if expected.len() != operands.len() {
                    return None;
                }
                for (operand, ty) in operands.iter().zip(expected) {
                    if operand.ty(&self.body.local_decls, self.tcx) != ty
                        || declared_constructor_origin(self.tcx, ty, self.operand(operand)?)?
                            != OriginKind::Declared
                    {
                        return None;
                    }
                }
                Some(OriginKind::Declared)
            }
            Rvalue::Cast(CastKind::IntToInt, operand, target)
                if operand.ty(&self.body.local_decls, self.tcx).is_bool()
                    && *target == self.tcx.types.u8
                    && *target == destination =>
            {
                (self.operand(operand)? == OriginKind::Declared).then_some(OriginKind::Declared)
            }
            _ => None,
        }
    }

    fn operand(&mut self, operand: &Operand<'tcx>) -> Option<OriginKind> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let origin = self.locals[place.local.as_usize()]?;
                let mut ty = self.body.local_decls[place.local].ty;
                for projection in place.projection {
                    if origin != OriginKind::Declared {
                        return None;
                    }
                    let ProjectionElem::Field(index, expected) = projection else {
                        return None;
                    };
                    let actual = match ty.kind() {
                        ty::Tuple(fields) => {
                            ty::Unnormalized::new_wip(*fields.get(index.as_usize())?)
                        }
                        ty::Adt(def, args) if def.is_struct() => {
                            def.non_enum_variant().fields.get(index)?.ty(self.tcx, args)
                        }
                        _ => return None,
                    };
                    ty = normalized_constructor_type(self.tcx, actual)?;
                    if ty != expected {
                        return None;
                    }
                }
                if matches!(operand, Operand::Move(_)) {
                    self.locals[place.local.as_usize()] = None;
                }
                Some(origin)
            }
            Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                if matches!(
                    ty.kind(),
                    ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)
                ) || ty.is_unit()
                {
                    return Some(OriginKind::Declared);
                }
                if let Const::Unevaluated(value, expected) = constant.const_
                    && value.promoted.is_none()
                    && matches!(
                        self.tcx.def_kind(value.def),
                        DefKind::Const | DefKind::AssocConst | DefKind::AnonConst
                    )
                    && constructor_type(expected)
                {
                    let instance = ty::Instance::new_raw(value.def, value.args);
                    if normalized_constructor_type(
                        self.tcx,
                        self.tcx
                            .type_of(value.def)
                            .instantiate(self.tcx, value.args),
                    )? != expected
                    {
                        return None;
                    }
                    let origin = check_closed_construction(
                        self.tcx,
                        instance,
                        &[],
                        self.active,
                        self.construction,
                    )?;
                    self.calls.push(identity(self.tcx, instance));
                    return Some(origin);
                }
                if let Const::Val(ConstValue::ZeroSized, ty) = constant.const_
                    && let ty::Adt(def, _) = ty.kind()
                    && def.is_struct()
                    && def.non_enum_variant().fields.is_empty()
                {
                    let env = ty::TypingEnv::fully_monomorphized();
                    let layout = self.tcx.layout_of(env.as_query_input(ty)).ok()?;
                    if layout.size.bytes() == 0 && !layout.is_uninhabited() {
                        return Some(OriginKind::Declared);
                    }
                }
                // CTFE may fold None to a niche scalar. Read its actual active variant and accept
                // only a fieldless enum variant: no erased payload, pointer, or transmute history.
                let ty::Adt(def, _) = ty.kind() else {
                    return None;
                };
                if self.tcx.lang_items().get(rustc_attr_ir::LangItem::Option) != Some(def.did()) {
                    return None;
                }
                let env = ty::TypingEnv::fully_monomorphized();
                let value = constant.const_.eval(self.tcx, env, constant.span).ok()?;
                let (ecx, operand) = rustc_const_eval::const_eval::mk_eval_cx_for_const_val(
                    self.tcx.at(constant.span),
                    env,
                    value,
                    ty,
                )?;
                let variant = ecx.read_discriminant(&operand).discard_err()?;
                let variant = def.variant(variant);
                (variant.name.as_str() == "None" && variant.fields.is_empty())
                    .then_some(OriginKind::Declared)
            }
            Operand::RuntimeChecks(_) => None,
        }
    }
}
