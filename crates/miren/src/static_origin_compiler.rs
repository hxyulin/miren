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
        if let Some(kind) =
            check_construction(tcx, instance, &mut HashSet::new(), &mut construction)
        {
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
    if !id.is_local()
        && (!tcx.is_mir_available(id)
            || !matches!(
                tcx.def_kind(id),
                DefKind::Fn
                    | DefKind::AssocFn
                    | DefKind::Const
                    | DefKind::AssocConst
                    | DefKind::AnonConst
            ))
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
