//! Compiler storage observations, never runtime allocation or raw-access permission.
use super::*;
use rustc_abi::Size;
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_middle::mir::{ClearCrossCrate, ConstOperand, ConstValue, Local, Location, Promoted};
use rustc_middle::ty::TypeVisitableExt;
use std::rc::{Rc, Weak};

#[derive(Clone)]
pub(super) struct Key {
    namespace: Rc<()>,
    index: usize,
}

#[derive(Clone, Default)]
pub(super) struct Slots {
    locals: BTreeMap<usize, Key>,
}

impl Slots {
    pub(super) fn len(&self) -> usize {
        self.locals.len()
    }
    pub(super) fn operand(&self, operand: &Operand<'_>) -> Option<Key> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.locals.get(&place.local.as_usize()).cloned()
            }
            Operand::Copy(_)
            | Operand::Move(_)
            | Operand::Constant(_)
            | Operand::RuntimeChecks(_) => None,
        }
    }

    pub(super) fn invalidate(&mut self, place: Place<'_>) {
        if place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Deref))
        {
            // Unknown aliases cannot retain local compiler-origin witnesses.
            self.locals.clear();
        } else {
            self.locals.remove(&place.local.as_usize());
        }
    }

    pub(super) fn publish(&mut self, place: Place<'_>, key: Option<Key>) {
        self.invalidate(place);
        if place.projection.is_empty()
            && let Some(key) = key
        {
            self.locals.insert(place.local.as_usize(), key);
        }
    }
}

struct Receipt<'tcx> {
    owner: ty::Instance<'tcx>,
    promoted: Promoted,
    original: Ty<'tcx>,
    allocation: AllocId,
    current: Rc<Body<'tcx>>,
    producer: Location,
    producer_retag: rustc_middle::mir::WithRetag,
}

// The namespace is intentionally not lifetime-parameterized; typed records never enter State.
pub(super) struct Registry<'tcx> {
    namespace: Option<Rc<()>>,
    caller: ty::Instance<'tcx>,
    body: Weak<Body<'tcx>>,
    context: Context,
    receipts: Vec<Receipt<'tcx>>,
}

impl<'tcx> Registry<'tcx> {
    pub(super) fn new(
        engine: &Engine<'tcx>,
        caller: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
    ) -> Self {
        Self {
            namespace: None,
            caller,
            body: Rc::downgrade(body),
            context: engine.terms.clone(),
            receipts: Vec::new(),
        }
    }

    fn current(&self, engine: &Engine<'tcx>, body: &Rc<Body<'tcx>>) -> Result<(), String> {
        if !self
            .body
            .upgrade()
            .is_some_and(|saved| Rc::ptr_eq(&saved, body))
            || !engine
                .bodies
                .borrow()
                .get(&self.caller)
                .is_some_and(|saved| Rc::ptr_eq(saved, body))
            || !self.context.boolean(true).belongs_to(&engine.terms)
        {
            return Err("compiler constant receipt has a foreign frame, Body or Context".into());
        }
        Ok(())
    }

    pub(super) fn paired_constant(
        &mut self,
        engine: &Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        location: Location,
        constant: &ConstOperand<'tcx>,
    ) -> Result<(Value, Option<Key>), String> {
        self.current(engine, body)?;
        let evaluated = constant
            .const_
            .eval(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                constant.span,
            )
            .map_err(|error| {
                format!(
                    "unsupported MIR constant {:?} evaluation: {error:?}",
                    constant.const_
                )
            })?;
        // Preserve the checked decoder and its post-decoding sharing before publishing anything.
        let value = engine.decoded_constant(constant.const_, constant.span, evaluated)?;
        let receipt = self.observe(engine, body, location, constant, evaluated);
        let key = receipt.map(|receipt| {
            let index = self.receipts.len();
            self.receipts.push(receipt);
            Key {
                namespace: self.namespace.get_or_insert_with(|| Rc::new(())).clone(),
                index,
            }
        });
        Ok((value, key))
    }

    pub(super) fn discard(&mut self, key: Option<Key>) {
        if let Some(key) = key
            && self
                .namespace
                .as_ref()
                .is_some_and(|ns| Rc::ptr_eq(ns, &key.namespace))
            && key.index.checked_add(1) == Some(self.receipts.len())
        {
            self.receipts.pop();
        }
    }

    fn observe(
        &self,
        engine: &Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        producer: Location,
        constant: &ConstOperand<'tcx>,
        evaluated: ConstValue,
    ) -> Option<Receipt<'tcx>> {
        if self.receipts.len() >= MAX_INPUT_VALUES
            || !self.caller.args.is_empty()
            || engine.tcx.generics_of(self.caller.def_id()).count() != 0
            || constant.user_ty.is_some()
            || !self.caller.def_id().is_local()
            || !matches!(self.caller.def, ty::InstanceKind::Item(_))
            || !matches!(
                engine.tcx.def_kind(self.caller.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
        {
            return None;
        }
        let raw_caller = engine.tcx.instance_mir(self.caller.def);
        let raw_statement = raw_caller
            .basic_blocks
            .get(producer.block)?
            .statements
            .get(producer.statement_index)?;
        let current_statement = body
            .basic_blocks
            .get(producer.block)?
            .statements
            .get(producer.statement_index)?;
        // Exact raw/current metadata is required for either actual compiler retag variant.
        let (raw_constant, producer_retag) =
            matching_constant_producer(raw_statement, current_statement)?;
        if raw_caller
            .source_scopes
            .get(raw_statement.source_info.scope)
            .is_none()
            || body
                .source_scopes
                .get(current_statement.source_info.scope)
                .is_none()
            || raw_constant != constant
        {
            return None;
        }
        let rustc_middle::mir::Const::Unevaluated(unevaluated, original) = constant.const_ else {
            return None;
        };
        if !unevaluated.args.is_empty()
            || !unevaluated.def.is_local()
            || engine.tcx.generics_of(unevaluated.def).count() != 0
            || !engine.tcx.is_mir_available(unevaluated.def)
            || !matches!(
                engine.tcx.def_kind(unevaluated.def),
                DefKind::Fn | DefKind::AssocFn
            )
        {
            return None;
        }
        let promoted = unevaluated.promoted?;
        let owner = ty::Instance::new_raw(unevaluated.def, unevaluated.args);
        let raw = engine.tcx.promoted_mir(unevaluated.def).get(promoted)?;
        closed_none_body(engine, raw, owner, promoted, original).ok()?;
        let current = owner
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, raw.clone()),
            )
            .ok()?;
        closed_none_body(engine, &current, owner, promoted, original).ok()?;
        same_closed_body(raw, &current).ok()?;
        let allocation = compiler_backing(engine, original, evaluated).ok()?;
        Some(Receipt {
            owner,
            promoted,
            original,
            allocation,
            current: Rc::new(current),
            producer,
            producer_retag,
        })
    }

    pub(super) fn validate_argument(
        &self,
        engine: &Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        key: &Key,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        self.current(engine, body)?;
        if !self
            .namespace
            .as_ref()
            .is_some_and(|namespace| Rc::ptr_eq(&key.namespace, namespace))
        {
            return Err("compiler constant receipt belongs to another namespace".into());
        }
        let receipt = self
            .receipts
            .get(key.index)
            .ok_or("compiler constant receipt key is outside its frame registry")?;
        if receipt.original != original {
            return Err("compiler constant receipt original operand type differs".into());
        }
        let raw = engine
            .tcx
            .promoted_mir(receipt.owner.def_id())
            .get(receipt.promoted)
            .ok_or("compiler constant receipt promoted Body is unavailable")?;
        closed_none_body(
            engine,
            raw,
            receipt.owner,
            receipt.promoted,
            receipt.original,
        )?;
        closed_none_body(
            engine,
            &receipt.current,
            receipt.owner,
            receipt.promoted,
            receipt.original,
        )?;
        same_closed_body(raw, &receipt.current)?;
        checked_allocation(engine, receipt.allocation)?;
        let current_statement = body
            .basic_blocks
            .get(receipt.producer.block)
            .and_then(|block| block.statements.get(receipt.producer.statement_index))
            .ok_or("compiler constant receipt producer is outside its current Body")?;
        let raw_caller = engine.tcx.instance_mir(self.caller.def);
        let raw_statement = raw_caller
            .basic_blocks
            .get(receipt.producer.block)
            .and_then(|block| block.statements.get(receipt.producer.statement_index))
            .ok_or("compiler constant receipt raw producer is unavailable")?;
        let (constant, retag) = matching_constant_producer(raw_statement, current_statement)
            .ok_or("compiler constant receipt raw/current producer metadata differs")?;
        if retag != receipt.producer_retag
            || constant.const_.ty() != receipt.original
            || !matches!(constant.const_, rustc_middle::mir::Const::Unevaluated(value, _)
                if value.def == receipt.owner.def_id() && value.args == receipt.owner.args
                    && value.promoted == Some(receipt.promoted))
        {
            return Err("compiler constant receipt retained producer metadata differs".into());
        }
        Ok(())
    }
}

// Both tags are observations of the actual constant producer, never modeled retag permission.
fn matching_constant_producer<'a, 'tcx>(
    raw: &'a rustc_middle::mir::Statement<'tcx>,
    current: &rustc_middle::mir::Statement<'tcx>,
) -> Option<(&'a ConstOperand<'tcx>, rustc_middle::mir::WithRetag)> {
    if raw.kind != current.kind
        || raw.source_info != current.source_info
        || !raw.debuginfos.is_empty()
        || !current.debuginfos.is_empty()
    {
        return None;
    }
    let StatementKind::Assign(assignment) = &raw.kind else {
        return None;
    };
    let Rvalue::Use(Operand::Constant(constant), retag) = &assignment.1 else {
        return None;
    };
    let retag = match retag {
        rustc_middle::mir::WithRetag::Yes => rustc_middle::mir::WithRetag::Yes,
        rustc_middle::mir::WithRetag::No => rustc_middle::mir::WithRetag::No,
    };
    Some((constant.as_ref(), retag))
}

pub(super) fn candidate_type<'tcx>(engine: &Engine<'tcx>, original: Ty<'tcx>) -> bool {
    matches!(original.kind(), ty::Ref(_, item, rustc_hir::Mutability::Not)
        if matches!(item.kind(), ty::Adt(def, args)
            if engine.tcx.lang_items().get(LangItem::Option) == Some(def.did())
                && args.len() == 1 && matches!(args.type_at(0).kind(), ty::Adt(nonzero, inner)
                    if engine.tcx.is_diagnostic_item(rustc_span::Symbol::intern("NonZero"),
                        nonzero.did()) && inner.len() == 1
                        && inner.type_at(0) == engine.tcx.types.u8)))
}

fn option8<'tcx>(engine: &Engine<'tcx>, original: Ty<'tcx>) -> Result<Ty<'tcx>, String> {
    if original.has_escaping_bound_vars() {
        return Err("compiler constant receipt has escaping original bound variables".into());
    }
    let ty::Ref(_, item, rustc_hir::Mutability::Not) = original.kind() else {
        return Err("compiler constant receipt needs an original shared reference".into());
    };
    if !candidate_type(engine, original) {
        return Err("compiler constant receipt needs exact Option<NonZeroU8>".into());
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let layout = engine.static_layout(*item)?;
    if !item.is_freeze(engine.tcx, env)
        || !engine.tcx.type_is_copy_modulo_regions(env, *item)
        || item.needs_drop(engine.tcx, env)
        || layout.size.bytes() != 1
        || layout.align.abi.bytes() != 1
    {
        return Err("compiler constant receipt storage policy/layout differs".into());
    }
    Ok(*item)
}

fn compiler_backing<'tcx>(
    engine: &Engine<'tcx>,
    original: Ty<'tcx>,
    evaluated: ConstValue,
) -> Result<AllocId, String> {
    option8(engine, original)?;
    let ConstValue::Scalar(Scalar::Ptr(pointer, width)) = evaluated else {
        return Err("compiler constant receipt lacks an evaluated compiler pointer".into());
    };
    let (provenance, offset) = pointer.prov_and_relative_offset();
    if !provenance.immutable()
        || !provenance.shared_ref()
        || offset != Size::ZERO
        || u64::from(width.get()) != u64::from(engine.tcx.sess.target.pointer_width) / 8
    {
        return Err("compiler constant receipt pointer flags, width or offset differ".into());
    }
    checked_allocation(engine, provenance.alloc_id())?;
    Ok(provenance.alloc_id())
}

fn checked_allocation(engine: &Engine<'_>, id: AllocId) -> Result<(), String> {
    let allocation = match engine.tcx.try_get_global_alloc(id) {
        Some(GlobalAlloc::Memory(allocation)) => allocation,
        Some(GlobalAlloc::Static(_)) => {
            return Err("static identity is not a promoted receipt".into());
        }
        Some(
            GlobalAlloc::Function { .. } | GlobalAlloc::VTable(..) | GlobalAlloc::TypeId { .. },
        )
        | None => {
            return Err("compiler constant receipt has no immutable Memory allocation".into());
        }
    };
    let allocation = allocation.inner();
    let range = alloc_range(Size::ZERO, Size::from_bytes(1));
    if allocation.len() != 1
        || allocation.align.bytes() != 1
        || allocation.mutability.is_mut()
        || !allocation.provenance().range_empty(range, &engine.tcx)
        || allocation.init_mask().is_range_initialized(range).is_err()
        || allocation
            .get_bytes_strip_provenance(&engine.tcx, range)
            .map_err(|_| "compiler constant receipt backing is unavailable")?
            != [0]
    {
        return Err("compiler constant receipt backing is not initialized immutable None".into());
    }
    Ok(())
}

fn closed_none_body<'tcx>(
    engine: &Engine<'tcx>,
    body: &Body<'tcx>,
    owner: ty::Instance<'tcx>,
    promoted: Promoted,
    original: Ty<'tcx>,
) -> Result<(), String> {
    let item = option8(engine, original)?;
    if body.source.instance != owner.def
        || body.source.promoted != Some(promoted)
        || body.phase
            != rustc_middle::mir::MirPhase::Runtime(rustc_middle::mir::RuntimePhase::PostCleanup)
        || body.pass_count != 1
        || body.source_scopes.len() != 1
        || body.local_decls.len() != 2
        || body.basic_blocks.len() != 1
        || body.arg_count != 0
        || body.coroutine.is_some()
        || !body.user_type_annotations.is_empty()
        || body.spread_arg.is_some()
        || !body.var_debug_info.is_empty()
        || !matches!(&body.required_consts, Some(constants) if constants.is_empty())
        || body.mentioned_items.is_some()
        || body.is_polymorphic
        || body.injection_phase.is_some()
        || body.tainted_by_errors.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
    {
        return Err(
            "compiler constant receipt promoted header is outside the closed schema".into(),
        );
    }
    let scope = &body.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)];
    if scope.parent_scope.is_some()
        || scope.inlined.is_some()
        || scope.inlined_parent_scope.is_some()
        || !matches!(&scope.local_data, ClearCrossCrate::Set(data)
            if data.lint_root.owner.def_id.to_def_id() == owner.def_id())
    {
        return Err("compiler constant receipt promoted source scope differs".into());
    }
    for (index, local) in body.local_decls.iter_enumerated() {
        if local.ty
            != if index.as_usize() == 0 {
                original
            } else {
                item
            }
            || local.mutability != rustc_hir::Mutability::Mut
            || local.user_ty.is_some()
            || !matches!(local.local_info, ClearCrossCrate::Clear)
            || local.source_info.scope.as_usize() != 0
        {
            return Err("compiler constant receipt promoted local declaration differs".into());
        }
    }
    let block = &body.basic_blocks[START_BLOCK];
    if block.is_cleanup
        || block.statements.len() != 2
        || !block.after_last_stmt_debuginfos.is_empty()
    {
        return Err("compiler constant receipt promoted block differs".into());
    }
    for statement in &block.statements {
        if !statement.debuginfos.is_empty() || statement.source_info.scope.as_usize() != 0 {
            return Err("compiler constant receipt promoted statement metadata differs".into());
        }
    }
    let StatementKind::Assign(first) = &block.statements[0].kind else {
        return Err("compiler constant receipt promoted None assignment is absent".into());
    };
    let Rvalue::Aggregate(kind, args) = &first.1 else {
        return Err("compiler constant receipt promoted None aggregate is absent".into());
    };
    let ty::Adt(option, option_args) = item.kind() else {
        return Err("compiler constant receipt original Option definition is absent".into());
    };
    if first.0 != Place::from(Local::from_usize(1))
        || !args.is_empty()
        || !matches!(kind.as_ref(), AggregateKind::Adt(def, variant, generics, user, field)
            if *def == option.did() && variant.as_usize() == 0 && generics == option_args
                && user.is_none() && field.is_none())
        || !option
            .variant(rustc_abi::VariantIdx::from_usize(0))
            .fields
            .is_empty()
        || engine.tcx.lang_items().get(LangItem::OptionNone)
            != Some(option.variant(rustc_abi::VariantIdx::from_usize(0)).def_id)
        || option
            .discriminant_for_variant(engine.tcx, rustc_abi::VariantIdx::from_usize(0))
            .val
            != 0
    {
        return Err("compiler constant receipt promoted None construction differs".into());
    }
    let StatementKind::Assign(second) = &block.statements[1].kind else {
        return Err("compiler constant receipt promoted reference assignment is absent".into());
    };
    let ty::Ref(region, _, _) = original.kind() else {
        return Err("compiler constant receipt original shared region is absent".into());
    };
    if second.0 != Place::from(Local::from_usize(0))
        || !matches!(&second.1, Rvalue::Ref(actual, BorrowKind::Shared, place)
            if actual == region && *place == Place::from(Local::from_usize(1)))
    {
        return Err("compiler constant receipt promoted shared borrow differs".into());
    }
    let terminator = block
        .terminator
        .as_ref()
        .ok_or("compiler constant receipt promoted terminator is absent")?;
    if !matches!(terminator.kind, TerminatorKind::Return)
        || !terminator.attributes.is_empty()
        || terminator.source_info.scope.as_usize() != 0
    {
        return Err("compiler constant receipt promoted terminal return differs".into());
    }
    Ok(())
}

// Both bodies already passed the independent complete schema; retain all permitted metadata too.
fn same_closed_body<'tcx>(raw: &Body<'tcx>, current: &Body<'tcx>) -> Result<(), String> {
    if raw.span != current.span
        || raw.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)].span
            != current.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)].span
        || !matches!((&raw.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)].local_data,
            &current.source_scopes[rustc_middle::mir::SourceScope::from_usize(0)].local_data),
            (ClearCrossCrate::Set(a), ClearCrossCrate::Set(b)) if a.lint_root == b.lint_root)
        || raw
            .local_decls
            .iter()
            .zip(current.local_decls.iter())
            .any(|(a, b)| a.ty != b.ty || a.source_info != b.source_info)
        || raw.basic_blocks[START_BLOCK]
            .statements
            .iter()
            .zip(current.basic_blocks[START_BLOCK].statements.iter())
            .any(|(a, b)| a.kind != b.kind || a.source_info != b.source_info)
        || raw.basic_blocks[START_BLOCK].terminator().source_info
            != current.basic_blocks[START_BLOCK].terminator().source_info
    {
        return Err("compiler constant receipt original/current promoted semantics differ".into());
    }
    Ok(())
}

#[cfg(test)]
#[path = "constant_reference_receipts_probe.rs"]
mod probe;
