//! Invocation-local primitive helper lease. No owner role enters the helper's arguments.
use super::*;
use crate::proof::mutable_u16::Storage;
use rustc_middle::mir::UnwindAction;
use std::rc::Weak;

fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    let attempted = engine.steps.checked_add_commit(count).ok_or_else(|| {
        engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "retained helper work overflow".into(),
        )
    })?;

    if attempted > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "retained helper shared execution step limit reached".into(),
        ));
    }
    Ok(())
}

// Price every existing retained source-validation invocation before executing it.
// The immutable Body allowance covers header/registry visits and all possible witness walks.
fn pay_source_validation(
    engine: &mut Engine<'_>,
    body: &Body<'_>,
    metadata: usize,
) -> Result<(), String> {
    let registry = engine.bodies.borrow().len();
    pay(engine, body.basic_blocks.len() + metadata + 4)?;
    let mut statements = 0usize;
    for block in body.basic_blocks.iter() {
        statements = statements
            .checked_add(block.statements.len())
            .ok_or("retained helper caller allowance overflow")?;
    }
    let occurrences = metadata
        .checked_mul(body.basic_blocks.len() + statements)
        .ok_or("retained helper witness allowance overflow")?;
    let source_work =
        body.local_decls.len() + registry + 24 + body.basic_blocks.len() + statements + occurrences;
    pay(engine, source_work)
}

// Authenticate the complete compiler signature independently of the mutable call cache.
// Only flat primitive/Unit types and generic primitive parameters enter normalization here.
fn checked_signature<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ty::PolyFnSig<'tcx>, String> {
    pay(engine, 8)?;
    let original = engine.tcx.fn_sig(instance.def_id());
    let raw = original.skip_binder();
    let count = raw.skip_binder().inputs_and_output.len();
    if count > MAX_INPUT_VALUES || instance.args.len() > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "retained helper signature exceeds the existing 512-value limit".into(),
        ));
    }
    pay(engine, count + instance.args.len() + 8)?;
    if !raw.bound_vars().is_empty()
        || raw.skip_binder().inputs_and_output.iter().any(|original| {
            !original.is_unit()
                && !engine.mutable_u16_primitive(original)
                && !matches!(original.kind(), ty::Param(_))
        })
        || instance.args.iter().any(|argument| match argument.kind() {
            ty::GenericArgKind::Type(original) => {
                !original.is_unit() && !engine.mutable_u16_primitive(original)
            }
            ty::GenericArgKind::Lifetime(_) => false,
            ty::GenericArgKind::Const(_) => true,
        })
    {
        return Err(engine.retained_error("retained helper original signature type domain differs"));
    }
    // Compiler types and binders are interned handles. The flat domain above bounds the
    // instantiated input graph before normalization, and comparison retains every FnSig flag.
    let normalized = engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            original.instantiate(engine.tcx, instance.args),
        )
        .map_err(|error| format!("retained helper original signature normalization: {error:?}"))?;
    pay(engine, count + 8)?;
    let cached = engine.call_poly_signature(instance)?;
    if cached != normalized {
        return Err(engine.retained_error("retained helper cached/original full signature differs"));
    }
    Ok(normalized)
}

fn primitive_value<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    value: &Value,
    conditions: &[Term],
) -> Result<(), String> {
    pay(engine, 5)?;
    match (original.kind(), value) {
        (ty::Tuple(types), Value::Unit) if types.is_empty() => Ok(()),
        (ty::Tuple(types), Value::Tuple(fields)) if types.is_empty() && fields.is_empty() => Ok(()),
        (ty::Bool, Value::Bool(term))
            if term.belongs_to(&engine.terms) && term.sort() == &Sort::Bool =>
        {
            Ok(())
        }
        (
            ty::Int(_) | ty::Uint(_),
            Value::Int {
                expression,
                bits,
                signed,
            },
        ) if engine.integer_type(original) == Some((*bits, *signed))
            && expression.belongs_to(&engine.terms)
            && expression.sort() == &Sort::BitVec(*bits) =>
        {
            Ok(())
        }
        (
            ty::Char,
            Value::Int {
                expression,
                bits: 32,
                signed: false,
            },
        ) if expression.belongs_to(&engine.terms) && expression.sort() == &Sort::BitVec(32) => {
            pay(engine, conditions.len() + 12)?;
            engine.prove_char_value(value, conditions)
        }
        (ty::Float(_), Value::Float { bits, .. }) if engine.float_type(original) == Some(*bits) => {
            pay(engine, conditions.len() + 12)?;
            characters::validate_float_encoding(&engine.terms, value, *bits)?;
            engine.prove_scalar_float(value, *bits, conditions)
        }
        _ => Err(engine.retained_error("retained helper primitive type/validity/Context differs")),
    }
}

struct Site<'tcx> {
    caller: ty::Instance<'tcx>,
    caller_body: Rc<Body<'tcx>>,
    callee: ty::Instance<'tcx>,
    callee_body: Rc<Body<'tcx>>,
    block: BasicBlock,
    target: BasicBlock,
    destination: Place<'tcx>,
}

struct RootOwner<'tcx> {
    owner: usize,
    caller: ty::Instance<'tcx>,
    caller_body: Rc<Body<'tcx>>,
    certificate: usize,
    allocation: usize,
    original: Ty<'tcx>,
    length: Term,
    data: Storage,
    generation: u64,
    phase: Phase,
}

struct Edge<'tcx> {
    caller: ty::Instance<'tcx>,
    caller_body: Rc<Body<'tcx>>,
    callee: ty::Instance<'tcx>,
    callee_body: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    block: BasicBlock,
    occurrence: usize,
    target: BasicBlock,
    destination: Place<'tcx>,
    parent: Option<Rc<Edge<'tcx>>>,
    token: Weak<()>,
    depth: usize,
}

pub(in crate::proof) struct Invocation<'tcx> {
    root: Rc<RootOwner<'tcx>>,
    edge: Rc<Edge<'tcx>>,
    token: Rc<()>,
}

// A normal-return proof tied to the exact immutable Body/Memory observation, not a role flag.
pub(in crate::proof) struct ReturnedOwner<'frame, 'tcx> {
    owner: usize,
    body: &'frame Body<'tcx>,
    memory: &'frame Memory,
}
impl<'tcx> ReturnedOwner<'_, 'tcx> {
    pub(in crate::proof) fn matches(&self, id: usize, body: &Body<'tcx>, memory: &Memory) -> bool {
        id == self.owner && std::ptr::eq(body, self.body) && std::ptr::eq(memory, self.memory)
    }
}

impl<'tcx> Invocation<'tcx> {
    fn capture(engine: &mut Engine<'tcx>, site: Site<'tcx>, state: &State) -> Result<Self, String> {
        let Site {
            caller,
            caller_body,
            callee,
            callee_body,
            block,
            target,
            destination,
        } = site;
        let owner = 0;
        pay(engine, state.memory.missing_places.entries().len() + 4)?;
        let Phase::Retained { metadata, .. } = &state.memory.mutable_u16[owner].phase else {
            return Err(engine.retained_error("retained helper capture needs retained phase"));
        };
        let witness_count = metadata.len();
        pay_source_validation(engine, &caller_body, witness_count)?;
        let backing = engine.mutable_u16_backing(owner, &state.memory)?;
        let phase_slots = match &backing.phase {
            Phase::Retained { metadata, .. } => metadata.len().saturating_mul(2),
            Phase::Idle | Phase::Pending { .. } | Phase::Active { .. } => {
                return Err(engine.retained_error("retained helper capture needs retained phase"));
            }
        };
        let columns = match &backing.data {
            Storage::Scalar(_) => 1,
            Storage::Product(columns) => columns.len(),
        };
        pay(engine, phase_slots + columns + 34)?;
        let original = engine
            .mutable_owner_certificate(backing.certificate)?
            .original;
        // Backing validation requires the entire Unit anchor initialized. MissingPlaces::check
        // with an empty projection rejects every descendant mask, so no owned mask clone exists.
        state
            .memory
            .check_projection_initialization(backing.allocation, &[])?;
        let signature = checked_signature(engine, callee)?;
        let root = Rc::new(RootOwner {
            owner,
            caller,
            caller_body: caller_body.clone(),
            certificate: backing.certificate,
            allocation: backing.allocation,
            original,
            length: backing.length.integer()?.0,
            data: backing.data.clone(),
            generation: backing.generation,
            phase: backing.phase.clone(),
        });
        let token = Rc::new(());
        let invocation = Self {
            root,
            edge: Rc::new(Edge {
                caller,
                occurrence: std::ptr::from_ref(&caller_body.basic_blocks[block].terminator().kind)
                    as usize,
                caller_body,
                callee,
                callee_body,
                signature,
                block,
                target,
                destination,
                parent: None,
                token: Rc::downgrade(&token),
                depth: 1,
            }),
            token,
        };
        invocation.check(engine, &invocation.edge.callee_body, &state.memory)?;
        Ok(invocation)
    }

    fn derive(
        &self,
        engine: &mut Engine<'tcx>,
        site: Site<'tcx>,
        state: &State,
        signature: ty::PolyFnSig<'tcx>,
    ) -> Result<Self, String> {
        self.check(engine, &site.caller_body, &state.memory)?;
        let depth = self
            .edge
            .depth
            .checked_add(1)
            .ok_or("retained helper depth overflow")?;
        // Each edge and its frame-local token/root handles use twenty logical slots.
        // Enforce live ancestry storage before allocating a new node.
        pay(engine, state.memory.storage_slots() + 36)?;
        let metadata_slots = match &self.root.phase {
            Phase::Retained { metadata, .. } => metadata.len().saturating_mul(2),
            Phase::Idle | Phase::Pending { .. } | Phase::Active { .. } => unreachable!(),
        };
        let columns = match &self.root.data {
            Storage::Scalar(_) => 1,
            Storage::Product(columns) => columns.len(),
        };
        if depth > engine.limits.max_call_depth
            || state
                .memory
                .storage_slots()
                .saturating_add(depth.saturating_mul(20) + 40 + metadata_slots + columns)
                > MAX_INPUT_VALUES
        {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained helper ancestry exceeds existing depth/storage limits".into(),
            ));
        }
        if site.caller != self.edge.callee || !Rc::ptr_eq(&site.caller_body, &self.edge.callee_body)
        {
            return Err(engine.retained_error("retained helper child has a different parent frame"));
        }
        pay(engine, 40)?;
        let token = Rc::new(());
        let invocation = Self {
            root: self.root.clone(),
            edge: Rc::new(Edge {
                caller: site.caller,
                occurrence: std::ptr::from_ref(
                    &site.caller_body.basic_blocks[site.block].terminator().kind,
                ) as usize,
                caller_body: site.caller_body,
                callee: site.callee,
                callee_body: site.callee_body,
                signature,
                block: site.block,
                target: site.target,
                destination: site.destination,
                parent: Some(self.edge.clone()),
                token: Rc::downgrade(&token),
                depth,
            }),
            token,
        };
        invocation.scope(engine, &invocation.edge.callee_body, &state.memory)?;
        Ok(invocation)
    }

    pub(in crate::proof) fn check_return<'frame>(
        &self,
        engine: &mut Engine<'tcx>,
        body: &'frame Body<'tcx>,
        state: &'frame State,
        value: &Value,
    ) -> Result<ReturnedOwner<'frame, 'tcx>, String> {
        self.check(engine, body, &state.memory)?;
        primitive_value(engine, body.return_ty(), value, &state.conditions)?;
        Ok(ReturnedOwner {
            owner: self.root.owner,
            body,
            memory: &state.memory,
        })
    }

    pub(in crate::proof) fn check(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Body<'tcx>,
        memory: &Memory,
    ) -> Result<(), String> {
        self.scope(engine, body, memory)?;
        let Phase::Retained { metadata, .. } = &self.root.phase else {
            unreachable!()
        };
        pay_source_validation(engine, &self.root.caller_body, metadata.len())?;
        engine.mutable_retained_frame(&self.root.caller_body, self.root.owner, memory)
    }

    pub(in crate::proof) fn scope(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Body<'tcx>,
        memory: &Memory,
    ) -> Result<(), String> {
        if self.edge.depth == 0
            || self.edge.depth > MAX_INPUT_VALUES
            || self.edge.depth > engine.limits.max_call_depth
        {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained helper ancestry walk exceeds existing depth/value limits".into(),
            ));
        }
        let registry = engine.bodies.borrow().len();
        let phase_work = match &self.root.phase {
            Phase::Retained { metadata, .. } => metadata.len().saturating_mul(2),
            Phase::Idle | Phase::Pending { .. } | Phase::Active { .. } => {
                return Err(engine.retained_error("retained helper snapshot phase differs"));
            }
        };
        let columns = match &self.root.data {
            Storage::Scalar(_) => 1,
            Storage::Product(columns) => columns.len(),
        };
        pay(
            engine,
            registry + memory.mutable_u16.len() + phase_work + columns + 15,
        )?;
        if !std::ptr::eq(body, self.edge.callee_body.as_ref())
            || Rc::strong_count(&self.token) != 1
            || !Weak::ptr_eq(&self.edge.token, &Rc::downgrade(&self.token))
            || memory.mutable_u16.len() != 1
        {
            return Err(engine.retained_error("retained helper current frame/depth differs"));
        }
        // Prepay the complete bounded linked walk before visiting any ancestor node.
        pay(engine, self.edge.depth * (registry + 40) + 4)?;
        let bodies = engine.bodies.borrow();
        let signatures = engine.call_signatures.borrow();
        let mut cursor = Some(self.edge.as_ref());
        let mut remaining = self.edge.depth;
        while let Some(edge) = cursor {
            let live = edge
                .token
                .upgrade()
                .ok_or_else(|| engine.retained_error("retained helper ancestor frame has ended"))?;
            if Rc::strong_count(&live) != 2 {
                return Err(
                    engine.retained_error("retained helper ancestor frame token is aliased")
                );
            }
            if remaining == 0
                || edge.depth != remaining
                || bodies
                    .get(&edge.callee)
                    .is_none_or(|held| !Rc::ptr_eq(held, &edge.callee_body))
                || bodies
                    .get(&edge.caller)
                    .is_none_or(|held| !Rc::ptr_eq(held, &edge.caller_body))
                || edge.callee_body.source.instance != edge.callee.def
                || edge.caller_body.source.instance != edge.caller.def
                || signatures.get(&edge.callee) != Some(&edge.signature)
            {
                return Err(
                    engine.retained_error("retained helper current ancestor source differs")
                );
            }
            let terminator = edge.caller_body.basic_blocks[edge.block].terminator();
            let TerminatorKind::Call {
                func: Operand::Constant(function),
                destination,
                target: Some(target),
                unwind,
                ..
            } = &terminator.kind
            else {
                return Err(engine.retained_error("retained helper original caller Call is absent"));
            };
            let ty::FnDef(id, args) = function.const_.ty().kind() else {
                return Err(engine.retained_error("retained helper original FnDef is absent"));
            };
            if engine.resolve_function_item(*id, args.skip_binder())? != edge.callee
                || std::ptr::from_ref(&terminator.kind) as usize != edge.occurrence
                || *destination != edge.destination
                || *target != edge.target
                || !matches!(unwind, UnwindAction::Unreachable)
            {
                return Err(
                    engine.retained_error("retained helper original occurrence/edge differs")
                );
            }
            match &edge.parent {
                Some(parent) => {
                    if parent.callee != edge.caller
                        || !Rc::ptr_eq(&parent.callee_body, &edge.caller_body)
                    {
                        return Err(
                            engine.retained_error("retained helper ancestor adjacency differs")
                        );
                    }
                    cursor = Some(parent.as_ref());
                }
                None => {
                    if edge.caller != self.root.caller
                        || !Rc::ptr_eq(&edge.caller_body, &self.root.caller_body)
                        || remaining != 1
                    {
                        return Err(engine.retained_error("retained helper issuing root differs"));
                    }
                    cursor = None;
                }
            }
            remaining -= 1;
        }
        if remaining != 0 {
            return Err(engine.retained_error("retained helper incomplete ancestor chain"));
        }
        drop(signatures);
        drop(bodies);
        let backing = memory
            .mutable_u16
            .get(self.root.owner)
            .ok_or("retained helper suspended owner is absent")?;
        let mut work = Work(0);
        work.charge(engine, memory.missing_places.entries().len())?;
        pay(engine, memory.missing_places.entries().len() + 14)?;
        memory.check_projection_initialization(self.root.allocation, &[])?;
        if !matches!(memory.get(self.root.allocation), Some(Some(Value::Unit))) {
            return Err(engine.retained_error("retained helper owner anchor was replaced"));
        }
        let current = engine
            .mutable_owner_certificate(backing.certificate)?
            .original;
        if backing.certificate != self.root.certificate
            || backing.allocation != self.root.allocation
            || current != self.root.original
            || backing.generation != self.root.generation
            || backing.length.integer()?.0 != self.root.length
            || backing.data != self.root.data
            || backing.phase != self.root.phase
            || backing.interval.is_some()
            || backing.hierarchy.is_some()
        {
            return Err(
                engine.retained_error("retained helper changed suspended typed owner state")
            );
        }
        // The ordinary incoming escape graph still validates every allocation. The owner's
        // validated Unit anchor needs no private-role exception or fabricated reference.
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn retained_helper_nested_call(
        &self,
        body: &Body<'tcx>,
        func: &Operand<'tcx>,
    ) -> Result<(), String> {
        let Operand::Constant(function) = func else {
            return Err(self.retained_error("retained helper nested/indirect call is unsupported"));
        };
        let ty::FnDef(id, args) = function.const_.ty().kind() else {
            return Err(self.retained_error("retained helper nested callee is unsupported"));
        };
        self.resolve_function_item(*id, args.skip_binder())?;
        if func.ty(&body.local_decls, self.tcx) != function.const_.ty() {
            return Err(self.retained_error("retained helper nested scalar calls are unsupported"));
        }
        Ok(())
    }

    pub(in crate::proof) fn retained_primitive_helper_call(
        &mut self,
        caller: ty::Instance<'tcx>,
        caller_body: &Rc<Body<'tcx>>,
        state: &mut State,
        call: ChildCall<'_, 'tcx>,
        parent: Option<&Invocation<'tcx>>,
    ) -> Result<Option<Vec<Return>>, String> {
        let ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            stack,
            site,
        } = call;
        if !state
            .memory
            .mutable_u16
            .iter()
            .any(|backing| matches!(backing.phase, Phase::Retained { .. }))
            || self.mutable_metadata_operation(instance)
            || super::super::super::identity::is_panic_call(self.tcx, instance.def_id())
            || self.is_core_panic_helper(instance.def_id())
        {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
        {
            return Ok(None);
        }
        let registry = self.bodies.borrow().len();
        pay(self, registry + args.len() + 8)?;
        let poly_signature = checked_signature(self, instance)?;
        let signature = poly_signature.skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || args.len() > MAX_INPUT_VALUES
            || signature
                .inputs()
                .iter()
                .any(|original| !original.is_unit() && !self.mutable_u16_primitive(*original))
            || !(signature.output().is_unit() || self.mutable_u16_primitive(signature.output()))
        {
            return Ok(None);
        }
        let Some(target) = target else {
            return Ok(None);
        };
        let TerminatorKind::Call {
            func: Operand::Constant(function),
            args: actual,
            destination: actual_destination,
            target: Some(actual_target),
            unwind,
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err(self.retained_error("retained helper requires original direct Call"));
        };
        let ty::FnDef(id, generic) = function.const_.ty().kind() else {
            return Err(self.retained_error("retained helper requires original FnDef"));
        };
        if self.resolve_function_item(*id, generic.skip_binder())? != instance
            || !std::ptr::eq(actual.as_ref(), args)
            || *actual_destination != destination
            || *actual_target != target
            || !std::ptr::eq(body, caller_body.as_ref())
            || destination.ty(&body.local_decls, self.tcx).ty != signature.output()
            || !destination.projection.is_empty()
            || !matches!(unwind, UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some_and(|spec| {
                spec.trusted || spec.storage_effect.is_some() || spec.returns_alias.is_some()
            })
            || self.foreign_rust_target(instance)?.is_some()
            || state.memory.mutable_u16.len() != 1
        {
            return Err(
                self.retained_error("retained helper original Call/signature/domain differs")
            );
        }
        let owner = 0;
        let Phase::Retained {
            carrier, metadata, ..
        } = &state.memory.mutable_u16[owner].phase
        else {
            unreachable!()
        };
        if parent.is_none() {
            let Value::MutableU16 { id, role } = self.raw_local(state, *carrier)? else {
                return Err(self.retained_error("retained helper caller carrier is absent"));
            };
            if id != owner {
                return Err(self.retained_error("retained helper caller owner differs"));
            }
            // Operand authentication invokes backing validation and current-frame validation.
            // Each remains a distinct performed source service and is prepaid separately.
            pay_source_validation(self, body, metadata.len())?;
            pay_source_validation(self, body, metadata.len())?;
            self.mutable_retained_operand(body, state, *carrier, owner, &role)?;
        }
        let witness_slots = metadata.len().saturating_mul(2);
        let backing_columns = match &state.memory.mutable_u16[owner].data {
            Storage::Scalar(_) => 1,
            Storage::Product(columns) => columns.len(),
        };
        pay(
            self,
            state.memory.storage_slots() + witness_slots + args.len() * 5 + 30,
        )?;
        if state
            .memory
            .storage_slots()
            .saturating_add(witness_slots + backing_columns + 40)
            > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained helper lease exceeds existing storage budget".into(),
            ));
        }
        let callee_body =
            array_iterator_constructors::steps::authenticated_helper_body(self, instance)?;
        self.mutable_u16_body_budget(&callee_body)?;
        if callee_body.arg_count != args.len()
            || callee_body.return_ty() != signature.output()
            || callee_body
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, ty)| callee_body.local_decls[local].ty != *ty)
            || callee_body.basic_blocks.iter().any(|block| {
                block.is_cleanup
                    || match &block.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. } => {
                            !matches!(unwind, UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err(self.retained_error("retained helper selected Body/schema differs"));
        }
        pay(self, 4)?;
        let site_descriptor = Site {
            caller,
            caller_body: caller_body.clone(),
            callee: instance,
            callee_body: callee_body.clone(),
            block,
            target,
            destination,
        };
        let invocation = match parent {
            Some(parent) => parent.derive(self, site_descriptor, state, poly_signature)?,
            None => Invocation::capture(self, site_descriptor, state)?,
        };
        let mut values = Vec::with_capacity(args.len());
        for (arg, original) in args.iter().zip(signature.inputs()) {
            if arg.node.ty(&body.local_decls, self.tcx) != *original {
                return Err(self.retained_error("retained helper original argument type differs"));
            }
            let value = self.evaluate_operand(site.0, body, state, &arg.node)?;
            primitive_value(self, *original, &value, &state.conditions)?;
            values.push(value);
        }
        self.typed_coroutine_snapshots(
            signature.inputs(),
            &values,
            &state.memory,
            &state.conditions,
        )?;
        pay(
            self,
            state.conditions.len() + state.memory.storage_slots() + 4,
        )?;
        let conditions = self.call_preconditions(
            instance,
            &values,
            state.conditions.clone(),
            &state.memory,
            site,
        )?;
        let frame = array_drop_glue::Frame::retained_helper(instance, invocation);
        let previous = std::mem::replace(
            &mut self.call_chain,
            stack.iter().copied().chain([instance.def_id()]).collect(),
        );
        let result = self.execute_body_with_protocol(
            frame,
            values,
            conditions,
            state.memory.clone(),
            stack,
            activation_flow::Flow::Unarmed,
        );
        if result.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        result.map(Some)
    }
}

#[cfg(test)]
mod tests;
