//! Inactive nested-lease experiment. No production role or Memory authority is changed.
use super::*;
use std::rc::{Rc, Weak};

type Checked<T> = Result<T, &'static str>;

#[derive(Clone)]
struct Origin {
    certificate: usize,
    allocation: usize,
    length: Value,
    context: Term,
}

#[derive(Clone)]
struct Owner<'tcx> {
    lease: u64,
    frames: Vec<Weak<Body<'tcx>>>,
}

#[derive(Clone)]
struct Tip<'tcx> {
    body: Weak<Body<'tcx>>,
    occurrence: usize,
    local: usize,
}

#[derive(Clone)]
struct Pending<'tcx> {
    lease: u64,
    parent: u64,
    tip: Tip<'tcx>,
}

#[derive(Clone)]
struct Ledger<'tcx> {
    origin: Rc<Origin>,
    issued: u64,
    epoch: u64,
    owners: Vec<Owner<'tcx>>,
    pending: Option<Pending<'tcx>>,
}

struct ReturnTicket<'tcx> {
    origin: Rc<Origin>,
    lease: u64,
    prefix: Vec<Owner<'tcx>>,
    selected: Weak<Body<'tcx>>,
}

struct ScalarTicket<'tcx> {
    origin: Rc<Origin>,
    owners: Vec<Owner<'tcx>>,
    selected: Weak<Body<'tcx>>,
}

#[derive(Clone, Copy)]
struct Metadata {
    lease: u64,
    epoch: u64,
}

fn same_body<'tcx>(weak: &Weak<Body<'tcx>>, body: &Body<'tcx>) -> bool {
    weak.upgrade()
        .is_some_and(|held| std::ptr::eq(held.as_ref(), body))
}

fn primitive(original: Ty<'_>) -> bool {
    matches!(
        original.kind(),
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)
    )
}

fn result_shape<'tcx>(engine: &Engine<'tcx>, original: Ty<'tcx>, result: &Value) -> Checked<()> {
    if original.is_unit() {
        return matches!(result, Value::Unit)
            .then_some(())
            .ok_or("Unit result");
    }
    let (width, signed) = match original.kind() {
        ty::Int(kind) => (
            kind.bit_width()
                .map(|bits| bits as u32)
                .unwrap_or(u32::from(engine.tcx.sess.target.pointer_width)),
            true,
        ),
        ty::Uint(kind) => (
            kind.bit_width()
                .map(|bits| bits as u32)
                .unwrap_or(u32::from(engine.tcx.sess.target.pointer_width)),
            false,
        ),
        // The inactive compiler probe deliberately exercises only Unit/integer results.
        _ => return Err("prototype result domain"),
    };
    let (term, actual_width, actual_signed) = result.integer().map_err(|_| "integer result")?;
    (width == actual_width && signed == actual_signed && term.belongs_to(&engine.terms))
        .then_some(())
        .ok_or("original result codec/context")
}

fn body_budget(body: &Body<'_>) -> Checked<()> {
    let mut work = body
        .local_decls
        .len()
        .saturating_add(body.basic_blocks.len());
    if body.coroutine.is_some() || body.spread_arg.is_some() || body.tainted_by_errors.is_some() {
        return Err("unsupported Body metadata");
    }
    if work > MAX_INPUT_VALUES {
        return Err("Body work budget");
    }
    for block in body.basic_blocks.iter() {
        work = work.saturating_add(block.statements.len());
        if work > MAX_INPUT_VALUES {
            return Err("Body work budget");
        }
        if block.is_cleanup
            || matches!(block.terminator().kind,
            TerminatorKind::Call { unwind, .. } | TerminatorKind::Drop { unwind, .. }
            | TerminatorKind::Assert { unwind, .. }
            if !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable))
        {
            return Err("selected unwind");
        }
    }
    (work <= MAX_INPUT_VALUES)
        .then_some(())
        .ok_or("Body work budget")
}

impl<'tcx> Ledger<'tcx> {
    fn new(engine: &Engine<'tcx>, body: &Rc<Body<'tcx>>, state: &State) -> Checked<Self> {
        let backing = engine
            .mutable_u16_backing(0, &state.memory)
            .map_err(|_| "backing")?;
        if backing.interval.is_some() || state.memory.mutable_u16.len() != 1 {
            return Err("whole single backing only");
        }
        let original = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
        if !matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut()
                && matches!(inner.kind(), ty::Slice(t) if *t == engine.tcx.types.u16))
            || !engine
                .mutable_u16_matches(original, 0, &state.memory, true)
                .map_err(|_| "original certificate")?
        {
            return Err("exact original u16");
        }
        body_budget(body)?;
        let ledger = Self {
            origin: Rc::new(Origin {
                certificate: backing.certificate,
                allocation: backing.allocation,
                length: backing.length.clone(),
                context: backing.data.clone(),
            }),
            issued: 0,
            epoch: 0,
            owners: vec![Owner {
                lease: 0,
                frames: vec![Rc::downgrade(body)],
            }],
            pending: None,
        };
        ledger.charge(state, 0)?;
        Ok(ledger)
    }

    fn slots(&self) -> usize {
        // Per owner: lease, parent position and all selected Body identities.
        self.owners
            .iter()
            .map(|owner| 2 + owner.frames.len())
            .sum::<usize>()
            + usize::from(self.pending.is_some()) * 4
            + 2
    }

    fn charge(&self, state: &State, added: usize) -> Checked<()> {
        if state
            .memory
            .storage_slots()
            .saturating_add(self.slots())
            .saturating_add(added)
            > MAX_INPUT_VALUES
        {
            return Err("shared storage budget");
        }
        Ok(())
    }

    fn current(&self, engine: &Engine<'tcx>, state: &State) -> Checked<()> {
        let backing = engine
            .mutable_u16_backing(0, &state.memory)
            .map_err(|_| "current backing")?;
        if backing.interval.is_some()
            || backing.certificate != self.origin.certificate
            || backing.allocation != self.origin.allocation
            || backing.length.integer().map_err(|_| "length")?.0
                != self.origin.length.integer().map_err(|_| "length")?.0
            || !backing.data.belongs_to(&engine.terms)
            || !self.origin.context.belongs_to(&engine.terms)
            || backing.data.sort() != self.origin.context.sort()
        {
            return Err("issued backing differs");
        }
        state
            .memory
            .missing_places
            .check(backing.allocation, &[])
            .map_err(|_| "owner mask")?;
        self.charge(state, 0)
    }

    fn top(&self, body: &Body<'tcx>) -> Checked<&Owner<'tcx>> {
        let top = self.owners.last().ok_or("owner missing")?;
        if !top
            .frames
            .last()
            .is_some_and(|frame| same_body(frame, body))
        {
            return Err("actual top Body differs");
        }
        Ok(top)
    }

    fn source_handle(
        &self,
        engine: &Engine<'tcx>,
        body: &Body<'tcx>,
        state: &State,
        source: usize,
    ) -> Checked<()> {
        let local = rustc_middle::mir::Local::from_usize(source);
        if !engine
            .mutable_u16_matches(body.local_decls[local].ty, 0, &state.memory, true)
            .map_err(|_| "source original type")?
            || !matches!(
                engine
                    .raw_local(state, source)
                    .map_err(|_| "source value")?,
                Value::MutableU16 {
                    id: 0,
                    role: symbolic::MutableU16Role::Root
                }
            )
        {
            return Err("shadow handle original type/value differs");
        }
        // Shadow handles are paired with Ledger IDs; no production Root role is promoted.
        engine
            .check_local_initialization(state, source, &[])
            .map_err(|_| "source mask")
    }

    fn access(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        lease: u64,
        body: &Body<'tcx>,
        source: usize,
    ) -> Checked<()> {
        self.current(engine, state)?;
        if self.pending.is_some() || self.top(body)?.lease != lease {
            return Err("lease suspended or revoked");
        }
        self.source_handle(engine, body, state, source)
    }

    fn lifetime(&self, engine: &Engine<'tcx>, state: &State, lease: u64) -> Checked<()> {
        self.current(engine, state)?;
        if !self.owners.iter().any(|owner| owner.lease == lease)
            || self
                .owners
                .iter()
                .flat_map(|owner| &owner.frames)
                .any(|frame| frame.upgrade().is_none())
        {
            return Err("not a retained live ancestor");
        }
        Ok(())
    }

    fn metadata(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        lease: u64,
        body: &Body<'tcx>,
        source: usize,
    ) -> Checked<Metadata> {
        self.access(engine, state, lease, body, source)?;
        Ok(Metadata {
            lease,
            epoch: self.epoch,
        })
    }

    fn metadata_access(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        metadata: Metadata,
        body: &Body<'tcx>,
        source: usize,
    ) -> Checked<()> {
        self.access(engine, state, metadata.lease, body, source)?;
        if metadata.epoch != self.epoch {
            return Err("stale observation epoch");
        }
        Ok(())
    }

    fn assignment<'a>(
        &self,
        body: &'a Body<'tcx>,
        statement: &'a StatementKind<'tcx>,
    ) -> Checked<&'a (Place<'tcx>, Rvalue<'tcx>)> {
        body_budget(body)?;
        if !body
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|s| std::ptr::eq(&s.kind, statement))
        {
            return Err("actual Assignment occurrence");
        }
        let StatementKind::Assign(assignment) = statement else {
            return Err("Assignment");
        };
        Ok(assignment)
    }

    fn stage(
        &mut self,
        engine: &Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        statement: &StatementKind<'tcx>,
        lease: u64,
    ) -> Checked<u64> {
        self.current(engine, state)?;
        let assignment = self.assignment(body, statement)?;
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = &assignment.1 else {
            return Err("actual mutable reborrow");
        };
        let destination = assignment.0;
        if source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || state.addresses[destination.local.as_usize()].is_some()
            || source.local == destination.local
            || !engine
                .mutable_u16_matches(body.local_decls[source.local].ty, 0, &state.memory, true)
                .map_err(|_| "source type")?
            || !engine
                .mutable_u16_matches(
                    body.local_decls[destination.local].ty,
                    0,
                    &state.memory,
                    true,
                )
                .map_err(|_| "destination type")?
        {
            return Err("private exact reborrow path");
        }
        self.source_handle(engine, body, state, source.local.as_usize())?;
        let tip = Tip {
            body: Rc::downgrade(body),
            occurrence: statement as *const _ as usize,
            local: destination.local.as_usize(),
        };
        if let Some(pending) = &mut self.pending {
            if pending.lease != lease
                || !same_body(&pending.tip.body, body)
                || pending.tip.local != source.local.as_usize()
            {
                return Err("only current pending tip advances");
            }
            pending.tip = tip;
            return Ok(lease);
        }
        self.access(engine, state, lease, body, source.local.as_usize())?;
        if self.owners.len() >= 3
            || self
                .owners
                .iter()
                .map(|owner| owner.frames.len())
                .sum::<usize>()
                >= MAX_INPUT_DEPTH
        {
            return Err("depth2 mutable owners");
        }
        self.charge(state, 4)?;
        let next = self.issued.checked_add(1).ok_or("issuer overflow")?;
        let epoch = self.epoch.checked_add(1).ok_or("epoch overflow")?;
        self.pending = Some(Pending {
            lease: next,
            parent: lease,
            tip,
        });
        self.issued = next;
        self.epoch = epoch;
        Ok(next)
    }

    fn enter(
        &mut self,
        engine: &Engine<'tcx>,
        caller: &Rc<Body<'tcx>>,
        state: &mut State,
        block: rustc_middle::mir::BasicBlock,
        selected: &Rc<Body<'tcx>>,
        instance: ty::Instance<'tcx>,
    ) -> Checked<ReturnTicket<'tcx>> {
        self.current(engine, state)?;
        body_budget(caller)?;
        body_budget(selected)?;
        let TerminatorKind::Call {
            func,
            args,
            target,
            unwind,
            destination,
            ..
        } = &caller.basic_blocks[block].terminator().kind
        else {
            return Err("actual Call");
        };
        let ty::FnDef(id, generic) = func.ty(&caller.local_decls, engine.tcx).kind() else {
            return Err("actual FnDef");
        };
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || engine.tcx.def_kind(*id) != DefKind::Fn
            || engine
                .resolve_function_item(*id, generic.skip_binder())
                .map_err(|_| "resolution")?
                != instance
            || !Rc::ptr_eq(
                &engine
                    .instantiated_body(instance)
                    .map_err(|_| "selected body")?,
                selected,
            )
            || target.is_none()
            || !destination.projection.is_empty()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
        {
            return Err("selected original Call");
        }
        let signature = engine.call_signature(instance).map_err(|_| "signature")?;
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || selected.arg_count != args.len()
            || !(signature.output().is_unit() || primitive(signature.output()))
            || selected.return_ty() != signature.output()
            || destination.ty(&caller.local_decls, engine.tcx).ty != signature.output()
            || !engine
                .mutable_u16_matches(signature.inputs()[0], 0, &state.memory, true)
                .map_err(|_| "argument type")?
            || signature.inputs().iter().skip(1).any(|ty| !primitive(*ty))
        {
            return Err("safe synchronous signature");
        }
        let pending = self.pending.as_ref().ok_or("pending required")?;
        let parent = self.top(caller)?;
        let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
            return Err("source place");
        };
        if pending.parent != parent.lease
            || !same_body(&pending.tip.body, caller)
            || source.local.as_usize() != pending.tip.local
            || !source.projection.is_empty()
            || !caller
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .any(|s| &s.kind as *const _ as usize == pending.tip.occurrence)
        {
            return Err("actual current tip Call");
        }
        self.source_handle(engine, caller, state, source.local.as_usize())?;
        self.charge(state, 3)?;
        let ticket = ReturnTicket {
            origin: self.origin.clone(),
            lease: pending.lease,
            prefix: self.owners.clone(),
            selected: Rc::downgrade(selected),
        };
        // Prototype consumes only this actual Call Move. Other operands remain ordinary effects.
        if matches!(args[0].node, Operand::Move(_)) {
            state
                .missing_places
                .consume(source.local.as_usize(), Vec::new())
                .map_err(|_| "Move budget")?;
        }
        self.owners.push(Owner {
            lease: pending.lease,
            frames: vec![Rc::downgrade(selected)],
        });
        self.pending = None;
        Ok(ticket)
    }

    fn push_scalar(
        &mut self,
        engine: &Engine<'tcx>,
        caller: &Rc<Body<'tcx>>,
        state: &State,
        block: rustc_middle::mir::BasicBlock,
        selected: &Rc<Body<'tcx>>,
        instance: ty::Instance<'tcx>,
    ) -> Checked<ScalarTicket<'tcx>> {
        self.current(engine, state)?;
        let top = self.top(caller)?;
        if self.pending.is_some()
            || top.lease == 0
            || self
                .owners
                .iter()
                .map(|owner| owner.frames.len())
                .sum::<usize>()
                >= MAX_INPUT_DEPTH
        {
            return Err("scalar caller owner");
        }
        body_budget(caller)?;
        body_budget(selected)?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &caller.basic_blocks[block].terminator().kind
        else {
            return Err("scalar Call");
        };
        let ty::FnDef(id, generic) = func.ty(&caller.local_decls, engine.tcx).kind() else {
            return Err("scalar FnDef");
        };
        let signature = engine
            .call_signature(instance)
            .map_err(|_| "scalar signature")?;
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || engine.tcx.def_kind(*id) != DefKind::Fn
            || engine
                .resolve_function_item(*id, generic.skip_binder())
                .map_err(|_| "scalar resolution")?
                != instance
            || !Rc::ptr_eq(
                &engine
                    .instantiated_body(instance)
                    .map_err(|_| "scalar body")?,
                selected,
            )
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || selected.arg_count != args.len()
            || signature.inputs().iter().any(|ty| !primitive(*ty))
            || !(signature.output().is_unit() || primitive(signature.output()))
            || signature.output() != selected.return_ty()
            || destination.ty(&caller.local_decls, engine.tcx).ty != signature.output()
            || target.is_none()
            || !destination.projection.is_empty()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
        {
            return Err("selected scalar protocol");
        }
        self.charge(state, 1)?;
        let ticket = ScalarTicket {
            origin: self.origin.clone(),
            owners: self.owners.clone(),
            selected: Rc::downgrade(selected),
        };
        self.owners
            .last_mut()
            .unwrap()
            .frames
            .push(Rc::downgrade(selected));
        Ok(ticket)
    }

    fn pop_scalar(
        &mut self,
        engine: &Engine<'tcx>,
        body: &Body<'tcx>,
        state: &State,
        ticket: &ScalarTicket<'tcx>,
        result: &Value,
        block: rustc_middle::mir::BasicBlock,
    ) -> Checked<()> {
        self.current(engine, state)?;
        self.top(body)?;
        if !matches!(
            body.basic_blocks[block].terminator().kind,
            TerminatorKind::Return
        ) || self.pending.is_some()
            || !Rc::ptr_eq(&self.origin, &ticket.origin)
            || !same_body(&ticket.selected, body)
            || self.owners.len() != ticket.owners.len()
            || !self.owners.iter().zip(&ticket.owners).enumerate().all(
                |(i, (current, expected))| {
                    current.lease == expected.lease
                        && current.frames.len()
                            == expected.frames.len() + usize::from(i + 1 == self.owners.len())
                        && current
                            .frames
                            .iter()
                            .zip(&expected.frames)
                            .all(|(a, b)| Weak::ptr_eq(a, b))
                },
            )
            || engine
                .mutable_u16_contains(result, &state.memory)
                .map_err(|_| "scalar graph")?
        {
            return Err("scalar normal Return identity");
        }
        result_shape(engine, body.return_ty(), result)?;
        engine
            .validate_tracked_value(result, state)
            .map_err(|_| "scalar result")?;
        engine
            .validate_incoming_frame_escape(state, state.memory.len())
            .map_err(|_| "scalar incoming graph")?;
        self.owners.last_mut().unwrap().frames.pop();
        Ok(())
    }

    fn finish(
        &mut self,
        engine: &Engine<'tcx>,
        body: &Body<'tcx>,
        state: &State,
        ticket: &ReturnTicket<'tcx>,
        result: &Value,
        block: rustc_middle::mir::BasicBlock,
    ) -> Checked<()> {
        self.current(engine, state)?;
        if !matches!(
            body.basic_blocks[block].terminator().kind,
            TerminatorKind::Return
        ) || self.pending.is_some()
            || !Rc::ptr_eq(&ticket.origin, &self.origin)
            || !same_body(&ticket.selected, body)
            || self.top(body)?.lease != ticket.lease
            || self.owners.len() != ticket.prefix.len() + 1
            || self.owners.last().unwrap().frames.len() != 1
            || !self
                .owners
                .iter()
                .zip(&ticket.prefix)
                .all(|(actual, expected)| {
                    actual.lease == expected.lease
                        && actual.frames.len() == expected.frames.len()
                        && actual
                            .frames
                            .iter()
                            .zip(&expected.frames)
                            .all(|(a, b)| Weak::ptr_eq(a, b))
                })
        {
            return Err("normal owner Return identity");
        }
        if engine
            .mutable_u16_contains(result, &state.memory)
            .map_err(|_| "result graph")?
        {
            return Err("returned role");
        }
        result_shape(engine, body.return_ty(), result)?;
        engine
            .validate_tracked_value(result, state)
            .map_err(|_| "returned graph")?;
        engine
            .validate_incoming_frame_escape(state, state.memory.len())
            .map_err(|_| "incoming graph")?;
        let epoch = self.epoch.checked_add(1).ok_or("epoch overflow")?;
        self.owners.pop();
        self.epoch = epoch;
        Ok(())
    }
}

fn compiler_cases<'tcx>(tcx: TyCtxt<'tcx>, output: &std::path::Path) {
    let limits = miren::AnalysisLimits::default();
    let mut engine = Engine {
        tcx,
        terms: Context::default(),
        next_symbol: std::cell::Cell::new(0),
        float_encodings: BTreeMap::new(),
        float_pairs: float_pairs::Registry::default(),
        abstraction_symbols: std::cell::RefCell::new(BTreeMap::new()),
        static_views: std::cell::RefCell::new(Vec::new()),
        static_origins: Default::default(),
        static_epoch: None,
        static_roots: None,
        function_pointers: std::cell::RefCell::new(Vec::new()),
        static_addresses: std::collections::HashMap::new(),
        tracked_addresses: Vec::new(),
        maybe_uninit_types: Vec::new(),
        scalar_slice_types: Vec::new(),
        composite_slice_types: Vec::new(),
        steps: 0,
        call_chain: Vec::new(),
        failed_call_chain: None,
        trait_objects: Vec::new(),
        input_depth: 0,
        input_values: 0,
        input_reservations: Vec::new(),
        owned_projection_certificates: Vec::new(),
        input_shapes: std::collections::HashMap::new(),
        zero_sized_inputs: std::collections::HashMap::new(),
        zero_sized_input_nodes: 0,
        prefer_lazy_inputs: false,
        building_mutable_input: false,
        unknown_causes: std::cell::RefCell::new(BTreeMap::new()),
        started: std::time::Instant::now(),
        config: miren::ContractConfig::default(),
        all_failures: false,
        induction: false,
        startup: false,
        isolated_startup: false,
        limits,
        resolved_contracts: BTreeMap::new(),
        solver: std::cell::RefCell::new(Solver::with_limits(limits)),
        mutable_u16_frames: Default::default(),
        mutable_integer_types: Vec::new(),
        mutable_u16_staging: Default::default(),
        coroutine_places: Default::default(),
        owned_box_types: Vec::new(),
        next_owned_region: 0,
        owned_box_constructors: Vec::new(),
        bodies: std::cell::RefCell::new(std::collections::HashMap::new()),
        call_signatures: std::cell::RefCell::new(std::collections::HashMap::new()),
        proof: Proof {
            status: ProofStatus::Proved,
            async_entry: false,
            assumptions: Vec::new(),
            entry_assumptions: Vec::new(),
            inputs: BTreeMap::new(),
            models: Vec::new(),
            invariants: Vec::new(),
            analyzed_bodies: Vec::new(),
            body_entries: Vec::new(),
            body_entries_truncated: false,
            obligations: Vec::new(),
            trusted_calls: Vec::new(),
            matched_contracts: Vec::new(),
            stopped_after_counterexample: false,
            replay_inputs: None,
        },
    };
    let find = |name: &str| {
        tcx.mir_keys(())
            .iter()
            .copied()
            .find(|local| {
                tcx.def_kind(local.to_def_id()) == DefKind::Fn
                    && tcx.item_name(local.to_def_id()).as_str() == name
            })
            .unwrap()
            .to_def_id()
    };
    let root_instance = engine
        .resolve_function_item(find("root"), tcx.mk_args(&[]))
        .unwrap();
    let outer_instance = engine
        .resolve_function_item(find("outer"), tcx.mk_args(&[]))
        .unwrap();
    let leaf_instance = engine
        .resolve_function_item(find("leaf"), tcx.mk_args(&[]))
        .unwrap();
    let root = engine.instantiated_body(root_instance).unwrap();
    let outer = engine.instantiated_body(outer_instance).unwrap();
    let leaf = engine.instantiated_body(leaf_instance).unwrap();
    let scalar_instance = engine
        .resolve_function_item(find("scalar"), tcx.mk_args(&[]))
        .unwrap();
    let scalar = engine.instantiated_body(scalar_instance).unwrap();
    for (name, body) in [("root", &root), ("outer", &outer), ("leaf", &leaf)] {
        std::fs::write(output.join(format!("{name}.mir")), format!("{body:#?}")).unwrap();
    }
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let value = engine
        .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
        .unwrap();
    let make_state = |body: &Body<'tcx>, memory: Memory| {
        let mut state = State {
            locals: vec![None; body.local_decls.len()],
            addresses: vec![None; body.local_decls.len()],
            missing_places: Default::default(),
            conditions: conditions.clone(),
            memory,
        };
        state.locals[1] = Some(value.clone());
        state
    };
    let mut root_state = make_state(&root, memory);
    let original_frontier =
        super::mutable_hierarchy::compiler_probe(&mut engine, &root, &outer, &leaf, &root_state);
    std::fs::write(
        output.join("original-is-empty-frontier.txt"),
        original_frontier,
    )
    .unwrap();
    let root_len_instance = engine
        .resolve_function_item(find("root_len"), tcx.mk_args(&[]))
        .unwrap();
    let root_len = engine.instantiated_body(root_len_instance).unwrap();
    let root_len_state = make_state(&root_len, root_state.memory.clone());
    super::mutable_hierarchy::compiler_production_probe(&mut engine, &root_len, &root_len_state);
    for name in ["root_leaf_len", "root_scalar"] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        let base = make_state(&body, root_state.memory.clone());
        super::mutable_hierarchy::compiler_non_candidate_probe(&mut engine, &body, &base);
        std::fs::write(
            output.join(format!("public-noncandidate-{name}.mir")),
            format!("{body:#?}"),
        )
        .unwrap();
    }
    for name in ["root_len", "outer_len", "leaf_len", "scalar"] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        std::fs::write(
            output.join(format!("prospective-{name}.mir")),
            format!("{body:#?}"),
        )
        .unwrap();
    }
    for (name, original, wrong) in [
        ("root_i32", tcx.types.i32, tcx.types.u32),
        ("root_usize", tcx.types.usize, tcx.types.u64),
        ("root_bool", tcx.types.bool, tcx.types.char),
        ("root_char", tcx.types.char, tcx.types.u32),
    ] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        super::mutable_hierarchy::compiler_element_boundary_probe(
            &mut engine,
            &body,
            original,
            wrong,
        );
    }
    for name in [
        "root_char",
        "outer_char",
        "leaf_char",
        "scalar_char",
        "root_scalar_char",
        "root_pair_char",
        "char_store",
    ] {
        let instance = engine
            .resolve_function_item(find(name), tcx.mk_args(&[]))
            .unwrap();
        let body = engine.instantiated_body(instance).unwrap();
        std::fs::write(
            output.join(format!("char-{name}.mir")),
            format!("{body:#?}"),
        )
        .unwrap();
    }
    std::fs::write(
        output.join("direct-adapter-trace.json"),
        serde_json::to_string_pretty(&engine.proof).unwrap(),
    )
    .unwrap();

    let mut ledger = Ledger::new(&engine, &root, &root_state).unwrap();
    let original_generation = root_state.memory.mutable_u16[0].generation;
    let mut forged_handle = root_state.clone();
    forged_handle.locals[1] = Some(Value::Unit);
    assert!(ledger.access(&engine, &forged_handle, 0, &root, 1).is_err());
    let root_metadata = ledger.metadata(&engine, &root_state, 0, &root, 1).unwrap();
    let root_call = call_block(tcx, &root, outer_instance.def_id());
    let outer_lease = stage_block(&mut ledger, &engine, &root, &mut root_state, root_call, 0);
    assert_eq!(outer_lease, 1);
    assert!(ledger.access(&engine, &root_state, 0, &root, 1).is_err());
    ledger.lifetime(&engine, &root_state, 0).unwrap();
    let initial_ref = root.basic_blocks[root_call]
        .statements
        .iter()
        .find(|statement| {
            matches!(&statement.kind, StatementKind::Assign(assignment)
            if matches!(assignment.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _)))
        })
        .unwrap();
    assert!(
        ledger
            .stage(&engine, &root, &root_state, &initial_ref.kind, outer_lease)
            .is_err()
    );
    let mut bad_tip = ledger.clone();
    bad_tip.pending.as_mut().unwrap().tip.occurrence = 0;
    assert!(
        bad_tip
            .enter(
                &engine,
                &root,
                &mut root_state.clone(),
                root_call,
                &outer,
                outer_instance
            )
            .is_err()
    );
    let mut overflowing = ledger.clone();
    overflowing.issued = u64::MAX;
    overflowing.pending = None;
    assert!(
        overflowing
            .stage(&engine, &root, &root_state, &initial_ref.kind, 0)
            .is_err()
    );
    let mut overflowing_epoch = ledger.clone();
    overflowing_epoch.epoch = u64::MAX;
    overflowing_epoch.pending = None;
    assert!(
        overflowing_epoch
            .stage(&engine, &root, &root_state, &initial_ref.kind, 0)
            .is_err()
    );
    let before_enter = ledger.clone();
    let mut consumed = root_state.clone();
    let tip = ledger.pending.as_ref().unwrap().tip.local;
    consumed.missing_places.consume(tip, Vec::new()).unwrap();
    assert!(
        ledger
            .enter(
                &engine,
                &root,
                &mut consumed,
                root_call,
                &outer,
                outer_instance
            )
            .is_err()
    );
    ledger = before_enter;
    let outer_ticket = ledger
        .enter(
            &engine,
            &root,
            &mut root_state,
            root_call,
            &outer,
            outer_instance,
        )
        .unwrap();
    let mut outer_state = make_state(&outer, root_state.memory.clone());
    ledger.access(&engine, &outer_state, 1, &outer, 1).unwrap();
    assert!(
        ledger
            .metadata_access(&engine, &root_state, root_metadata, &root, 1)
            .is_err()
    );
    let old_parent_metadata = ledger
        .metadata(&engine, &outer_state, 1, &outer, 1)
        .unwrap();
    let leaf_call = call_block(tcx, &outer, leaf_instance.def_id());
    let leaf_lease = stage_block(&mut ledger, &engine, &outer, &mut outer_state, leaf_call, 1);
    assert_eq!(leaf_lease, 2);
    ledger.lifetime(&engine, &outer_state, 1).unwrap();
    assert!(ledger.access(&engine, &outer_state, 1, &outer, 1).is_err());
    let wrong_body = Rc::new((*outer).clone());
    assert!(ledger.top(&wrong_body).is_err());
    let leaf_ticket = ledger
        .enter(
            &engine,
            &outer,
            &mut outer_state,
            leaf_call,
            &leaf,
            leaf_instance,
        )
        .unwrap();
    let mut leaf_state = make_state(&leaf, outer_state.memory.clone());
    let leaf_metadata = ledger.metadata(&engine, &leaf_state, 2, &leaf, 1).unwrap();
    let before = leaf_state.memory.mutable_u16[0].data.clone();
    let bits = u32::from(tcx.sess.target.pointer_width);
    let index = symbolic::integer(&engine.terms, 0, bits, false)
        .integer()
        .unwrap()
        .0
        .clone();
    let word = symbolic::integer(&engine.terms, 19, 16, false)
        .integer()
        .unwrap()
        .0
        .clone();
    let changed = engine
        .terms
        .apply(Op::Store, &[before.clone(), index, word])
        .unwrap();
    Rc::make_mut(&mut leaf_state.memory.mutable_u16)[0].data = changed.clone();
    let scalar_call = call_block(tcx, &leaf, scalar_instance.def_id());
    let before_scalar_issued = ledger.issued;
    let scalar_ticket = ledger
        .push_scalar(
            &engine,
            &leaf,
            &leaf_state,
            scalar_call,
            &scalar,
            scalar_instance,
        )
        .unwrap();
    assert_eq!(ledger.issued, before_scalar_issued);
    let mut scalar_state = make_state(&scalar, leaf_state.memory.clone());
    scalar_state.locals[1] = Some(symbolic::integer(&engine.terms, 19, 16, false));
    assert!(
        ledger
            .finish(
                &engine,
                &leaf,
                &leaf_state,
                &leaf_ticket,
                &Value::Unit,
                return_block(&leaf)
            )
            .is_err()
    );
    assert!(
        ledger
            .pop_scalar(
                &engine,
                &leaf,
                &leaf_state,
                &scalar_ticket,
                &Value::Unit,
                return_block(&leaf)
            )
            .is_err()
    );
    ledger
        .pop_scalar(
            &engine,
            &scalar,
            &scalar_state,
            &scalar_ticket,
            scalar_state.locals[1].as_ref().unwrap(),
            return_block(&scalar),
        )
        .unwrap();
    assert_eq!(ledger.issued, before_scalar_issued);
    assert!(
        ledger
            .access(&engine, &scalar_state, 2, &scalar, 1)
            .is_err()
    );
    assert_eq!(ledger.top(&leaf).unwrap().lease, 2);
    let leaf_return = return_block(&leaf);
    assert!(
        ledger
            .finish(
                &engine,
                &outer,
                &leaf_state,
                &outer_ticket,
                &Value::Unit,
                return_block(&outer)
            )
            .is_err()
    );
    let mut forged = ledger.clone();
    forged.origin = Rc::new((*ledger.origin).clone());
    assert!(
        forged
            .finish(
                &engine,
                &leaf,
                &leaf_state,
                &leaf_ticket,
                &Value::Unit,
                leaf_return
            )
            .is_err()
    );
    let mut ancestor_prefix = ledger.clone();
    ancestor_prefix.owners[0].lease = 99;
    assert!(
        ancestor_prefix
            .finish(
                &engine,
                &leaf,
                &leaf_state,
                &leaf_ticket,
                &Value::Unit,
                leaf_return
            )
            .is_err()
    );
    let mut owner_mask = leaf_state.clone();
    owner_mask
        .memory
        .missing_places
        .consume(ledger.origin.allocation, Vec::new())
        .unwrap();
    assert!(
        ledger
            .finish(
                &engine,
                &leaf,
                &owner_mask,
                &leaf_ticket,
                &Value::Unit,
                leaf_return
            )
            .is_err()
    );
    assert!(
        ledger
            .finish(
                &engine,
                &leaf,
                &leaf_state,
                &leaf_ticket,
                leaf_state.locals[1].as_ref().unwrap(),
                leaf_return
            )
            .is_err()
    );
    let mut malformed_body = (*leaf).clone();
    malformed_body.spread_arg = Some(rustc_middle::mir::Local::from_usize(1));
    assert!(body_budget(&malformed_body).is_err());
    let mut wrong_memory = leaf_state.clone();
    Rc::make_mut(&mut wrong_memory.memory.mutable_u16)[0].certificate += 1;
    assert!(
        ledger
            .finish(
                &engine,
                &leaf,
                &wrong_memory,
                &leaf_ticket,
                &Value::Unit,
                leaf_return
            )
            .is_err()
    );
    let mut frame_pending = ledger.clone();
    frame_pending
        .owners
        .last_mut()
        .unwrap()
        .frames
        .push(Rc::downgrade(&leaf));
    assert!(
        frame_pending
            .finish(
                &engine,
                &leaf,
                &leaf_state,
                &leaf_ticket,
                &Value::Unit,
                leaf_return
            )
            .is_err()
    );
    ledger
        .finish(
            &engine,
            &leaf,
            &leaf_state,
            &leaf_ticket,
            &Value::Unit,
            leaf_return,
        )
        .unwrap();
    assert_eq!(ledger.issued, 2);
    assert_eq!(ledger.owners.last().unwrap().lease, 1);
    outer_state.memory = leaf_state.memory.clone();
    ledger.access(&engine, &outer_state, 1, &outer, 1).unwrap();
    assert!(ledger.lifetime(&engine, &outer_state, 2).is_err());
    assert!(
        ledger
            .metadata_access(&engine, &outer_state, old_parent_metadata, &outer, 1)
            .is_err()
    );
    assert!(
        ledger
            .metadata_access(&engine, &leaf_state, leaf_metadata, &leaf, 1)
            .is_err()
    );
    assert_eq!(outer_state.memory.mutable_u16[0].data, changed);
    let fresh_metadata = ledger
        .metadata(&engine, &outer_state, 1, &outer, 1)
        .unwrap();
    ledger
        .metadata_access(&engine, &outer_state, fresh_metadata, &outer, 1)
        .unwrap();
    // Replay a real compiler occurrence for a second independent round; IDs never restore.
    let mut second_state = make_state(&outer, outer_state.memory.clone());
    let second_lease = stage_block(
        &mut ledger,
        &engine,
        &outer,
        &mut second_state,
        leaf_call,
        1,
    );
    assert_eq!(second_lease, 3);
    let second_ticket = ledger
        .enter(
            &engine,
            &outer,
            &mut second_state,
            leaf_call,
            &leaf,
            leaf_instance,
        )
        .unwrap();
    assert!(ledger.lifetime(&engine, &second_state, 2).is_err());
    let second_leaf_state = make_state(&leaf, second_state.memory.clone());
    ledger
        .finish(
            &engine,
            &leaf,
            &second_leaf_state,
            &second_ticket,
            &Value::Unit,
            leaf_return,
        )
        .unwrap();
    // Consumed parent handles stay consumed when the parent lease resumes.
    second_state.missing_places.consume(1, Vec::new()).unwrap();
    assert!(ledger.access(&engine, &second_state, 1, &outer, 1).is_err());
    assert!(second_state.missing_places.check(1, &[]).is_err());
    ledger
        .finish(
            &engine,
            &outer,
            &outer_state,
            &outer_ticket,
            &Value::Unit,
            return_block(&outer),
        )
        .unwrap();
    assert_eq!(ledger.issued, 3);
    assert_eq!(ledger.owners.last().unwrap().lease, 0);
    assert!(ledger.lifetime(&engine, &outer_state, 1).is_err());
    assert_eq!(
        outer_state.memory.mutable_u16[0].generation,
        original_generation
    );
    assert_eq!(outer_state.memory.mutable_u16[0].data, changed);
    let mut budget_state = root_state.clone();
    while budget_state.memory.storage_slots() < MAX_INPUT_VALUES {
        budget_state.memory.push(Some(Value::Unit));
    }
    assert!(ledger.charge(&budget_state, 0).is_err());
    let mut expired = ledger.clone();
    let held = Rc::new((*root).clone());
    expired.owners[0].frames = vec![Rc::downgrade(&held)];
    drop(held);
    assert!(expired.lifetime(&engine, &root_state, 0).is_err());
    assert!(expired.top(&root).is_err());
    let context = Context::default();
    let mut wrong_context = root_state.clone();
    Rc::make_mut(&mut wrong_context.memory.mutable_u16)[0].data =
        context.symbol(0, before.sort().clone()).unwrap();
    assert!(ledger.current(&engine, &wrong_context).is_err());
    std::fs::write(
        output.join("checkpoint.txt"),
        concat!(
            "shadow and scoped public Call/staging/Return tests passed; ",
            "production issuer false; no CLI support\n"
        ),
    )
    .unwrap();
}

fn call_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee: DefId,
) -> rustc_middle::mir::BasicBlock {
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                return None;
            };
            matches!(func.ty(&body.local_decls, tcx).kind(), ty::FnDef(id, _) if *id == callee)
                .then_some(block)
        })
        .unwrap()
}

fn return_block(body: &Body<'_>) -> rustc_middle::mir::BasicBlock {
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            matches!(data.terminator().kind, TerminatorKind::Return).then_some(block)
        })
        .unwrap()
}

fn stage_block<'tcx>(
    ledger: &mut Ledger<'tcx>,
    engine: &Engine<'tcx>,
    body: &Rc<Body<'tcx>>,
    state: &mut State,
    block: rustc_middle::mir::BasicBlock,
    parent: u64,
) -> u64 {
    let mut lease = parent;
    let mut tips = Vec::new();
    for statement in &body.basic_blocks[block].statements {
        if let StatementKind::Assign(assignment) = &statement.kind
            && matches!(assignment.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            lease = ledger
                .stage(engine, body, state, &statement.kind, lease)
                .unwrap();
            state.locals[assignment.0.local.as_usize()] = state.locals[1].clone();
            tips.push(assignment.0.local.as_usize());
        }
    }
    assert!(!tips.is_empty());
    if tips.len() > 1 {
        assert_ne!(tips[0], ledger.pending.as_ref().unwrap().tip.local);
    }
    lease
}

#[test]
fn compiler_nested_whole_u16_inactive_lifecycle() {
    struct Capture {
        output: std::path::PathBuf,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            compiler_cases(tcx, &self.output);
            rustc_driver::Compilation::Stop
        }
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "miren-stage209-parent208-compiler-{}-{nonce}",
        std::process::id()
    ));
    eprintln!(
        "Stage209 actual208 unique compiler scratch: {}",
        root.display()
    );
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("fixture.rs");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "#[inline(never)] fn scalar(word:u16)->u16 { word ^ 0 }\n",
            "#[inline(never)] fn leaf(v:&mut[u16]) { if !v.is_empty() { v[0]=scalar(v[0]); } }\n",
            "#[inline(never)] fn outer(v:&mut[u16]) { leaf(&mut *(&mut *v)); leaf(v); }\n",
            "pub fn root(v:&mut[u16]) { outer(v); }\n",
            "#[inline(never)] fn leaf_len(v:&mut[u16]) { if v.len()>0 { ",
            "v[0]=scalar(v[0]); } }\n",
            "#[inline(never)] fn outer_len(v:&mut[u16]) { leaf_len(&mut *(&mut *v)); ",
            "leaf_len(v); }\n",
            "pub fn root_len(v:&mut[u16]) { outer_len(v); }\n",
            "pub fn root_leaf_len(v:&mut[u16]) { leaf_len(v); }\n",
            "pub fn root_scalar(word:u16)->u16 { scalar(word) }\n",
            "pub fn root_wrapping(word:u16)->u16 { word.wrapping_add(1) }\n",
            "pub fn root_pair(pair:(i16,u16))->u16 { pair.1.wrapping_add(1) }\n",
            "#[inline(never)] fn leaf_i32(v:&mut[i32]) { if v.len()>0 { v[0]=17; } }\n",
            "#[inline(never)] fn outer_i32(v:&mut[i32]) { leaf_i32(&mut *(&mut *v)); }\n",
            "pub fn root_i32(v:&mut[i32]) { outer_i32(v); }\n",
            "#[inline(never)] fn leaf_usize(v:&mut[usize]) { if v.len()>0 { v[0]=17; } }\n",
            "#[inline(never)] fn outer_usize(v:&mut[usize]) { leaf_usize(&mut *(&mut *v)); }\n",
            "pub fn root_usize(v:&mut[usize]) { outer_usize(v); }\n",
            "#[inline(never)] fn leaf_bool(v:&mut[bool]) { if v.len()>0 { v[0]=true; } }\n",
            "#[inline(never)] fn outer_bool(v:&mut[bool]) { leaf_bool(&mut *(&mut *v)); }\n",
            "pub fn root_bool(v:&mut[bool]) { outer_bool(v); }\n",
            "#[inline(never)] fn scalar_char(word:char)->char { word }\n",
            "#[inline(never)] fn leaf_char(v:&mut[char]) { if v.len()>0 { ",
            "v[0]=scalar_char('a'); } }\n",
            "#[inline(never)] fn outer_char(v:&mut[char]) { leaf_char(&mut *(&mut *v)); }\n",
            "pub fn root_char(v:&mut[char]) { outer_char(v); }\n",
            "pub fn root_scalar_char(word:char)->char { scalar_char(word) }\n",
            "pub fn root_pair_char(pair:(u32,char))->char { scalar_char(pair.1) }\n",
            "pub fn char_store(v:&mut[char],index:usize,word:char) { v[index]=word; }\n"
        ),
    )
    .unwrap();
    for (target, tag) in [(None, "host"), (Some("thumbv7em-none-eabihf"), "arm")] {
        for opt in [0, 2] {
            let output = root.join(format!("{tag}-o{opt}"));
            std::fs::create_dir_all(&output).unwrap();
            let mut args = vec![
                "rustc".into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                source.display().to_string(),
                "--out-dir".into(),
                output.display().to_string(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={opt}"),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            std::fs::write(output.join("command.txt"), args.join("\n")).unwrap();
            rustc_driver::run_compiler(&args, &mut Capture { output });
        }
    }
}
