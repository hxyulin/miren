//! Private branch-local activation transport. Arming is confined to compiler tests for now.
use super::*;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

const ACTIVATION_STRUCTURAL_WORK_LIMIT: usize = 2048;

#[derive(Clone, Debug)]
pub(super) enum Flow {
    Unarmed,
    Armed(Armed),
}

#[derive(Clone, Debug)]
pub(super) struct Armed {
    engine: Rc<()>,
    frame: Rc<Frame>,
    receipts: Rc<Vec<Receipt>>,
    retained_floor: Rc<Vec<Receipt>>,
    pending: Option<Rc<Frame>>,
    work: Rc<RefCell<Work>>,
}

#[derive(Debug)]
struct Frame {
    identity: Rc<()>,
    entry: Rc<()>,
    entry_slot: usize,
    parent: Option<Rc<()>>,
    incoming: Rc<Vec<Receipt>>,
    depth: usize,
    work: Rc<RefCell<Work>>,
}

#[derive(Clone, Debug)]
struct Receipt {
    origin: Rc<mutable_hierarchy::Origin>,
    backing: usize,
    issued: u64,
    epoch: u64,
}

#[derive(Debug)]
struct Work {
    used: usize,
    limit: usize,
    checked: Vec<Rc<()>>,
}

impl Work {
    fn charge(&mut self, count: usize) -> Result<(), String> {
        if self.limit == 0 || self.limit > ACTIVATION_STRUCTURAL_WORK_LIMIT {
            return Err("activation structural policy is invalid".into());
        }
        self.used = self
            .used
            .checked_add(count)
            .ok_or("activation work overflow")?;
        if self.used > self.limit {
            return Err(format!(
                "activation transport exceeds shared work budget: used {}, last charge {count}",
                self.used
            ));
        }
        Ok(())
    }
}

struct Entry<'tcx> {
    instance: ty::Instance<'tcx>,
    identity: Rc<()>,
    body: Weak<Body<'tcx>>,
}

pub(super) struct Registry<'tcx> {
    identity: Rc<()>,
    entries: Vec<Entry<'tcx>>,
}

impl Default for Registry<'_> {
    fn default() -> Self {
        Self {
            identity: Rc::new(()),
            entries: Vec::new(),
        }
    }
}

impl Flow {
    pub(super) fn require_unarmed(&self) -> Result<(), String> {
        match self {
            Self::Unarmed => Ok(()),
            Self::Armed(_) => Err("armed activation adapter is not implemented".into()),
        }
    }

    pub(super) fn unarmed_leaf(&self) -> Result<Self, String> {
        self.require_unarmed()?;
        Ok(Self::Unarmed)
    }

    pub(super) fn charge(&self, count: usize) -> Result<(), String> {
        match self {
            Self::Unarmed => Ok(()),
            Self::Armed(flow) => flow.work.borrow_mut().charge(count),
        }
    }

    fn constant_clone_leaf(value: &Value) -> Result<(), String> {
        match value {
            Value::MutableU16 {
                role: symbolic::MutableU16Role::Ghost { .. },
                ..
            } => Err("armed activation Ghost clone is unsupported".into()),
            Value::MutableU16 { .. }
            | Value::RawPointer { .. }
            | Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Elements(_)
            | Value::Uninitialized
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => Ok(()),
            Value::OwnedRegion { .. }
            | Value::OwnedSnapshot(_)
            | Value::MaybeUninit { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::TrackedPointer { .. }
            | Value::RawSlice { .. }
            | Value::Bytes { .. }
            | Value::CompositeSlice { .. }
            | Value::ScalarSlice { .. }
            | Value::Adt { .. }
            | Value::Enum { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::Reference { .. }
            | Value::SliceIterator { .. }
            | Value::Tuple(_)
            | Value::MetadataPointer(_)
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::StaticText
            | Value::FormatArguments => {
                Err("armed activation recursive local clone is unsupported".into())
            }
        }
    }

    fn clone_constant_local(value: &Value) -> Result<Value, String> {
        Self::constant_clone_leaf(value)?;
        // Every accepted variant has constant-size fields or immutable Rc payloads.
        // InputValue shares its InputShape and Term; Elements shares its vector.
        Ok(value.clone())
    }

    fn clone_armed_continuation(
        &self,
        state: &State,
        conditions: Vec<Term>,
        memory: Memory,
    ) -> Result<State, String> {
        self.charge(state.locals.len().saturating_add(state.addresses.len()))?;
        // Validation and construction share this single charged per-slot traversal.
        // There is no later Vec<Value>::clone pass and no recursive owned payload.
        let mut locals = Vec::with_capacity(state.locals.len());
        for local in &state.locals {
            locals.push(local.as_ref().map(Self::clone_constant_local).transpose()?);
        }
        self.charge_masks(&state.missing_places)?;
        self.charge(state.constant_receipts.len().saturating_mul(2))?;
        Ok(State {
            flow: self.clone(),
            locals,
            constant_receipts: state.constant_receipts.clone(),
            missing_places: state.missing_places.clone(),
            conditions,
            addresses: state.addresses.clone(),
            memory,
        })
    }

    #[cfg(test)]
    pub(super) fn structural_limit(&self) -> Option<usize> {
        match self {
            Self::Unarmed => None,
            Self::Armed(flow) => Some(flow.work.borrow().limit),
        }
    }

    pub(super) fn validate_arguments(&self, arguments: &[Value]) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        self.charge(arguments.len())?;
        for value in arguments {
            Self::constant_clone_leaf(value)?;
        }
        Ok(())
    }

    pub(super) fn clone_argument(&self, value: &Value) -> Result<Value, String> {
        if matches!(self, Self::Unarmed) {
            return Ok(value.clone());
        }
        self.charge(1)?;
        Self::clone_constant_local(value)
    }

    pub(super) fn charge_clone_value(&self, value: &Value) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        self.charge(1)?;
        Self::constant_clone_leaf(value)
    }

    pub(super) fn charge_masks(
        &self,
        masks: &initialized_places::MissingPlaces,
    ) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        // Validate entries, then clone their vector in a separate traversal.
        self.charge(masks.entries().len().saturating_mul(2))?;
        for (_, path) in masks.entries() {
            self.charge(path.len())?;
        }
        Ok(())
    }

    fn charge_continuation(&self, state: &State) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        self.charge(state.locals.len().saturating_add(state.addresses.len()))?;
        for value in state.locals.iter().flatten() {
            self.charge_clone_value(value)?;
        }
        self.charge_masks(&state.missing_places)
    }

    pub(super) fn charge_call_memory(
        &self,
        conditions: &[Term],
        memory: &Memory,
    ) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        self.charge(conditions.len())?;
        memory.activation_charge_clone(self)
    }

    pub(super) fn charge_branch(&self, state: &State) -> Result<(), String> {
        if matches!(self, Self::Unarmed) {
            return Ok(());
        }
        self.charge_continuation(state)?;
        self.charge(state.conditions.len())?;
        state.memory.activation_charge_clone(self)
    }

    pub(super) fn charge_publication(&self, state: &State, place: Place<'_>) -> Result<(), String> {
        if matches!(self, Self::Unarmed) || place.projection.is_empty() {
            return Ok(());
        }
        self.charge(place.projection.len())?;
        let value = state.locals[place.local.as_usize()]
            .as_ref()
            .ok_or("armed publication root is unavailable")?;
        match value {
            Value::Elements(fields) => {
                // The shared Elements clone is constant work; an actual write may detach
                // its vector. Charge every borrowed field and cloned value beforehand.
                self.charge(fields.len())?;
                for field in fields.iter() {
                    self.charge_clone_value(field)?;
                }
                Ok(())
            }
            Value::MutableU16 { .. }
            | Value::OwnedRegion { .. }
            | Value::OwnedSnapshot(_)
            | Value::Uninitialized
            | Value::MaybeUninit { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::RawPointer { .. }
            | Value::TrackedPointer { .. }
            | Value::RawSlice { .. }
            | Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Bytes { .. }
            | Value::CompositeSlice { .. }
            | Value::ScalarSlice { .. }
            | Value::Adt { .. }
            | Value::Enum { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::Reference { .. }
            | Value::SliceIterator { .. }
            | Value::Tuple(_)
            | Value::MetadataPointer(_)
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => {
                Err("armed activation projected publication is not implemented".into())
            }
        }
    }

    fn floor_contains(receipts: &[Receipt], incoming: &[Receipt]) -> bool {
        incoming.iter().all(|floor| {
            receipts.iter().any(|r| {
                Rc::ptr_eq(&r.origin, &floor.origin)
                    && r.backing == floor.backing
                    && r.issued >= floor.issued
                    && r.epoch >= floor.epoch
            })
        })
    }

    fn validate_floor(&self) -> Result<(), String> {
        if let Self::Armed(flow) = self {
            if flow.receipts.len() > MAX_INPUT_VALUES
                || flow.frame.incoming.len() > MAX_INPUT_VALUES
                || flow.retained_floor.len() > MAX_INPUT_VALUES
            {
                return Err("activation receipt extent exceeds its independent bound".into());
            }
            let incoming_same = Rc::ptr_eq(&flow.receipts, &flow.frame.incoming);
            let retained_same = Rc::ptr_eq(&flow.receipts, &flow.retained_floor);
            let incoming_work = if incoming_same {
                1
            } else {
                flow.receipts
                    .len()
                    .saturating_mul(flow.frame.incoming.len())
            };
            let retained_work = if retained_same {
                1
            } else {
                flow.receipts
                    .len()
                    .saturating_mul(flow.retained_floor.len())
            };
            self.charge(incoming_work.saturating_add(retained_work))?;
            if (!incoming_same && !Self::floor_contains(&flow.receipts, &flow.frame.incoming))
                || (!retained_same && !Self::floor_contains(&flow.receipts, &flow.retained_floor))
            {
                return Err("activation Return lost its incoming floor or pending call".into());
            }
        }
        Ok(())
    }

    pub(super) fn validate_return(&self) -> Result<(), String> {
        if matches!(self, Self::Armed(flow) if flow.pending.is_some()) {
            return Err("activation Return lost its incoming floor or pending call".into());
        }
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn activation_armed_call_route(
        &self,
        flow: &Flow,
        instance: ty::Instance<'tcx>,
    ) -> Result<bool, String> {
        if matches!(flow, Flow::Unarmed) {
            return Ok(false);
        }
        if self.specification(instance)?.is_some() || !self.contracts(instance.def_id()).is_empty()
        {
            return Err("armed activation contract adapter is not implemented".into());
        }
        if self.issued_float_is_empty_candidate(instance) {
            return Err("armed Float metadata adapter is not implemented".into());
        }
        if self.mutable_metadata_operation(instance) {
            return Ok(true);
        }
        let id = instance.def_id();
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !id.is_local()
            || !matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn)
            || (self.tcx.def_kind(id) == DefKind::AssocFn
                && self.tcx.associated_item(id).is_method())
            || !self.tcx.is_mir_available(id)
        {
            return Err("armed activation target adapter is not implemented".into());
        }
        let signature = self.tcx.fn_sig(id).instantiate_identity().skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return Err("armed activation target ABI is not implemented".into());
        }
        Ok(false)
    }

    pub(super) fn activation_prepare_body(
        &self,
        flow: &Flow,
        instance: ty::Instance<'tcx>,
    ) -> Result<Rc<Body<'tcx>>, String> {
        let Flow::Armed(armed) = flow else {
            return self.instantiated_body(instance);
        };
        if self.specification(instance)?.is_some() || !self.contracts(instance.def_id()).is_empty()
        {
            return Err("armed activation contract adapter is not implemented".into());
        }
        {
            let registry = self.activation.borrow();
            if registry.entries.len() > MAX_INPUT_VALUES {
                return Err("activation body registry capacity reached".into());
            }
            let mut selected = None;
            for entry in &registry.entries {
                flow.charge(1)?;
                if entry.instance == instance {
                    selected = Some(entry);
                    break;
                }
            }
            if let Some(entry) = selected {
                let body = entry
                    .body
                    .upgrade()
                    .ok_or("activation prepared body expired")?;
                flow.charge(instance.args.len().saturating_add(1))?;
                if !self
                    .bodies
                    .borrow()
                    .get(&instance)
                    .is_some_and(|cached| Rc::ptr_eq(cached, &body))
                {
                    return Err("activation prepared body cache key changed".into());
                }
                let checked_count = armed.work.borrow().checked.len();
                if checked_count > MAX_INPUT_VALUES {
                    return Err("activation checked-entry capacity reached".into());
                }
                flow.charge(1)?;
                let mut checked = false;
                for index in 0..checked_count {
                    flow.charge(1)?;
                    if Rc::ptr_eq(&armed.work.borrow().checked[index], &entry.identity) {
                        checked = true;
                        break;
                    }
                }
                if checked {
                    // The exact full key and still-live Rc were bounded under this same outer work.
                    // No body is cloned and no normalization query is repeated on this path.
                    return Ok(body);
                }
            }
        }
        // Bound and charge the exact Engine cache lookup before selecting a shared body.
        if self.bodies.borrow().len() > MAX_INPUT_VALUES {
            return Err("activation Engine body cache exceeds bounded extent".into());
        }
        // HashMap get hashes the selected full key; it does not traverse every Body.
        flow.charge(instance.args.len().saturating_add(1))?;
        let cached = self.bodies.borrow().get(&instance).cloned();
        let mut admission_work = 0;
        let body = if let Some(body) = cached {
            self.activation_borrowed_signature(instance, &mut admission_work, flow)?;
            self.activation_borrowed_publication(instance, &body, &mut admission_work, flow)?;
            body
        } else {
            // Only actual instantiation/deep cloning needs the original MIR inventory.
            self.activation_borrowed_preflight(instance, &mut admission_work, flow)?;
            // Original inventory bounds every caller-visible Body clone/fold input pass.
            // The scans already performed are not credits for these separate operations.
            flow.charge(admission_work.saturating_mul(3))?;
            let body = self.instantiated_body(instance)?;
            self.activation_borrowed_publication(instance, &body, &mut admission_work, flow)?;
            body
        };
        let (token, _) = self.activation_entry(instance, &body, flow)?;
        if armed.work.borrow().checked.len() >= MAX_INPUT_VALUES {
            return Err("activation checked-entry capacity reached".into());
        }
        flow.charge(1)?;
        armed.work.borrow_mut().checked.push(token);
        Ok(body)
    }

    pub(super) fn activation_preclone(
        &self,
        flow: &Flow,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if matches!(flow, Flow::Unarmed) {
            return Ok(());
        }
        self.activation_prepare_body(flow, instance).map(|_| ())
    }

    fn activation_entry(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        flow: &Flow,
    ) -> Result<(Rc<()>, usize), String> {
        let mut registry = self.activation.borrow_mut();
        flow.charge(registry.entries.len().saturating_add(1))?;
        if let Some((slot, entry)) = registry
            .entries
            .iter()
            .enumerate()
            .find(|(_, e)| e.instance == instance)
        {
            let actual = entry
                .body
                .upgrade()
                .ok_or("activation body evidence expired")?;
            if !Rc::ptr_eq(&actual, body) {
                return Err("activation body evidence changed under the same full Instance".into());
            }
            return Ok((entry.identity.clone(), slot));
        }
        if registry.entries.len() >= MAX_INPUT_VALUES {
            return Err("activation body registry capacity reached".into());
        }
        let identity = Rc::new(());
        let slot = registry.entries.len();
        registry.entries.push(Entry {
            instance,
            identity: identity.clone(),
            body: Rc::downgrade(body),
        });
        Ok((identity, slot))
    }

    pub(super) fn activation_validate(&self, flow: &Flow, memory: &Memory) -> Result<(), String> {
        let Flow::Armed(armed) = flow else {
            return Ok(());
        };
        flow.validate_floor()?;
        let registry = self.activation.borrow();
        if !Rc::ptr_eq(&registry.identity, &armed.engine)
            || !Rc::ptr_eq(&armed.work, &armed.frame.work)
        {
            return Err("activation flow belongs to another Engine".into());
        }
        if registry.entries.len() > MAX_INPUT_VALUES {
            return Err("activation body registry capacity reached".into());
        }
        flow.charge(armed.receipts.len())?;
        // Slots belong to this append-only private registry. The opaque Rc token still
        // authenticates the slot; a numeric position alone grants no body authority.
        flow.charge(1)?;
        let entry = registry
            .entries
            .get(armed.frame.entry_slot)
            .filter(|entry| Rc::ptr_eq(&entry.identity, &armed.frame.entry))
            .ok_or("activation frame has no authenticated body entry")?;
        let body = entry
            .body
            .upgrade()
            .ok_or("activation frame body expired")?;
        flow.charge(entry.instance.args.len().saturating_add(1))?;
        let bodies = self.bodies.borrow();
        if !bodies
            .get(&entry.instance)
            .is_some_and(|actual| Rc::ptr_eq(actual, &body))
        {
            return Err("activation exact body cache association changed".into());
        }
        for receipt in armed.receipts.iter() {
            self.mutable_hierarchy_activation_live(
                memory,
                receipt.backing,
                &receipt.origin,
                receipt.issued,
                receipt.epoch,
                flow,
            )?;
        }
        Ok(())
    }

    pub(super) fn activation_call_flow(
        &self,
        caller: &mut Flow,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        memory: &Memory,
        stack: &[DefId],
    ) -> Result<Flow, String> {
        self.activation_validate(caller, memory)?;
        if matches!(caller, Flow::Unarmed) {
            return Ok(Flow::Unarmed);
        }
        let hierarchy_depth = self.activation_hierarchy_depth(caller, memory)?;
        let Flow::Armed(armed) = caller else {
            unreachable!()
        };
        let prospective_depth = armed
            .frame
            .depth
            .saturating_add(1)
            .saturating_add(stack.len().saturating_add(1))
            .saturating_add(hierarchy_depth);
        if armed.pending.is_some() || prospective_depth > MAX_INPUT_DEPTH {
            return Err("activation call has pending work or exceeds existing depth".into());
        }
        // Legacy duplicate ancestors are refused, not silently removed from the depth sum.
        armed.work.borrow_mut().charge(
            stack
                .len()
                .saturating_mul(stack.len())
                .saturating_add(stack.len()),
        )?;
        if stack
            .iter()
            .enumerate()
            .any(|(i, id)| stack[..i].contains(id))
            || stack.contains(&instance.def_id())
        {
            return Err("activation call stack is not acyclic".into());
        }
        let count = armed.receipts.len();
        caller.charge(count.saturating_add(3))?;
        let (entry, entry_slot) = self.activation_entry(instance, body, caller)?;
        let Flow::Armed(armed) = caller else {
            unreachable!()
        };
        let frame = Rc::new(Frame {
            identity: Rc::new(()),
            entry,
            entry_slot,
            parent: Some(armed.frame.identity.clone()),
            incoming: armed.receipts.clone(),
            depth: armed.frame.depth + 1,
            work: armed.work.clone(),
        });
        if frame.depth >= MAX_INPUT_DEPTH {
            return Err("activation frame depth exceeded".into());
        }
        armed.pending = Some(frame.clone());
        Ok(Flow::Armed(Armed {
            engine: armed.engine.clone(),
            frame,
            receipts: armed.receipts.clone(),
            retained_floor: armed.receipts.clone(),
            pending: None,
            work: armed.work.clone(),
        }))
    }

    pub(super) fn activation_observe(
        &self,
        flow: &mut Flow,
        memory: &Memory,
    ) -> Result<(), String> {
        let Flow::Armed(armed) = flow else {
            return Ok(());
        };
        let Some(backing) = memory.mutable_hierarchy else {
            return Ok(());
        };
        let count = armed.receipts.len();
        let (origin, issued, epoch) =
            self.mutable_hierarchy_activation_snapshot(memory, backing, flow)?;
        // One charged borrowed scan identifies the receipt; COW materialization is
        // charged separately before cloning the shared vector. No second search occurs.
        flow.charge(count)?;
        let Flow::Armed(armed) = flow else {
            unreachable!()
        };
        let found = armed
            .receipts
            .iter()
            .position(|r| Rc::ptr_eq(&r.origin, &origin));
        if let Some(index) = found {
            let old = &armed.receipts[index];
            if old.backing != backing || issued < old.issued || epoch < old.epoch {
                return Err("activation observation rolled back its existing receipt".into());
            }
        }
        if found.is_none() && count >= MAX_INPUT_VALUES {
            return Err("activation receipt capacity reached".into());
        }
        let copied = if Rc::strong_count(&armed.receipts) > 1 {
            count
        } else {
            0
        };
        flow.charge(copied.saturating_add(1))?;
        let Flow::Armed(armed) = flow else {
            unreachable!()
        };
        let receipts = Rc::make_mut(&mut armed.receipts);
        if let Some(index) = found {
            let old = &mut receipts[index];
            old.issued = issued;
            old.epoch = epoch;
        } else {
            receipts.push(Receipt {
                origin,
                backing,
                issued,
                epoch,
            });
        }
        armed.retained_floor = armed.receipts.clone();
        self.activation_validate(flow, memory)
    }

    pub(super) fn adopt_flow_return(
        &self,
        state: &State,
        conditions: Vec<Term>,
        memory: Memory,
        returned_flow: Flow,
    ) -> Result<State, String> {
        match (&state.flow, &returned_flow) {
            (Flow::Unarmed, Flow::Unarmed) => {}
            (Flow::Armed(caller), Flow::Armed(child)) => {
                let expected = caller
                    .pending
                    .as_ref()
                    .ok_or("activation caller has no pending nonce")?;
                if !Rc::ptr_eq(&caller.engine, &child.engine)
                    || !Rc::ptr_eq(&caller.work, &child.work)
                    || !Rc::ptr_eq(expected, &child.frame)
                    || !child
                        .frame
                        .parent
                        .as_ref()
                        .is_some_and(|p| Rc::ptr_eq(p, &caller.frame.identity))
                {
                    return Err(
                        "activation Return substituted engine, work, nonce or branch".into(),
                    );
                }
            }
            (Flow::Unarmed, Flow::Armed(_)) | (Flow::Armed(_), Flow::Unarmed) => {
                return Err("activation Return erased or fabricated armed transport".into());
            }
        }
        returned_flow.validate_return()?;
        self.activation_validate(&returned_flow, &memory)?;
        if let Flow::Armed(child) = &returned_flow {
            // Bound the complete backing/receipt search before inspecting current origins.
            returned_flow.charge(
                memory
                    .mutable_u16
                    .len()
                    .saturating_mul(child.receipts.len().max(1)),
            )?;
            for id in 0..memory.mutable_u16.len() {
                if let Some(origin) = self.mutable_hierarchy_activation_origin(&memory, id)
                    && !child
                        .receipts
                        .iter()
                        .any(|receipt| receipt.backing == id && Rc::ptr_eq(&receipt.origin, origin))
                {
                    return Err("activation Return lost a current Memory origin receipt".into());
                }
            }
        }
        self.activation_validate(&state.flow, &state.memory)?;
        let flow = match (&state.flow, &returned_flow) {
            (Flow::Unarmed, Flow::Unarmed) => Flow::Unarmed,
            (Flow::Armed(caller), Flow::Armed(child)) => {
                let expected = caller
                    .pending
                    .as_ref()
                    .ok_or("activation caller has no pending nonce")?;
                state
                    .flow
                    .charge(child.receipts.len().saturating_mul(caller.receipts.len()))?;
                if !Rc::ptr_eq(&caller.work, &child.work)
                    || !Rc::ptr_eq(expected, &child.frame)
                    || !child
                        .frame
                        .parent
                        .as_ref()
                        .is_some_and(|p| Rc::ptr_eq(p, &caller.frame.identity))
                    || !Flow::floor_contains(&child.receipts, &caller.receipts)
                {
                    return Err(
                        "activation Return substituted its nonce, branch or incoming floor".into(),
                    );
                }
                state.flow.charge(1)?;
                Flow::Armed(Armed {
                    engine: caller.engine.clone(),
                    frame: caller.frame.clone(),
                    receipts: child.receipts.clone(),
                    retained_floor: child.retained_floor.clone(),
                    pending: None,
                    work: caller.work.clone(),
                })
            }
            (Flow::Unarmed, Flow::Armed(_)) | (Flow::Armed(_), Flow::Unarmed) => {
                return Err("activation Return erased or fabricated armed transport".into());
            }
        };
        if matches!(flow, Flow::Unarmed) {
            return Ok(state.continuation(conditions, memory));
        }
        flow.clone_armed_continuation(state, conditions, memory)
    }

    #[cfg(test)]
    pub(super) fn activation_test_root(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
    ) -> Result<Flow, String> {
        self.activation_test_root_limit(instance, body, ACTIVATION_STRUCTURAL_WORK_LIMIT)
    }

    #[cfg(test)]
    pub(super) fn activation_test_legacy_root(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
    ) -> Result<Flow, String> {
        self.activation_test_root_limit(instance, body, MAX_INPUT_VALUES)
    }

    #[cfg(test)]
    fn activation_test_root_limit(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        limit: usize,
    ) -> Result<Flow, String> {
        let engine = self.activation.borrow().identity.clone();
        let work = Rc::new(RefCell::new(Work {
            used: 0,
            limit,
            checked: Vec::new(),
        }));
        let mut seed = Flow::Armed(Armed {
            engine,
            frame: Rc::new(Frame {
                identity: Rc::new(()),
                entry: Rc::new(()),
                entry_slot: usize::MAX,
                parent: None,
                incoming: Rc::new(Vec::new()),
                depth: 0,
                work: work.clone(),
            }),
            receipts: Rc::new(Vec::new()),
            retained_floor: Rc::new(Vec::new()),
            pending: None,
            work,
        });
        // Root issuance authenticates the caller's exact cached Body before any armed
        // destination capture, argument effect or hierarchy staging can borrow it.
        let prepared = self.activation_prepare_body(&seed, instance)?;
        if !Rc::ptr_eq(&prepared, body) {
            return Err("activation root caller Body differs from the Engine cache".into());
        }
        let (entry, entry_slot) = self.activation_entry(instance, body, &seed)?;
        let Flow::Armed(armed) = &mut seed else {
            unreachable!()
        };
        let frame = Rc::get_mut(&mut armed.frame).unwrap();
        frame.entry = entry;
        frame.entry_slot = entry_slot;
        Ok(seed)
    }
}

#[cfg(test)]
impl<'tcx> Engine<'tcx> {
    pub(super) fn activation_test_resource_controls(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        memory: &Memory,
    ) {
        let mut flow = self.activation_test_root(instance, body).unwrap();
        let Flow::Armed(armed) = &mut flow else {
            unreachable!()
        };
        armed.work.borrow_mut().used = ACTIVATION_STRUCTURAL_WORK_LIMIT;
        let count = self.bodies.borrow().len();
        assert!(matches!(self.activation_prepare_body(&flow, instance),
            Err(reason) if reason.contains("shared work budget")));
        assert_eq!(self.bodies.borrow().len(), count);
        assert!(Rc::ptr_eq(
            self.bodies.borrow().get(&instance).unwrap(),
            body
        ));
        for invalid_slot in [false, true] {
            let mut forged = self.activation_test_root(instance, body).unwrap();
            let Flow::Armed(armed) = &mut forged else {
                unreachable!()
            };
            let frame = Rc::get_mut(&mut armed.frame).unwrap();
            if invalid_slot {
                frame.entry_slot = usize::MAX;
            } else {
                frame.entry = Rc::new(());
            }
            assert!(matches!(self.activation_validate(&forged, memory),
                Err(reason) if reason.contains("no authenticated body entry")));
        }
        let mut cyclic = self.activation_test_root(instance, body).unwrap();
        assert!(matches!(self.activation_call_flow(
            &mut cyclic, instance, body, memory, &[instance.def_id()]),
            Err(reason) if reason.contains("not acyclic")));
        let mut replacement = self.activation_test_root(instance, body).unwrap();
        let original = self
            .bodies
            .borrow_mut()
            .insert(instance, Rc::new((**body).clone()))
            .unwrap();
        assert!(
            matches!(self.activation_prepare_body(&replacement, instance),
            Err(reason) if reason.contains("prepared body cache key changed"))
        );
        self.bodies.borrow_mut().insert(instance, original);
        replacement = self.activation_test_root(instance, body).unwrap();
        self.activation_validate(&replacement, memory).unwrap();
        let mut depth = self.activation_test_root(instance, body).unwrap();
        assert!(
            matches!(self.activation_call_flow(&mut depth, instance, body, memory,
            &[instance.def_id(); MAX_INPUT_DEPTH]),
            Err(reason) if reason.contains("exceeds existing depth"))
        );
    }

    pub(super) fn activation_test_cached_and_original_controls(
        &self,
        root: ty::Instance<'tcx>,
        root_body: &Rc<Body<'tcx>>,
        cached: ty::Instance<'tcx>,
        original: ty::Instance<'tcx>,
    ) {
        let cached_body = self.instantiated_body(cached).unwrap();
        for signature_fault in [false, true] {
            let flow = self.activation_test_root(root, root_body).unwrap();
            let mut forged = (*cached_body).clone();
            if signature_fault {
                forged.local_decls[rustc_middle::mir::RETURN_PLACE].ty = self.tcx.types.u64;
            } else {
                let declaration = forged.local_decls[rustc_middle::mir::RETURN_PLACE].clone();
                for _ in 0..=MAX_INPUT_VALUES {
                    forged.local_decls.push(declaration.clone());
                }
            }
            let old = self
                .bodies
                .borrow_mut()
                .insert(cached, Rc::new(forged))
                .unwrap();
            let failed = self.activation_prepare_body(&flow, cached);
            self.bodies.borrow_mut().insert(cached, old);
            if signature_fault {
                assert!(
                    matches!(failed, Err(reason) if reason.contains("original signature differs"))
                );
            } else {
                assert!(failed.is_err());
            }
        }
        assert!(!self.bodies.borrow().contains_key(&original));
        let count = self.bodies.borrow().len();
        let flow = self.activation_test_root(root, root_body).unwrap();
        assert!(matches!(self.activation_prepare_body(&flow, original),
            Err(reason) if reason.contains("Tuple production or copy")));
        assert_eq!(self.bodies.borrow().len(), count);
        eprintln!("carrier cache-hit payload/signature and cache-miss original Tuple refusals");
    }

    pub(super) fn activation_test_empty_return(
        &mut self,
        root: ty::Instance<'tcx>,
        root_body: &Rc<Body<'tcx>>,
        empty: ty::Instance<'tcx>,
        base: &State,
        issued_memory: &Memory,
    ) {
        let mut caller = base.clone();
        caller.flow = self.activation_test_root(root, root_body).unwrap();
        let before = caller.memory.mutable_u16[0].data.clone();
        let results = self
            .call_instance_flow(
                &mut caller.flow,
                empty,
                Vec::new(),
                caller.conditions.clone(),
                caller.memory.clone(),
                (
                    &[root.def_id()],
                    (root.def_id(), self.tcx.def_span(root.def_id())),
                ),
            )
            .unwrap();
        assert_eq!(results.len(), 1);
        let returned = results.into_iter().next().unwrap();
        let Flow::Armed(armed) = &returned.flow else {
            panic!("empty receipt set must remain armed")
        };
        assert!(armed.receipts.is_empty());
        assert!(armed.retained_floor.is_empty());
        assert_eq!(
            returned.value.integer().unwrap(),
            symbolic::integer(&self.terms, 17, 16, false)
                .integer()
                .unwrap()
        );
        assert_eq!(returned.memory.mutable_u16[0].data, before);
        assert!(matches!(
            self.adopt_flow_return(
                &caller,
                returned.conditions.clone(),
                returned.memory.clone(),
                Flow::Unarmed,
            ),
            Err(reason) if reason.contains("erased or fabricated")
        ));
        assert!(matches!(self.adopt_flow_return(
            &caller,
            returned.conditions.clone(),
            issued_memory.clone(),
            returned.flow.clone(),
        ), Err(reason) if reason.contains("lost a current Memory origin receipt")));
        let adopted = self
            .adopt_flow_return(&caller, returned.conditions, returned.memory, returned.flow)
            .unwrap();
        assert!(matches!(&adopted.flow, Flow::Armed(a) if a.receipts.is_empty()));
        assert_eq!(adopted.memory.mutable_u16[0].data, before);
        eprintln!(
            "carrier actual Armed-empty Return preserved; issued Memory substitution refused"
        );
    }

    pub(super) fn activation_test_unsupported_route(
        &self,
        root: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        unsupported: ty::Instance<'tcx>,
    ) {
        let flow = self.activation_test_root(root, body).unwrap();
        let obligations = self.proof.obligations.len();
        let cache = self.bodies.borrow().len();
        let before = self.terms.bit_vector(0x51ee_2011, 64).unwrap();
        assert!(
            matches!(self.activation_armed_call_route(&flow, unsupported),
            Err(reason) if reason.contains("target adapter is not implemented"))
        );
        let after = self.terms.bit_vector(0x51ee_2012, 64).unwrap();
        assert_eq!(after.id(), before.id() + 1);
        assert_eq!(self.proof.obligations.len(), obligations);
        assert_eq!(self.bodies.borrow().len(), cache);
    }

    pub(super) fn activation_test_unsupported_execution(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        base: &State,
    ) {
        let flow = self.activation_test_root(instance, body).unwrap();
        let obligations = self.proof.obligations.len();
        let entries = self.proof.body_entries.len();
        let cache = self.bodies.borrow().len();
        let failed_chain = self.failed_call_chain.clone();
        assert!(matches!(self.execute_with_flow(
            instance,
            vec![base.locals[1].clone().unwrap()],
            base.conditions.clone(),
            base.memory.clone(),
            &[],
            flow,
        ), Err(reason) if reason.contains("target adapter is not implemented")));
        // Caller argument/reborrow MIR may construct terms before this Call. The separate
        // exact route control above verifies that admission itself constructs none.
        assert_eq!(self.proof.obligations.len(), obligations);
        assert_eq!(self.proof.body_entries.len(), entries + 1);
        assert_eq!(self.bodies.borrow().len(), cache);
        self.failed_call_chain = failed_chain;
        eprintln!("carrier actual unsupported Call rejected before target entry/query");
    }

    pub(super) fn activation_test_sibling_receipts(&self, first: &Return, second: &Return) {
        let (Flow::Armed(left), Flow::Armed(right)) = (&first.flow, &second.flow) else {
            panic!("actual armed sibling Returns required")
        };
        assert!(Rc::ptr_eq(&left.frame, &right.frame));
        assert!(!Rc::ptr_eq(&left.receipts, &right.receipts));
        assert!(Rc::ptr_eq(&left.receipts, &left.retained_floor));
        assert!(Rc::ptr_eq(&right.receipts, &right.retained_floor));
        let before = left.receipts[0].issued;
        let mut forged_branch = left.receipts.clone();
        Rc::make_mut(&mut forged_branch)[0].issued += 1;
        assert_eq!(left.receipts[0].issued, before);
        assert_eq!(right.receipts[0].issued, before);
        assert!(!Rc::ptr_eq(&forged_branch, &left.retained_floor));
    }

    pub(super) fn activation_test_work_used(&self, flow: &Flow) -> usize {
        match flow {
            Flow::Unarmed => 0,
            Flow::Armed(armed) => armed.work.borrow().used,
        }
    }

    pub(super) fn activation_test_return_controls(
        &self,
        caller: &State,
        returned: &Return,
        control: super::activation_flow_probe::ReturnFault,
    ) {
        let checked = |flow: Flow, memory: Memory| {
            self.adopt_flow_return(caller, returned.conditions.clone(), memory, flow)
        };
        let Flow::Armed(original) = &returned.flow else {
            panic!("actual armed Return required")
        };
        assert!(!original.receipts.is_empty());
        match control {
            super::activation_flow_probe::ReturnFault::Erased => {
                assert!(matches!(checked(Flow::Unarmed, returned.memory.clone()),
            Err(reason) if reason.contains("erased or fabricated")));
            }
            super::activation_flow_probe::ReturnFault::OtherEngine => {
                let mut forged = original.clone();
                forged.engine = Rc::new(());
                assert!(
                    matches!(checked(Flow::Armed(forged), returned.memory.clone()),
            Err(reason) if reason.contains("substituted engine, work, nonce"))
                );
            }
            super::activation_flow_probe::ReturnFault::LostFloor => {
                let mut forged = original.clone();
                forged.receipts = Rc::new(Vec::new());
                assert!(
                    matches!(checked(Flow::Armed(forged), returned.memory.clone()),
            Err(reason) if reason.contains("lost its incoming floor"))
                );
            }
            super::activation_flow_probe::ReturnFault::ClearedEnvelope => {
                let mut forged = original.clone();
                forged.receipts = Rc::new(Vec::new());
                forged.retained_floor = forged.receipts.clone();
                assert!(
                    matches!(checked(Flow::Armed(forged), returned.memory.clone()),
                    Err(reason) if reason.contains("lost its incoming floor"))
                );
            }
            super::activation_flow_probe::ReturnFault::StaleEnvelope => {
                let mut forged = original.clone();
                let old = &original.frame.incoming[0];
                assert!(
                    original.receipts[0].issued > old.issued
                        || original.receipts[0].epoch > old.epoch
                );
                let receipt = &mut Rc::make_mut(&mut forged.receipts)[0];
                receipt.issued = old.issued;
                receipt.epoch = old.epoch;
                forged.retained_floor = forged.receipts.clone();
                assert!(
                    matches!(checked(Flow::Armed(forged), returned.memory.clone()),
                    Err(reason) if reason.contains("exact observed generation"))
                );
            }
            super::activation_flow_probe::ReturnFault::OtherWork => {
                let mut forged = original.clone();
                forged.work = Rc::new(RefCell::new(Work {
                    used: 0,
                    limit: ACTIVATION_STRUCTURAL_WORK_LIMIT,
                    checked: Vec::new(),
                }));
                assert!(
                    matches!(checked(Flow::Armed(forged), returned.memory.clone()),
            Err(reason) if reason.contains("substituted engine, work, nonce"))
                );
            }
            super::activation_flow_probe::ReturnFault::DeletedHierarchy => {
                let mut deleted = returned.memory.clone();
                Rc::make_mut(&mut deleted.mutable_u16)[original.receipts[0].backing].hierarchy =
                    None;
                assert!(matches!(checked(returned.flow.clone(), deleted),
            Err(reason) if reason.contains("activation hierarchy disappeared")));
            }
            super::activation_flow_probe::ReturnFault::AdvancedGeneration => {
                let mut rolled_back = original.clone();
                Rc::make_mut(&mut rolled_back.receipts)[0].issued += 1;
                assert!(
                    matches!(checked(Flow::Armed(rolled_back), returned.memory.clone()),
            Err(reason) if reason.contains("current Memory lost its origin or exact observed generation"))
                );
            }
            super::activation_flow_probe::ReturnFault::ExpiredBody => {
                let entry_instance = self
                    .activation
                    .borrow()
                    .entries
                    .iter()
                    .find(|entry| Rc::ptr_eq(&entry.identity, &original.frame.entry))
                    .unwrap()
                    .instance;
                let body = self.bodies.borrow_mut().remove(&entry_instance).unwrap();
                let expired = checked(returned.flow.clone(), returned.memory.clone());
                self.bodies.borrow_mut().insert(entry_instance, body);
                assert!(
                    matches!(expired, Err(reason) if reason.contains("body cache association changed"))
                );
            }
            super::activation_flow_probe::ReturnFault::OtherCall => {
                let mut other_call = caller.clone();
                let Flow::Armed(parent) = &mut other_call.flow else {
                    unreachable!()
                };
                let old = parent.pending.as_ref().unwrap();
                parent.pending = Some(Rc::new(Frame {
                    identity: Rc::new(()),
                    entry: old.entry.clone(),
                    entry_slot: old.entry_slot,
                    parent: old.parent.clone(),
                    incoming: old.incoming.clone(),
                    depth: old.depth,
                    work: old.work.clone(),
                }));
                assert!(
                    matches!(self.adopt_flow_return(&other_call, returned.conditions.clone(),
            returned.memory.clone(), returned.flow.clone()),
            Err(reason) if reason.contains("substituted engine, work, nonce"))
                );
            }
        }
    }
}

#[cfg(test)]
pub(super) fn test_work_controls() {
    let mut work = Work {
        used: MAX_INPUT_VALUES - 1,
        limit: MAX_INPUT_VALUES,
        checked: Vec::new(),
    };
    work.charge(1).unwrap();
    assert!(work.charge(1).is_err());
    let mut outer = Work {
        used: ACTIVATION_STRUCTURAL_WORK_LIMIT - 1,
        limit: ACTIVATION_STRUCTURAL_WORK_LIMIT,
        checked: Vec::new(),
    };
    outer.charge(1).unwrap();
    assert!(outer.charge(1).is_err());
    let mut work = Work {
        used: usize::MAX,
        limit: ACTIVATION_STRUCTURAL_WORK_LIMIT,
        checked: Vec::new(),
    };
    assert!(work.charge(1).is_err());
    assert!(Flow::Unarmed.charge(usize::MAX).is_ok());
    let terms = Context::default();
    let ghost = Value::MutableU16 {
        id: 0,
        role: symbolic::MutableU16Role::Ghost {
            certificate: 0,
            element: symbolic::ScalarSliceElement::Integer {
                bits: 16,
                signed: false,
            },
            length: Box::new(Value::Tuple(vec![Value::Unit])),
            data: terms.bit_vector(0, 16).unwrap(),
        },
    };
    assert!(Flow::constant_clone_leaf(&ghost).is_err());
    assert!(Flow::clone_constant_local(&ghost).is_err());
    assert!(Flow::constant_clone_leaf(&Value::Tuple(vec![Value::Unit])).is_err());
    let shape = Rc::new(symbolic::input::InputShape {
        kind: symbolic::input::InputKind::Unit,
        slots: 0,
        height: 1,
    });
    let input = Value::Input(symbolic::input::InputValue {
        shape: shape.clone(),
        start: 0,
        seed: terms.bit_vector(0, 16).unwrap(),
    });
    let Value::Input(copied) = Flow::clone_constant_local(&input).unwrap() else {
        unreachable!()
    };
    assert!(Rc::ptr_eq(&shape, &copied.shape));
    let Value::Input(original) = input else {
        unreachable!()
    };
    assert_eq!(original.seed, copied.seed);
}
