//! Scoped actual destruction of compiler-derived fieldless Box payloads.
use super::*;
use crate::symbolic::MemoryProjection;
use rustc_middle::mir::{BasicBlock, Location, Statement};
use std::rc::Rc;

mod formatting;
#[cfg(test)]
mod lifecycle_tests;
#[cfg(test)]
mod receipt_tests;
pub(super) mod work;

pub(super) fn pay(engine: &mut Engine<'_>, work: usize) -> Result<(), String> {
    engine.steps = engine.steps.saturating_add(work);
    if engine.steps > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "executable Box shared execution step limit reached".into(),
        ));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    BoxGlue,
    PayloadGlue,
    Destructor,
    BoxDrop,
    Alignment,
    Layout,
    Helper,
    Format,
}
struct BodySource<'tcx> {
    instance: ty::Instance<'tcx>,
    current: Rc<Body<'tcx>>,
    kind: Kind,
    signature: Option<ty::PolyFnSig<'tcx>>,
}
pub(super) struct Source<'tcx> {
    constructor: owned_box_constructor_source::Certificate<'tcx>,
    constructor_instance: ty::Instance<'tcx>,
    payload: Ty<'tcx>,
    original: Ty<'tcx>,
    layout: owned_box_payloads::ZeroLayout,
    context: Term,
    bodies: Vec<BodySource<'tcx>>,
}

#[derive(Clone, Debug)]
pub(super) struct Progress {
    source: usize,
    entry: Option<Rc<()>>,
    box_allocation: Option<usize>,
    phase: Phase,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Ready,
    PayloadLeased(usize),
    PayloadDropped(usize),
    Retired,
}
pub(super) struct Invocation<'tcx> {
    key: u64,
    certificate: usize,
    source: Rc<Source<'tcx>>,
    entry: Rc<()>,
    box_allocation: usize,
    instance: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    kind: Kind,
}

pub(super) struct Occurrence<'tcx> {
    caller: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    block: BasicBlock,
    constructor: ty::Instance<'tcx>,
    payload: Ty<'tcx>,
    local: usize,
    destination: usize,
    state: *const State,
    context: Term,
}

/// Issued only after taking the real Box glue's initialized payload once.
/// This witness binds storage; it does not permit numeric pointer observations.
pub(super) struct PayloadWitness<'a, 'tcx> {
    invocation: &'a Invocation<'tcx>,
    allocation: usize,
    block: BasicBlock,
}

impl<'tcx> PayloadWitness<'_, 'tcx> {
    pub(super) fn original(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        allocation: usize,
    ) -> Result<Ty<'tcx>, String> {
        if allocation != self.allocation
            || self.invocation.kind != Kind::BoxGlue
            || self.block.as_usize() != 0
            || !self.invocation.source.context.belongs_to(&engine.terms)
        {
            return Err("Box payload storage witness occurrence differs".into());
        }
        self.invocation.check_identity(engine, &state.memory)?;
        let region = state
            .memory
            .owned_region(self.invocation.key, self.invocation.certificate)?;
        if region.execution.as_ref().map(|progress| progress.phase)
            != Some(Phase::PayloadLeased(allocation))
            || state
                .memory
                .get(allocation)
                .and_then(Option::as_ref)
                .is_none()
        {
            return Err("Box payload storage witness lacks its sole lease".into());
        }
        Ok(self.invocation.source.payload)
    }
}

fn transport_clone_work(
    engine: &mut Engine<'_>,
    value: &Value,
    nodes: &mut usize,
) -> Result<usize, String> {
    match value {
        Value::OwnedRegion { .. } => {
            pay(engine, 1)?;
            *nodes += 1;
            if *nodes > MAX_INPUT_VALUES {
                return Err("Box transport clone exceeds existing 512-node bound".into());
            }
            Ok(8) // Inline logical identity only; no payload is cloned here.
        }
        Value::Reference { projection, .. } => {
            pay(engine, 1 + projection.len())?;
            *nodes += 1;
            if *nodes > MAX_INPUT_VALUES || projection.len() > MAX_INPUT_DEPTH {
                return Err("Box transport clone exceeds existing node/depth bounds".into());
            }
            for part in projection {
                match part {
                    MemoryProjection::Field(_) | MemoryProjection::Variant(_) => {}
                    MemoryProjection::Index(_)
                    | MemoryProjection::TypedIndex { .. }
                    | MemoryProjection::Slice { .. }
                    | MemoryProjection::Chunks { .. } => {
                        return Err("Box lease reference clone projection unsupported".into());
                    }
                }
            }
            Ok(8 + 2 * projection.len())
        }
        _ => array_iterator_constructors::box_value_clone_work(engine, value, nodes),
    }
}

/// Planning and payment precede each possible Rc detachment. The two payload catalogues
/// are never concurrent owners: region.payload becomes None before typed storage receives T.
fn prepay_memory_mutation(engine: &mut Engine<'_>, memory: &Memory) -> Result<(), String> {
    pay(engine, 1 + memory.len() + memory.owned_regions.len())?;
    if memory.len() > MAX_INPUT_VALUES || memory.owned_regions.len() > MAX_INPUT_VALUES {
        return Err("Box lease Memory clone exceeds existing 512-node bound".into());
    }
    let mut work = 24 + memory.len() + memory.owned_regions.len() * 16;
    let mut nodes = 0;
    for value in memory.iter().flatten() {
        work += transport_clone_work(engine, value, &mut nodes)?;
    }
    for region in memory.owned_regions.iter() {
        if let Some(value) = &region.payload {
            work += transport_clone_work(engine, value, &mut nodes)?;
        }
    }
    // Owner records hold inline fields and an Rc scope. Type entries are interned handles.
    pay(
        engine,
        work + 5 * memory.initialized_owners.len() + 3 * engine.initialized_type_count(),
    )
}

fn original_owner_roles(
    engine: &mut Engine<'_>,
    value: &Value,
    identity: (u64, usize),
    depth: usize,
    nodes: &mut usize,
) -> Result<usize, String> {
    pay(engine, 1)?;
    *nodes += 1;
    if *nodes > MAX_INPUT_VALUES || depth >= MAX_INPUT_DEPTH {
        return Err("Box root owner alias scan exceeds existing node/depth bounds".into());
    }
    match value {
        Value::OwnedRegion {
            key,
            certificate,
            kind,
        } if *key == identity.0 => {
            if *certificate != identity.1 || *kind != symbolic::OwnedRegionKind::Owner {
                return Err("Box root owner retains private alias or changed type identity".into());
            }
            Ok(1)
        }
        Value::Tuple(fields) => {
            let mut count = 0;
            for field in fields {
                count += original_owner_roles(engine, field, identity, depth + 1, nodes)?
            }
            Ok(count)
        }
        Value::Elements(fields) => {
            let mut count = 0;
            for field in fields.iter() {
                count += original_owner_roles(engine, field, identity, depth + 1, nodes)?
            }
            Ok(count)
        }
        Value::Adt { fields, .. } => {
            let mut count = 0;
            for (_, field) in fields.iter() {
                count += original_owner_roles(engine, field, identity, depth + 1, nodes)?
            }
            Ok(count)
        }
        Value::Enum { variants, .. } => {
            let mut count = 0;
            for field in variants {
                count += original_owner_roles(engine, field, identity, depth + 1, nodes)?
            }
            Ok(count)
        }
        Value::MaybeUninit {
            payload: Some(payload),
            ..
        } => original_owner_roles(engine, payload, identity, depth + 1, nodes),
        Value::OwnedRegion { .. }
        | Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedSnapshot(_)
        | Value::Reference { .. }
        | Value::Uninitialized
        | Value::MaybeUninit { payload: None, .. }
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
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Unit => Ok(0),
    }
}

fn sole_original_owner(
    engine: &mut Engine<'_>,
    state: &State,
    identity: (u64, usize),
) -> Result<(), String> {
    pay(engine, state.locals.len() + state.memory.len() + 4)?;
    let mut nodes = 0;
    let mut owners = 0;
    for (local, value) in state.locals.iter().enumerate() {
        if state.addresses.get(local) == Some(&None)
            && let Some(value) = value
        {
            owners += original_owner_roles(engine, value, identity, 0, &mut nodes)?;
        }
    }
    for value in state.memory.iter().flatten() {
        owners += original_owner_roles(engine, value, identity, 0, &mut nodes)?;
    }
    if owners != 1 {
        return Err("Box root Drop requires exactly one executable owner occurrence".into());
    }
    Ok(())
}

impl<'tcx> Invocation<'tcx> {
    pub(in crate::proof) fn contract_instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }

    pub(in crate::proof) fn check_contract_source(
        &self,
        engine: &mut Engine<'tcx>,
        memory: &Memory,
    ) -> Result<(), String> {
        self.check_identity(engine, memory)?;
        self.source.current(engine)
    }

    fn child(
        &self,
        engine: &mut Engine<'tcx>,
        instance: ty::Instance<'tcx>,
    ) -> Result<Self, String> {
        self.source.current(engine)?;
        pay(engine, self.source.bodies.len() + 32)?;
        let source = self
            .source
            .bodies
            .iter()
            .find(|source| source.instance == instance)
            .ok_or("Box child has no independently authenticated actual source")?;
        Ok(Self {
            key: self.key,
            certificate: self.certificate,
            source: self.source.clone(),
            entry: self.entry.clone(),
            box_allocation: self.box_allocation,
            instance,
            body: source.current.clone(),
            kind: source.kind,
        })
    }
    fn check_identity(&self, engine: &Engine<'tcx>, memory: &Memory) -> Result<(), String> {
        let entry = engine
            .owned_box_types
            .get(self.certificate)
            .ok_or("Box invocation type certificate is absent")?;
        let region = memory.owned_region(self.key, self.certificate)?;
        let progress = region
            .execution
            .as_ref()
            .ok_or("Box execution phase is absent")?;
        if !region.sealed
            || entry.original != self.source.original
            || entry.payload != self.source.payload
            || entry.executable != Some(progress.source)
            || !engine
                .executable_box_sources
                .get(progress.source)
                .is_some_and(|source| Rc::ptr_eq(source, &self.source))
            || progress.box_allocation != Some(self.box_allocation)
            || !progress
                .entry
                .as_ref()
                .is_some_and(|entry| Rc::ptr_eq(entry, &self.entry))
        {
            return Err("Box invocation owner/type/entry identity differs".into());
        }
        let Some(Value::OwnedRegion {
            key,
            certificate,
            kind: symbolic::OwnedRegionKind::Owner,
        }) = memory.get(self.box_allocation).and_then(Option::as_ref)
        else {
            return Err("Box invocation tracked original owner is absent".into());
        };
        if *key != self.key || *certificate != self.certificate {
            return Err("Box invocation tracked original owner differs".into());
        }
        let (fields, original) = engine
            .typed_memory_evidence(memory, self.box_allocation, &[])?
            .ok_or("Box invocation original typed owner is absent")?;
        if !fields.is_empty() || original != self.source.original {
            return Err("Box invocation original typed owner differs".into());
        }
        memory.missing_places.check(self.box_allocation, &[])?;
        Ok(())
    }

    fn check(&self, engine: &mut Engine<'tcx>, state: &State) -> Result<(), String> {
        state.flow.require_unarmed()?;
        self.source.current(engine)?;
        pay(
            engine,
            32 + state.memory.initialized_owners.len()
                + state.memory.owned_regions.len()
                + state.memory.missing_places.entries().len(),
        )?;
        if !self.source.bodies.iter().any(|source| {
            source.instance == self.instance
                && source.kind == self.kind
                && Rc::ptr_eq(&source.current, &self.body)
        }) {
            return Err("Box invocation current full Instance/Body differs".into());
        }
        self.check_identity(engine, &state.memory)?;
        let region = state.memory.owned_region(self.key, self.certificate)?;
        match region.execution.as_ref().unwrap().phase {
            Phase::Ready => {
                if self.kind != Kind::BoxGlue
                    || !fieldless_value(
                        engine,
                        self.source.payload,
                        region
                            .payload
                            .as_ref()
                            .ok_or("Box ready payload is absent")?,
                    )?
                {
                    return Err("Box ready phase requires its initialized payload".into());
                }
            }
            Phase::PayloadLeased(allocation) => {
                if allocation == self.box_allocation || region.payload.is_some() {
                    return Err("Box lease duplicates its payload owner".into());
                }
                let (fields, original) = engine
                    .typed_memory_evidence(&state.memory, allocation, &[])?
                    .ok_or("Box payload lease original typed owner is absent")?;
                if !fields.is_empty()
                    || original != self.source.payload
                    || !fieldless_value(
                        engine,
                        original,
                        state
                            .memory
                            .get(allocation)
                            .and_then(Option::as_ref)
                            .ok_or("Box leased payload is absent")?,
                    )?
                {
                    return Err("Box payload lease original storage differs".into());
                }
                state.memory.missing_places.check(allocation, &[])?;
            }
            Phase::PayloadDropped(allocation) => {
                if region.payload.is_some()
                    || state
                        .memory
                        .get(allocation)
                        .and_then(Option::as_ref)
                        .is_some()
                    || !matches!(
                        self.kind,
                        Kind::BoxGlue | Kind::BoxDrop | Kind::Alignment | Kind::Layout
                    )
                {
                    return Err("Box consumed payload escaped its normal continuation".into());
                }
                if state.memory.missing_places.check(allocation, &[]).is_ok() {
                    return Err("Box consumed payload retains initialized storage".into());
                }
            }
            Phase::Retired => return Err("Box retired invocation cannot execute".into()),
        }
        Ok(())
    }

    fn lease_payload(
        &self,
        engine: &mut Engine<'tcx>,
        state: &mut State,
        block: BasicBlock,
    ) -> Result<usize, String> {
        self.check(engine, state)?;
        if self.kind != Kind::BoxGlue
            || block.as_usize() != 0
            || !matches!(&self.body.basic_blocks[block].terminator().kind,
                TerminatorKind::Drop { place, .. }
                if place.local.as_usize() == 6 && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref))
            || state
                .memory
                .owned_region(self.key, self.certificate)?
                .execution
                .as_ref()
                .map(|progress| progress.phase)
                != Some(Phase::Ready)
        {
            return Err("Box payload lease requires the actual once-only T Drop occurrence".into());
        }
        if state.memory.storage_slots().saturating_add(2) > memory::MAX_ALLOCATIONS
            || state.memory.initialized_owners.len() >= MAX_INPUT_VALUES
            || engine.initialized_type_count() >= MAX_INPUT_VALUES
        {
            return Err("Box payload lease exceeds existing storage/type bounds".into());
        }
        prepay_memory_mutation(engine, &state.memory)?;
        let allocation = state.memory.len();
        let region = state.memory.owned_region_mut(self.key, self.certificate)?;
        let payload = region
            .payload
            .take()
            .ok_or("Box initialized payload was already consumed")?;
        region.execution.as_mut().unwrap().phase = Phase::PayloadLeased(allocation);
        state.memory.push(Some(payload));
        let witness = PayloadWitness {
            invocation: self,
            allocation,
            block,
        };
        engine.bind_box_payload_storage(&witness, state, allocation)?;
        Ok(allocation)
    }

    /// Called by the actual PayloadGlue executor on each normal child return.
    /// A panic has no Return and therefore cannot reach this transition.
    fn finish_payload(&self, engine: &mut Engine<'tcx>, result: &mut Return) -> Result<(), String> {
        if self.kind != Kind::PayloadGlue || !matches!(result.value, Value::Unit) {
            return Err("Box payload consumption requires actual Unit glue return".into());
        }
        result.flow.require_unarmed()?;
        self.source.current(engine)?;
        pay(
            engine,
            32 + result.memory.initialized_owners.len()
                + result.memory.owned_regions.len()
                + result.memory.missing_places.entries().len(),
        )?;
        self.check_identity(engine, &result.memory)?;
        let region = result.memory.owned_region(self.key, self.certificate)?;
        let Phase::PayloadLeased(allocation) = region.execution.as_ref().unwrap().phase else {
            return Err("Box payload normal return lacks its active lease".into());
        };
        if region.payload.is_some() || allocation == self.box_allocation {
            return Err("Box payload normal return has duplicate ownership".into());
        }
        let (fields, original) = engine
            .typed_memory_evidence(&result.memory, allocation, &[])?
            .ok_or("Box payload normal return lacks original typed storage")?;
        if !fields.is_empty()
            || original != self.source.payload
            || !fieldless_value(
                engine,
                original,
                result
                    .memory
                    .get(allocation)
                    .and_then(Option::as_ref)
                    .ok_or("Box payload normal return storage is absent")?,
            )?
        {
            return Err("Box payload normal return original storage differs".into());
        }
        result.memory.missing_places.check(allocation, &[])?;
        let mut masks =
            array_iterator_constructors::box_clone_masks(engine, &result.memory.missing_places)?;
        pay(engine, masks.entries().len() * 2 + 4)?;
        masks.consume(allocation, Vec::new())?;
        prepay_memory_mutation(engine, &result.memory)?;
        result.memory.missing_places = masks;
        result.memory.retire_initialized_owner(allocation);
        result.memory[allocation] = None;
        result
            .memory
            .owned_region_mut(self.key, self.certificate)?
            .execution
            .as_mut()
            .unwrap()
            .phase = Phase::PayloadDropped(allocation);
        Ok(())
    }

    /// Separate from the legacy payload-preserving retirement API. No T is restored.
    fn retire_consumed(
        &self,
        engine: &mut Engine<'tcx>,
        result: &mut Return,
    ) -> Result<(), String> {
        if self.kind != Kind::BoxGlue || !matches!(result.value, Value::Unit) {
            return Err("Box retirement requires actual outer glue Unit return".into());
        }
        result.flow.require_unarmed()?;
        self.source.current(engine)?;
        pay(
            engine,
            32 + result.memory.initialized_owners.len()
                + result.memory.owned_regions.len()
                + result.memory.missing_places.entries().len(),
        )?;
        self.check_identity(engine, &result.memory)?;
        let region = result.memory.owned_region(self.key, self.certificate)?;
        let Phase::PayloadDropped(allocation) = region.execution.as_ref().unwrap().phase else {
            return Err("Box outer return cannot retire an undestroyed payload".into());
        };
        if region.payload.is_some()
            || result
                .memory
                .get(allocation)
                .and_then(Option::as_ref)
                .is_some()
            || result.memory.missing_places.check(allocation, &[]).is_ok()
        {
            return Err("Box consumed retirement retains initialized payload".into());
        }
        prepay_memory_mutation(engine, &result.memory)?;
        let region = result.memory.owned_region_mut(self.key, self.certificate)?;
        region.execution.as_mut().unwrap().phase = Phase::Retired;
        region.live = false;
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn executable_box_core_call(
        &mut self,
        parent: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<Return>>, String> {
        let Some(parent) = parent else {
            return Ok(None);
        };
        if !matches!(
            parent.kind,
            Kind::BoxGlue | Kind::PayloadGlue | Kind::BoxDrop
        ) {
            return Ok(None);
        }
        if matches!(callee.def, ty::InstanceKind::Intrinsic(_)) {
            return Ok(None);
        }
        parent.check(self, state)?;
        if !Rc::ptr_eq(body, &parent.body) || direct_callee(self, body, block.as_usize())? != callee
        {
            return Err("Box core Call current/original occurrence differs".into());
        }
        let child = parent.child(self, callee)?;
        let expected: &[(usize, bool)] = match (parent.kind, block.as_usize(), child.kind) {
            (Kind::BoxGlue, 2, Kind::BoxDrop) | (Kind::PayloadGlue, 0, Kind::Destructor) => {
                &[(2, true)]
            }
            (Kind::BoxDrop, 6, Kind::Alignment) => &[(10, false)],
            (Kind::BoxDrop, 8, Kind::Layout) => &[(8, false), (9, false)],
            _ => return Err("Box core Call source frame edge differs".into()),
        };
        let TerminatorKind::Call {
            args,
            target: Some(_),
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("Box core Call lacks actual normal edge".into());
        };
        if args.len() != expected.len() {
            return Err("Box core Call exact argument count differs".into());
        }
        pay(self, args.len() * 16 + 8)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(args.len())
            .map_err(|_| "Box core argument allocation failed")?;
        let mut masks = array_iterator_constructors::box_clone_masks(self, &state.missing_places)?;
        for (argument, (local, moved)) in args.iter().zip(expected.iter().copied()) {
            if !matches!(&argument.node, Operand::Move(place)
                if moved && place.local.as_usize() == local && place.projection.is_empty())
                && !matches!(&argument.node, Operand::Copy(place)
                    if !moved && place.local.as_usize() == local && place.projection.is_empty())
                || state.addresses.get(local) != Some(&None)
            {
                return Err("Box core Call original Copy/Move source differs".into());
            }
            pay(self, state.missing_places.entries().len() + 8)?;
            state.missing_places.check(local, &[])?;
            let value = state
                .locals
                .get(local)
                .and_then(Option::as_ref)
                .ok_or("Box core Call initialized source absent")?;
            let work = transport_clone_work(self, value, &mut 0)?;
            pay(self, work)?;
            values.push(value.clone());
            if moved {
                pay(self, masks.entries().len() * 2 + 4)?;
                masks.consume(local, Vec::new())?;
            }
        }
        // Validate every original argument before consuming any source local.
        if parent.kind == Kind::BoxGlue
            && !matches!(values.as_slice(), [Value::Reference { allocation, projection,
                mutable: true }]
                if *allocation == parent.box_allocation && projection.is_empty())
        {
            return Err("Box core receiver does not retain the original Box owner".into());
        }
        if parent.kind == Kind::PayloadGlue {
            let region = state.memory.owned_region(parent.key, parent.certificate)?;
            let Phase::PayloadLeased(allocation) = region.execution.as_ref().unwrap().phase else {
                return Err("Box payload glue Call lacks active typed lease".into());
            };
            if !matches!(values.as_slice(), [Value::Reference { allocation: target,
                projection, mutable: true }]
                if *target == allocation && projection.is_empty())
            {
                return Err("Box payload glue Call receiver differs from actual lease".into());
            }
        }
        for (local, moved) in expected.iter().copied() {
            if moved {
                pay(self, state.constant_receipts.len() + 4)?;
                state.locals[local] = None;
                state
                    .constant_receipts
                    .invalidate(Place::from(rustc_middle::mir::Local::from_usize(local)));
            }
        }
        state.missing_places = masks;
        pay(self, state.conditions.len() + 1)?;
        let conditions = state.conditions.clone();
        let conditions = self.call_box_preconditions(
            &child,
            &values,
            conditions,
            &state.memory,
            (
                parent.instance.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        self.execute_box_invocation(child, values, state, conditions, stack)
            .map(Some)
    }

    pub(super) fn executable_box_drop_place(
        &mut self,
        caller: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<State>>, String> {
        let TerminatorKind::Drop { place, .. } = &body.basic_blocks[block].terminator().kind else {
            return Ok(None);
        };
        if !place.projection.is_empty() {
            return Ok(None);
        }
        let local = place.local.as_usize();
        let slot = if let Some(allocation) = state.addresses.get(local).copied().flatten() {
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals.get(local).and_then(Option::as_ref)
        };
        let Some(Value::OwnedRegion {
            key,
            certificate,
            kind: symbolic::OwnedRegionKind::Owner,
        }) = slot
        else {
            return Ok(None);
        };
        let (key, certificate) = (*key, *certificate);
        pay(self, self.owned_box_types.len() + 8)?;
        let Some(source_index) = self
            .owned_box_types
            .get(certificate)
            .and_then(|entry| entry.executable)
        else {
            return Ok(None);
        };
        state.flow.require_unarmed()?;
        if caller_source(self, body)? != caller {
            return Err("Box root Drop caller source differs".into());
        }
        pay(self, 16)?;
        let source = self
            .executable_box_sources
            .get(source_index)
            .ok_or("Box root Drop executable source is absent")?
            .clone();
        source.current(self)?;
        if place.ty(&body.local_decls, self.tcx).ty != source.original {
            return Err("Box root Drop original place type differs".into());
        }
        self.check_place_initialization(state, *place)?;
        sole_original_owner(self, state, (key, certificate))?;
        let region = state.memory.owned_region(key, certificate)?;
        if !region.sealed
            || region.payload.is_none()
            || !matches!(&region.execution, Some(progress) if progress.source == source_index
                && progress.phase == Phase::Ready && progress.entry.is_none()
                    && progress.box_allocation.is_none())
        {
            return Err("Box root Drop requires its fresh branch-local initialized owner".into());
        }
        self.preflight_owned_type_storage(body, state, *place)?;
        let masks =
            array_iterator_constructors::box_mask_clone_work(self, &state.memory.missing_places)?;
        prepay_memory_mutation(self, &state.memory)?;
        pay(self, masks + state.missing_places.entries().len() * 4 + 48)?;
        let argument = self.borrow_typed(body, state, *place, true)?;
        let Value::Reference {
            allocation,
            projection,
            mutable: true,
        } = &argument
        else {
            return Err("Box root Drop requires actual retained mutable caller storage".into());
        };
        if !projection.is_empty() {
            return Err("Box root Drop caller storage must be whole".into());
        }
        let allocation = *allocation;
        self.bind_owned_type_storage(body, state, *place)?;
        let instance = ty::Instance::resolve_drop_glue(self.tcx, source.original);
        pay(self, 32 + source.bodies.len())?;
        let actual = source
            .bodies
            .iter()
            .find(|part| part.instance == instance && part.kind == Kind::BoxGlue)
            .ok_or("Box root Drop exact outer glue source is absent")?;
        let entry = Rc::new(());
        let current = actual.current.clone();
        let region = state.memory.owned_region_mut(key, certificate)?;
        let progress = region.execution.as_mut().unwrap();
        progress.entry = Some(entry.clone());
        progress.box_allocation = Some(allocation);
        let invocation = Invocation {
            key,
            certificate,
            source,
            entry,
            box_allocation: allocation,
            instance,
            body: current,
            kind: Kind::BoxGlue,
        };
        invocation.check(self, state)?;
        pay(self, state.conditions.len() + 12)?;
        let conditions = state.conditions.clone();
        let conditions = self.call_box_preconditions(
            &invocation,
            std::slice::from_ref(&argument),
            conditions,
            &state.memory,
            (
                caller.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        let results =
            self.execute_box_invocation(invocation, vec![argument], state, conditions, stack)?;
        pay(self, results.len() + 1)?;
        let mut continuations = Vec::new();
        continuations
            .try_reserve_exact(results.len())
            .map_err(|_| "Box root Drop continuation allocation failed")?;
        for result in results {
            // The actual outer executor has already retired the consumed region. Clone the
            // caller continuation without granting a new active invocation after retirement.
            self.executable_box_continuation_work(state)?;
            let mut continuation =
                self.adopt_flow_return(state, result.conditions, result.memory, result.flow)?;
            let region = continuation
                .memory
                .owned_regions
                .iter()
                .find(|region| region.key == key && region.certificate == certificate)
                .ok_or("Box root Drop consumed region disappeared")?;
            if region.live
                || region.payload.is_some()
                || !matches!(&region.execution, Some(progress) if progress.phase == Phase::Retired)
            {
                return Err("Box root Drop normal result did not retire its consumed owner".into());
            }
            let mut masks = array_iterator_constructors::box_clone_masks(
                self,
                &continuation.memory.missing_places,
            )?;
            pay(self, masks.entries().len() * 2 + 4)?;
            masks.consume(allocation, Vec::new())?;
            prepay_memory_mutation(self, &continuation.memory)?;
            continuation.memory.missing_places = masks;
            continuation.memory.retire_initialized_owner(allocation);
            continuation.memory[allocation] = None;
            continuation.addresses[local] = None;
            continuation.locals[local] = None;
            continuations.push(continuation);
        }
        Ok(Some(continuations))
    }

    pub(super) fn executable_box_constructor(
        &mut self,
        receipt: Occurrence<'tcx>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        arguments: &[Value],
        state: &mut State,
    ) -> Result<Value, String> {
        let [value] = arguments else {
            return Err("executable Box constructor requires its single moved payload".into());
        };
        #[cfg(test)]
        let receipt = receipt_tests::controls(self, receipt, body, block, callee, value, state)?;
        receipt.after(self, body, block, callee, value, state)?;
        pay(self, self.executable_box_sources.len() + 32)?;
        let previous = self.executable_box_sources.iter().position(|source| {
            source.payload == receipt.payload && source.constructor_instance == callee
        });
        let source_index = if let Some(index) = previous {
            pay(self, 8)?;
            let source = self.executable_box_sources[index].clone();
            source.validate(self)?;
            index
        } else {
            if self.executable_box_sources.len() >= MAX_INPUT_VALUES {
                return Err("executable Box source registry exceeds512 entries".into());
            }
            let source = Source::prepare(self, callee)?;
            pay(self, self.executable_box_sources.len() + 16)?;
            let index = self.executable_box_sources.len();
            self.executable_box_sources.push(Rc::new(source));
            index
        };
        pay(self, self.owned_box_types.len() + 64)?;
        let source = self.executable_box_sources[source_index].clone();
        source.current(self)?;
        let mut entry = self.prepare_nominal_box_type(receipt.payload)?;
        if entry.original != source.original || entry.slots != 1 || entry.shape.is_some() {
            return Err("executable Box constructor original fieldless type differs".into());
        }
        entry.executable = Some(source_index);
        if self.owned_box_types.iter().any(|existing| {
            existing.original == entry.original && existing.executable != Some(source_index)
        }) {
            return Err("executable Box cannot reuse another ownership protocol".into());
        }
        if state.memory.storage_slots().saturating_add(1) > memory::MAX_ALLOCATIONS
            || self.owned_box_types.len() >= MAX_INPUT_VALUES
        {
            return Err("executable Box constructor exceeds existing storage/type bounds".into());
        }
        let key = self.next_owned_region;
        let next = key
            .checked_add(1)
            .ok_or("executable Box generation overflows")?;
        if state
            .memory
            .owned_regions
            .iter()
            .any(|region| region.key == key)
        {
            return Err("executable Box generation has already been issued".into());
        }
        let work = array_iterator_constructors::box_value_clone_work(self, value, &mut 0)?;
        prepay_memory_mutation(self, &state.memory)?;
        pay(self, work + self.owned_box_types.len() * 8 + 32)?;
        let payload = value.clone();
        let certificate = self.register_nominal_box(entry)?;
        state.memory.issue_owned_region(key, certificate)?;
        state
            .memory
            .initialize_owned_region(key, certificate, payload)?;
        let region = state.memory.owned_region_mut(key, certificate)?;
        region.execution = Some(Progress {
            source: source_index,
            entry: None,
            box_allocation: None,
            phase: Phase::Ready,
        });
        state.memory.seal_owned_region(key, certificate)?;
        self.next_owned_region = next;
        self.record_model(
            callee.def_id(),
            "complete constructor source/normal-path certificate; actual moved payload \
             and executable typed Drop protocol",
        );
        Ok(Value::OwnedRegion {
            key,
            certificate,
            kind: symbolic::OwnedRegionKind::Owner,
        })
    }

    pub(super) fn executable_box_format_call(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        state: &State,
    ) -> Result<Option<Value>, String> {
        let Some(invocation) = invocation else {
            return Ok(None);
        };
        formatting::literal(self, invocation, body, block, callee, state)
    }

    pub(super) fn executable_box_layout_call(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        state: &mut State,
    ) -> Result<Option<Value>, String> {
        let Some(invocation) = invocation else {
            return Ok(None);
        };
        if invocation.kind != Kind::BoxDrop || !matches!(callee.def, ty::InstanceKind::Intrinsic(_))
        {
            return Ok(None);
        }
        invocation.check(self, state)?;
        layout_intrinsic(self, callee, invocation.source.payload)?;
        if !Rc::ptr_eq(body, &invocation.body)
            || !matches!(block.as_usize(), 0 | 4)
            || direct_callee(self, body, block.as_usize())? != callee
        {
            return Err("Box layout intrinsic actual occurrence differs".into());
        }
        let TerminatorKind::Call {
            args,
            target: Some(_),
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("Box layout intrinsic lacks actual normal Call".into());
        };
        if args.len() != 1
            || !matches!(&args[0].node,
            Operand::Copy(place) | Operand::Move(place)
                if place.local.as_usize() == 3 && place.projection.is_empty())
        {
            return Err("Box layout intrinsic exact private argument differs".into());
        }
        pay(self, state.missing_places.entries().len() + 24)?;
        state.missing_places.check(3, &[])?;
        if state.addresses.get(3) != Some(&None)
            || !matches!(state.locals.get(3).and_then(Option::as_ref),
                Some(Value::OwnedRegion { key, certificate,
                    kind: symbolic::OwnedRegionKind::Pointer })
                    if *key == invocation.key && *certificate == invocation.certificate)
        {
            return Err("Box layout intrinsic lacks authenticated logical pointer role".into());
        }
        let name = self.tcx.item_name(callee.def_id());
        let value = match (block.as_usize(), name.as_str(), &args[0].node) {
            (0, "size_of_val", Operand::Copy(_)) => 0,
            (4, "align_of_val", Operand::Move(_)) => invocation.source.layout.alignment(),
            _ => return Err("Box layout intrinsic size/alignment occurrence differs".into()),
        };
        if let Operand::Move(place) = args[0].node {
            let mut masks =
                array_iterator_constructors::box_clone_masks(self, &state.missing_places)?;
            pay(
                self,
                masks.entries().len() * 2 + state.constant_receipts.len() + 8,
            )?;
            masks.consume(3, Vec::new())?;
            state.missing_places = masks;
            state.locals[3] = None;
            state.constant_receipts.invalidate(place);
        }
        pay(self, 16)?;
        Ok(Some(symbolic::integer(
            &self.terms,
            value,
            invocation.source.layout.bits(),
            false,
        )))
    }

    pub(super) fn executable_box_adopt_work(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        state: &State,
    ) -> Result<(), String> {
        let Some(invocation) = invocation else {
            return Ok(());
        };
        invocation.check(self, state)?;
        self.executable_box_continuation_work(state)
    }

    fn executable_box_continuation_work(&mut self, state: &State) -> Result<(), String> {
        if state.locals.len() > MAX_INPUT_VALUES
            || state.addresses.len() > MAX_INPUT_VALUES
            || state.constant_receipts.len() > MAX_INPUT_VALUES
        {
            return Err("Box continuation clone exceeds existing 512-node bounds".into());
        }
        pay(self, state.locals.len() + 1)?;
        let mut work =
            8 + state.locals.len() + state.addresses.len() + 8 * state.constant_receipts.len();
        let mut nodes = 0;
        for value in state.locals.iter().flatten() {
            work += transport_clone_work(self, value, &mut nodes)?;
        }
        work += array_iterator_constructors::box_mask_clone_work(self, &state.missing_places)?;
        pay(self, work)
    }

    pub(super) fn executable_box_element_drop(
        &mut self,
        parent: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        block: BasicBlock,
        stack: &[DefId],
    ) -> Result<Option<Vec<State>>, String> {
        let Some(parent) = parent else {
            return Ok(None);
        };
        parent.check(self, state)?;
        if !Rc::ptr_eq(body, &parent.body) || parent.kind != Kind::BoxGlue || block.as_usize() != 0
        {
            return Err("Box nested Drop requires the exact leased payload protocol".into());
        }
        pay(self, 8 + state.missing_places.entries().len())?;
        state.missing_places.check(6, &[])?;
        if state.addresses.get(6) != Some(&None)
            || !matches!(state.locals.get(6).and_then(Option::as_ref),
                Some(Value::OwnedRegion { key, certificate,
                    kind: symbolic::OwnedRegionKind::Pointer })
                    if *key == parent.key && *certificate == parent.certificate)
        {
            return Err("Box real T Drop lacks its authenticated logical pointer role".into());
        }
        let child_instance = ty::Instance::resolve_drop_glue(self.tcx, parent.source.payload);
        let child = parent.child(self, child_instance)?;
        if child.kind != Kind::PayloadGlue {
            return Err("Box real T Drop child source family differs".into());
        }
        let allocation = parent.lease_payload(self, state, block)?;
        #[cfg(test)]
        lifecycle_tests::leased(self, parent, &child, state, block)?;
        pay(self, state.conditions.len() + 12)?;
        let argument = Value::Reference {
            allocation,
            projection: Vec::new(),
            mutable: true,
        };
        let conditions = state.conditions.clone();
        let conditions = self.call_box_preconditions(
            &child,
            std::slice::from_ref(&argument),
            conditions,
            &state.memory,
            (
                parent.instance.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        let results =
            self.execute_box_invocation(child, vec![argument], state, conditions, stack)?;
        pay(self, results.len() + 1)?;
        let mut continuations = Vec::new();
        continuations
            .try_reserve_exact(results.len())
            .map_err(|_| "Box Drop continuation allocation failed")?;
        for result in results {
            self.executable_box_adopt_work(Some(parent), state)?;
            let continuation =
                self.adopt_flow_return(state, result.conditions, result.memory, result.flow)?;
            parent.check(self, &continuation)?;
            continuations.push(continuation);
        }
        Ok(Some(continuations))
    }

    pub(super) fn executable_box_helper_execute(
        &mut self,
        parent: &Invocation<'tcx>,
        body: &Rc<Body<'tcx>>,
        instance: ty::Instance<'tcx>,
        arguments: Vec<Value>,
        state: &State,
        call: (&[DefId], (DefId, Span)),
    ) -> Result<Vec<Return>, String> {
        parent.check(self, state)?;
        if !Rc::ptr_eq(body, &parent.body) {
            return Err("Box child call parent Body differs".into());
        }
        let child = parent.child(self, instance)?;
        match (parent.kind, child.kind) {
            (Kind::BoxGlue, Kind::BoxDrop)
            | (Kind::PayloadGlue, Kind::Destructor)
            | (Kind::BoxDrop, Kind::Alignment | Kind::Layout)
            | (Kind::Destructor | Kind::Helper, Kind::Helper | Kind::Format) => {}
            _ => return Err("Box active destruction unexpected child frame edge".into()),
        }
        let (stack, site) = call;
        pay(self, state.conditions.len() + 1)?;
        let conditions = state.conditions.clone();
        let conditions =
            self.call_box_preconditions(&child, &arguments, conditions, &state.memory, site)?;
        self.execute_box_invocation(child, arguments, state, conditions, stack)
    }

    pub(super) fn executable_box_statement(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        location: Location,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        if invocation.kind == Kind::BoxDrop {
            return self.executable_box_drop_metadata(invocation, body, state, location);
        }
        if invocation.kind == Kind::Layout {
            invocation.check(self, state)?;
            if !Rc::ptr_eq(body, &invocation.body) {
                return Err("Box Layout scalar transport Body differs".into());
            }
            let statement = &body.basic_blocks[location.block].statements[location.statement_index];
            if let StatementKind::Assign(pair) = &statement.kind
                && matches!(&pair.1, Rvalue::Cast(CastKind::Transmute, ..))
            {
                if location.block.as_usize() != 0
                    || location.statement_index != 3
                    || pair.0.local.as_usize() != 8
                    || !pair.0.projection.is_empty()
                    || !matches!(&pair.1,
                        Rvalue::Cast(CastKind::Transmute, Operand::Copy(place), original)
                        if place.local.as_usize() == 2 && place.projection.is_empty()
                            && *original == self.tcx.types.usize)
                    || state.addresses.get(2) != Some(&None)
                    || state.addresses.get(8) != Some(&None)
                {
                    return Err("Box Layout original Alignment-to-usize occurrence differs".into());
                }
                pay(self, state.missing_places.entries().len() * 3 + 24)?;
                state.missing_places.check(2, &[])?;
                let value = state
                    .locals
                    .get(2)
                    .and_then(Option::as_ref)
                    .ok_or("Box Layout original scalar is absent")?;
                let (term, bits, signed) = value.integer()?;
                if !term.belongs_to(&self.terms)
                    || bits != invocation.source.layout.bits()
                    || signed
                    || !matches!(symbolic::constant(&term),
                        Some(symbolic::Constant::BitVec { value, .. })
                        if value == invocation.source.layout.alignment())
                {
                    return Err("Box Layout scalar differs from original alignment".into());
                }
                state.locals[8] = Some(value.clone());
                state.missing_places.initialize(8, &[]);
                return Ok(true);
            }
            return Ok(false);
        }
        if invocation.kind != Kind::BoxGlue {
            return Ok(false);
        }
        invocation.check(self, state)?;
        if !Rc::ptr_eq(body, &invocation.body) {
            return Err("Box glue statement Body differs".into());
        }
        let StatementKind::Assign(pair) =
            &body.basic_blocks[location.block].statements[location.statement_index].kind
        else {
            return Ok(false);
        };
        if location.statement_index != 0 || !pair.0.projection.is_empty() {
            return Err("Box glue private transport assignment differs".into());
        }
        pay(self, 24)?;
        let Some(Value::Reference {
            allocation,
            projection,
            mutable: true,
        }) = state.locals.get(1).and_then(Option::as_ref)
        else {
            return Err("Box glue original tracked mutable receiver is absent".into());
        };
        state.missing_places.check(1, &[])?;
        if *allocation != invocation.box_allocation
            || !projection.is_empty()
            || state.addresses.get(1) != Some(&None)
        {
            return Err("Box glue original tracked mutable receiver differs".into());
        }
        let allocation = *allocation;
        let (local, value) = match location.block.as_usize() {
            0 if pair.0.local.as_usize() == 6
                && matches!(&pair.1,
                Rvalue::Cast(CastKind::Transmute, Operand::Copy(place), target)
                if place.local.as_usize() == 1 && place.projection.len() == 3
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && matches!(place.projection[1], ProjectionElem::Field(index, _)
                        if index.as_usize() == 0)
                    && matches!(place.projection[2], ProjectionElem::Field(index, _)
                        if index.as_usize() == 0)
                    && matches!(target.kind(), ty::RawPtr(child, rustc_hir::Mutability::Not)
                        if *child == invocation.source.payload)) =>
            {
                (
                    6,
                    Value::OwnedRegion {
                        key: invocation.key,
                        certificate: invocation.certificate,
                        kind: symbolic::OwnedRegionKind::Pointer,
                    },
                )
            }
            2 if pair.0.local.as_usize() == 2
                && matches!(&pair.1,
                Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, place)
                if place.local.as_usize() == 1 && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)) =>
            {
                (
                    2,
                    Value::Reference {
                        allocation,
                        projection: Vec::new(),
                        mutable: true,
                    },
                )
            }
            _ => return Err("Box glue private transport original occurrence differs".into()),
        };
        if state.addresses.get(local) != Some(&None) || state.locals.get(local).is_none() {
            return Err("Box glue private transport destination is addressed or absent".into());
        }
        pay(self, 8 + 2 * state.missing_places.entries().len())?;
        state.locals[local] = Some(value);
        state.missing_places.initialize(local, &[]);
        Ok(true)
    }

    fn executable_box_drop_metadata(
        &mut self,
        invocation: &Invocation<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        location: Location,
    ) -> Result<bool, String> {
        invocation.check(self, state)?;
        if !Rc::ptr_eq(body, &invocation.body) {
            return Err("Box drop metadata current Body differs".into());
        }
        pay(self, 8 + state.missing_places.entries().len())?;
        state.missing_places.check(1, &[])?;
        if state.addresses.get(1) != Some(&None)
            || !matches!(state.locals.get(1).and_then(Option::as_ref),
                Some(Value::Reference { allocation, projection, mutable: true })
                    if *allocation == invocation.box_allocation && projection.is_empty())
        {
            return Err("Box drop metadata original tracked receiver differs".into());
        }
        let StatementKind::Assign(pair) =
            &body.basic_blocks[location.block].statements[location.statement_index].kind
        else {
            return Ok(false);
        };
        let ordinal = (location.block.as_usize(), location.statement_index);
        if !matches!(ordinal, (0, 2 | 3 | 6 | 7) | (7, 0)) {
            return Ok(false);
        }
        if !pair.0.projection.is_empty() || state.addresses[pair.0.local.as_usize()].is_some() {
            return Err("Box private drop metadata destination differs".into());
        }
        let pointer = || Value::OwnedRegion {
            key: invocation.key,
            certificate: invocation.certificate,
            kind: symbolic::OwnedRegionKind::Pointer,
        };
        pay(self, 32)?;
        let value = match ordinal {
            (0, 2) if pair.0.local.as_usize() == 15 => pointer(),
            (0, 3) if pair.0.local.as_usize() == 16 => {
                // The canonical original BoxDrop schema binds this exact fieldless PhantomData
                // local. Preserve its original nominal value instead of an observable placeholder.
                let original = body.local_decls[pair.0.local].ty;
                let ty::Adt(def, args) = original.kind() else {
                    return Err("Box drop PhantomData original type differs".into());
                };
                if self.tcx.lang_items().phantom_data() != Some(def.did())
                    || args.type_at(0) != invocation.source.payload
                    || !def.non_enum_variant().fields.is_empty()
                {
                    return Err("Box drop PhantomData original fieldless identity differs".into());
                }
                pay(self, 1024)?;
                self.constructed(original, 0, Vec::new())?
            }
            (0, 6 | 7) if matches!(pair.0.local.as_usize(), 3 | 4) => {
                if !matches!(state.locals.get(15).and_then(Option::as_ref),
                    Some(Value::OwnedRegion { key, certificate,
                        kind: symbolic::OwnedRegionKind::Pointer })
                        if *key == invocation.key && *certificate == invocation.certificate)
                {
                    return Err("Box drop metadata pointer source differs".into());
                }
                pointer()
            }
            (7, 0) if pair.0.local.as_usize() == 9 => {
                let Some(value) = state.locals.get(10).and_then(Option::as_ref) else {
                    return Err("Box drop alignment scalar source absent".into());
                };
                let (term, bits, signed) = value.integer()?;
                if !term.belongs_to(&self.terms)
                    || bits != invocation.source.layout.bits()
                    || signed
                    || !matches!(symbolic::constant(&term),
                        Some(symbolic::Constant::BitVec { value, .. })
                        if value == invocation.source.layout.alignment())
                {
                    return Err("Box drop alignment differs from original compiler layout".into());
                }
                pay(self, 8)?;
                value.clone()
            }
            _ => return Err("Box drop metadata original occurrence differs".into()),
        };
        pay(self, 8 + 2 * state.missing_places.entries().len())?;
        let local = pair.0.local.as_usize();
        state.locals[local] = Some(value);
        state.missing_places.initialize(local, &[]);
        Ok(true)
    }

    fn execute_box_invocation(
        &mut self,
        invocation: Invocation<'tcx>,
        arguments: Vec<Value>,
        state: &State,
        conditions: Vec<Term>,
        stack: &[DefId],
    ) -> Result<Vec<Return>, String> {
        invocation.check(self, state)?;
        if !state.memory.incoming_byte_roots.is_empty()
            || !state.memory.startup_values.is_empty()
            || !state.memory.isolated_static_types.is_empty()
            || !state.memory.startup_overwritten.is_empty()
            || !state.memory.static_uninitialized.is_empty()
        {
            return Err("Box active destruction auxiliary Memory clone domain unsupported".into());
        }
        let masks =
            array_iterator_constructors::box_clone_masks(self, &state.memory.missing_places)?;
        pay(self, stack.len() + 32)?;
        let memory = state.memory.clone_with_iterator_drop_masks(masks);
        let instance = invocation.instance;
        let kind = invocation.kind;
        let chain = stack.iter().copied().chain([instance.def_id()]).collect();
        // Keep a shallow authenticated receipt for normal-only consumption after the actual
        // executor returns. No execution result, condition or payload is cached in this receipt.
        pay(self, 32)?;
        let completion = Invocation {
            key: invocation.key,
            certificate: invocation.certificate,
            source: invocation.source.clone(),
            entry: invocation.entry.clone(),
            box_allocation: invocation.box_allocation,
            instance,
            body: invocation.body.clone(),
            kind,
        };
        let previous = std::mem::replace(&mut self.call_chain, chain);
        let result = self.execute_body_with_protocol(
            array_drop_glue::Frame::box_destruction(instance, invocation),
            arguments,
            conditions,
            memory,
            stack,
            activation_flow::Flow::Unarmed,
        );
        if result.is_err() && self.failed_call_chain.is_none() {
            if let Err(error) = pay(self, self.call_chain.len() + 1) {
                self.call_chain = previous;
                return Err(error);
            }
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        let mut results = result?;
        for result in &mut results {
            match kind {
                Kind::PayloadGlue => {
                    completion.finish_payload(self, result)?;
                    #[cfg(test)]
                    lifecycle_tests::consumed(self, &completion, result)?;
                }
                Kind::BoxGlue => {
                    completion.retire_consumed(self, result)?;
                    #[cfg(test)]
                    lifecycle_tests::retired(self, &completion, result)?;
                }
                Kind::Destructor
                | Kind::BoxDrop
                | Kind::Alignment
                | Kind::Layout
                | Kind::Helper
                | Kind::Format => {
                    completion.source.current(self)?;
                    pay(
                        self,
                        result.memory.initialized_owners.len()
                            + result.memory.owned_regions.len()
                            + result.memory.missing_places.entries().len()
                            + 32,
                    )?;
                    completion.check_identity(self, &result.memory)?;
                }
            }
        }
        Ok(results)
    }

    pub(super) fn executable_box_arguments(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        arguments: &[Value],
        memory: &Memory,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        if !matches!(
            invocation.kind,
            Kind::BoxGlue | Kind::BoxDrop | Kind::Layout
        ) {
            return Ok(false);
        }
        invocation.source.current(self)?;
        pay(
            self,
            24 + memory.initialized_owners.len()
                + memory.owned_regions.len()
                + memory.missing_places.entries().len(),
        )?;
        invocation.check_identity(self, memory)?;
        if !Rc::ptr_eq(body, &invocation.body) {
            return Err("Box private core frame argument source differs".into());
        }
        match invocation.kind {
            Kind::BoxGlue | Kind::BoxDrop => {
                if !matches!(arguments, [Value::Reference { allocation, projection,
                mutable: true }]
                    if *allocation == invocation.box_allocation && projection.is_empty())
                {
                    return Err("Box private core tracked receiver differs".into());
                }
            }
            Kind::Layout => {
                let [size, alignment] = arguments else {
                    return Err("Box private Layout scalar arguments differ".into());
                };
                for (value, expected) in
                    [(size, 0), (alignment, invocation.source.layout.alignment())]
                {
                    pay(self, 8)?;
                    let (term, bits, signed) = value.integer()?;
                    if !term.belongs_to(&self.terms)
                        || bits != invocation.source.layout.bits()
                        || signed
                        || !matches!(symbolic::constant(&term),
                            Some(symbolic::Constant::BitVec { value, .. }) if value == expected)
                    {
                        return Err(
                            "Box private Layout original size/alignment facts differ".into()
                        );
                    }
                }
            }
            Kind::PayloadGlue
            | Kind::Destructor
            | Kind::Alignment
            | Kind::Helper
            | Kind::Format => {
                return Err("Box private core observation domain differs".into());
            }
        }
        if self.specification(invocation.instance)?.is_some()
            || self
                .configured_contracts(invocation.instance)?
                .iter()
                .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
        {
            return Err("Box private core contract observations remain unsupported".into());
        }
        Ok(true)
    }

    pub(super) fn executable_box_escape(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        value: &Value,
        incoming: usize,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        invocation.check(self, state)?;
        if !Rc::ptr_eq(body, &invocation.body) {
            return Err("Box destruction return source Body differs".into());
        }
        if matches!(value, Value::OwnedRegion { .. } | Value::Reference { .. }) {
            return Err("Box destruction return cannot expose private ownership or a lease".into());
        }
        let clone_work = transport_clone_work(self, value, &mut 0)?;
        pay(self, incoming + 16 + clone_work)?;
        self.return_value(value.clone(), state, incoming)?;
        self.executable_box_incoming_work(invocation, state, incoming, invocation.box_allocation)?;
        self.validate_incoming_frame_escape_with_box(
            state,
            incoming,
            invocation.box_allocation,
            invocation.key,
            invocation.certificate,
        )?;
        Ok(true)
    }

    pub(super) fn executable_box_call_gate(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        function: &Operand<'tcx>,
    ) -> Result<(), String> {
        let Some(invocation) = invocation else {
            return Ok(());
        };
        invocation.check(self, state)?;
        pay(self, 12)?;
        if !Rc::ptr_eq(body, &invocation.body) || !matches!(function, Operand::Constant(_)) {
            return Err("Box active destruction indirect call/Body unsupported".into());
        }
        let ty::FnDef(id, arguments) = function.ty(&body.local_decls, self.tcx).kind() else {
            return Err("Box active destruction requires an original function item".into());
        };
        pay(self, arguments.skip_binder().len() + 4)?;
        let callee = self.resolve_function_item(*id, arguments.skip_binder())?;
        match callee.def {
            ty::InstanceKind::Item(id)
                if matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) =>
            {
                array_iterator_constructors::authenticated_box_signature(self, callee)?;
                if self.foreign_rust_target(callee)?.is_some()
                    || self.specification(callee)?.is_some_and(|spec| {
                        spec.trusted
                            || spec.storage_effect.is_some()
                            || spec.returns_alias.is_some()
                    })
                {
                    return Err(
                        "Box active destruction configured/foreign adapter unsupported".into(),
                    );
                }
                if !invocation
                    .source
                    .bodies
                    .iter()
                    .any(|source| source.instance == callee)
                    && !crate::identity::is_panic_call(self.tcx, id)
                    && !self.is_core_panic_helper(id)
                {
                    return Err("Box active destruction has no authenticated actual callee".into());
                }
            }
            ty::InstanceKind::Intrinsic(_) if invocation.kind == Kind::BoxDrop => {
                layout_intrinsic(self, callee, invocation.source.payload)?;
            }
            ty::InstanceKind::Intrinsic(_) if invocation.kind == Kind::Alignment => {
                count_intrinsic(self, callee)?;
            }
            _ => return Err("Box active destruction resolved adapter unsupported".into()),
        }
        Ok(())
    }

    pub(super) fn executable_box_statement_gate(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        statement: &Statement<'tcx>,
    ) -> Result<(), String> {
        let Some(invocation) = invocation else {
            return Ok(());
        };
        invocation.check(self, state)?;
        pay(self, 8)?;
        if !Rc::ptr_eq(body, &invocation.body) {
            return Err("Box active destruction statement Body differs".into());
        }
        let StatementKind::Assign(pair) = &statement.kind else {
            return Ok(());
        };
        if matches!(invocation.kind, Kind::Destructor | Kind::Helper)
            && (matches!(
                &pair.1,
                Rvalue::RawPtr(..)
                    | Rvalue::Cast(
                        CastKind::Transmute
                            | CastKind::BoxDerefTransmute
                            | CastKind::PointerWithExposedProvenance
                            | CastKind::PointerExposeProvenance
                            | CastKind::PtrToPtr,
                        ..
                    )
            ) || matches!(&pair.1, Rvalue::BinaryOp(_, operands)
                    if [&operands.0, &operands.1].iter().any(|operand|
                        matches!(operand.ty(&body.local_decls, self.tcx).kind(),
                            ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..)))))
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "Box child Drop physical address operations remain unsupported".into(),
            ));
        }
        Ok(())
    }
}

fn fieldless_value<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    value: &Value,
) -> Result<bool, String> {
    pay(engine, 8)?;
    let ty::Adt(definition, _) = original.kind() else {
        return Ok(false);
    };
    let mut id = definition.did();
    let mut bytes = 0usize;
    for depth in 0..16 {
        pay(engine, 4)?;
        let key = engine.tcx.def_key(id);
        if let Some(name) = key.disambiguated_data.data.get_opt_name() {
            bytes = bytes.saturating_add(name.as_str().len());
        }
        bytes = bytes.saturating_add(32); // Fixed punctuation and u32 disambiguator envelope.
        if bytes > 512 {
            return Err("executable Box original name exceeds512-byte bound".into());
        }
        match key.parent {
            Some(index) => {
                id = DefId {
                    krate: id.krate,
                    index,
                }
            }
            None => {
                pay(engine, 8)?;
                bytes += engine.tcx.crate_name(id.krate).as_str().len() + 32;
                if bytes > 512 {
                    return Err("executable Box original name exceeds512-byte bound".into());
                }
                pay(engine, bytes + 16)?;
                let name = engine.tcx.def_path_str(definition.did());
                if name.len() > bytes {
                    return Err("executable Box original name envelope differs".into());
                }
                return Ok(
                    matches!(value,Value::Adt{name:actual,variant:0,is_option:false,
                    discriminant:0,fields} if fields.is_empty() && *actual==name),
                );
            }
        }
        if depth == 15 {
            return Err("executable Box original name exceedsdepth16".into());
        }
    }
    Err("executable Box original name absent".into())
}
fn requires_execution<'tcx>(engine: &mut Engine<'tcx>, payload: Ty<'tcx>) -> Result<bool, String> {
    pay(engine, 64)?;
    if !payload.needs_drop(engine.tcx, ty::TypingEnv::fully_monomorphized()) {
        return Ok(false);
    }
    let certificate = match owned_box_effect_free_drop::certify_type(engine.tcx, payload) {
        Ok(certificate) => certificate,
        Err(_) => return Ok(false),
    };
    if !engine.tcx.is_mir_available(certificate.destructor.def_id()) {
        return Ok(false);
    }
    let raw = engine.tcx.instance_mir(certificate.destructor.def);
    Ok(owned_box_effect_free_drop::destructor_body(
        engine.tcx,
        certificate.destructor,
        raw,
        &certificate,
    )
    .is_err())
}
fn caller_source<'tcx>(
    engine: &mut Engine<'tcx>,
    body: &Rc<Body<'tcx>>,
) -> Result<ty::Instance<'tcx>, String> {
    let registered = engine.bodies.borrow().len();
    pay(engine, 8 + 3 * registered)?;
    let instance = {
        let registered = engine.bodies.borrow();
        if registered.len() > MAX_INPUT_VALUES {
            return Err("executable Box caller registry exceeds512".into());
        }
        let mut matches = registered
            .iter()
            .filter(|(_, current)| Rc::ptr_eq(current, body));
        let instance = *matches
            .next()
            .ok_or("executable Box caller source absent")?
            .0;
        if matches.next().is_some() {
            return Err("executable Box caller full Instance is ambiguous".into());
        }
        instance
    };
    array_iterator_constructors::authenticated_box_callable(engine, instance)?;
    let current = array_iterator_constructors::authenticated_box_item_source(engine, instance)?;
    if !Rc::ptr_eq(&current, body) {
        return Err("executable Box caller original/current source differs".into());
    }
    Ok(instance)
}
impl<'tcx> Engine<'tcx> {
    pub(super) fn box_occurrence_before(
        &mut self,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        state: &State,
    ) -> Result<Option<Occurrence<'tcx>>, String> {
        if self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
            != Some(callee.def_id())
            || callee.args.len() != 1
        {
            return Ok(None);
        }
        let payload = callee.args.type_at(0);
        if !requires_execution(self, payload)? {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        let caller = caller_source(self, body)?;
        pay(self, 24)?;
        let TerminatorKind::Call {
            func: Operand::Constant(function),
            args,
            destination,
            target: Some(_),
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("executable Box occurrence lacks direct original Call".into());
        };
        if !destination.projection.is_empty()
            || state.addresses.get(destination.local.as_usize()) != Some(&None)
            || !matches!(state.locals.get(destination.local.as_usize()), Some(None))
            || destination.ty(&body.local_decls, self.tcx).ty != self.original_box_type(payload)?
        {
            return Err(
                "executable Box occurrence destination requires a fresh original whole Box local"
                    .into(),
            );
        }
        let ty::FnDef(id, parameters) = function.const_.ty().kind() else {
            return Err("executable Box occurrence lacks original FnDef".into());
        };
        if self.resolve_function_item(*id, parameters.skip_binder())? != callee {
            return Err("executable Box occurrence selected Instance differs".into());
        }
        let [argument] = args.as_ref() else {
            return Err("executable Box occurrence has wrong argument arity".into());
        };
        let Operand::Move(place) = argument.node else {
            return Err("executable Box occurrence requires exact initialized Move".into());
        };
        let local = place.local.as_usize();
        if !place.projection.is_empty()
            || state.addresses.get(local) != Some(&None)
            || place.ty(&body.local_decls, self.tcx).ty != payload
        {
            return Err("executable Box occurrence source type/place differs".into());
        }
        pay(self, 8 + state.missing_places.entries().len())?;
        state.missing_places.check(local, &[])?;
        let value = state
            .locals
            .get(local)
            .and_then(Option::as_ref)
            .ok_or("executable Box occurrence initialized source absent")?;
        if !fieldless_value(self, payload, value)? {
            return Err("executable Box occurrence initialized typed source differs".into());
        }
        pay(self, 16)?;
        Ok(Some(Occurrence {
            caller,
            body: body.clone(),
            block,
            constructor: callee,
            payload,
            local,
            destination: destination.local.as_usize(),
            state,
            context: self.terms.boolean(true),
        }))
    }
}
impl<'tcx> Occurrence<'tcx> {
    fn after(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        callee: ty::Instance<'tcx>,
        value: &Value,
        state: &State,
    ) -> Result<(), String> {
        pay(engine, 24 + state.missing_places.entries().len())?;
        if !self.context.belongs_to(&engine.terms)
            || !std::ptr::eq(self.state, state)
            || !Rc::ptr_eq(body, &self.body)
            || block != self.block
            || callee != self.constructor
            || callee.args.type_at(0) != self.payload
            || state.locals.get(self.local).is_none()
            || state.addresses.get(self.local) != Some(&None)
            || state.missing_places.check(self.local, &[]).is_ok()
            || state.addresses.get(self.destination) != Some(&None)
            || !matches!(state.locals.get(self.destination), Some(None))
            || !fieldless_value(engine, self.payload, value)?
        {
            return Err("executable Box actual Move/result/invocation receipt differs".into());
        }
        // Core Move consumes the initialization footprint, retaining inaccessible bytes.
        // Residual bytes are data only; they cannot become another initialized carrier.
        if let Some(residual) = state.locals[self.local].as_ref()
            && !fieldless_value(engine, self.payload, residual)?
        {
            return Err(
                "executable Box consumed residual differs from original fieldless T".into(),
            );
        }
        if caller_source(engine, body)? != self.caller {
            return Err("executable Box caller receipt source changed".into());
        }
        Ok(())
    }
}

fn body_source<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    kind: Kind,
) -> Result<BodySource<'tcx>, String> {
    let (current, signature) = match instance.def {
        ty::InstanceKind::Item(_) => {
            let signature =
                array_iterator_constructors::authenticated_box_signature(engine, instance)?;
            if engine.foreign_rust_target(instance)?.is_some()
                || engine.specification(instance)?.is_some_and(|spec| {
                    spec.trusted || spec.storage_effect.is_some() || spec.returns_alias.is_some()
                })
            {
                return Err("executable Box source summary/foreign adapter unsupported".into());
            }
            (
                array_iterator_constructors::authenticated_box_item_source(engine, instance)?,
                Some(signature),
            )
        }
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_))) => (
            array_iterator_constructors::authenticated_box_drop_source(engine, instance)?,
            None,
        ),
        _ => return Err("executable Box source adapter unsupported".into()),
    };
    pay(engine, 12)?;
    Ok(BodySource {
        instance,
        current,
        kind,
        signature,
    })
}
fn direct_callee<'tcx>(
    engine: &Engine<'tcx>,
    body: &Body<'tcx>,
    block: usize,
) -> Result<ty::Instance<'tcx>, String> {
    let TerminatorKind::Call {
        func: Operand::Constant(function),
        ..
    } = &body.basic_blocks[BasicBlock::from_usize(block)]
        .terminator()
        .kind
    else {
        return Err("executable Box source lacks original direct edge".into());
    };
    let ty::FnDef(id, arguments) = function.const_.ty().kind() else {
        return Err("executable Box source edge has no FnDef".into());
    };
    engine.resolve_function_item(*id, arguments.skip_binder())
}

fn push_source<'tcx>(
    engine: &mut Engine<'tcx>,
    sources: &mut Vec<BodySource<'tcx>>,
    source: BodySource<'tcx>,
) -> Result<(), String> {
    pay(engine, 8 + 4 * sources.len())?;
    if sources.len() >= 16 {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "executable Box source exceeds16 records".into(),
        ));
    }
    sources
        .try_reserve_exact(1)
        .map_err(|_| "executable Box source allocation failed")?;
    sources.push(source);
    Ok(())
}
fn layout_intrinsic<'tcx>(
    engine: &mut Engine<'tcx>,
    callee: ty::Instance<'tcx>,
    payload: Ty<'tcx>,
) -> Result<(), String> {
    // This closed compiler signature has no region/constant graph and one fieldless type argument.
    // Inspect exact raw types before substitution; this is not a general intrinsic signature gate.
    pay(engine, 64)?;
    let ty::InstanceKind::Intrinsic(id) = callee.def else {
        return Err("executable Box layout operation lacks exact intrinsic Instance".into());
    };
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("core source unavailable")?
        .krate;
    if id.krate != core
        || callee.args.len() != 1
        || callee.args.type_at(0) != payload
        || !matches!(
            engine.tcx.item_name(id).as_str(),
            "size_of_val" | "align_of_val"
        )
    {
        return Err("executable Box layout intrinsic identity/type differs".into());
    }
    let original = engine.tcx.fn_sig(id);
    let raw = original.skip_binder();
    let inputs = raw.skip_binder().inputs();
    if !raw.bound_vars().is_empty()
        || inputs.len() != 1
        || raw.skip_binder().output() != engine.tcx.types.usize
        || raw.skip_binder().safety() != rustc_hir::Safety::Unsafe
        || raw.skip_binder().abi() != rustc_abi::ExternAbi::Rust
        || raw.skip_binder().c_variadic()
        || !matches!(inputs[0].kind(), ty::RawPtr(inner, mutable)
            if !mutable.is_mut() && matches!(inner.kind(), ty::Param(p) if p.index==0))
    {
        return Err("executable Box layout intrinsic raw full signature differs".into());
    }
    pay(engine, 64)?;
    let expected = engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            original.instantiate(engine.tcx, callee.args),
        )
        .map_err(|_| "executable Box layout intrinsic normalization failed")?;
    pay(engine, 8)?;
    if engine
        .call_signatures
        .borrow()
        .get(&callee)
        .is_some_and(|cached| *cached != expected)
    {
        return Err("executable Box layout intrinsic cached full signature differs".into());
    }
    Ok(())
}
fn count_intrinsic<'tcx>(
    engine: &mut Engine<'tcx>,
    callee: ty::Instance<'tcx>,
) -> Result<(), String> {
    pay(engine, 64)?;
    let ty::InstanceKind::Intrinsic(id) = callee.def else {
        return Err("executable Box count operation requires actual intrinsic".into());
    };
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("core source unavailable")?
        .krate;
    if id.krate != core
        || engine.tcx.item_name(id).as_str() != "ctpop"
        || callee.args.len() != 1
        || callee.args.type_at(0) != engine.tcx.types.usize
    {
        return Err("executable Box count intrinsic identity/type differs".into());
    }
    let original = engine.tcx.fn_sig(id);
    let raw = original.skip_binder();
    let inputs = raw.skip_binder().inputs();
    if !raw.bound_vars().is_empty()
        || inputs.len() != 1
        || !matches!(inputs[0].kind(), ty::Param(p) if p.index==0)
        || raw.skip_binder().output() != engine.tcx.types.u32
        || raw.skip_binder().safety() != rustc_hir::Safety::Safe
        || raw.skip_binder().abi() != rustc_abi::ExternAbi::Rust
        || raw.skip_binder().c_variadic()
    {
        return Err("executable Box count intrinsic raw full signature differs".into());
    }
    pay(engine, 64)?;
    let expected = engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            original.instantiate(engine.tcx, callee.args),
        )
        .map_err(|_| "executable Box count intrinsic normalization failed")?;
    pay(engine, 8)?;
    if engine
        .call_signatures
        .borrow()
        .get(&callee)
        .is_some_and(|cached| *cached != expected)
    {
        return Err("executable Box count intrinsic cached full signature differs".into());
    }
    Ok(())
}
fn helper_graph<'tcx>(
    engine: &mut Engine<'tcx>,
    sources: &mut Vec<BodySource<'tcx>>,
    payload: Ty<'tcx>,
) -> Result<(), String> {
    let mut cursor = 2;
    let mut edges = 0;
    while cursor < sources.len() {
        pay(engine, 12)?;
        let body = sources[cursor].current.clone();
        let kind = sources[cursor].kind;
        let source_instance = sources[cursor].instance;
        cursor += 1;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            pay(engine, 4)?;
            if kind == Kind::BoxDrop && ![0, 4, 5, 6, 7, 8, 9, 3].contains(&block.as_usize()) {
                continue;
            }
            if (kind == Kind::Alignment && ![0, 3, 1].contains(&block.as_usize()))
                || (kind == Kind::Layout && ![0, 1].contains(&block.as_usize()))
            {
                continue;
            }

            if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
                continue;
            }
            edges += 1;
            pay(engine, 16 + sources.len())?;
            if edges > 512 {
                return Err("executable Box helper source exceeds512 edges".into());
            }
            let callee = direct_callee(engine, &body, block.as_usize())?;
            if matches!(callee.def, ty::InstanceKind::Intrinsic(_)) {
                if kind == Kind::BoxDrop {
                    layout_intrinsic(engine, callee, payload)?;
                } else if kind == Kind::Alignment {
                    count_intrinsic(engine, callee)?;
                } else {
                    return Err("executable Box helper intrinsic frontier unsupported".into());
                }
                continue;
            }
            array_iterator_constructors::authenticated_box_callable(engine, callee)?;
            if engine.foreign_rust_target(callee)?.is_some()
                || engine.specification(callee)?.is_some_and(|spec| {
                    spec.trusted || spec.storage_effect.is_some() || spec.returns_alias.is_some()
                })
            {
                return Err("executable Box helper configured/foreign summary unsupported".into());
            }
            if crate::identity::is_panic_call(engine.tcx, callee.def_id())
                || engine.is_core_panic_helper(callee.def_id())
            {
                continue;
            } // Existing actual panic primitive, never an invented available Body.
            if sources.iter().any(|source| source.instance == callee) {
                continue;
            }
            pay(engine, 16)?;
            let parent = engine.tcx.parent(callee.def_id());
            let formatting = engine.tcx.item_name(callee.def_id()).as_str() == "from_str"
                && matches!(
                    engine.tcx.def_kind(parent),
                    DefKind::Impl { of_trait: false }
                )
                && matches!(engine.tcx.type_of(parent).instantiate(engine.tcx, callee.args)
                    .skip_norm_wip().kind(), ty::Adt(def, _)
                    if engine.tcx.lang_items().get(LangItem::FormatArguments) == Some(def.did()));
            let child_kind = if kind == Kind::BoxDrop && block.as_usize() == 6 {
                Kind::Alignment
            } else if kind == Kind::BoxDrop && block.as_usize() == 8 {
                Kind::Layout
            } else if formatting {
                Kind::Format
            } else {
                Kind::Helper
            };
            if child_kind == Kind::Helper && source_instance == callee {
                return Err("executable Box recursive helper remains unsupported".into());
            }
            let source = body_source(engine, callee, child_kind)?;
            if child_kind == Kind::Format {
                formatting::schema(engine, &source.current)?;
            }
            if matches!(child_kind, Kind::Alignment | Kind::Layout) {
                pay(engine, 4 * 65536)?;
                let core = engine
                    .tcx
                    .lang_items()
                    .sized_trait()
                    .ok_or("core unavailable")?
                    .krate;
                let raw = engine.tcx.instance_mir(callee.def);
                let encoded = pure_comparison_templates::encode_template_with_alloc(
                    engine.tcx,
                    raw,
                    core,
                    Some(source_instance.def_id().krate),
                )?;
                let definition = pure_comparison_templates::owned_definition_key(callee.def_id());
                pay(engine, encoded.len() + definition.len() + 16)?;
                let expected = if child_kind == Kind::Alignment {
                    owned_box_templates::BoxTemplateFamily::AlignmentPrecondition
                } else {
                    owned_box_templates::BoxTemplateFamily::LayoutPrecondition
                };
                if owned_box_templates::executable_drop_family(&definition, &encoded)
                    != Some(expected)
                {
                    return Err("executable Box layout precondition original schema differs".into());
                }
            }
            push_source(engine, sources, source)?;
        }
    }
    Ok(())
}
impl<'tcx> Source<'tcx> {
    fn prepare(engine: &mut Engine<'tcx>, constructor: ty::Instance<'tcx>) -> Result<Self, String> {
        let certificate = owned_box_constructor_source::prepare(engine, constructor)?;
        let payload = constructor.args.type_at(0);
        pay(engine, 96)?; // Separate original Box identity, fieldless metadata and layout services.
        let original = engine.original_box_type(payload)?;
        let layout = owned_box_payloads::ZeroLayout::for_type(engine.tcx, payload)?;
        let mut bodies = Vec::new();
        let glue = ty::Instance::resolve_drop_glue(engine.tcx, original);
        let outer = body_source(engine, glue, Kind::BoxGlue)?;
        pay(engine, 64 + outer.current.local_decls.len() * 8)?;
        let nominal = owned_box_payloads::Certificate::fieldless(engine.tcx, payload)?;
        owned_box_glue::nominal_glue(engine.tcx, glue, &outer.current, &nominal, original)?;
        let box_drop = direct_callee(engine, &outer.current, 2)?;
        let payload_glue = ty::Instance::resolve_drop_glue(engine.tcx, payload);
        let inner = body_source(engine, payload_glue, Kind::PayloadGlue)?;
        pay(engine, 64 + inner.current.local_decls.len() * 8)?;
        let typed = owned_box_effect_free_drop::certify_type(engine.tcx, payload)?;
        owned_box_effect_free_drop::payload_glue(engine.tcx, payload_glue, &inner.current, &typed)?;
        push_source(engine, &mut bodies, outer)?;
        push_source(engine, &mut bodies, inner)?;
        let destructor = body_source(engine, typed.destructor, Kind::Destructor)?;
        push_source(engine, &mut bodies, destructor)?;
        let actual_drop = body_source(engine, box_drop, Kind::BoxDrop)?;
        // Separate canonical materialization payment. Original/current typed comparison above
        // remains independent and no constructor component cache domain is widened.
        pay(engine, 4 * 65536)?;
        let raw = engine.tcx.instance_mir(box_drop.def);
        let core = engine
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("core source unavailable")?
            .krate;
        let encoded = pure_comparison_templates::encode_template_with_alloc(
            engine.tcx,
            raw,
            core,
            Some(box_drop.def_id().krate),
        )?;
        let definition = pure_comparison_templates::owned_definition_key(box_drop.def_id());
        pay(engine, encoded.len() + definition.len() + 16)?;
        if owned_box_templates::executable_drop_family(&definition, &encoded)
            != Some(owned_box_templates::BoxTemplateFamily::BoxDrop)
        {
            return Err("executable Box selected Drop source schema differs".into());
        }
        push_source(engine, &mut bodies, actual_drop)?;
        helper_graph(engine, &mut bodies, payload)?;
        pay(engine, 32)?;
        Ok(Self {
            constructor: certificate,
            constructor_instance: constructor,
            payload,
            original,
            layout,
            context: engine.terms.boolean(true),
            bodies,
        })
    }
    fn current(&self, engine: &mut Engine<'tcx>) -> Result<(), String> {
        pay(engine, 16 + self.bodies.len() * 8)?;
        if !self.context.belongs_to(&engine.terms) {
            return Err("executable Box immutable source Context differs".into());
        }
        let bodies = engine.bodies.borrow();
        let signatures = engine.call_signatures.borrow();
        for source in &self.bodies {
            if !bodies
                .get(&source.instance)
                .is_some_and(|body| Rc::ptr_eq(body, &source.current))
                || source.signature.is_some_and(|original| {
                    signatures
                        .get(&source.instance)
                        .is_some_and(|cached| *cached != original)
                })
            {
                return Err("executable Box current Body/full signature source changed".into());
            }
        }
        Ok(())
    }
    fn validate(&self, engine: &mut Engine<'tcx>) -> Result<(), String> {
        pay(engine, 16 + self.bodies.len() * 8)?;
        if !self.context.belongs_to(&engine.terms)
            || engine.original_box_type(self.payload)? != self.original
            || owned_box_payloads::ZeroLayout::for_type(engine.tcx, self.payload)? != self.layout
        {
            return Err("executable Box source original type/layout/Context differs".into());
        }
        self.constructor.validate(engine)?;
        for source in &self.bodies {
            let current = body_source(engine, source.instance, source.kind)?;
            if !Rc::ptr_eq(&current.current, &source.current) {
                return Err("executable Box immutable current Body source changed".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn executable_box_actual_source_frontier() {
        struct Check;
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                for name in ["Panicking", "HelperMarker"] {
                    let id = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == DefKind::AssocFn
                                && tcx.item_name(id.to_def_id()).as_str() == "drop"
                                && matches!(tcx.fn_sig(id.to_def_id()).instantiate_identity()
                            .skip_binder().inputs()[0].kind(),ty::Ref(_, child, _)
                            if matches!(child.kind(),ty::Adt(def,_) if
                                tcx.item_name(def.did()).as_str()==name))
                        })
                        .unwrap();
                    let receiver = tcx
                        .fn_sig(id.to_def_id())
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()[0];
                    let ty::Ref(_, payload, _) = receiver.kind() else {
                        unreachable!()
                    };
                    let mut engine = Engine::new(
                        tcx,
                        &config,
                        VerificationOptions {
                            all_failures: false,
                            induction: false,
                            startup: false,
                            isolated_startup: false,
                            async_entry: false,
                            limits: miren::AnalysisLimits {
                                max_steps: 2_000_000,
                                ..Default::default()
                            },
                        },
                    );
                    let constructor = engine
                        .resolve_function_item(
                            tcx.get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
                                .unwrap(),
                            tcx.mk_args(&[(*payload).into()]),
                        )
                        .unwrap();
                    let result = Source::prepare(&mut engine, constructor);
                    println!(
                        "EXECUTABLE_BOX_SOURCE name={name} work={} result={:?}",
                        engine.steps,
                        result.as_ref().map(|source| source.bodies.len())
                    );
                    let source =
                        result.expect("actual Box/T source must be available at diagnostic budget");
                    source.validate(&mut engine).unwrap();
                    assert!(engine.owned_box_types.is_empty());
                    assert_eq!(engine.next_owned_region, 0);
                    assert!(engine.proof.body_entries.is_empty());
                }
                rustc_driver::Compilation::Stop
            }
        }
        let directory =
            std::env::temp_dir().join(format!("box-executable-source-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        let args = vec![
            "rustc".into(),
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tests/fixtures/effect_free_zst_box_drop.rs"
            )
            .into(),
            "--crate-type=lib".into(),
            "--edition=2024".into(),
            "-Cpanic=abort".into(),
            "-Coverflow-checks=yes".into(),
            "-Zmir-opt-level=0".into(),
            "-Copt-level=0".into(),
            "--out-dir".into(),
            directory.to_str().unwrap().into(),
            "--sysroot".into(),
            String::from_utf8(sysroot.stdout).unwrap().trim().into(),
        ];
        rustc_driver::run_compiler(&args, &mut Check);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
