//! Distinct payments for executed frame, branch and observation work.
use super::*;

#[derive(Clone, Copy)]
pub(in crate::proof) enum Observation {
    Entry,
    Requires,
    FinalArguments,
    Result,
}

#[cfg(test)]
mod tests;

fn bound(engine: &mut Engine<'_>, count: usize, domain: &str) -> Result<(), String> {
    pay(engine, 1)?;
    if count > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            format!("Box {domain} exceeds existing 512-node bound"),
        ));
    }
    Ok(())
}

fn memory_clone_work(engine: &mut Engine<'_>, memory: &Memory) -> Result<usize, String> {
    pay(engine, 8)?;
    // These are unsupported by execute_box_invocation before its Memory clone too.
    if !memory.incoming_byte_roots.is_empty()
        || !memory.startup_values.is_empty()
        || !memory.isolated_static_types.is_empty()
        || !memory.startup_overwritten.is_empty()
        || !memory.static_uninitialized.is_empty()
    {
        return Err("Box branch auxiliary Memory clone domain unsupported".into());
    }
    // allocations, regions, mutable backing and typed owners retain Rc vector identities.
    // Only the independent initialization ledger owns nested vectors in this domain.
    Ok(24 + array_iterator_constructors::box_mask_clone_work(engine, &memory.missing_places)?)
}

/// Borrowed planning has its own paid visits; no semantic graph observations are cached.
fn incoming_graph_work(
    engine: &mut Engine<'_>,
    value: &Value,
    memory: &Memory,
    depth: usize,
    nodes: &mut usize,
    visited: &mut Vec<usize>,
) -> Result<usize, String> {
    pay(engine, 1)?;
    *nodes += 1;
    if *nodes > MAX_INPUT_VALUES || depth >= MAX_INPUT_DEPTH {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box incoming graph exceeds existing 512-node/depth16 bounds".into(),
        ));
    }
    let mut work = 4;
    match value {
        Value::Reference { allocation, .. }
        | Value::Cell { allocation }
        | Value::LocalAtomic { allocation, .. } => {
            if let Value::Reference { projection, .. } = value {
                bound(engine, projection.len(), "incoming reference projection")?;
                pay(engine, projection.len())?;
                for part in projection {
                    match part {
                        MemoryProjection::Field(_) | MemoryProjection::Variant(_) => {}
                        MemoryProjection::Index(_)
                        | MemoryProjection::TypedIndex { .. }
                        | MemoryProjection::Slice { .. }
                        | MemoryProjection::Chunks { .. } => {
                            return Err("Box incoming dynamic projection work unsupported".into());
                        }
                    }
                }
                work += projection.len();
            }
            pay(engine, 1 + visited.len())?;
            work += 4 + 2 * visited.len();
            if !visited.contains(allocation) {
                // Planning Vec growth is paid independently of the future validators'
                // visited vectors. Existing shared-trait visit charges remain untouched.
                pay(engine, visited.len() + 2)?;
                visited.push(*allocation);
                work += 6 + 3 * visited.len();
                if let Some(Some(stored)) = memory.get(*allocation) {
                    work += incoming_graph_work(engine, stored, memory, depth + 1, nodes, visited)?;
                }
            }
        }
        Value::Tuple(fields)
        | Value::Enum {
            variants: fields, ..
        } => {
            bound(engine, fields.len(), "incoming fields")?;
            for field in fields {
                work += incoming_graph_work(engine, field, memory, depth + 1, nodes, visited)?;
            }
        }
        Value::Elements(fields) => {
            bound(engine, fields.len(), "incoming elements")?;
            for field in fields.iter() {
                work += incoming_graph_work(engine, field, memory, depth + 1, nodes, visited)?;
            }
        }
        Value::Adt { fields, .. } => {
            bound(engine, fields.len(), "incoming ADT fields")?;
            for (_, field) in fields {
                work += incoming_graph_work(engine, field, memory, depth + 1, nodes, visited)?;
            }
        }
        Value::OwnedRegion {
            kind: symbolic::OwnedRegionKind::Owner,
            ..
        }
        | Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Atomic { .. }
        | Value::RawPointer { .. }
        | Value::Uninitialized
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Unit => {}
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Bytes { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. } => {
            return Err("Box incoming auxiliary graph planning domain unsupported".into());
        }
    }
    Ok(work)
}

fn snapshot_work(
    engine: &mut Engine<'_>,
    value: &Value,
    memory: &Memory,
    depth: usize,
    nodes: &mut usize,
) -> Result<usize, String> {
    pay(engine, 1)?;
    *nodes += 1;
    if *nodes > MAX_INPUT_VALUES || depth >= MAX_INPUT_DEPTH {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box argument snapshot exceeds existing 512-node/depth16 bounds".into(),
        ));
    }
    match value {
        Value::Reference {
            allocation,
            projection,
            ..
        } => {
            bound(engine, projection.len(), "snapshot projection")?;
            if projection.len() > MAX_INPUT_DEPTH {
                return Err("Box snapshot projection exceeds existing depth16 bound".into());
            }
            let mut stored = memory
                .get(*allocation)
                .and_then(Option::as_ref)
                .ok_or("Box snapshot backing unavailable")?;
            let mut clone_nodes = 0;
            // reference_storage clones the backing, then materializes (clones) the
            // intermediate once per projection and clones each selected field.
            let mut work = transport_clone_work(engine, stored, &mut clone_nodes)? + 8;
            let masks = memory.missing_places.entries();
            bound(engine, masks.len(), "snapshot initialization entries")?;
            for (_, path) in masks {
                bound(engine, path.len(), "snapshot initialization path")?;
                pay(engine, path.len() + 1)?;
                work += 2 * (path.len() + projection.len() + 1);
            }
            for part in projection {
                pay(engine, 1)?;
                work += transport_clone_work(engine, stored, &mut clone_nodes)?;
                stored = match (part, stored) {
                    (MemoryProjection::Field(index), Value::Adt { fields, .. }) => fields
                        .get(*index)
                        .map(|(_, value)| value)
                        .ok_or("Box snapshot ADT field absent")?,
                    (MemoryProjection::Field(index), Value::Tuple(fields)) => fields
                        .get(*index)
                        .ok_or("Box snapshot tuple field absent")?,
                    (MemoryProjection::Variant(expected), Value::Adt { variant, .. })
                        if expected == variant =>
                    {
                        continue;
                    }
                    (
                        MemoryProjection::Field(_)
                        | MemoryProjection::Variant(_)
                        | MemoryProjection::Index(_)
                        | MemoryProjection::TypedIndex { .. }
                        | MemoryProjection::Slice { .. }
                        | MemoryProjection::Chunks { .. },
                        _,
                    ) => {
                        return Err("Box snapshot dynamic/opaque projection unsupported".into());
                    }
                };
                work += transport_clone_work(engine, stored, &mut clone_nodes)?;
            }
            work += snapshot_work(engine, stored, memory, depth + 1, nodes)?;
            Ok(work)
        }
        Value::Tuple(fields) => {
            bound(engine, fields.len(), "snapshot tuple")?;
            let mut work = 2 + fields.len();
            for field in fields {
                work += snapshot_work(engine, field, memory, depth + 1, nodes)?;
            }
            Ok(work)
        }
        Value::Elements(fields) => {
            bound(engine, fields.len(), "snapshot elements")?;
            let mut work = 3 + fields.len();
            for field in fields.iter() {
                work += snapshot_work(engine, field, memory, depth + 1, nodes)?;
            }
            Ok(work)
        }
        Value::Adt { name, fields, .. } => {
            bound(engine, name.len(), "snapshot ADT name")?;
            bound(engine, fields.len(), "snapshot ADT fields")?;
            let mut work = name.len() + 8 + fields.len();
            for (name, field) in fields {
                bound(engine, name.len(), "snapshot field name")?;
                work += name.len() + 2 + snapshot_work(engine, field, memory, depth + 1, nodes)?;
            }
            Ok(work)
        }
        Value::Enum {
            discriminant,
            variants,
            ..
        } => {
            bound(engine, variants.len(), "snapshot enum")?;
            let mut work = 4 + variants.len() + transport_clone_work(engine, discriminant, &mut 0)?;
            for variant in variants {
                work += snapshot_work(engine, variant, memory, depth + 1, nodes)?;
            }
            Ok(work)
        }
        Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Atomic { .. }
        | Value::RawPointer { .. }
        | Value::Uninitialized
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Unit => transport_clone_work(engine, value, &mut 0),
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Bytes { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::Cell { .. }
        | Value::LocalAtomic { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. } => {
            Err("Box argument auxiliary snapshot planning domain unsupported".into())
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn executable_box_binding_clone_work(
        &mut self,
        bindings: &BTreeMap<String, Value>,
    ) -> Result<(), String> {
        bound(self, bindings.len(), "postcondition bindings")?;
        let mut work = 4 + 8 * bindings.len();
        let mut nodes = 0;
        for (name, value) in bindings {
            bound(self, name.len(), "binding key")?;
            work += name.len() + 2 + transport_clone_work(self, value, &mut nodes)?;
        }
        pay(self, work)
    }

    pub(in crate::proof) fn executable_box_configured_binding_work(
        &mut self,
        body: &Body<'tcx>,
        values: &[Value],
    ) -> Result<(), String> {
        bound(self, body.var_debug_info.len(), "contract debug names")?;
        bound(self, self.config.functions.len(), "configured selectors")?;
        let mut work = 8;
        let mut nodes = 0;
        for debug in &body.var_debug_info {
            pay(self, 1)?;
            if let VarDebugInfoContents::Place(place) = debug.value
                && place.projection.is_empty()
                && place.local.as_usize() > 0
                && place.local.as_usize() <= body.arg_count
            {
                let name = debug.name.as_str();
                bound(self, name.len(), "compiler binding name")?;
                let value = values
                    .get(place.local.as_usize() - 1)
                    .ok_or("Box contract snapshot parameter unavailable")?;
                work += 16 + 2 * name.len() + transport_clone_work(self, value, &mut nodes)?;
            }
        }
        // Plan every compatible alias candidate by borrowed metadata. Actual selection
        // remains configured_bindings' original operation, once. This is a conservative
        // upper prepayment, not a fabricated selection or duplicated snapshot execution.
        let functions = self.config.functions.len();
        for index in 0..functions {
            pay(self, 1)?;
            let count = self.config.functions[index].arguments.len();
            bound(self, count, "configured argument aliases")?;
            if count == values.len() {
                for (argument, value) in values.iter().enumerate() {
                    pay(self, 1)?;
                    let bytes = self.config.functions[index].arguments[argument].len();
                    bound(self, bytes, "configured binding name")?;
                    work += 8
                        + bytes
                        + body.var_debug_info.len()
                        + transport_clone_work(self, value, &mut nodes)?;
                }
            }
        }
        pay(self, work)
    }

    pub(in crate::proof) fn executable_box_snapshot_work(
        &mut self,
        arguments: &[Value],
        memory: &Memory,
        observation: Observation,
    ) -> Result<(), String> {
        bound(self, arguments.len(), "argument observations")?;
        let mut nodes = 0;
        let mut work = 2 + arguments.len();
        for argument in arguments {
            work += snapshot_work(self, argument, memory, 0, &mut nodes)?;
        }
        // The tag identifies a service occurrence, never source or raw-access permission.
        let phase = match observation {
            Observation::Entry => None,
            Observation::Requires => Some(0),
            Observation::FinalArguments => Some(1),
            Observation::Result => Some(2),
        };
        #[cfg(test)]
        tests::contract_near_limit(self, phase);
        #[cfg(not(test))]
        let _ = phase;
        pay(self, work)?;
        #[cfg(test)]
        tests::contract_publication(phase);
        Ok(())
    }

    pub(in crate::proof) fn executable_box_snapshots(
        &mut self,
        arguments: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Vec<Value>, String> {
        self.executable_box_snapshot_work(arguments, memory, Observation::Entry)?;
        // Authenticated Box Item signatures already reject Coroutine families. For that
        // domain typed_coroutine_snapshots delegates to this same ordinary snapshot route;
        // omit its redundant type walk rather than discount work that still executes.
        self.snapshots(arguments, memory, conditions)
    }

    pub(in crate::proof) fn executable_box_contract_snapshots(
        &mut self,
        arguments: &[Value],
        memory: &Memory,
        conditions: &[Term],
        observation: Observation,
    ) -> Result<Vec<Value>, String> {
        self.executable_box_snapshot_work(arguments, memory, observation)?;
        self.snapshots(arguments, memory, conditions)
    }

    pub(in crate::proof) fn executable_box_final_argument_work(
        &mut self,
        body: &Body<'tcx>,
        state: &State,
    ) -> Result<(), String> {
        bound(self, body.arg_count, "final arguments")?;
        let mut work = 2 + body.arg_count;
        let mut nodes = 0;
        for local in body.args_iter() {
            pay(self, 1)?;
            let index = local.as_usize();
            let value = match state.addresses.get(index).copied().flatten() {
                Some(allocation) => state.memory.get(allocation).and_then(Option::as_ref),
                None => state.locals.get(index).and_then(Option::as_ref),
            }
            .ok_or("Box final argument initialized value unavailable")?;
            work += transport_clone_work(self, value, &mut nodes)?;
            let masks = if state.addresses[index].is_some() {
                &state.memory.missing_places
            } else {
                &state.missing_places
            };
            bound(
                self,
                masks.entries().len(),
                "final argument initialization entries",
            )?;
            // Whole-local checks use empty-prefix comparisons; no path payload is cloned.
            work += masks.entries().len() + 1;
        }
        pay(self, work)
    }

    pub(in crate::proof) fn executable_box_incoming_work(
        &mut self,
        invocation: &Invocation<'tcx>,
        state: &State,
        incoming: usize,
        authorized: usize,
    ) -> Result<(), String> {
        pay(self, 1)?;
        if authorized != invocation.box_allocation {
            return Err("Box incoming work authorized allocation differs".into());
        }
        bound(self, incoming, "incoming allocations")?;
        if incoming > state.memory.len() || !state.memory.static_uninitialized.is_empty() {
            return Err("Box incoming graph original allocation/static domain differs".into());
        }
        pay(self, incoming + 4)?;
        let mut work = 4;
        let mut nodes = 0;
        for (allocation, value) in state.memory[..incoming].iter().enumerate() {
            if allocation != authorized
                && let Some(value) = value
            {
                work += incoming_graph_work(
                    self,
                    value,
                    &state.memory,
                    0,
                    &mut nodes,
                    &mut Vec::new(),
                )?;
            }
        }
        #[cfg(test)]
        tests::near_limit(
            self,
            tests::Phase::Incoming,
            Some(invocation.kind),
            Some(state),
        );
        pay(self, work)?;
        #[cfg(test)]
        tests::publication(tests::Phase::Incoming);
        Ok(())
    }
    pub(in crate::proof) fn executable_box_argument_clone_work(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        arguments: &[Value],
    ) -> Result<(), String> {
        if invocation.is_some() {
            bound(self, arguments.len(), "mutable argument clone")?;
            let mut nodes = 0;
            let mut work = 2 + arguments.len();
            for argument in arguments {
                work += transport_clone_work(self, argument, &mut nodes)?;
            }
            pay(self, work)?;
        }
        Ok(())
    }

    pub(in crate::proof) fn executable_box_stack_work(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        count: usize,
    ) -> Result<(), String> {
        if invocation.is_some() {
            bound(self, count, "executed stack")?;
            pay(self, count + 4)?;
        }
        Ok(())
    }

    pub(in crate::proof) fn executable_box_frame_work(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        locals: usize,
        arguments: usize,
    ) -> Result<(), String> {
        if let Some(invocation) = invocation {
            pay(self, 1)?;
            if !matches!(
                invocation.kind,
                Kind::BoxGlue
                    | Kind::PayloadGlue
                    | Kind::Destructor
                    | Kind::BoxDrop
                    | Kind::Alignment
                    | Kind::Layout
                    | Kind::Helper
            ) {
                return Err("Box executable frame allocation kind differs".into());
            }
            bound(self, locals, "frame locals")?;
            bound(self, arguments, "frame arguments")?;
            // Two Option vectors and their headers; original argument-type handle vector.
            #[cfg(test)]
            tests::near_limit(self, tests::Phase::Frame, Some(invocation.kind), None);
            #[cfg(test)]
            tests::frame_count(invocation.kind, locals);
            pay(self, 8 + 2 * locals + arguments)?;
            #[cfg(test)]
            tests::publication(tests::Phase::Frame);
        }
        Ok(())
    }

    pub(in crate::proof) fn executable_box_switch_work(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        state: &State,
        targets: usize,
    ) -> Result<(), String> {
        let Some(invocation) = invocation else {
            return Ok(());
        };
        invocation.check(self, state)?;
        state.flow.require_unarmed()?;
        bound(self, targets, "switch targets")?;
        bound(self, state.conditions.len(), "branch conditions")?;
        bound(
            self,
            state.conditions.len() + targets,
            "post-switch conditions",
        )?;
        bound(self, state.constant_receipts.len(), "branch receipts")?;
        if targets != 0 {
            self.executable_box_continuation_work(state)?;
        }
        // continuation_work pays one locals/addresses/receipt/local-mask clone.
        // Every actual State clone owns those same containers independently.
        // Plan additional clones separately rather than applying a discounted multiplier.
        for _ in 1..targets {
            self.executable_box_continuation_work(state)?;
        }
        let memory = memory_clone_work(self, &state.memory)?;
        // Bool/Int equality and negation, exclusion vector, each cloned conditions vector,
        // branch push and otherwise extension. Terms retain Rc nodes; expression trees
        // are not recursively duplicated by Term::clone.
        #[cfg(test)]
        tests::near_limit(
            self,
            tests::Phase::Switch,
            Some(invocation.kind),
            Some(state),
        );
        pay(
            self,
            8 + targets * (memory + 3 * state.conditions.len() + 40),
        )?;
        #[cfg(test)]
        tests::publication(tests::Phase::Switch);
        Ok(())
    }

    pub(in crate::proof) fn executable_box_retry_clone(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        path: &retry_frontiers::Path,
    ) -> Result<retry_frontiers::Path, String> {
        if invocation.is_some() {
            bound(self, path.len(), "retry metadata")?;
            // BTreeMap cloning owns a new entry tree, even though its keys are inline.
            pay(self, 4 + 8 * path.len())?;
        }
        Ok(path.clone())
    }
}
