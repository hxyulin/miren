use super::storage_locations::{StorageLocation, validate_static_epoch};
use super::*;

impl<'tcx> Engine<'tcx> {
    pub(super) fn validate_tracked_value(
        &self,
        value: &Value,
        state: &State,
    ) -> Result<(), String> {
        self.validate_shared_trait_graph(value, state)?;
        self.validate_typed_reference_graph(value, state, None, &mut Vec::new())?;
        self.validate_static_initialization_graph(value, state, &mut Vec::new())
    }

    pub(super) fn validate_frame_escape(
        &self,
        value: &Value,
        state: &State,
        incoming: usize,
    ) -> Result<(), String> {
        self.return_value(value.clone(), state, incoming)?;
        self.validate_incoming_frame_escape(state, incoming)
    }

    pub(super) fn validate_incoming_frame_escape(
        &self,
        state: &State,
        incoming: usize,
    ) -> Result<(), String> {
        for value in state.memory[..incoming].iter().flatten() {
            self.validate_shared_trait_graph(value, state)?;
            Self::reference_graph(
                value,
                state,
                Some(incoming),
                &mut Vec::new(),
                false,
                Some(self),
            )?;
            self.validate_static_initialization_graph(value, state, &mut Vec::new())?;
        }
        Ok(())
    }

    pub(super) fn validate_typed_reference_graph(
        &self,
        value: &Value,
        state: &State,
        incoming: Option<usize>,
        visited: &mut Vec<usize>,
    ) -> Result<(), String> {
        Self::reference_graph(value, state, incoming, visited, true, Some(self))
    }

    #[cfg(test)]
    pub(super) fn validate_reference_graph(
        value: &Value,
        state: &State,
        incoming: Option<usize>,
        visited: &mut Vec<usize>,
    ) -> Result<(), String> {
        Self::reference_graph(value, state, incoming, visited, true, None)
    }

    #[cfg(test)]
    pub(super) fn mutable_hierarchy_test_lifetime_graph(
        value: &Value,
        state: &State,
    ) -> Result<(), String> {
        Self::reference_graph(value, state, None, &mut Vec::new(), false, None)
    }

    fn reference_graph(
        value: &Value,
        state: &State,
        incoming: Option<usize>,
        visited: &mut Vec<usize>,
        initialized: bool,
        engine: Option<&Self>,
    ) -> Result<(), String> {
        if let Value::Reference {
            allocation,
            projection,
            ..
        } = value
        {
            if initialized {
                if let Some(engine) = engine {
                    if !engine.check_drop_shared_reference(
                        *allocation,
                        projection,
                        &state.memory,
                        &state.conditions,
                    )? {
                        engine.check_memory_initialization(
                            &state.memory,
                            *allocation,
                            projection,
                        )?;
                    }
                } else {
                    state
                        .memory
                        .check_projection_initialization(*allocation, projection)?;
                }
            }
            for part in projection {
                if let symbolic::MemoryProjection::TypedIndex { index, .. } = part {
                    Self::reference_graph(index, state, incoming, visited, initialized, engine)?;
                }
            }
        }
        match value {
            Value::MutableU16 { id, role } => {
                if incoming.is_some() {
                    return Err("private mutable u16 roles cannot escape a frame".into());
                }
                if !matches!(role, symbolic::MutableU16Role::Ghost { .. }) {
                    let backing = state
                        .memory
                        .mutable_u16
                        .get(*id)
                        .ok_or("mutable u16 identity was not issued")?;
                    if backing.hierarchy.is_some() && state.memory.mutable_hierarchy != Some(*id) {
                        return Err("hierarchy graph has no current Memory namespace".into());
                    }
                    let live = backing.hierarchy.as_ref().map_or_else(
                        || super::mutable_u16_children::role_live(backing, role),
                        |hierarchy| hierarchy.role_valid(role, initialized),
                    );
                    if !live {
                        return Err(
                            "mutable u16 graph retains suspended or expired child role".into()
                        );
                    }
                    state
                        .memory
                        .check_projection_initialization(backing.allocation, &[])?;
                    if !matches!(
                        state.memory.get(backing.allocation),
                        Some(Some(Value::Unit))
                    ) {
                        return Err("mutable u16 backing is unavailable".into());
                    }
                }
                Ok(())
            }
            Value::OwnedRegion {
                key,
                certificate,
                kind,
            } => {
                if initialized || *kind != symbolic::OwnedRegionKind::Owner {
                    let region = state.memory.owned_region(*key, *certificate)?;
                    if *kind != symbolic::OwnedRegionKind::ConstructorPointer {
                        state.memory.owned_region_payload(*key, *certificate)?;
                    } else if region.sealed {
                        return Err("sealed owner cannot reuse a constructor pointer".into());
                    }
                }
                Ok(())
            }
            Value::OwnedSnapshot(_) => {
                Err("contract owned-region ghost is not an executable graph".into())
            }
            Value::ScalarSlice { length, .. } | Value::CompositeSlice { length, .. } => {
                Self::reference_graph(length, state, incoming, visited, initialized, engine)
            }
            Value::MaybeUninit { payload, .. } => {
                if let Some(payload) = payload {
                    Self::reference_graph(payload, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::Reference { allocation, .. }
            | Value::Cell { allocation }
            | Value::LocalAtomic { allocation, .. } => {
                if initialized && !matches!(value, Value::Reference { .. }) {
                    state.memory.missing_places.check(*allocation, &[])?;
                }
                if matches!(value, Value::Reference { .. })
                    && incoming.is_some_and(|limit| *allocation >= limit)
                {
                    return Err(
                        "reference to frame-owned storage cannot escape its frame".to_owned()
                    );
                }
                let stored =
                    StorageLocation::tracked(*allocation, false).read_storage(&state.memory)?;
                if !visited.contains(allocation) {
                    visited.push(*allocation);
                    Self::reference_graph(stored, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::Adt { fields, .. } => {
                for (_, value) in fields {
                    Self::reference_graph(value, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::Enum { variants, .. } => {
                for value in variants {
                    Self::reference_graph(value, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::Tuple(fields) => {
                for value in fields {
                    Self::reference_graph(value, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::Elements(fields) => {
                for value in fields {
                    Self::reference_graph(value, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::TrackedPointer { reference, .. } => {
                Self::reference_graph(reference, state, incoming, visited, initialized, engine)
            }
            Value::RawSlice { source, .. }
            | Value::SliceIterator { source, .. }
            | Value::MetadataPointer(source)
            | Value::TraitObject { source, .. }
            | Value::DebugReference { source, .. } => {
                Self::reference_graph(source, state, incoming, visited, initialized, engine)
            }
            Value::StaticSlice {
                source,
                epoch,
                elements,
                ..
            } => {
                Self::reference_graph(source, state, incoming, visited, initialized, engine)?;
                validate_static_epoch(&state.memory, *epoch)?;
                for element in elements {
                    Self::reference_graph(element, state, incoming, visited, initialized, engine)?;
                }
                Ok(())
            }
            Value::StaticView { epoch, .. } => validate_static_epoch(&state.memory, *epoch),
            Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Bytes { .. }
            | Value::Atomic { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::RawPointer { .. }
            | Value::Uninitialized
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state(memory: Vec<Option<Value>>) -> State {
        State {
            flow: activation_flow::Flow::Unarmed,
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: initialized_places::MissingPlaces::default(),
            locals: Vec::new(),
            addresses: Vec::new(),
            conditions: Vec::new(),
            memory: memory.into(),
        }
    }

    fn reference(allocation: usize, mutable: bool) -> Value {
        Value::Reference {
            allocation,
            projection: Vec::new(),
            mutable,
        }
    }

    #[test]
    fn a_frame_borrow_hidden_inside_caller_storage_cannot_escape() {
        let caller = Value::Tuple(vec![reference(1, true)]);
        let state = state(vec![
            Some(caller),
            Some(symbolic::integer(&Context::default(), 7, 16, false)),
        ]);
        let error = Engine::validate_reference_graph(
            &reference(0, false),
            &state,
            Some(1),
            &mut Vec::new(),
        )
        .unwrap_err();
        assert!(error.contains("frame-owned"));
    }

    #[test]
    fn dead_borrows_are_rejected_inside_aggregates() {
        let borrowed = Value::Tuple(vec![reference(0, true)]);
        let state = state(vec![None]);
        let error =
            Engine::validate_reference_graph(&borrowed, &state, None, &mut Vec::new()).unwrap_err();
        assert!(error.contains("dead or uninitialized"));
    }

    #[test]
    fn shared_adt_fields_keep_dead_and_frame_owned_reference_checks() {
        let value = Value::Adt {
            name: "Borrowed".into(),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![("borrow".into(), reference(0, true))].into(),
        };
        let branch = value.clone();
        let dead = state(vec![None]);
        let live = state(vec![Some(Value::Unit)]);
        for value in [&value, &branch] {
            let error =
                Engine::validate_reference_graph(value, &dead, None, &mut Vec::new()).unwrap_err();
            assert!(error.contains("dead or uninitialized"));
            let error = Engine::validate_reference_graph(value, &live, Some(0), &mut Vec::new())
                .unwrap_err();
            assert!(error.contains("frame-owned"));
            Engine::validate_reference_graph(value, &live, Some(1), &mut Vec::new()).unwrap();
        }
    }

    #[test]
    fn trait_objects_retain_dead_and_frame_owned_reference_checks() {
        let object = Value::TraitObject {
            source: Box::new(reference(0, true)),
            id: 0,
            place: false,
        };
        let dead = state(vec![None]);
        let live = state(vec![Some(Value::Unit)]);
        let error =
            Engine::validate_reference_graph(&object, &dead, None, &mut Vec::new()).unwrap_err();
        assert!(error.contains("dead or uninitialized"));
        let error =
            Engine::validate_reference_graph(&object, &live, Some(0), &mut Vec::new()).unwrap_err();
        assert!(error.contains("frame-owned"));
        Engine::validate_reference_graph(&object, &live, Some(1), &mut Vec::new()).unwrap();
        assert!(object.contains_mutable());
    }

    #[test]
    fn dead_owned_atomic_backing_is_rejected_inside_aggregates() {
        let atomic = Value::Tuple(vec![Value::LocalAtomic {
            allocation: 0,
            bits: 8,
            signed: false,
        }]);
        let state = state(vec![None]);
        let error =
            Engine::validate_reference_graph(&atomic, &state, None, &mut Vec::new()).unwrap_err();
        assert!(error.contains("dead or uninitialized"));
    }

    #[test]
    fn tracked_pointer_addresses_keep_dead_and_frame_owned_reference_evidence() {
        let context = Context::default();
        let pointer = Value::TrackedPointer {
            reference: Box::new(reference(0, false)),
            address: context.bit_vector(1, 64).unwrap(),
            bits: 64,
        };
        let dead = state(vec![None]);
        assert!(Engine::validate_reference_graph(&pointer, &dead, None, &mut Vec::new()).is_err());
        let live = state(vec![Some(Value::Unit)]);
        Engine::validate_reference_graph(&pointer, &live, None, &mut Vec::new()).unwrap();
        let error = Engine::validate_reference_graph(&pointer, &live, Some(0), &mut Vec::new())
            .unwrap_err();
        assert!(error.contains("frame-owned"));
    }

    #[test]
    fn nonowning_heap_handles_remain_live_checked_in_lifetime_only_escape_scans() {
        let mut state = state(vec![]);
        state.memory.issue_owned_region(7, 3).unwrap();
        state
            .memory
            .initialize_owned_region(7, 3, Value::Unit)
            .unwrap();
        state.memory.seal_owned_region(7, 3).unwrap();
        for kind in [
            symbolic::OwnedRegionKind::Shared,
            symbolic::OwnedRegionKind::BorrowedOwner,
            symbolic::OwnedRegionKind::Pointer,
        ] {
            let borrowed = Value::OwnedRegion {
                key: 7,
                certificate: 3,
                kind,
            };
            Engine::reference_graph(&borrowed, &state, Some(0), &mut Vec::new(), false, None)
                .unwrap();
        }
        state.memory.retire_owned_region(7, 3).unwrap();
        for kind in [
            symbolic::OwnedRegionKind::Shared,
            symbolic::OwnedRegionKind::BorrowedOwner,
            symbolic::OwnedRegionKind::Pointer,
        ] {
            let borrowed = Value::OwnedRegion {
                key: 7,
                certificate: 3,
                kind,
            };
            assert!(
                Engine::reference_graph(&borrowed, &state, Some(0), &mut Vec::new(), false, None)
                    .is_err()
            );
        }
        let consumed_owner = Value::OwnedRegion {
            key: 7,
            certificate: 3,
            kind: symbolic::OwnedRegionKind::Owner,
        };
        Engine::reference_graph(
            &consumed_owner,
            &state,
            Some(0),
            &mut Vec::new(),
            false,
            None,
        )
        .unwrap();
        assert!(
            Engine::validate_reference_graph(&consumed_owner, &state, None, &mut Vec::new())
                .is_err()
        );
    }

    #[test]
    fn nested_incoming_references_keep_their_storage_identity() {
        let borrowed = Value::Tuple(vec![reference(0, true), reference(1, false)]);
        let state = state(vec![
            Some(symbolic::integer(&Context::default(), 7, 16, false)),
            Some(Value::Tuple(vec![reference(0, false)])),
        ]);
        Engine::validate_reference_graph(&borrowed, &state, Some(2), &mut Vec::new()).unwrap();
    }

    #[test]
    fn typed_indices_retain_owner_lifetime_and_reject_hidden_index_borrows() {
        let context = Context::default();
        let projected = Value::Reference {
            allocation: 0,
            projection: vec![symbolic::MemoryProjection::TypedIndex {
                index: Box::new(symbolic::integer(&context, 1, 64, false)),
                certificate: 0,
            }],
            mutable: false,
        };
        let live = state(vec![Some(Value::Unit)]);
        Engine::validate_reference_graph(&projected, &live, Some(1), &mut Vec::new()).unwrap();
        let dead = state(vec![None]);
        assert!(
            Engine::validate_reference_graph(&projected, &dead, None, &mut Vec::new())
                .unwrap_err()
                .contains("dead or uninitialized")
        );
        assert!(
            Engine::validate_reference_graph(&projected, &live, Some(0), &mut Vec::new())
                .unwrap_err()
                .contains("frame-owned")
        );
        let malformed = Value::Reference {
            allocation: 0,
            projection: vec![symbolic::MemoryProjection::TypedIndex {
                index: Box::new(reference(1, false)),
                certificate: 0,
            }],
            mutable: false,
        };
        let dead_index = state(vec![Some(Value::Unit), None]);
        assert!(
            Engine::validate_reference_graph(&malformed, &dead_index, None, &mut Vec::new())
                .unwrap_err()
                .contains("dead or uninitialized")
        );
    }
}
