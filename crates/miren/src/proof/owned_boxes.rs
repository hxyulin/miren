//! Private logical ownership for compiler-certified zero-sized Box constructors.
//! These handles do not denote numeric addresses or ordinary frame allocations.
use super::*;
use rustc_span::Symbol;
use symbolic::OwnedRegionKind;

#[derive(Clone, Copy, Debug)]
pub(super) struct BoxType<'tcx> {
    pub(super) original: Ty<'tcx>,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn unit_box_type(&self) -> Result<Ty<'tcx>, String> {
        let owned = self
            .tcx
            .lang_items()
            .owned_box()
            .ok_or("Box identity is unavailable")?;
        let constructor = self
            .tcx
            .get_diagnostic_item(Symbol::intern("box_new"))
            .filter(|id| id.krate == owned.krate)
            .ok_or("Box constructor identity is unavailable")?;
        let args = self.tcx.mk_args(&[self.tcx.types.unit.into()]);
        let signature = self
            .tcx
            .fn_sig(constructor)
            .instantiate(self.tcx, args)
            .skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs() != [self.tcx.types.unit]
        {
            return Err("Box constructor has a different original safe signature".into());
        }
        let ty::Adt(def, arguments) = signature.output().kind() else {
            return Err("Box constructor output is not its owned type".into());
        };
        if def.did() != owned || arguments.type_at(0) != self.tcx.types.unit {
            return Err("Box constructor output has a different original payload".into());
        }
        Ok(signature.output())
    }

    pub(super) fn register_unit_box(&mut self) -> Result<usize, String> {
        let original = self.unit_box_type()?;
        if let Some(index) = self
            .owned_box_types
            .iter()
            .position(|entry| entry.original == original)
        {
            return Ok(index);
        }
        if self.owned_box_types.len() >= 512 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "Box type certificate exceeds its node budget".into(),
            ));
        }
        let index = self.owned_box_types.len();
        self.owned_box_types.push(BoxType { original });
        Ok(index)
    }

    pub(super) fn validate_owned_region(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<(), String> {
        let Value::OwnedRegion {
            key,
            certificate,
            kind,
        } = value
        else {
            return Err("expected a private owned-region handle".into());
        };
        let entry = self
            .owned_box_types
            .get(*certificate)
            .ok_or("owned region lacks an issued original type certificate")?;
        if entry.original != self.unit_box_type()? {
            return Err("owned region original type certificate differs".into());
        }
        if matches!(kind, OwnedRegionKind::ConstructorPointer) {
            let region = memory
                .owned_region(*key, *certificate)
                .map_err(|detail| self.categorized_error(UnknownCategory::Semantics, detail))?;
            if region.sealed {
                return Err("constructor pointer cannot observe a sealed owner".into());
            }
            return Ok(());
        }
        if !matches!(
            memory
                .owned_region_payload(*key, *certificate)
                .map_err(|detail| self.categorized_error(UnknownCategory::Semantics, detail))?,
            Value::Unit
        ) {
            return Err("owned region does not contain its certified initialized Unit".into());
        }
        Ok(())
    }

    pub(super) fn issue_unit_box(
        &mut self,
        memory: &mut Memory,
        initialized: bool,
    ) -> Result<Value, String> {
        let certificate = self.register_unit_box()?;
        let key = self.next_owned_region;
        self.next_owned_region = key
            .checked_add(1)
            .ok_or("owned region generation overflows")?;
        memory
            .issue_owned_region(key, certificate)
            .map_err(|reason| self.categorized_error(UnknownCategory::ResourceLimit, reason))?;
        if initialized {
            memory.initialize_owned_region(key, certificate, Value::Unit)?;
            memory.seal_owned_region(key, certificate)?;
        }
        Ok(Value::OwnedRegion {
            key,
            certificate,
            kind: if initialized {
                OwnedRegionKind::Owner
            } else {
                OwnedRegionKind::ConstructorPointer
            },
        })
    }

    pub(super) fn owned_region_rekind(
        &self,
        value: &Value,
        memory: &Memory,
        expected: OwnedRegionKind,
        target: OwnedRegionKind,
    ) -> Result<Value, String> {
        self.validate_owned_region(value, memory)?;
        let Value::OwnedRegion {
            key,
            certificate,
            kind,
        } = value
        else {
            unreachable!()
        };
        if *kind != expected {
            return Err("owned region transport has a different role".into());
        }
        Ok(Value::OwnedRegion {
            key: *key,
            certificate: *certificate,
            kind: target,
        })
    }

    pub(super) fn owned_region_read(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        self.validate_owned_region(value, memory)?;
        let Value::OwnedRegion {
            key,
            certificate,
            kind:
                OwnedRegionKind::Owner
                | OwnedRegionKind::BorrowedOwner
                | OwnedRegionKind::Pointer
                | OwnedRegionKind::Shared,
        } = value
        else {
            return Err("owned region does not grant a readonly payload observation".into());
        };
        Ok(memory.owned_region_payload(*key, *certificate)?.clone())
    }

    fn current_construction<'a>(
        &'a self,
        body: &Body<'tcx>,
        value: &Value,
        memory: &Memory,
    ) -> Result<&'a owned_box_constructors::Constructor<'tcx>, String> {
        self.validate_owned_region(value, memory)?;
        let Value::OwnedRegion {
            key,
            certificate,
            kind: OwnedRegionKind::ConstructorPointer,
        } = value
        else {
            return Err("expected a private unsealed constructor pointer".into());
        };
        let id = memory
            .owned_region(*key, *certificate)?
            .construction
            .ok_or("Box constructor pointer lacks its actual transport certificate")?;
        let construction = self
            .owned_box_constructors
            .get(id)
            .ok_or("Box constructor transport certificate is unavailable")?;
        let original = construction
            .body
            .upgrade()
            .ok_or("Box constructor transport body has expired")?;
        if !std::ptr::eq(original.as_ref(), body) {
            return Err("Box constructor pointer belongs to a different actual body".into());
        }
        Ok(construction)
    }

    pub(super) fn owned_constructor_cast(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        rvalue: &Rvalue<'tcx>,
        value: &Value,
    ) -> Result<Option<Value>, String> {
        if !matches!(
            value,
            Value::OwnedRegion {
                kind: OwnedRegionKind::ConstructorPointer,
                ..
            }
        ) {
            return Ok(None);
        }
        let Rvalue::Cast(kind, operand, target) = rvalue else {
            return Err("constructor transport requires its exact original cast".into());
        };
        let (kind, target) = (*kind, *target);
        let construction = self.current_construction(body, value, &state.memory)?;
        if !matches!(operand, Operand::Copy(place)
            if place.local == construction.raw && place.projection.is_empty())
        {
            return Err("constructor cast did not use its original issued pointer local".into());
        }
        let location = if matches!(kind, CastKind::PtrToPtr) {
            construction
                .pointer_cast
                .ok_or("constructor cast is not part of its certified source")?
        } else {
            construction.seal
        };
        let statement = &body.basic_blocks[location.block].statements[location.statement_index];
        let StatementKind::Assign(assignment) = &statement.kind else {
            unreachable!()
        };
        if !std::ptr::eq(&assignment.1, rvalue)
            || (matches!(kind, CastKind::Transmute) && assignment.0.local != construction.owner)
        {
            return Err(
                "constructor phase operation is not the exact certified MIR occurrence".into(),
            );
        }
        match kind {
            CastKind::PtrToPtr
                if construction.typed.is_some()
                    && matches!(target.kind(), ty::RawPtr(inner, mutable)
                    if *inner == self.tcx.types.unit && mutable.is_mut()) =>
            {
                Ok(Some(value.clone()))
            }
            CastKind::Transmute if target == self.unit_box_type()? => {
                let Value::OwnedRegion {
                    key, certificate, ..
                } = value
                else {
                    unreachable!()
                };
                state.memory.seal_owned_region(*key, *certificate)?;
                Ok(Some(Value::OwnedRegion {
                    key: *key,
                    certificate: *certificate,
                    kind: OwnedRegionKind::Owner,
                }))
            }
            _ => Err(
                "private constructor pointer cannot be cast outside its certified protocol".into(),
            ),
        }
    }

    pub(super) fn owned_constructor_store(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        if !matches!(place.projection.as_ref(), [ProjectionElem::Deref]) {
            return Ok(false);
        }
        let value = self.local(state, place.local.as_usize())?;
        if !matches!(
            value,
            Value::OwnedRegion {
                kind: OwnedRegionKind::ConstructorPointer,
                ..
            }
        ) {
            return Ok(false);
        }
        let construction = self.current_construction(body, &value, &state.memory)?;
        if construction.typed != Some(place.local)
            || construction.elided_unit_store
            || !initialized_unit(replacement)
        {
            return Err("Box constructor payload write differs from its actual typed store".into());
        }
        let location = construction
            .store
            .ok_or("constructor write is not part of its certified source")?;
        let statement = &body.basic_blocks[location.block].statements[location.statement_index];
        if !std::ptr::eq(&statement.kind, occurrence) {
            return Err("constructor store is not the exact certified MIR occurrence".into());
        }
        let Value::OwnedRegion {
            key, certificate, ..
        } = value
        else {
            unreachable!()
        };
        state
            .memory
            .initialize_owned_region(key, certificate, Value::Unit)?;
        Ok(true)
    }

    pub(super) fn owned_box_type_value(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
        memory: &Memory,
    ) -> Result<(), String> {
        let Value::OwnedRegion {
            kind, certificate, ..
        } = value
        else {
            if matches!(value, Value::OwnedSnapshot(_)) {
                return Err("contract Box snapshot cannot become executable storage".into());
            }
            return Ok(());
        };
        self.validate_owned_region(value, memory)?;
        let original = self.owned_box_types[*certificate].original;
        let allowed = match kind {
            OwnedRegionKind::Owner => expected == original,
            OwnedRegionKind::BorrowedOwner => expected == original,
            OwnedRegionKind::Shared => matches!(expected.kind(), ty::Ref(_, inner, mutable)
                if *inner == self.tcx.types.unit && !mutable.is_mut()),
            OwnedRegionKind::Pointer => matches!(expected.kind(), ty::RawPtr(inner, mutable)
                if *inner == self.tcx.types.unit && !mutable.is_mut()),
            OwnedRegionKind::Unique => {
                let ty::Adt(def, args) = original.kind() else {
                    unreachable!()
                };
                expected
                    == def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)]
                        .ty(self.tcx, args)
                        .skip_norm_wip()
            }
            OwnedRegionKind::ConstructorPointer => {
                matches!(expected.kind(), ty::RawPtr(inner, mutable)
                if (*inner == self.tcx.types.unit || *inner == self.tcx.types.u8)
                    && mutable.is_mut())
            }
        };
        if allowed {
            Ok(())
        } else {
            Err("owned region role differs from its exact original compiler type".into())
        }
    }

    pub(super) fn owned_box_project(
        &self,
        value: &Value,
        projection: rustc_middle::mir::PlaceElem<'tcx>,
        memory: &Memory,
    ) -> Result<Option<Value>, String> {
        if !matches!(value, Value::OwnedRegion { .. }) {
            return Ok(None);
        }
        self.validate_owned_region(value, memory)?;
        let Value::OwnedRegion {
            kind, certificate, ..
        } = value
        else {
            unreachable!()
        };
        match (kind, projection) {
            (
                OwnedRegionKind::Owner | OwnedRegionKind::BorrowedOwner,
                ProjectionElem::Field(field, original),
            ) if field.as_usize() == 0 => {
                let expected = self.owned_box_types[*certificate].original;
                let ty::Adt(def, args) = expected.kind() else {
                    unreachable!()
                };
                if original
                    != def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)]
                        .ty(self.tcx, args)
                        .skip_norm_wip()
                {
                    return Err(
                        "Box field projection differs from its original declaration type".into(),
                    );
                }
                self.owned_region_rekind(value, memory, *kind, OwnedRegionKind::Unique)
                    .map(Some)
            }
            (
                OwnedRegionKind::Owner
                | OwnedRegionKind::BorrowedOwner
                | OwnedRegionKind::Pointer
                | OwnedRegionKind::Shared,
                ProjectionElem::Deref,
            ) => self.owned_region_read(value, memory).map(Some),
            _ => Err("owned region projection is outside its readonly typed protocol".into()),
        }
    }

    pub(super) fn owned_box_deref_cast(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        self.owned_box_type_value(source, value, memory)?;
        if !matches!(target.kind(), ty::RawPtr(inner, mutable)
            if *inner == self.tcx.types.unit && !mutable.is_mut())
        {
            return Err(
                "Box dereference transport only permits a readonly original Unit pointer".into(),
            );
        }
        self.owned_region_rekind(
            value,
            memory,
            OwnedRegionKind::Unique,
            OwnedRegionKind::Pointer,
        )
    }

    pub(super) fn validate_owned_raw_borrow(
        &self,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        if state.memory.owned_regions.is_empty() {
            return Ok(());
        }
        let mut root = self.local(state, place.local.as_usize())?;
        for _ in 0..16 {
            if !region_occurrences(std::slice::from_ref(&root))?.is_empty() {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "private owned region transport cannot issue a raw address".into(),
                ));
            }
            if matches!(root, Value::Reference { .. }) {
                root = self.reference_storage(&root, &state.memory, &state.conditions)?;
            } else {
                return Ok(());
            }
        }
        Err(self.categorized_error(
            UnknownCategory::ResourceLimit,
            "owned raw-borrow source exceeds the existing depth budget".into(),
        ))
    }

    pub(super) fn owned_box_shared_borrow(
        &self,
        state: &State,
        place: Place<'tcx>,
        mutable: bool,
    ) -> Result<Option<Value>, String> {
        if mutable && !state.memory.owned_regions.is_empty() {
            let root = self.local(state, place.local.as_usize())?;
            if region_occurrences(std::slice::from_ref(&root))?
                .iter()
                .any(|(_, _, role)| *role == OwnedRegionKind::BorrowedOwner)
            {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "readonly virtual Box cannot acquire mutable storage authority".into(),
                ));
            }
        }
        if !matches!(place.projection.as_ref(), [ProjectionElem::Deref]) {
            return Ok(None);
        }
        let source = self.local(state, place.local.as_usize())?;
        if !matches!(source, Value::OwnedRegion { .. }) {
            return Ok(None);
        }
        if mutable {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "logical owned Box region grants readonly Unit borrowing only".into(),
            ));
        }
        let Value::OwnedRegion { kind, .. } = &source else {
            unreachable!()
        };
        if !matches!(
            kind,
            OwnedRegionKind::Pointer
                | OwnedRegionKind::Owner
                | OwnedRegionKind::BorrowedOwner
                | OwnedRegionKind::Shared
        ) {
            return Err("owned Box borrow lacks its certified readonly dereference origin".into());
        }
        self.owned_region_rekind(&source, &state.memory, *kind, OwnedRegionKind::Shared)
            .map(Some)
    }

    pub(super) fn owned_box_drop(
        &mut self,
        original: Ty<'tcx>,
        value: &Value,
        state: &mut State,
        location: DefId,
    ) -> Result<bool, String> {
        if !matches!(value, Value::OwnedRegion { .. }) {
            return Ok(false);
        }
        self.owned_box_type_value(original, value, &state.memory)?;
        if !matches!(
            value,
            Value::OwnedRegion {
                kind: OwnedRegionKind::Owner,
                ..
            }
        ) {
            return Err("only the executable owned Box may retire its region".into());
        }
        let glue = ty::Instance::resolve_drop_glue(self.tcx, original);
        owned_box_templates::certify_unit_protocol(self.tcx, glue)?;
        let Value::OwnedRegion {
            key, certificate, ..
        } = value
        else {
            unreachable!()
        };
        state.memory.retire_owned_region(*key, *certificate)?;
        self.record_model(
            location,
            "complete selected Unit Box DropGlue/Global zero-size certificate; region retired",
        );
        Ok(true)
    }

    pub(super) fn owned_box_return(&self, value: &Value, memory: &Memory) -> Result<(), String> {
        self.validate_owned_region(value, memory)?;
        if !matches!(
            value,
            Value::OwnedRegion {
                kind: OwnedRegionKind::Owner | OwnedRegionKind::Shared,
                ..
            }
        ) {
            return Err(
                "private constructor or pointer role cannot escape its typed protocol".into(),
            );
        }
        Ok(())
    }

    pub(super) fn validate_borrowed_box_store(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        if state.memory.owned_regions.is_empty() {
            return Ok(());
        }
        let contains = region_occurrences(std::slice::from_ref(value))?
            .iter()
            .any(|(_, _, kind)| *kind == OwnedRegionKind::BorrowedOwner);
        if contains
            && (!matches!(
                value,
                Value::OwnedRegion {
                    kind: OwnedRegionKind::BorrowedOwner,
                    ..
                }
            ) || !place.projection.is_empty()
                || place.local.as_usize() <= body.arg_count
                || state.addresses[place.local.as_usize()].is_some())
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "readonly virtual Box storage is limited to private whole local temporaries".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn evaluate_owned_call_operand(
        &self,
        id: DefId,
        body: &Body<'tcx>,
        state: &mut State,
        instance: ty::Instance<'tcx>,
        argument_count: usize,
        operand: &Operand<'tcx>,
    ) -> Result<Value, String> {
        if !state.memory.owned_regions.is_empty()
            && matches!(operand, Operand::Copy(_))
            && argument_count == 1
            && pure_comparison_templates::owned_definition_key(instance.def_id())
                == "DefId(core::mem::drop)"
        {
            let value = self.operand(id, body, state, operand)?;
            if matches!(
                value,
                Value::OwnedRegion {
                    kind: OwnedRegionKind::Owner,
                    ..
                }
            ) {
                self.owned_box_type_value(self.unit_box_type()?, &value, &state.memory)?;
                owned_box_templates::certify_unit_protocol(self.tcx, instance)?;
                return Ok(value);
            }
        }
        self.evaluate_operand(id, body, state, operand)
    }

    pub(super) fn validate_owned_call_arguments(
        &self,
        values: &[Value],
        memory: &Memory,
    ) -> Result<(), String> {
        if memory.owned_regions.is_empty() {
            return Ok(());
        }
        if region_occurrences(values)?
            .iter()
            .any(|(_, _, kind)| *kind == OwnedRegionKind::BorrowedOwner)
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "readonly virtual Box cannot become a by-value call owner".into(),
            ));
        }
        let owners = owner_occurrences(values)?;
        for owner in &owners {
            if owners.iter().filter(|other| *other == owner).count() != 1 {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "call duplicates an executable owned Box owner".into(),
                ));
            }
            memory.owned_region_payload(owner.0, owner.1)?;
        }
        Ok(())
    }

    pub(super) fn owned_box_call(
        &mut self,
        body: &std::rc::Rc<Body<'tcx>>,
        block: rustc_middle::mir::BasicBlock,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &mut State,
    ) -> Result<Option<Value>, String> {
        let constructor = self.tcx.get_diagnostic_item(Symbol::intern("box_new"));
        if constructor == Some(instance.def_id()) {
            if instance.args.type_at(0) != self.tcx.types.unit {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "owned Box constructor currently requires the exact Unit payload".into(),
                ));
            }
            if !matches!(values, [value] if initialized_unit(value)) {
                return Err("Box constructor payload differs from initialized Unit".into());
            }
            owned_box_templates::certify_unit_protocol(self.tcx, instance)?;
            let result = self.issue_unit_box(&mut state.memory, true)?;
            self.record_model(
                instance.def_id(),
                "complete selected Box/Global Unit zero-branch certificate; logical owned region",
            );
            return Ok(Some(result));
        }
        if pure_comparison_templates::owned_definition_key(instance.def_id())
            == "DefId(alloc::boxed::box_new_uninit)"
        {
            let original = self.unit_box_type()?;
            let construction =
                owned_box_constructors::certify_inlined(self.tcx, body, block, original)?;
            if self.owned_box_constructors.len() >= 512 {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "Box constructor transport exceeds its certificate budget".into(),
                ));
            }
            let elided = construction.elided_unit_store;
            let id = self.owned_box_constructors.len();
            self.owned_box_constructors.push(construction);
            let result = self.issue_unit_box(&mut state.memory, false)?;
            let Value::OwnedRegion {
                key, certificate, ..
            } = &result
            else {
                unreachable!()
            };
            state
                .memory
                .owned_region_mut(*key, *certificate)?
                .construction = Some(id);
            if elided {
                state
                    .memory
                    .initialize_owned_region(*key, *certificate, Value::Unit)?;
            }
            self.record_model(
                instance.def_id(),
                "complete inlined Unit Box issue/store/seal certificate; no numeric pointer rights",
            );
            return Ok(Some(result));
        }
        if pure_comparison_templates::owned_definition_key(instance.def_id())
            == "DefId(core::mem::drop)"
            && matches!(
                values,
                [Value::OwnedRegion {
                    kind: OwnedRegionKind::Owner,
                    ..
                }]
            )
        {
            let [owner] = values else { unreachable!() };
            self.validate_owned_region(owner, &state.memory)?;
            owned_box_templates::certify_unit_protocol(self.tcx, instance)?;
            let Value::OwnedRegion {
                key, certificate, ..
            } = owner
            else {
                unreachable!()
            };
            state.memory.retire_owned_region(*key, *certificate)?;
            self.record_model(
                instance.def_id(),
                "complete selected owned Unit drop certificate; same logical region retired",
            );
            return Ok(Some(Value::Unit));
        }
        Ok(None)
    }
}

fn initialized_unit(value: &Value) -> bool {
    matches!(value, Value::Unit) || matches!(value, Value::Tuple(fields) if fields.is_empty())
}

pub(super) fn owner_occurrences(values: &[Value]) -> Result<Vec<(u64, usize)>, String> {
    Ok(region_occurrences(values)?
        .into_iter()
        .filter_map(|(key, certificate, kind)| {
            (kind == OwnedRegionKind::Owner).then_some((key, certificate))
        })
        .collect())
}

pub(super) fn region_occurrences(
    values: &[Value],
) -> Result<Vec<(u64, usize, OwnedRegionKind)>, String> {
    if values.len() > 512 {
        return Err("owned occurrence input exceeds the existing node budget".into());
    }
    let mut pending: Vec<(&Value, usize)> = values.iter().map(|value| (value, 0)).collect();
    let mut nodes = 0_usize;
    let mut owners = Vec::new();
    while let Some((value, depth)) = pending.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or("owned occurrence budget overflows")?;
        if nodes > 512 || depth >= 16 {
            return Err("owned occurrence traversal exceeds the existing node/depth budget".into());
        }
        let children = match value {
            Value::Tuple(fields) => fields.len(),
            Value::Elements(fields) => fields.len(),
            Value::Adt { fields, .. } => fields.len(),
            Value::Enum { variants, .. } => variants.len(),
            Value::MaybeUninit {
                payload: Some(_), ..
            } => 1,
            _ => 0,
        };
        if nodes.saturating_add(pending.len()).saturating_add(children) > 512 {
            return Err("owned occurrence traversal exceeds the existing node budget".into());
        }
        match value {
            Value::MutableU16 { .. } => {}
            Value::OwnedRegion {
                key,
                certificate,
                kind,
            } => owners.push((*key, *certificate, *kind)),
            Value::Tuple(fields) => pending.extend(fields.iter().map(|field| (field, depth + 1))),
            Value::Elements(fields) => {
                pending.extend(fields.iter().map(|field| (field, depth + 1)))
            }
            Value::Adt { fields, .. } => {
                pending.extend(fields.iter().map(|(_, field)| (field, depth + 1)))
            }
            Value::Enum { variants, .. } => {
                pending.extend(variants.iter().map(|field| (field, depth + 1)))
            }
            Value::MaybeUninit {
                payload: Some(payload),
                ..
            } => pending.push((payload, depth + 1)),
            Value::OwnedSnapshot(_)
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
            | Value::Unit => {}
        }
    }
    Ok(owners)
}

impl Engine<'_> {
    pub(super) fn validate_owned_exit(
        &self,
        memory: &Memory,
        initial_regions: usize,
        arguments: &[(u64, usize)],
        returned: &Value,
    ) -> Result<(), String> {
        if memory.owned_regions.is_empty() {
            return Ok(());
        }
        let returned = owner_occurrences(std::slice::from_ref(returned))?;
        for owner in &returned {
            if returned.iter().filter(|other| *other == owner).count() != 1 {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "return duplicates an executable owned-region owner".into(),
                ));
            }
            memory.owned_region_payload(owner.0, owner.1)?;
        }
        let mut obligations = arguments.to_vec();
        for region in memory
            .owned_regions
            .get(initial_regions..)
            .ok_or("initial owned-region inventory exceeds current memory")?
        {
            if !obligations.contains(&(region.key, region.certificate)) {
                obligations.push((region.key, region.certificate));
            }
        }
        for (key, certificate) in obligations {
            let region = memory
                .owned_regions
                .iter()
                .find(|region| region.key == key && region.certificate == certificate)
                .ok_or("owned responsibility disappeared from returned memory")?;
            if region.live && !returned.contains(&(key, certificate)) {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "live owned Box must retire or transfer its exact executable owner".into(),
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn executable_owner_occurrences_preserve_duplicates_and_exclude_borrows_and_ghosts() {
        let owner = Value::OwnedRegion {
            key: 5,
            certificate: 2,
            kind: OwnedRegionKind::Owner,
        };
        let borrowed = Value::OwnedRegion {
            key: 5,
            certificate: 2,
            kind: OwnedRegionKind::Shared,
        };
        assert_eq!(
            owner_occurrences(&[owner.clone(), owner.clone()]).unwrap(),
            vec![(5, 2), (5, 2)]
        );
        assert_eq!(
            owner_occurrences(&[borrowed, Value::OwnedSnapshot(Box::new(owner.clone()))]).unwrap(),
            Vec::<(u64, usize)>::new()
        );
        assert_eq!(
            owner_occurrences(&[Value::Tuple(vec![owner])]).unwrap(),
            vec![(5, 2)]
        );
        assert!(owner_occurrences(&vec![Value::Unit; 513]).is_err());
    }
}
