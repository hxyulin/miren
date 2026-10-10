//! Direct incoming mutable u16 roots. Metadata and ghosts have no data-write authority.
use super::*;
use symbolic::MutableU16Role;

#[derive(Clone, Debug)]
pub(super) struct Backing {
    pub(super) allocation: usize,
    pub(super) length: Value,
    pub(super) data: Term,
    pub(super) generation: u64,
    pub(super) phase: super::mutable_u16_children::Phase,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_u16_type(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut() && matches!(inner.kind(), ty::Slice(element)
                if *element == self.tcx.types.u16))
    }

    fn mutable_u16_shared_type(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, inner, mutability)
            if !mutability.is_mut() && matches!(inner.kind(), ty::Slice(element)
                if *element == self.tcx.types.u16))
    }

    fn mutable_u16_error(&self, detail: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, detail.into())
    }

    pub(super) fn mutable_u16_input(
        &mut self,
        memory: &mut Memory,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        if memory.storage_slots().saturating_add(2) > MAX_INPUT_VALUES
            || self.input_values.saturating_add(2) > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 root exceeds existing storage budget".into(),
            ));
        }
        let layout = self.static_layout(self.tcx.types.u16)?;
        if layout.size.bytes() != 2 {
            return Err("mutable u16 root requires exact two-byte compiler layout".into());
        }
        self.input_values += 2;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max = ((1_u128 << (bits - 1)) - 1) / 2;
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let data = self.fresh(Sort::Array(
            Box::new(Sort::BitVec(bits)),
            Box::new(Sort::BitVec(16)),
        ));
        let allocation = memory.len();
        memory.push(Some(Value::Unit));
        let id = memory.mutable_u16.len();
        std::rc::Rc::make_mut(&mut memory.mutable_u16).push(Backing {
            allocation,
            length: Value::Int {
                expression: length,
                bits,
                signed: false,
            },
            data,
            generation: 0,
            phase: super::mutable_u16_children::Phase::Idle,
        });
        Ok(Value::MutableU16 {
            id,
            role: MutableU16Role::Root,
        })
    }

    pub(super) fn mutable_u16_backing<'a>(
        &self,
        id: usize,
        memory: &'a Memory,
    ) -> Result<&'a Backing, String> {
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("mutable u16 root identity was not issued")?;
        memory.check_projection_initialization(backing.allocation, &[])?;
        if !matches!(memory.get(backing.allocation), Some(Some(Value::Unit))) {
            return Err(self.mutable_u16_error("mutable u16 root backing is unavailable"));
        }
        self.mutable_u16_terms(&backing.length, &backing.data)?;
        Ok(backing)
    }

    fn mutable_u16_terms(&self, length: &Value, data: &Term) -> Result<(), String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (term, width, signed) = length.integer()?;
        if width != bits
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
            || data.sort() != &Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(16)))
            || !data.belongs_to(&self.terms)
        {
            return Err("mutable u16 backing has a different width, sort or context".into());
        }
        Ok(())
    }

    pub(super) fn mutable_u16_length(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        let Value::MutableU16 { id, role } = value else {
            return Err("expected a private mutable u16 role".into());
        };
        match role {
            MutableU16Role::Root
            | MutableU16Role::Metadata { .. }
            | MutableU16Role::Child { .. }
            | MutableU16Role::ChildMetadata { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                Ok(self.mutable_u16_backing(*id, memory)?.length.clone())
            }
            MutableU16Role::Ghost { length, data } => {
                self.mutable_u16_terms(length, data)?;
                Ok((**length).clone())
            }
        }
    }

    pub(super) fn mutable_u16_snapshot(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        let Value::MutableU16 { id, role } = value else {
            return Err("expected mutable u16 snapshot source".into());
        };
        match role {
            MutableU16Role::Root | MutableU16Role::Child { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                let backing = self.mutable_u16_backing(*id, memory)?;
                Ok(Value::MutableU16 {
                    id: *id,
                    role: MutableU16Role::Ghost {
                        length: Box::new(backing.length.clone()),
                        data: backing.data.clone(),
                    },
                })
            }
            MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                self.mutable_u16_backing(*id, memory)?;
                Ok(value.clone())
            }
            MutableU16Role::Ghost { length, data } => {
                self.mutable_u16_terms(length, data)?;
                Ok(value.clone())
            }
        }
    }

    pub(super) fn mutable_u16_read(
        &self,
        body: Option<&Body<'tcx>>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        let value = self.raw_local(state, place.local.as_usize())?;
        let Value::MutableU16 { id, role } = value else {
            return Ok(None);
        };
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        if place.projection.is_empty() {
            return Ok(Some(Value::MutableU16 { id, role }));
        }
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. }) {
            return Err(self.mutable_u16_error("mutable u16 metadata cannot observe data"));
        }
        let [ProjectionElem::Deref, ProjectionElem::Index(index)] = place.projection.as_ref()
        else {
            return Err(self.mutable_u16_error("mutable u16 root needs direct element observation"));
        };
        let body = body.ok_or("mutable u16 data observation needs original compiler Body")?;
        if !self.mutable_u16_type(body.local_decls[place.local].ty)
            || body.local_decls[*index].ty != self.tcx.types.usize
            || place.ty(&body.local_decls, self.tcx).ty != self.tcx.types.u16
        {
            return Err("mutable u16 element differs from original compiler type".into());
        }
        let index = self.local(state, index.as_usize())?;
        self.mutable_u16_index(&index, &backing.length, &state.conditions)?;
        Ok(Some(Value::Int {
            expression: self.terms.apply(
                Op::Select,
                &[backing.data.clone(), index.integer()?.0.clone()],
            )?,
            bits: 16,
            signed: false,
        }))
    }

    fn mutable_u16_index(
        &self,
        index: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let (term, bits, signed) = index.integer()?;
        if bits != u32::from(self.tcx.sess.target.pointer_width)
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("mutable u16 index requires original target usize context".into());
        }
        let in_bounds = symbolic::binary(&self.terms, "lt", index.clone(), length.clone())?;
        if self.feasible(
            &[
                conditions.to_vec(),
                vec![symbolic::not(&in_bounds.boolean()?)],
            ]
            .concat(),
        )? {
            return Err(self.mutable_u16_error("mutable u16 index bounds are not established"));
        }
        Ok(())
    }

    pub(super) fn mutable_u16_store(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
    ) -> Result<bool, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(false);
        }
        let Ok(root) = self.raw_local(state, place.local.as_usize()) else {
            return Ok(false);
        };
        let Value::MutableU16 { id, role } = root else {
            return Ok(false);
        };
        if place.projection.is_empty() {
            return if matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. }) {
                Err(self.mutable_u16_error("mutable u16 root assignment transport is unsupported"))
            } else {
                Ok(false)
            };
        }
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. }) {
            return Err(self.mutable_u16_error("mutable u16 metadata has no write authority"));
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        let [ProjectionElem::Deref, ProjectionElem::Index(index)] = place.projection.as_ref()
        else {
            return Err(self.mutable_u16_error("mutable u16 store requires direct whole element"));
        };
        if !self.mutable_u16_type(body.local_decls[place.local].ty)
            || body.local_decls[*index].ty != self.tcx.types.usize
            || place.ty(&body.local_decls, self.tcx).ty != self.tcx.types.u16
        {
            return Err("mutable u16 store differs from original compiler type".into());
        }
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let index = self.local(state, index.as_usize())?;
        self.mutable_u16_index(&index, &backing.length, &state.conditions)?;
        let (term, bits, signed) = replacement.integer()?;
        if bits != 16 || signed || term.sort() != &Sort::BitVec(16) || !term.belongs_to(&self.terms)
        {
            return Err("mutable u16 replacement requires unsigned BV16 in current context".into());
        }
        let data = self.terms.apply(
            Op::Store,
            &[
                backing.data.clone(),
                index.integer()?.0.clone(),
                term.clone(),
            ],
        )?;
        std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id].data = data;
        Ok(true)
    }

    pub(super) fn mutable_u16_metadata(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        let root = self.raw_local(state, place.local.as_usize())?;
        let Value::MutableU16 { id, role } = root else {
            return Ok(None);
        };
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. })
            || place.projection.as_ref() != [ProjectionElem::Deref]
            || !self.mutable_u16_type(body.local_decls[place.local].ty)
        {
            return Err(self.mutable_u16_error("mutable u16 metadata needs original direct root"));
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        self.mutable_u16_backing(id, &state.memory)?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        Ok(Some(Value::MutableU16 {
            id,
            role: match role {
                MutableU16Role::Child { generation } => {
                    MutableU16Role::ChildMetadata { generation }
                }
                MutableU16Role::Root => MutableU16Role::Metadata {
                    generation: self.mutable_u16_backing(id, &state.memory)?.generation,
                },
                MutableU16Role::Metadata { .. }
                | MutableU16Role::ChildMetadata { .. }
                | MutableU16Role::Ghost { .. } => {
                    return Err("mutable u16 metadata source has no data authority".into());
                }
            },
        }))
    }
    pub(super) fn mutable_u16_store_role(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(());
        }
        if self.mutable_u16_contains(value, &state.memory)?
            && !matches!(value, Value::MutableU16 { .. })
        {
            return Err(self.mutable_u16_error("mutable u16 roles cannot enter aggregate storage"));
        }
        if let Value::MutableU16 { id, role } = value {
            if matches!(role, MutableU16Role::Child { .. }) {
                return self.mutable_u16_staging_store(body, state, place, *id, role);
            }
            if !matches!(
                role,
                MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. }
            ) || !place.projection.is_empty()
                || place.local.as_usize() <= body.arg_count
                || state.addresses[place.local.as_usize()].is_some()
            {
                return Err(
                    self.mutable_u16_error("mutable u16 roles need private metadata temporary")
                );
            }
            let original = body.local_decls[place.local].ty;
            let inner = match original.kind() {
                ty::Ref(_, inner, mutability) if !mutability.is_mut() => *inner,
                ty::RawPtr(inner, mutability) if !mutability.is_mut() => *inner,
                _ => return Err("mutable u16 metadata destination has a different type".into()),
            };
            if !matches!(inner.kind(), ty::Slice(element) if *element == self.tcx.types.u16) {
                return Err("mutable u16 metadata destination needs original u16 slice".into());
            }
            self.mutable_u16_backing(*id, &state.memory)?;
            self.mutable_u16_role_live(*id, role, &state.memory)?;
        }
        Ok(())
    }

    pub(super) fn mutable_u16_call_allowed(
        &self,
        body: &Body<'tcx>,
        state: &State,
        instance: ty::Instance<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
    ) -> Result<(), String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(());
        }
        for arg in args {
            if let Operand::Copy(place) | Operand::Move(place) = arg.node {
                let value = self.read_place(state, place, Some(body))?;
                if self.mutable_u16_contains(&value, &state.memory)?
                    && !matches!(value, Value::MutableU16 { .. })
                {
                    return Err(self.mutable_u16_error(
                        "mutable u16 roles cannot enter ordinary aggregate calls",
                    ));
                }
                if let Value::MutableU16 { id, role } = value {
                    self.check_local_initialization(state, place.local.as_usize(), &[])?;
                    self.mutable_u16_backing(id, &state.memory)?;
                    if args.len() != 1
                        || !place.projection.is_empty()
                        || !matches!(
                            role,
                            MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. }
                        )
                        || self.tcx.lang_items().get(LangItem::SliceLen) != Some(instance.def_id())
                        || !self.mutable_u16_shared_type(body.local_decls[place.local].ty)
                    {
                        return Err(self.mutable_u16_error(
                            "mutable u16 roles require selected metadata-only operation",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn certify_mutable_u16_len(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        let core = self
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("core identity is unavailable")?
            .krate;
        if self.tcx.lang_items().get(LangItem::SliceLen) != Some(instance.def_id())
            || instance.def_id().krate != core
        {
            return Err("mutable u16 length requires actual core SliceLen identity".into());
        }
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.output() != self.tcx.types.usize
            || signature.inputs().len() != 1
            || !matches!(signature.inputs()[0].kind(), ty::Ref(_, inner, mutability)
                if !mutability.is_mut() && matches!(inner.kind(), ty::Slice(element)
                    if *element == self.tcx.types.u16))
        {
            return Err("mutable u16 SliceLen has a different original signature".into());
        }
        let body = self.instantiated_body(instance)?;
        if body.arg_count != 1
            || body.local_decls.len() != 2
            || body.basic_blocks.len() != 1
            || body.local_decls[rustc_middle::mir::RETURN_PLACE].ty != self.tcx.types.usize
            || !matches!(body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty.kind(),
                ty::Ref(_, inner, mutability) if !mutability.is_mut()
                    && matches!(inner.kind(), ty::Slice(element) if *element == self.tcx.types.u16))
        {
            return Err("mutable u16 SliceLen body has a different original schema".into());
        }
        let block = &body.basic_blocks[START_BLOCK];
        let [statement] = block.statements.as_slice() else {
            return Err("mutable u16 SliceLen body has extra effects".into());
        };
        if block.is_cleanup || !matches!(block.terminator().kind, TerminatorKind::Return) {
            return Err("mutable u16 SliceLen body does not return its metadata directly".into());
        }
        let StatementKind::Assign(assignment) = &statement.kind else {
            return Err("mutable u16 SliceLen body has a different statement".into());
        };
        let (destination, value) = assignment.as_ref();
        if destination.local != rustc_middle::mir::RETURN_PLACE
            || !destination.projection.is_empty()
            || !matches!(value, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(source))
                if source.local.as_usize() == 1 && source.projection.is_empty())
        {
            return Err("mutable u16 SliceLen does not return the exact receiver metadata".into());
        }
        Ok(())
    }
    pub(super) fn mutable_u16_contains(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<bool, String> {
        let mut pending = vec![(value, 0_usize)];
        let mut visited = Vec::new();
        let mut nodes = 0_usize;
        while let Some((value, depth)) = pending.pop() {
            nodes += 1;
            if nodes > 512 || depth >= 16 || nodes + pending.len() > 512 {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable u16 role traversal exceeds existing node/depth budget".into(),
                ));
            }
            let children = match value {
                Value::Tuple(fields) => fields.len(),
                Value::Elements(fields) => fields.len(),
                Value::Adt { fields, .. } => fields.len(),
                Value::Enum { variants, .. } => variants.len().saturating_add(1),
                Value::StaticSlice { elements, .. } => elements.len().saturating_add(1),
                Value::SliceIterator { unchecked, .. } => unchecked.len().saturating_add(3),
                Value::RawSlice { .. } => 2,
                _ => 1,
            };
            if nodes.saturating_add(pending.len()).saturating_add(children) > 512 {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable u16 role traversal exceeds existing node budget".into(),
                ));
            }
            match value {
                Value::MutableU16 { .. } => return Ok(true),
                Value::Tuple(fields) => pending.extend(fields.iter().map(|v| (v, depth + 1))),
                Value::Elements(fields) => pending.extend(fields.iter().map(|v| (v, depth + 1))),
                Value::Adt { fields, .. } => {
                    pending.extend(fields.iter().map(|(_, v)| (v, depth + 1)))
                }
                Value::Enum {
                    discriminant,
                    variants,
                    ..
                } => {
                    pending.push((discriminant, depth + 1));
                    pending.extend(variants.iter().map(|v| (v, depth + 1)));
                }
                Value::Reference {
                    allocation,
                    projection,
                    ..
                } => {
                    memory.check_projection_initialization(*allocation, projection)?;
                    if !visited.contains(allocation) {
                        visited.push(*allocation);
                        if let Some(Some(value)) = memory.get(*allocation) {
                            pending.push((value, depth + 1));
                        } else {
                            return Err("mutable u16 role traversal found dead reference".into());
                        }
                    }
                }
                Value::Cell { allocation } | Value::LocalAtomic { allocation, .. } => {
                    memory.check_projection_initialization(*allocation, &[])?;
                    if !visited.contains(allocation) {
                        visited.push(*allocation);
                        if let Some(Some(value)) = memory.get(*allocation) {
                            pending.push((value, depth + 1));
                        } else {
                            return Err("mutable u16 role traversal found dead storage".into());
                        }
                    }
                }
                Value::StaticSlice {
                    source, elements, ..
                } => {
                    pending.push((source, depth + 1));
                    pending.extend(elements.iter().map(|v| (v, depth + 1)));
                }
                Value::SliceIterator {
                    source,
                    front,
                    back,
                    unchecked,
                    ..
                } => {
                    pending.extend([
                        (source.as_ref(), depth + 1),
                        (front.as_ref(), depth + 1),
                        (back.as_ref(), depth + 1),
                    ]);
                    pending.extend(unchecked.iter().map(|v| (v, depth + 1)));
                }
                Value::RawSlice { source, length } => {
                    pending.extend([(source.as_ref(), depth + 1), (length.as_ref(), depth + 1)]);
                }
                Value::OwnedSnapshot(source)
                | Value::MetadataPointer(source)
                | Value::TraitObject { source, .. }
                | Value::DebugReference { source, .. }
                | Value::TrackedPointer {
                    reference: source, ..
                } => pending.push((source, depth + 1)),
                Value::MaybeUninit { payload, .. } => {
                    if let Some(payload) = payload {
                        pending.push((payload, depth + 1));
                    }
                }
                Value::OwnedRegion { .. }
                | Value::Input(_)
                | Value::Bool(_)
                | Value::Int { .. }
                | Value::Float { .. }
                | Value::Bytes { .. }
                | Value::CompositeSlice { .. }
                | Value::ScalarSlice { .. }
                | Value::Uninitialized
                | Value::StaticView { .. }
                | Value::RawPointer { .. }
                | Value::Atomic { .. }
                | Value::StaticText
                | Value::FormatArguments
                | Value::FunctionPointer { .. }
                | Value::Function
                | Value::Unit => {}
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn compiler_metadata_roles_and_branch_backing_preserve_source_and_ghost_identity() {
        struct Check {
            checked: bool,
        }
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                let limits = miren::AnalysisLimits::default();
                let all_failures = false;
                let induction = false;
                let startup = false;
                let isolated_startup = false;
                let async_entry = false;
                let mut engine = Engine {
                    tcx,
                    terms: Context::default(),
                    next_symbol: std::cell::Cell::new(0),
                    float_encodings: BTreeMap::new(),
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
                    config: config.clone(),
                    all_failures,
                    induction,
                    startup,
                    isolated_startup,
                    limits,
                    resolved_contracts: BTreeMap::new(),
                    solver: std::cell::RefCell::new(Solver::with_limits(limits)),
                    mutable_u16_frames: Default::default(),
                    mutable_u16_staging: Default::default(),
                    coroutine_places: Default::default(),
                    owned_box_types: Vec::new(),
                    next_owned_region: 0,
                    owned_box_constructors: Vec::new(),
                    bodies: std::cell::RefCell::new(std::collections::HashMap::new()),
                    call_signatures: std::cell::RefCell::new(std::collections::HashMap::new()),
                    proof: Proof {
                        status: ProofStatus::Proved,
                        async_entry,
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
                let len = tcx.lang_items().get(LangItem::SliceLen).unwrap();
                let args = tcx.mk_args(&[tcx.types.u16.into()]);
                let instance = engine.resolve_function_item(len, args).unwrap();
                engine.certify_mutable_u16_len(instance).unwrap();
                let original = engine.instantiated_body(instance).unwrap();
                let mut wrong = (*original).clone();
                let StatementKind::Assign(assignment) =
                    &mut wrong.basic_blocks.as_mut()[START_BLOCK].statements[0].kind
                else {
                    panic!("assignment")
                };
                assignment.1 = Rvalue::Use(
                    Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1))),
                    rustc_middle::mir::WithRetag::No,
                );
                engine
                    .bodies
                    .borrow_mut()
                    .insert(instance, std::rc::Rc::new(wrong));
                assert!(engine.certify_mutable_u16_len(instance).is_err());
                engine.bodies.borrow_mut().insert(instance, original);
                engine.certify_mutable_u16_len(instance).unwrap();
                let mut memory = Memory::default();
                let mut conditions = Vec::new();
                let root = engine
                    .mutable_u16_input(&mut memory, &mut conditions)
                    .unwrap();
                let ghost = engine.mutable_u16_snapshot(&root, &memory).unwrap();
                let Value::MutableU16 { id, .. } = root else {
                    panic!("root")
                };
                let old_data = memory.mutable_u16[id].data.clone();
                let probe = tcx
                    .hir_body_owners()
                    .find(|id| tcx.item_name(id.to_def_id()).as_str() == "probe")
                    .unwrap();
                let probe_instance = engine
                    .resolve_function_item(probe.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let body = engine.instantiated_body(probe_instance).unwrap();
                let bits = u32::from(tcx.sess.target.pointer_width);
                let index = symbolic::integer(&engine.terms, 1, bits, false);
                conditions.push(
                    symbolic::binary(
                        &engine.terms,
                        "lt",
                        index.clone(),
                        memory.mutable_u16[id].length.clone(),
                    )
                    .unwrap()
                    .boolean()
                    .unwrap(),
                );
                let mut state = State {
                    locals: vec![None; body.local_decls.len()],
                    addresses: vec![None; body.local_decls.len()],
                    conditions,
                    memory,
                    missing_places: Default::default(),
                };
                state.locals[1] = Some(root.clone());
                state.locals[2] = Some(index);
                state.locals[3] = Some(symbolic::integer(&engine.terms, 41, 16, false));
                let place = Place {
                    local: rustc_middle::mir::Local::from_usize(1),
                    projection: tcx.mk_place_elems(&[
                        ProjectionElem::Deref,
                        ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                    ]),
                };
                engine.check_mutable_u16_child_roles(&body, &state);
                let original_state = state.clone();
                let word = state.locals[3].clone().unwrap();
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &word)
                        .unwrap()
                );
                assert_eq!(original_state.memory.mutable_u16[id].data, old_data);
                assert_ne!(state.memory.mutable_u16[id].data, old_data);
                let Value::MutableU16 {
                    role: MutableU16Role::Ghost { data, .. },
                    ..
                } = ghost
                else {
                    panic!("ghost")
                };
                assert_eq!(data, old_data);
                let returned =
                    original_state.continuation(state.conditions.clone(), state.memory.clone());
                assert_eq!(
                    returned.memory.mutable_u16[id].data,
                    state.memory.mutable_u16[id].data
                );
                assert_ne!(
                    returned.memory.mutable_u16[id].data,
                    original_state.memory.mutable_u16[id].data
                );
                assert!(
                    engine
                        .mutable_u16_read(Some(&body), &returned, place)
                        .unwrap()
                        .is_some()
                );
                let mut dead = returned.clone();
                let allocation = dead.memory.mutable_u16[id].allocation;
                dead.memory[allocation] = None;
                assert!(engine.mutable_u16_read(Some(&body), &dead, place).is_err());
                let mut consumed = returned.clone();
                consumed.missing_places.consume(1, Vec::new()).unwrap();
                assert!(
                    engine
                        .mutable_u16_read(Some(&body), &consumed, place)
                        .is_err()
                );
                let wrong = Value::Int {
                    expression: engine.terms.bit_vector(1, 16).unwrap(),
                    bits: 16,
                    signed: true,
                };
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &wrong)
                        .is_err()
                );
                let foreign = Context::default();
                let wrong = Value::Int {
                    expression: foreign.bit_vector(1, 16).unwrap(),
                    bits: 16,
                    signed: false,
                };
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &wrong)
                        .is_err()
                );
                let metadata = Value::MutableU16 {
                    id,
                    role: MutableU16Role::Metadata { generation: 0 },
                };
                assert!(
                    engine
                        .mutable_u16_contains(&Value::Tuple(vec![metadata.clone()]), &state.memory)
                        .unwrap()
                );
                assert!(
                    engine
                        .mutable_u16_store_role(
                            &body,
                            &state,
                            Place::from(rustc_middle::mir::Local::from_usize(3)),
                            &Value::Tuple(vec![metadata])
                        )
                        .is_err()
                );
                assert!(engine.mutable_u16_backing(id + 1, &state.memory).is_err());
                let mut masked_backing = state.memory.clone();
                let allocation = masked_backing.mutable_u16[id].allocation;
                masked_backing
                    .missing_places
                    .consume(allocation, Vec::new())
                    .unwrap();
                assert!(engine.mutable_u16_backing(id, &masked_backing).is_err());
                let shared = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "shared")
                    .unwrap();
                let shared_instance = engine
                    .resolve_function_item(shared.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let shared_body = engine.instantiated_body(shared_instance).unwrap();
                let mut metadata_state = state.clone();
                metadata_state.locals = vec![None; shared_body.local_decls.len()];
                metadata_state.addresses = vec![None; shared_body.local_decls.len()];
                metadata_state.locals[1] = Some(Value::MutableU16 {
                    id,
                    role: MutableU16Role::Metadata { generation: 0 },
                });
                let argument = rustc_span::Spanned {
                    node: Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1))),
                    span: rustc_span::DUMMY_SP,
                };
                assert!(
                    engine
                        .mutable_u16_call_allowed(
                            &shared_body,
                            &metadata_state,
                            shared_instance,
                            std::slice::from_ref(&argument)
                        )
                        .is_err()
                );
                engine
                    .mutable_u16_call_allowed(&shared_body, &metadata_state, instance, &[argument])
                    .unwrap();
                let mut wrong_backing = state.memory.clone();
                std::rc::Rc::make_mut(&mut wrong_backing.mutable_u16)[id].data = foreign
                    .symbol(
                        0,
                        Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(16))),
                    )
                    .unwrap();
                assert!(engine.mutable_u16_backing(id, &wrong_backing).is_err());
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-mutable-u16-certificate-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            r#"#![no_std]
pub fn shared(values: &[u16]) -> usize { values.len() }
pub fn scalar(word: u16) -> u16 { word ^ 0 }
pub fn probe(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() { values[index] = word; }
}
"#,
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        for level in ["0", "2"] {
            let mut check = Check { checked: false };
            rustc_driver::run_compiler(
                &[
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Cpanic=abort".into(),
                    format!("-Copt-level={level}"),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                    "--sysroot".into(),
                    String::from_utf8(sysroot.stdout.clone())
                        .unwrap()
                        .trim()
                        .into(),
                ],
                &mut check,
            );
            assert!(check.checked);
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}
