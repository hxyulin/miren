//! Direct incoming mutable integer and Bool roots. Metadata and ghosts have no data-write authority.
use super::*;
use symbolic::MutableU16Role;

#[derive(Clone, Debug)]
pub(super) struct IntegerCertificate<'tcx> {
    original: Ty<'tcx>,
    element: symbolic::ScalarSliceElement,
    bytes: u64,
    alignment: u64,
}

#[derive(Clone, Debug)]
pub(super) struct Backing {
    pub(super) certificate: usize,
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
                if self.mutable_integer_element(*element)))
    }

    fn mutable_integer_element(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
            && original != self.tcx.types.u8
    }

    fn mutable_integer_certificate(&self, id: usize) -> Result<&IntegerCertificate<'tcx>, String> {
        let certificate = self
            .mutable_integer_types
            .get(id)
            .ok_or("mutable integer element certificate was not issued")?;
        if !self.mutable_integer_element(certificate.original) {
            return Err("mutable integer certificate has an unsupported original type".into());
        }
        let layout = self.static_layout(certificate.original)?;
        if (certificate.original == self.tcx.types.bool
            && (layout.size.bytes() != 1 || layout.align.abi.bytes() != 1))
            || self.scalar_slice_element(certificate.original)? != Some(certificate.element)
            || layout.size.bytes() != certificate.bytes
            || layout.align.abi.bytes() != certificate.alignment
        {
            return Err("mutable integer certificate differs from original compiler layout".into());
        }
        Ok(certificate)
    }

    pub(super) fn mutable_integer_pending_message(
        &self,
        certificate: usize,
    ) -> Result<&'static str, String> {
        Ok(
            if self.mutable_integer_certificate(certificate)?.original == self.tcx.types.u16 {
                "mutable u16 staging needs a pending child"
            } else if self.mutable_integer_certificate(certificate)?.original == self.tcx.types.bool
            {
                "mutable bool staging needs a pending child"
            } else {
                "mutable integer staging needs a pending child"
            },
        )
    }

    pub(super) fn mutable_u16_matches(
        &self,
        original: Ty<'tcx>,
        id: usize,
        memory: &Memory,
        mutable: bool,
    ) -> Result<bool, String> {
        let backing = self.mutable_u16_backing(id, memory)?;
        let certificate = self.mutable_integer_certificate(backing.certificate)?;
        Ok(matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut() == mutable && matches!(inner.kind(), ty::Slice(element)
                if *element == certificate.original)))
    }

    fn mutable_u16_error(&self, detail: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, detail.into())
    }

    pub(super) fn mutable_u16_input(
        &mut self,
        original: Ty<'tcx>,
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
        if !self.mutable_integer_element(original) {
            return Err("mutable integer input needs exact admitted primitive".into());
        }
        let element = self
            .scalar_slice_element(original)?
            .ok_or("mutable integer codec is unavailable")?;
        let layout = self.static_layout(original)?;
        let certificate = if let Some(id) = self
            .mutable_integer_types
            .iter()
            .position(|certificate| certificate.original == original)
        {
            id
        } else {
            if self.mutable_integer_types.len() >= MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable integer certificates exceed existing budget".into(),
                ));
            }
            let id = self.mutable_integer_types.len();
            self.mutable_integer_types.push(IntegerCertificate {
                original,
                element,
                bytes: layout.size.bytes(),
                alignment: layout.align.abi.bytes(),
            });
            id
        };
        self.input_values += 2;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max = ((1_u128 << (bits - 1)) - 1) / u128::from(layout.size.bytes());
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let data = self.fresh(Sort::Array(
            Box::new(Sort::BitVec(bits)),
            Box::new(super::scalar_slices::scalar_slice_sort(element)?),
        ));
        let allocation = memory.len();
        memory.push(Some(Value::Unit));
        let id = memory.mutable_u16.len();
        std::rc::Rc::make_mut(&mut memory.mutable_u16).push(Backing {
            certificate,
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
        self.mutable_u16_terms(backing.certificate, &backing.length, &backing.data)?;
        Ok(backing)
    }

    fn mutable_u16_terms(
        &self,
        certificate: usize,
        length: &Value,
        data: &Term,
    ) -> Result<(), String> {
        let element = self.mutable_integer_certificate(certificate)?.element;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (term, width, signed) = length.integer()?;
        if width != bits
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
            || data.sort()
                != &Sort::Array(
                    Box::new(Sort::BitVec(bits)),
                    Box::new(super::scalar_slices::scalar_slice_sort(element)?),
                )
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
            MutableU16Role::Ghost {
                certificate,
                element,
                length,
                data,
            } => {
                self.mutable_u16_terms(*certificate, length, data)?;
                if self.mutable_integer_certificate(*certificate)?.element != *element {
                    return Err("mutable integer ghost codec differs from its certificate".into());
                }
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
                        certificate: backing.certificate,
                        element: self
                            .mutable_integer_certificate(backing.certificate)?
                            .element,
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
            MutableU16Role::Ghost {
                certificate,
                element,
                length,
                data,
            } => {
                self.mutable_u16_terms(*certificate, length, data)?;
                if self.mutable_integer_certificate(*certificate)?.element != *element {
                    return Err("mutable integer ghost codec differs from its certificate".into());
                }
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
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)?
            || body.local_decls[*index].ty != self.tcx.types.usize
            || place.ty(&body.local_decls, self.tcx).ty
                != self
                    .mutable_integer_certificate(backing.certificate)?
                    .original
        {
            return Err("mutable u16 element differs from original compiler type".into());
        }
        let index = self.local(state, index.as_usize())?;
        self.mutable_u16_index(&index, &backing.length, &state.conditions)?;
        Ok(Some(super::scalar_slices::decode_scalar_element(
            &self.terms,
            self.mutable_integer_certificate(backing.certificate)?
                .element,
            self.terms.apply(
                Op::Select,
                &[backing.data.clone(), index.integer()?.0.clone()],
            )?,
        )?))
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
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)?
            || body.local_decls[*index].ty != self.tcx.types.usize
            || place.ty(&body.local_decls, self.tcx).ty
                != self
                    .mutable_integer_certificate(backing.certificate)?
                    .original
        {
            return Err("mutable u16 store differs from original compiler type".into());
        }
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let index = self.local(state, index.as_usize())?;
        self.mutable_u16_index(&index, &backing.length, &state.conditions)?;
        let certificate = self.mutable_integer_certificate(backing.certificate)?;
        let term = self.mutable_scalar_replacement(certificate, replacement)?;
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

    fn mutable_scalar_replacement(
        &self,
        certificate: &IntegerCertificate<'tcx>,
        replacement: &Value,
    ) -> Result<Term, String> {
        if certificate.element == symbolic::ScalarSliceElement::Bool {
            let Value::Bool(term) = replacement else {
                return Err(
                    "mutable Bool replacement requires logical Bool in current context".into(),
                );
            };
            if certificate.original != self.tcx.types.bool
                || term.sort() != &Sort::Bool
                || !term.belongs_to(&self.terms)
            {
                return Err(
                    "mutable Bool replacement differs from issued type, sort or context".into(),
                );
            }
            return Ok(term.clone());
        }
        let (term, bits, signed) = replacement.integer()?;
        let symbolic::ScalarSliceElement::Integer {
            bits: expected_bits,
            signed: expected_signed,
        } = certificate.element
        else {
            return Err("mutable integer replacement certificate has a different kind".into());
        };
        if bits != expected_bits
            || signed != expected_signed
            || term.sort() != &Sort::BitVec(expected_bits)
            || !term.belongs_to(&self.terms)
        {
            return Err(if certificate.original == self.tcx.types.u16 {
                "mutable u16 replacement requires unsigned BV16 in current context".into()
            } else {
                "mutable integer replacement differs from issued width, sign or context".into()
            });
        }
        Ok(term.clone())
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
            || !self.mutable_u16_matches(
                body.local_decls[place.local].ty,
                id,
                &state.memory,
                true,
            )?
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
            if !matches!(inner.kind(), ty::Slice(element)
                if *element == self.mutable_integer_certificate(
                    self.mutable_u16_backing(*id, &state.memory)?.certificate)?.original)
            {
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
                        || !self.mutable_u16_matches(
                            body.local_decls[place.local].ty,
                            id,
                            &state.memory,
                            false,
                        )?
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
                    if self.mutable_integer_element(*element)))
        {
            return Err("mutable u16 SliceLen has a different original signature".into());
        }
        let ty::Ref(_, signature_slice, _) = signature.inputs()[0].kind() else {
            return Err("mutable integer SliceLen receiver differs".into());
        };
        let ty::Slice(signature_element) = signature_slice.kind() else {
            return Err("mutable integer SliceLen element differs".into());
        };
        let body = self.instantiated_body(instance)?;
        if body.arg_count != 1
            || body.local_decls.len() != 2
            || body.basic_blocks.len() != 1
            || body.local_decls[rustc_middle::mir::RETURN_PLACE].ty != self.tcx.types.usize
            || !matches!(body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty.kind(),
                ty::Ref(_, inner, mutability) if !mutability.is_mut()
                    && matches!(inner.kind(), ty::Slice(element) if element == signature_element))
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
                    .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
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
                for (original_name, wrong_name) in
                    [("caller_i32", "caller_u32"), ("caller_usize", "caller_u64")]
                {
                    let find = |name: &str| {
                        tcx.hir_body_owners()
                            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == name)
                            .unwrap()
                            .to_def_id()
                    };
                    let own_instance = engine
                        .resolve_function_item(find(original_name), tcx.mk_args(&[]))
                        .unwrap();
                    let wrong_instance = engine
                        .resolve_function_item(find(wrong_name), tcx.mk_args(&[]))
                        .unwrap();
                    let own_body = engine.instantiated_body(own_instance).unwrap();
                    let wrong_body = engine.instantiated_body(wrong_instance).unwrap();
                    let local = rustc_middle::mir::Local::from_usize(1);
                    let ty::Ref(_, slice, _) = own_body.local_decls[local].ty.kind() else {
                        panic!("reference")
                    };
                    let ty::Slice(element) = slice.kind() else {
                        panic!("slice")
                    };
                    let mut memory = Memory::default();
                    let mut conditions = Vec::new();
                    let root = engine
                        .mutable_u16_input(*element, &mut memory, &mut conditions)
                        .unwrap();
                    assert!(
                        engine
                            .mutable_u16_matches(own_body.local_decls[local].ty, 0, &memory, true)
                            .unwrap()
                    );
                    assert!(
                        !engine
                            .mutable_u16_matches(wrong_body.local_decls[local].ty, 0, &memory, true)
                            .unwrap()
                    );
                    let certificate = memory.mutable_u16[0].certificate;
                    let old_certificate = engine.mutable_integer_types[certificate].clone();
                    engine.mutable_integer_types[certificate].bytes = 0;
                    assert!(engine.mutable_u16_backing(0, &memory).is_err());
                    engine.mutable_integer_types[certificate] = old_certificate.clone();
                    engine.mutable_integer_types[certificate].alignment = 0;
                    assert!(engine.mutable_u16_backing(0, &memory).is_err());
                    engine.mutable_integer_types[certificate] = old_certificate;
                    let mut state = State {
                        locals: vec![None; wrong_body.local_decls.len()],
                        addresses: vec![None; wrong_body.local_decls.len()],
                        conditions,
                        memory,
                        missing_places: Default::default(),
                    };
                    state.locals[1] = Some(root);
                    let bits = u32::from(tcx.sess.target.pointer_width);
                    state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                    let ty::Ref(_, wrong_slice, _) = wrong_body.local_decls[local].ty.kind() else {
                        panic!("reference")
                    };
                    let ty::Slice(wrong_element) = wrong_slice.kind() else {
                        panic!("slice")
                    };
                    let (width, signed) = engine.integer_type(*wrong_element).unwrap();
                    state.locals[3] = Some(symbolic::integer(&engine.terms, 17, width, signed));
                    let (block, instance) = wrong_body
                        .basic_blocks
                        .iter_enumerated()
                        .find_map(|(block, data)| {
                            if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                                && let ty::FnDef(id, args) =
                                    func.ty(&wrong_body.local_decls, tcx).kind()
                                && tcx.item_name(*id).as_str().starts_with("child_")
                            {
                                Some((
                                    block,
                                    engine
                                        .resolve_function_item(*id, args.skip_binder())
                                        .unwrap(),
                                ))
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let TerminatorKind::Call {
                        args,
                        destination,
                        target,
                        ..
                    } = &wrong_body.basic_blocks[block].terminator().kind
                    else {
                        panic!("call")
                    };
                    let before = state.memory.mutable_u16[0].data.clone();
                    assert!(
                        engine
                            .mutable_u16_child_call(
                                &mut state,
                                super::super::mutable_u16_children::ChildCall {
                                    body: &wrong_body,
                                    block,
                                    instance,
                                    args,
                                    destination: *destination,
                                    target: *target,
                                    stack: &[],
                                    site: (wrong_instance.def_id(), rustc_span::DUMMY_SP),
                                }
                            )
                            .is_err()
                    );
                    assert_eq!(state.memory.mutable_u16[0].data, before);
                    assert_eq!(
                        state.memory.mutable_u16[0].phase,
                        super::super::mutable_u16_children::Phase::Idle
                    );
                    let place = Place {
                        local,
                        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                    };
                    let destination = Place::from(rustc_middle::mir::Local::from_usize(4));
                    let value = Rvalue::Ref(
                        tcx.lifetimes.re_erased,
                        BorrowKind::Mut {
                            kind: rustc_middle::mir::MutBorrowKind::Default,
                        },
                        place,
                    );
                    let occurrence = StatementKind::Assign(Box::new((destination, value)));
                    let StatementKind::Assign(assignment) = &occurrence else {
                        panic!("assign")
                    };
                    assert!(
                        engine
                            .mutable_u16_stage(
                                &wrong_body,
                                &mut state,
                                destination,
                                &assignment.1,
                                &occurrence
                            )
                            .is_err()
                    );
                    let len = engine
                        .resolve_function_item(
                            tcx.lang_items().get(LangItem::SliceLen).unwrap(),
                            tcx.mk_args(&[(*wrong_element).into()]),
                        )
                        .unwrap();
                    let metadata = Value::MutableU16 {
                        id: 0,
                        role: MutableU16Role::Metadata { generation: 0 },
                    };
                    assert!(
                        engine
                            .builtin(
                                &wrong_body,
                                len,
                                std::slice::from_ref(&metadata),
                                std::slice::from_ref(&metadata),
                                &mut state,
                                rustc_span::DUMMY_SP
                            )
                            .is_err()
                    );
                    let mut ghost = engine
                        .mutable_u16_snapshot(state.locals[1].as_ref().unwrap(), &state.memory)
                        .unwrap();
                    let Value::MutableU16 {
                        role: MutableU16Role::Ghost { element, .. },
                        ..
                    } = &mut ghost
                    else {
                        panic!("ghost")
                    };
                    *element = symbolic::ScalarSliceElement::Integer {
                        bits: width,
                        signed,
                    };
                    // i32/u32 share width; usize/u64 share codec. Original types still differ.
                    if original_name == "caller_i32" {
                        assert!(engine.mutable_u16_snapshot(&ghost, &state.memory).is_err());
                    }
                }
                let mut bool_memory = Memory::default();
                let mut bool_conditions = Vec::new();
                let bool_root = engine
                    .mutable_u16_input(tcx.types.bool, &mut bool_memory, &mut bool_conditions)
                    .unwrap();
                let ghost = engine
                    .mutable_u16_snapshot(&bool_root, &bool_memory)
                    .unwrap();
                let certificate = bool_memory.mutable_u16[0].certificate;
                let issued = engine.mutable_integer_types[certificate].clone();
                assert_eq!(issued.element, symbolic::ScalarSliceElement::Bool);
                assert_eq!((issued.bytes, issued.alignment), (1, 1));
                let good = Value::Bool(engine.terms.boolean(true));
                assert!(engine.mutable_scalar_replacement(&issued, &good).is_ok());
                for wrong in [
                    symbolic::integer(&engine.terms, 1, 8, false),
                    Value::Bool(foreign.boolean(true)),
                    Value::Bool(engine.terms.bit_vector(1, 8).unwrap()),
                ] {
                    assert!(engine.mutable_scalar_replacement(&issued, &wrong).is_err());
                }
                for wrong_type in [tcx.types.u8, tcx.types.i8] {
                    engine.mutable_integer_types[certificate].original = wrong_type;
                    assert!(engine.mutable_u16_backing(0, &bool_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for (bytes, alignment) in [(0, 1), (1, 2)] {
                    engine.mutable_integer_types[certificate].bytes = bytes;
                    engine.mutable_integer_types[certificate].alignment = alignment;
                    assert!(engine.mutable_u16_backing(0, &bool_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for context in [&engine.terms, &foreign] {
                    let mut corrupt = bool_memory.clone();
                    std::rc::Rc::make_mut(&mut corrupt.mutable_u16)[0].data = context
                        .symbol(
                            99,
                            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8))),
                        )
                        .unwrap();
                    assert!(engine.mutable_u16_backing(0, &corrupt).is_err());
                }
                let bool_definition = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "bool_probe")
                    .unwrap();
                let bool_instance = engine
                    .resolve_function_item(bool_definition.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let bool_body = engine.instantiated_body(bool_instance).unwrap();
                std::rc::Rc::make_mut(&mut bool_memory.mutable_u16)[0].length =
                    symbolic::integer(&engine.terms, 2, bits, false);
                let mut bool_state = State {
                    locals: vec![None; bool_body.local_decls.len()],
                    addresses: vec![None; bool_body.local_decls.len()],
                    conditions: bool_conditions,
                    memory: bool_memory.clone(),
                    missing_places: Default::default(),
                };
                bool_state.locals[1] = Some(bool_root.clone());
                bool_state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                let bool_place = Place {
                    local: rustc_middle::mir::Local::from_usize(1),
                    projection: tcx.mk_place_elems(&[
                        ProjectionElem::Deref,
                        ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                    ]),
                };
                assert!(
                    engine
                        .mutable_u16_store(&bool_body, &mut bool_state, bool_place, &good)
                        .unwrap()
                );
                assert!(matches!(
                    engine
                        .mutable_u16_read(Some(&bool_body), &bool_state, bool_place)
                        .unwrap(),
                    Some(Value::Bool(_))
                ));
                assert!(
                    !engine
                        .mutable_u16_matches(
                            body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty,
                            0,
                            &bool_state.memory,
                            true
                        )
                        .unwrap()
                );
                bool_state.locals[1] = Some(ghost.clone());
                assert!(
                    engine
                        .mutable_u16_read(Some(&bool_body), &bool_state, bool_place)
                        .is_err()
                );
                let old_data = bool_memory.mutable_u16[0].data.clone();
                std::rc::Rc::make_mut(&mut bool_memory.mutable_u16)[0].data = engine
                    .terms
                    .apply(
                        Op::Store,
                        &[
                            old_data,
                            engine.terms.bit_vector(0, bits).unwrap(),
                            engine.terms.boolean(true),
                        ],
                    )
                    .unwrap();
                assert!(engine.mutable_u16_length(&ghost, &bool_memory).is_ok());
                if let Value::MutableU16 {
                    role: MutableU16Role::Ghost { data, .. },
                    ..
                } = ghost
                {
                    assert_ne!(data, bool_memory.mutable_u16[0].data);
                } else {
                    panic!("detached ghost");
                }
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
#[inline(never)]
pub fn child_i32(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_u32(values: &mut [u32], index: usize, word: u32) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_usize(values: &mut [usize], index: usize, word: usize) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_u64(values: &mut [u64], index: usize, word: u64) {
    if index < values.len() {
        values[index] = word;
    }
}
pub fn caller_i32(values: &mut [i32], index: usize, word: i32) {
    child_i32(values, index, word);
    let _ = values.len();
}
pub fn caller_u32(values: &mut [u32], index: usize, word: u32) {
    child_u32(values, index, word);
    let _ = values.len();
}
pub fn caller_usize(values: &mut [usize], index: usize, word: usize) {
    child_usize(values, index, word);
    let _ = values.len();
}
pub fn caller_u64(values: &mut [u64], index: usize, word: u64) {
    child_u64(values, index, word);
    let _ = values.len();
}
pub fn shared(values: &[u16]) -> usize {
    values.len()
}
pub fn scalar(word: u16) -> u16 {
    word ^ 0
}
pub fn bool_probe(values: &mut [bool], index: usize, word: bool) {
    if index < values.len() { values[index] = word; }
}
pub fn probe(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = word;
    }
}
"#,
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for level in ["0", "2"] {
                let mut check = Check { checked: false };
                let mut arguments = vec![
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
                ];
                if let Some(target) = target {
                    arguments.extend(["--target".into(), target.into()]);
                }
                rustc_driver::run_compiler(&arguments, &mut check);
                assert!(check.checked);
            }
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}
