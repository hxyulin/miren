//! One synchronous, whole-slice child. Authority is branch-local; compiler facts are weakly held.
use super::*;
use symbolic::MutableU16Role;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Phase {
    Idle,
    Pending { certificate: usize },
    Active { frames: Vec<usize> },
}

pub(super) struct Staging<'tcx> {
    body: std::rc::Weak<Body<'tcx>>,
    destination: usize,
    occurrence: usize,
}

pub(super) fn role_live(backing: &super::mutable_u16::Backing, role: &MutableU16Role) -> bool {
    match role {
        MutableU16Role::Root => backing.phase == Phase::Idle,
        MutableU16Role::Metadata { generation } => {
            backing.phase == Phase::Idle && *generation == backing.generation
        }
        MutableU16Role::Child { generation } | MutableU16Role::ChildMetadata { generation } => {
            matches!(&backing.phase, Phase::Active { frames } if !frames.is_empty())
                && *generation == backing.generation
        }
        MutableU16Role::Ghost { .. } => true,
    }
}

pub(super) struct ChildCall<'a, 'tcx> {
    pub(super) body: &'a Body<'tcx>,
    pub(super) block: rustc_middle::mir::BasicBlock,
    pub(super) instance: ty::Instance<'tcx>,
    pub(super) args: &'a [rustc_span::Spanned<Operand<'tcx>>],
    pub(super) destination: Place<'tcx>,
    pub(super) target: Option<rustc_middle::mir::BasicBlock>,
    pub(super) stack: &'a [DefId],
    pub(super) site: (DefId, Span),
}

impl<'tcx> Engine<'tcx> {
    fn mutable_u16_child_error(&self, detail: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, detail.into())
    }

    pub(super) fn mutable_u16_role_live(
        &self,
        id: usize,
        role: &MutableU16Role,
        memory: &Memory,
    ) -> Result<(), String> {
        let backing = self.mutable_u16_backing(id, memory)?;
        let valid = role_live(backing, role);
        if !valid {
            return Err(self.mutable_u16_child_error(
                "mutable u16 role is suspended or its child generation has ended",
            ));
        }
        Ok(())
    }

    pub(super) fn mutable_u16_exit(
        &self,
        body: &Body<'tcx>,
        arguments: &[Value],
        memory: &Memory,
    ) -> Result<(), String> {
        for (id, backing) in memory.mutable_u16.iter().enumerate() {
            match &backing.phase {
                Phase::Idle => {}
                Phase::Pending { .. } => {
                    return Err(self.mutable_u16_child_error(
                        "pending mutable u16 child cannot leave a frame",
                    ));
                }
                Phase::Active { frames } => {
                    self.mutable_u16_frame_top(body, frames)?;
                    let count = arguments
                        .iter()
                        .filter(|argument| {
                            matches!(argument,
                        Value::MutableU16 { id: argument_id,
                            role: MutableU16Role::Child { generation } }
                            if *argument_id == id && *generation == backing.generation)
                        })
                        .count();
                    if count != usize::from(frames.len() == 1) {
                        return Err(self.mutable_u16_child_error(
                            "active mutable u16 child has no frame grant",
                        ));
                    }
                    self.mutable_u16_backing(id, memory)?;
                }
            }
        }
        Ok(())
    }

    fn mutable_u16_body_budget(&self, body: &Body<'tcx>) -> Result<(), String> {
        if body.coroutine.is_some() || body.tainted_by_errors.is_some() || body.spread_arg.is_some()
        {
            return Err(
                self.mutable_u16_child_error("mutable u16 child Body metadata is unsupported")
            );
        }
        let mut work = body
            .basic_blocks
            .len()
            .saturating_add(body.local_decls.len());
        if work > MAX_INPUT_VALUES || body.local_decls.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 child Body exceeds existing certificate budget".into(),
            ));
        }
        for block in body.basic_blocks.iter() {
            work = work.saturating_add(block.statements.len());
            if work > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable u16 child Body exceeds existing certificate budget".into(),
                ));
            }
        }
        Ok(())
    }

    pub(super) fn mutable_u16_direct_metadata(
        &self,
        body: &Body<'tcx>,
        state: &State,
        operand: &Operand<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        let Operand::Copy(place) = operand else {
            return Ok(None);
        };
        let Value::MutableU16 { id, role } = self.raw_local(state, place.local.as_usize())? else {
            return Ok(None);
        };
        if !place.projection.is_empty()
            || !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. })
            || !self.mutable_u16_matches(
                body.local_decls[place.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Ok(None);
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        Ok(Some(
            self.mutable_u16_backing(id, &state.memory)?.length.clone(),
        ))
    }

    fn mutable_u16_staging_tip(
        &self,
        body: &Body<'tcx>,
        state: &State,
        local: usize,
        id: usize,
        generation: u64,
    ) -> Result<(), String> {
        self.check_local_initialization(state, local, &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let Phase::Pending { certificate } = backing.phase else {
            let detail = self.mutable_integer_pending_message(backing.certificate)?;
            return Err(self.mutable_u16_child_error(detail));
        };
        let certificates = self.mutable_u16_staging.borrow();
        let certificate = certificates
            .get(certificate)
            .ok_or("mutable u16 staging certificate was not issued")?;
        let original = certificate
            .body
            .upgrade()
            .ok_or("mutable u16 staging Body expired")?;
        self.mutable_u16_body_budget(&original)?;
        if !std::ptr::eq(original.as_ref(), body)
            || certificate.destination != local
            || backing.generation != generation
            || !original.basic_blocks.iter().any(|block| {
                block.statements.iter().any(|statement| {
                    std::ptr::from_ref(&statement.kind) as usize == certificate.occurrence
                })
            })
        {
            return Err(self.mutable_u16_child_error("mutable u16 staging identity differs"));
        }
        Ok(())
    }

    pub(super) fn mutable_u16_stage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(false);
        }
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Ok(false);
        };
        if !matches!(occurrence, StatementKind::Assign(assignment)
            if assignment.0 == destination && std::ptr::eq(&assignment.1, value))
        {
            return Err("mutable u16 staging differs from its actual assignment".into());
        }
        let Ok(Value::MutableU16 { id, role }) = self.raw_local(state, source.local.as_usize())
        else {
            return Ok(false);
        };
        if source.projection.as_ref() != [ProjectionElem::Deref]
            || !self.mutable_u16_matches(
                body.local_decls[source.local].ty,
                id,
                &state.memory,
                true,
            )?
            || !self.mutable_u16_matches(
                body.local_decls[destination.local].ty,
                id,
                &state.memory,
                true,
            )?
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || state.addresses[destination.local.as_usize()].is_some()
            || source.local == destination.local
        {
            return Err(
                self.mutable_u16_child_error("mutable u16 staging needs a private whole tip")
            );
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])?;
        let generation = match role {
            MutableU16Role::Root => {
                self.mutable_u16_role_live(id, &role, &state.memory)?;
                self.mutable_u16_backing(id, &state.memory)?
                    .generation
                    .checked_add(1)
                    .ok_or("mutable u16 child generation overflow")?
            }
            MutableU16Role::Child { generation } => {
                self.mutable_u16_staging_tip(body, state, source.local.as_usize(), id, generation)?;
                generation
            }
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::Ghost { .. } => {
                return Err(
                    self.mutable_u16_child_error("mutable u16 metadata cannot stage a child")
                );
            }
        };
        let original = self
            .bodies
            .borrow()
            .values()
            .find(|candidate| std::ptr::eq(candidate.as_ref(), body))
            .cloned()
            .ok_or("mutable u16 staging needs an authenticated instantiated Body")?;
        self.mutable_u16_body_budget(&original)?;
        if !original.basic_blocks.iter().any(|block| {
            block
                .statements
                .iter()
                .any(|statement| std::ptr::eq(&statement.kind, occurrence))
        }) {
            return Err("mutable u16 staging occurrence is not in the original Body".into());
        }
        let mut certificates = self.mutable_u16_staging.borrow_mut();
        if certificates
            .len()
            .saturating_add(self.mutable_u16_frames.borrow().len())
            >= MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 staging exceeds existing certificate budget".into(),
            ));
        }
        let certificate = certificates.len();
        certificates.push(Staging {
            body: std::rc::Rc::downgrade(&original),
            destination: destination.local.as_usize(),
            occurrence: std::ptr::from_ref(occurrence) as usize,
        });
        drop(certificates);
        let backing = &mut std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id];
        backing.generation = generation;
        backing.phase = Phase::Pending { certificate };
        self.write(
            state,
            destination,
            Value::MutableU16 {
                id,
                role: MutableU16Role::Child { generation },
            },
        )?;
        Ok(true)
    }

    pub(super) fn mutable_u16_staging_store(
        &self,
        _body: &Body<'tcx>,
        _state: &State,
        _place: Place<'tcx>,
        _id: usize,
        _role: &MutableU16Role,
    ) -> Result<(), String> {
        Err(self.mutable_u16_child_error(
            "mutable u16 child storage needs its exact staging occurrence",
        ))
    }

    fn mutable_u16_primitive(&self, original: Ty<'tcx>) -> bool {
        matches!(
            original.kind(),
            ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Float(_)
        )
    }

    pub(super) fn mutable_u16_child_call(
        &mut self,
        state: &mut State,
        call: ChildCall<'_, 'tcx>,
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
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        let mut source = None;
        for (position, arg) in args.iter().enumerate() {
            if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                let value = self.raw_local(state, place.local.as_usize())?;
                if self.mutable_u16_contains(&value, &state.memory)? {
                    let Value::MutableU16 { id, role } = value else {
                        return Err(
                            self.mutable_u16_child_error("mutable u16 child has nested roles")
                        );
                    };
                    if matches!(
                        role,
                        MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. }
                    ) {
                        continue;
                    }
                    if source.is_some() || !place.projection.is_empty() {
                        return Err(self.mutable_u16_child_error(
                            "mutable u16 child duplicates root authority",
                        ));
                    }
                    source = Some((position, *place, id, role));
                }
            }
        }
        let Some((position, place, id, role)) = source else {
            return self.mutable_u16_scalar_child(
                state,
                ChildCall {
                    body,
                    block,
                    instance,
                    args,
                    destination,
                    target,
                    stack,
                    site,
                },
            );
        };
        let signature = self.tcx.erase_and_anonymize_regions(
            self.tcx
                .fn_sig(instance.def_id())
                .instantiate(self.tcx, instance.args)
                .skip_binder(),
        );
        let caller = &body.basic_blocks[block].terminator().kind;
        let TerminatorKind::Call { func, unwind, .. } = caller else {
            return Err("mutable u16 child certificate needs actual Call".into());
        };
        if !matches!(func.ty(&body.local_decls, self.tcx).kind(), ty::FnDef(definition, _)
            if *definition == instance.def_id())
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::Fn
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || !self.mutable_u16_matches(signature.inputs()[position], id, &state.memory, true)?
            || !self.mutable_u16_matches(
                body.local_decls[place.local].ty,
                id,
                &state.memory,
                true,
            )?
            || signature
                .inputs()
                .iter()
                .enumerate()
                .any(|(i, ty)| i != position && !self.mutable_u16_primitive(*ty))
            || !(signature.output().is_unit() || self.mutable_u16_primitive(signature.output()))
            || destination.ty(&body.local_decls, self.tcx).ty != signature.output()
            || !destination.projection.is_empty()
            || target.is_none()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
        {
            return Err(
                self.mutable_u16_child_error("mutable u16 child needs direct abort-only Rust body")
            );
        }
        let selected = self.instantiated_body(instance)?;
        self.mutable_u16_body_budget(&selected)?;
        if selected.arg_count != args.len()
            || selected.local_decls.len() <= position + 1
            || !self.mutable_u16_matches(
                selected.local_decls[rustc_middle::mir::Local::from_usize(position + 1)].ty,
                id,
                &state.memory,
                true,
            )?
            || selected
                .args_iter()
                .zip(signature.inputs())
                .enumerate()
                .any(|(i, (local, original))| {
                    if i == position {
                        !self.mutable_u16_type(selected.local_decls[local].ty)
                    } else {
                        selected.local_decls[local].ty != *original
                    }
                })
            || selected.return_ty() != signature.output()
            || selected.basic_blocks.iter().any(|block| {
                block.is_cleanup
                    || match &block.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err(self.mutable_u16_child_error(
                "mutable u16 child has unsupported selected unwind/schema",
            ));
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        let generation = match role {
            MutableU16Role::Root => {
                self.mutable_u16_role_live(id, &role, &state.memory)?;
                if matches!(args[position].node, Operand::Move(_)) {
                    return Err(self.mutable_u16_child_error(
                        "mutable u16 moved parent transport is deferred",
                    ));
                }
                self.mutable_u16_backing(id, &state.memory)?
                    .generation
                    .checked_add(1)
                    .ok_or("mutable u16 child generation overflow")?
            }
            MutableU16Role::Child { generation } => {
                self.mutable_u16_staging_tip(body, state, place.local.as_usize(), id, generation)?;
                generation
            }
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::Ghost { .. } => {
                return Err(
                    self.mutable_u16_child_error("mutable u16 child source lacks root authority")
                );
            }
        };
        // All role duplication, signature and body checks precede sequential operand effects.
        let mut values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            if i == position {
                if matches!(arg.node, Operand::Move(_)) {
                    if state.addresses[place.local.as_usize()].is_some() {
                        return Err(
                            self.mutable_u16_child_error("mutable u16 staging cannot be addressed")
                        );
                    }
                    state
                        .missing_places
                        .consume(place.local.as_usize(), Vec::new())?;
                }
                values.push(Value::MutableU16 {
                    id,
                    role: MutableU16Role::Child { generation },
                });
            } else {
                values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
            }
        }
        let frame = self.mutable_u16_register_frame(&selected)?;
        if state.memory.storage_slots().saturating_add(1) > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 frame exceeds existing storage budget".into(),
            ));
        }
        let backing = &mut std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id];
        backing.generation = generation;
        backing.phase = Phase::Active {
            frames: vec![frame],
        };
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        // execute_body has completed its actual returned-value, capture and incoming-storage
        // graph checks before publishing Return. No executable role is stored in caller memory:
        // aggregate, addressed and projected role stores are refused by the ordinary store gate.
        for result in &mut results {
            self.mutable_u16_role_live(id, &MutableU16Role::Child { generation }, &result.memory)?;
            if result.memory.mutable_u16[id].phase
                != (Phase::Active {
                    frames: vec![frame],
                })
            {
                return Err(self
                    .mutable_u16_child_error("mutable u16 owner release has outstanding frames"));
            }
            if self.mutable_u16_contains(&result.value, &result.memory)? {
                return Err(
                    self.mutable_u16_child_error("mutable u16 child result retains authority")
                );
            }
            std::rc::Rc::make_mut(&mut result.memory.mutable_u16)[id].phase = Phase::Idle;
        }
        Ok(Some(results))
    }
    fn mutable_u16_register_frame(&self, body: &std::rc::Rc<Body<'tcx>>) -> Result<usize, String> {
        self.mutable_u16_body_budget(body)?;
        let mut frames = self.mutable_u16_frames.borrow_mut();
        if let Some(id) = frames.iter().position(|frame| {
            frame
                .upgrade()
                .is_some_and(|original| std::ptr::eq(original.as_ref(), body.as_ref()))
        }) {
            return Ok(id);
        }
        if frames
            .len()
            .saturating_add(self.mutable_u16_staging.borrow().len())
            >= MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 frame certificates exceed existing budget".into(),
            ));
        }
        let id = frames.len();
        frames.push(std::rc::Rc::downgrade(body));
        Ok(id)
    }

    fn mutable_u16_frame_top(&self, body: &Body<'tcx>, frames: &[usize]) -> Result<(), String> {
        if frames.is_empty() || frames.len() > MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 active frame stack exceeds existing depth budget".into(),
            ));
        }
        let certificates = self.mutable_u16_frames.borrow();
        let original = certificates
            .get(*frames.last().unwrap())
            .and_then(std::rc::Weak::upgrade)
            .ok_or("mutable u16 frame Body expired or was not issued")?;
        if !std::ptr::eq(original.as_ref(), body) {
            return Err(self.mutable_u16_child_error("mutable u16 ancestor frame identity differs"));
        }
        Ok(())
    }

    fn mutable_u16_scalar_child(
        &mut self,
        state: &mut State,
        call: ChildCall<'_, 'tcx>,
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
        let active: Vec<_> = state
            .memory
            .mutable_u16
            .iter()
            .enumerate()
            .filter_map(|(id, backing)| match &backing.phase {
                Phase::Active { frames } => Some((id, backing.generation, frames.clone())),
                Phase::Idle | Phase::Pending { .. } => None,
            })
            .collect();
        let [(id, generation, frames)] = active.as_slice() else {
            return if active.is_empty() {
                Ok(None)
            } else {
                Err(self.mutable_u16_child_error("mutable u16 scalar call has ambiguous ancestry"))
            };
        };
        // Certified SliceLen and actual panic obligations retain their original distinct paths.
        if self.tcx.lang_items().get(LangItem::SliceLen) == Some(instance.def_id())
            || super::super::identity::is_panic_call(self.tcx, instance.def_id())
            || self.is_core_panic_helper(instance.def_id())
        {
            return Ok(None);
        }
        self.mutable_u16_frame_top(body, frames)?;
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_binder();
        let TerminatorKind::Call { func, unwind, .. } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("mutable u16 scalar frame needs actual Call".into());
        };
        if !matches!(func.ty(&body.local_decls, self.tcx).kind(), ty::FnDef(definition, _)
            if *definition == instance.def_id())
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::Fn
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || signature
                .inputs()
                .iter()
                .any(|original| !self.mutable_u16_primitive(*original))
            || !(signature.output().is_unit() || self.mutable_u16_primitive(signature.output()))
            || destination.ty(&body.local_decls, self.tcx).ty != signature.output()
            || !destination.projection.is_empty()
            || target.is_none()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
        {
            return Err(self.mutable_u16_child_error(
                "mutable u16 ancestor admits only direct scalar Rust frames",
            ));
        }
        for arg in args {
            if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                let value = self.read_place(state, *place, Some(body))?;
                if self.mutable_u16_contains(&value, &state.memory)? {
                    return Err(self.mutable_u16_child_error(
                        "mutable u16 scalar frame cannot receive private roles",
                    ));
                }
            }
        }
        let selected = self.instantiated_body(instance)?;
        self.mutable_u16_body_budget(&selected)?;
        if selected.arg_count != args.len()
            || selected.return_ty() != signature.output()
            || selected
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, original)| selected.local_decls[local].ty != *original)
            || selected.basic_blocks.iter().any(|block| {
                block.is_cleanup
                    || match &block.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err(self.mutable_u16_child_error(
                "mutable u16 scalar frame selected schema/unwind differs",
            ));
        }
        if frames.len() >= MAX_INPUT_DEPTH
            || state.memory.storage_slots().saturating_add(1) > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 ancestor stack exceeds existing storage/depth budget".into(),
            ));
        }
        let frame = self.mutable_u16_register_frame(&selected)?;
        let mut next_frames = frames.clone();
        next_frames.push(frame);
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
        }
        std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[*id].phase = Phase::Active {
            frames: next_frames.clone(),
        };
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        for result in &mut results {
            let backing = self.mutable_u16_backing(*id, &result.memory)?;
            if backing.generation != *generation
                || backing.phase
                    != (Phase::Active {
                        frames: next_frames.clone(),
                    })
                || self.mutable_u16_contains(&result.value, &result.memory)?
            {
                return Err(self.mutable_u16_child_error(
                    "mutable u16 scalar return changed its ancestor grant",
                ));
            }
            std::rc::Rc::make_mut(&mut result.memory.mutable_u16)[*id].phase = Phase::Active {
                frames: frames.clone(),
            };
        }
        Ok(Some(results))
    }
}

#[cfg(test)]
impl<'tcx> Engine<'tcx> {
    pub(super) fn check_mutable_u16_child_roles(&mut self, body: &Body<'tcx>, state: &State) {
        let mut active = state.clone();
        let backing = &mut std::rc::Rc::make_mut(&mut active.memory.mutable_u16)[0];
        backing.generation = 1;
        backing.phase = Phase::Active {
            frames: vec![
                self.mutable_u16_register_frame(
                    &self
                        .bodies
                        .borrow()
                        .values()
                        .find(|original| std::ptr::eq(original.as_ref(), body))
                        .cloned()
                        .unwrap(),
                )
                .unwrap(),
            ],
        };
        let child = Value::MutableU16 {
            id: 0,
            role: MutableU16Role::Child { generation: 1 },
        };
        let metadata = Value::MutableU16 {
            id: 0,
            role: MutableU16Role::ChildMetadata { generation: 1 },
        };
        active.locals[1] = Some(child.clone());
        self.mutable_u16_role_live(0, &MutableU16Role::Child { generation: 1 }, &active.memory)
            .unwrap();
        assert!(
            self.mutable_u16_role_live(0, &MutableU16Role::Root, &active.memory)
                .is_err()
        );
        assert!(
            self.mutable_u16_role_live(0, &MutableU16Role::Child { generation: 0 }, &active.memory)
                .is_err()
        );
        self.mutable_u16_length(&metadata, &active.memory).unwrap();
        let operand = Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1)));
        self.mutable_u16_direct_metadata(body, &active, &operand)
            .unwrap()
            .unwrap();
        assert!(
            self.mutable_u16_direct_metadata(
                body,
                &active,
                &Operand::Move(Place::from(rustc_middle::mir::Local::from_usize(1)))
            )
            .unwrap()
            .is_none()
        );
        let mut unavailable = active.clone();
        unavailable.missing_places.consume(1, Vec::new()).unwrap();
        assert!(
            self.mutable_u16_direct_metadata(body, &unavailable, &operand)
                .is_err()
        );
        let mut wrong = body.clone();
        let shared = self
            .tcx
            .hir_body_owners()
            .find(|owner| self.tcx.item_name(owner.to_def_id()).as_str() == "shared")
            .unwrap();
        let shared_instance = self
            .resolve_function_item(shared.to_def_id(), self.tcx.mk_args(&[]))
            .unwrap();
        let shared_body = self.instantiated_body(shared_instance).unwrap();
        wrong.local_decls[rustc_middle::mir::Local::from_usize(1)].ty =
            shared_body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
        assert!(
            self.mutable_u16_direct_metadata(&wrong, &active, &operand)
                .unwrap()
                .is_none()
        );

        let ghost = self.mutable_u16_snapshot(&child, &active.memory).unwrap();
        self.mutable_u16_exit(body, std::slice::from_ref(&child), &active.memory)
            .unwrap();
        assert!(self.mutable_u16_exit(body, &[], &active.memory).is_err());
        assert!(
            self.mutable_u16_exit(body, &[child.clone(), child.clone()], &active.memory)
                .is_err()
        );
        let scalar = self
            .tcx
            .hir_body_owners()
            .find(|owner| self.tcx.item_name(owner.to_def_id()).as_str() == "scalar")
            .unwrap();
        let instance = self
            .resolve_function_item(scalar.to_def_id(), self.tcx.mk_args(&[]))
            .unwrap();
        let scalar_body = self.instantiated_body(instance).unwrap();
        let scalar_frame = self.mutable_u16_register_frame(&scalar_body).unwrap();
        let Phase::Active { frames } =
            &mut std::rc::Rc::make_mut(&mut active.memory.mutable_u16)[0].phase
        else {
            panic!("active owner")
        };
        frames.push(scalar_frame);
        assert_eq!(
            active.memory.storage_slots(),
            state.memory.storage_slots() + 2
        );
        assert!(
            self.mutable_u16_exit(body, std::slice::from_ref(&child), &active.memory)
                .is_err()
        );
        self.mutable_u16_exit(&scalar_body, &[], &active.memory)
            .unwrap();
        assert!(
            self.mutable_u16_exit(&scalar_body, std::slice::from_ref(&child), &active.memory)
                .is_err()
        );
        let Phase::Active { frames } =
            &mut std::rc::Rc::make_mut(&mut active.memory.mutable_u16)[0].phase
        else {
            panic!("active scalar")
        };
        frames.pop();
        let mut full = active.clone();
        while full.memory.storage_slots() < MAX_INPUT_VALUES {
            full.memory.push(Some(Value::Unit));
        }
        let before = full.memory.len();
        assert!(
            self.raw_tracked_pointer(
                body,
                &mut full,
                Place::from(rustc_middle::mir::Local::from_usize(2)),
                false
            )
            .is_err()
        );
        assert_eq!(full.memory.len(), before);
        let original = self
            .bodies
            .borrow()
            .values()
            .find(|original| std::ptr::eq(original.as_ref(), body))
            .cloned()
            .unwrap();
        let (occurrence, _) = original
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .map(|statement| (&statement.kind, ()))
            .next()
            .unwrap();
        let mut certificates = self.mutable_u16_staging.borrow_mut();
        let certificate = certificates.len();
        certificates.push(Staging {
            body: std::rc::Rc::downgrade(&original),
            destination: 1,
            occurrence: std::ptr::from_ref(occurrence) as usize,
        });
        drop(certificates);
        std::rc::Rc::make_mut(&mut active.memory.mutable_u16)[0].phase =
            Phase::Pending { certificate };
        self.mutable_u16_staging_tip(body, &active, 1, 0, 1)
            .unwrap();
        assert!(
            self.mutable_u16_staging_tip(body, &active, 2, 0, 1)
                .is_err()
        );
        assert!(
            self.mutable_u16_staging_tip(body, &active, 1, 0, 2)
                .is_err()
        );
        let other = std::rc::Rc::new((*original).clone());
        assert!(
            self.mutable_u16_staging_tip(&other, &active, 1, 0, 1)
                .is_err()
        );
        assert!(self.mutable_u16_exit(body, &[], &active.memory).is_err());
        self.mutable_u16_staging.borrow_mut()[certificate].body = std::rc::Rc::downgrade(&other);
        drop(other);
        assert!(
            self.mutable_u16_staging_tip(body, &active, 1, 0, 1)
                .is_err()
        );
        std::rc::Rc::make_mut(&mut active.memory.mutable_u16)[0].phase = Phase::Idle;
        assert!(self.mutable_u16_length(&metadata, &active.memory).is_err());
        assert!(self.mutable_u16_snapshot(&child, &active.memory).is_err());
        self.mutable_u16_snapshot(&ghost, &active.memory).unwrap();
        self.mutable_u16_role_live(0, &MutableU16Role::Root, &active.memory)
            .unwrap();
        assert!(
            self.mutable_u16_role_live(
                0,
                &MutableU16Role::Metadata { generation: 0 },
                &active.memory
            )
            .is_err()
        );
        assert_eq!(state.memory.mutable_u16[0].phase, Phase::Idle);
        assert_eq!(state.memory.mutable_u16[0].generation, 0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn child_generations_revoke_metadata_without_mutating_sibling_memory() {
        let terms = Context::default();
        let mut memory = Memory::default();
        memory.push(Some(Value::Unit));
        std::rc::Rc::make_mut(&mut memory.mutable_u16).push(super::super::mutable_u16::Backing {
            certificate: 0,
            allocation: 0,
            length: symbolic::integer(&terms, 129, 64, false),
            data: terms
                .symbol(
                    0,
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(16))),
                )
                .unwrap(),
            generation: 0,
            phase: Phase::Idle,
        });
        let sibling = memory.clone();
        let backing = &mut std::rc::Rc::make_mut(&mut memory.mutable_u16)[0];
        backing.generation = 1;
        backing.phase = Phase::Active { frames: vec![0] };
        assert!(!role_live(backing, &MutableU16Role::Root));
        assert!(!role_live(
            backing,
            &MutableU16Role::Metadata { generation: 0 }
        ));
        assert!(role_live(backing, &MutableU16Role::Child { generation: 1 }));
        assert!(!role_live(
            backing,
            &MutableU16Role::Child { generation: 2 }
        ));
        assert_eq!(memory.storage_slots(), sibling.storage_slots() + 1);
        std::rc::Rc::make_mut(&mut memory.mutable_u16)[0].phase = Phase::Idle;
        assert!(!role_live(
            &memory.mutable_u16[0],
            &MutableU16Role::ChildMetadata { generation: 1 }
        ));
        assert!(role_live(&memory.mutable_u16[0], &MutableU16Role::Root));
        assert!(role_live(
            &sibling.mutable_u16[0],
            &MutableU16Role::Metadata { generation: 0 }
        ));
    }
}
