//! Same-frame retained mutable Range views; full typed backing is never detached.
use super::mutable_u16_children::{ChildCall, Phase};
use super::*;
use rustc_middle::mir::{BasicBlock, Local};
use std::rc::{Rc, Weak};
use symbolic::MutableU16Role;

#[derive(Clone)]
pub(super) struct Certificate<'tcx> {
    body: Weak<Body<'tcx>>,
    backing: usize,
    allocation: usize,
    original: usize,
    generation: u64,
    call: BasicBlock,
    occurrence: usize,
    intermediate: usize,
    carrier: usize,
    stage: usize,
    start: Term,
    end: Term,
    capacity: Term,
}

// Semantic visits/services, not CPU instructions. Every traversal pays before visiting.
pub(super) struct Work(pub(super) usize);
impl Work {
    pub(super) fn charge(&mut self, engine: &Engine<'_>, count: usize) -> Result<(), String> {
        self.0 = self.0.checked_add(count).ok_or_else(|| {
            engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained service work overflow".into(),
            )
        })?;
        if self.0 > MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained service exceeds its existing 512-node budget".into(),
            ));
        }
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    fn retained_error(&self, reason: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, reason.into())
    }

    fn retained_body(&self, body: &Body<'tcx>, work: &mut Work) -> Result<Rc<Body<'tcx>>, String> {
        let bodies = self.bodies.borrow();
        work.charge(self, body.local_decls.len())?;
        work.charge(self, body.basic_blocks.len())?;
        work.charge(self, bodies.len())?;
        work.charge(self, 24)?;
        if body.coroutine.is_some() || body.tainted_by_errors.is_some() || body.spread_arg.is_some()
        {
            return Err(self.retained_error("retained original Body metadata is unsupported"));
        }
        for block in body.basic_blocks.iter() {
            work.charge(self, block.statements.len())?;
        }
        bodies
            .values()
            .find(|b| std::ptr::eq(b.as_ref(), body))
            .cloned()
            .ok_or("retained view requires current original Body".into())
    }

    pub(super) fn validate_mutable_retained(
        &self,
        id: usize,
        backing: &super::mutable_u16::Backing,
    ) -> Result<(), String> {
        let Phase::Retained {
            certificate,
            carrier,
            offset,
            length,
            metadata,
        } = &backing.phase
        else {
            return Ok(());
        };
        let mut work = Work(0);
        work.charge(self, metadata.len().saturating_mul(3))?;
        let issued = self.mutable_retained.borrow();
        let origin = issued
            .get(*certificate)
            .ok_or("retained view certificate is not issued")?;
        let body = origin
            .body
            .upgrade()
            .ok_or("retained view original Body expired")?;
        self.retained_body(&body, &mut Work(0))?;
        let terminator = body
            .basic_blocks
            .get(origin.call)
            .ok_or("retained view original Call missing")?
            .terminator();
        if origin.backing != id
            || origin.allocation != backing.allocation
            || origin.original != backing.certificate
            || origin.generation != backing.generation
            || (*carrier != origin.intermediate && *carrier != origin.carrier)
            || origin.occurrence != std::ptr::from_ref(&terminator.kind) as usize
            || !matches!(&terminator.kind, TerminatorKind::Call {destination, target: Some(_), ..}
                if destination.projection.is_empty()
                    && destination.local.as_usize() == origin.intermediate)
            || backing.interval.is_some()
            || backing.hierarchy.is_some()
        {
            return Err(self.retained_error("retained view original identity or phase differs"));
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for term in [offset, length, &origin.start, &origin.end, &origin.capacity] {
            if !term.belongs_to(&self.terms) || term.sort() != &Sort::BitVec(bits) {
                return Err(self.retained_error("retained view terms have wrong type or Context"));
            }
        }
        if backing.length.integer()?.0 != origin.capacity
            || *offset != origin.start
            || *length
                != self
                    .terms
                    .apply(Op::BvSub, &[origin.end.clone(), origin.start.clone()])?
        {
            return Err(self.retained_error("retained view differs from its issued extent"));
        }
        let original = self
            .mutable_owner_certificate(backing.certificate)?
            .original;
        if !self.mutable_owner_type(
            body.local_decls
                .get(Local::from_usize(*carrier))
                .ok_or("retained view carrier declaration missing")?
                .ty,
            original,
        ) {
            return Err(self.retained_error("retained view carrier original type differs"));
        }
        for &(local, occurrence) in metadata {
            let statement = self.retained_original_statement(&body, occurrence, &mut work)?;
            if !matches!(statement, StatementKind::Assign(pair)
                if pair.0.projection.is_empty() && pair.0.local.as_usize() == local
                    && matches!(&pair.1,
                        Rvalue::Ref(_, BorrowKind::Shared, p)
                        | Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::FakeForPtrMetadata, p)
                        if p.local.as_usize() == origin.carrier
                            && p.projection.as_ref() == [ProjectionElem::Deref]))
            {
                return Err(self.retained_error("retained metadata original occurrence differs"));
            }
        }
        Ok(())
    }

    pub(super) fn mutable_retained_frame(
        &self,
        body: &Body<'tcx>,
        id: usize,
        memory: &Memory,
    ) -> Result<(), String> {
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("retained backing identity is not issued")?;
        self.validate_mutable_retained(id, backing)?;
        let Phase::Retained {
            certificate,
            carrier,
            ..
        } = &backing.phase
        else {
            return Err(self.retained_error("retained view lacks local owner phase"));
        };
        let issued = self.mutable_retained.borrow();
        let origin = &issued[*certificate];
        if *carrier != origin.carrier
            || !origin
                .body
                .upgrade()
                .is_some_and(|held| std::ptr::eq(held.as_ref(), body))
        {
            return Err(self.retained_error("retained view needs its current same-frame carrier"));
        }
        Ok(())
    }

    // Caller has already authenticated this immutable Body. Pay the actual occurrence
    // walk without repeating unrelated declaration/registry validation for each witness.
    fn retained_original_statement<'a>(
        &self,
        body: &'a Body<'tcx>,
        occurrence: usize,
        work: &mut Work,
    ) -> Result<&'a StatementKind<'tcx>, String> {
        work.charge(self, body.basic_blocks.len())?;
        for block in body.basic_blocks.iter() {
            work.charge(self, block.statements.len())?;
            if let Some(statement) = block
                .statements
                .iter()
                .find(|s| std::ptr::from_ref(&s.kind) as usize == occurrence)
            {
                return Ok(&statement.kind);
            }
        }
        Err(self.retained_error("retained metadata original occurrence is unavailable"))
    }

    // A backing/frame certificate authenticates storage, never an arbitrary operand.
    pub(super) fn mutable_retained_operand(
        &self,
        body: &Body<'tcx>,
        state: &State,
        local: usize,
        id: usize,
        role: &MutableU16Role,
    ) -> Result<(), String> {
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let Phase::Retained {
            carrier, metadata, ..
        } = &backing.phase
        else {
            return Ok(());
        };
        self.mutable_retained_frame(body, id, &state.memory)?;
        self.check_local_initialization(state, local, &[])?;
        if state.addresses[local].is_some() {
            return Err(self.retained_error("retained operand cannot use addressed carrier"));
        }
        let valid = match role {
            MutableU16Role::Child { generation } => {
                local == *carrier && *generation == backing.generation
            }
            MutableU16Role::ChildMetadata { generation } => {
                *generation == backing.generation && metadata.iter().any(|&(at, _)| at == local)
            }
            MutableU16Role::Root
            | MutableU16Role::Metadata { .. }
            | MutableU16Role::Ghost { .. }
            | MutableU16Role::HierarchyChild { .. }
            | MutableU16Role::HierarchyMetadata { .. } => false,
        };
        if !valid {
            return Err(self.retained_error("retained operand lacks current carrier witness"));
        }
        Ok(())
    }

    fn retained_exclusive_receiver(&self, state: &State, receiver: usize) -> Result<(), String> {
        let mut work = Work(0);
        work.charge(self, state.locals.len())?;
        work.charge(self, state.memory.owned_regions.len())?;
        work.charge(self, state.memory.mutable_u16.len().saturating_mul(5))?;
        work.charge(self, state.memory.storage_slots())?;
        work.charge(self, state.missing_places.entries().len())?;
        let mut consumed = std::collections::BTreeSet::new();
        for (owner, missing) in state.missing_places.entries() {
            if missing.is_empty() {
                work.charge(self, 1)?;
                consumed.insert(*owner);
            }
        }
        for local in 0..state.locals.len() {
            work.charge(self, 1)?;
            if consumed.contains(&local) {
                continue;
            }
            let value = if let Some(allocation) = state.addresses[local] {
                state.memory.get(allocation).and_then(Option::as_ref)
            } else {
                state.locals[local].as_ref()
            };
            let Some(value) = value else {
                continue;
            };
            if local == receiver {
                if state.addresses[local].is_some() {
                    return Err(self.retained_error("retained receiver cannot be addressed"));
                }
                continue;
            }
            if matches!(
                value,
                Value::MutableU16 {
                    role: MutableU16Role::Root,
                    ..
                }
            ) {
                continue;
            }
            if self.mutable_u16_contains_with_work(value, &state.memory, Some(&mut work))? {
                return Err(self.retained_error("retained issuance has another executable carrier"));
            }
        }
        work.charge(self, state.memory.len())?;
        for value in state.memory.iter().flatten() {
            if matches!(
                value,
                Value::MutableU16 {
                    role: MutableU16Role::Root,
                    ..
                }
            ) {
                continue;
            }
            if self.mutable_u16_contains_with_work(value, &state.memory, Some(&mut work))? {
                return Err(
                    self.retained_error("retained issuance has a stored executable carrier")
                );
            }
        }
        work.charge(self, state.memory.owned_regions.len())?;
        for region in state.memory.owned_regions.iter() {
            if let Some(value) = &region.payload
                && self.mutable_u16_contains_with_work(value, &state.memory, Some(&mut work))?
            {
                return Err(self.retained_error("retained issuance has an owned stored carrier"));
            }
        }
        #[cfg(test)]
        println!("retained paid exclusive receiver nodes={}", work.0);
        Ok(())
    }

    pub(super) fn mutable_retained_shared_stage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        let (source, fake) = match value {
            Rvalue::Ref(_, BorrowKind::Shared, source) => (source, false),
            Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::FakeForPtrMetadata, source) => {
                (source, true)
            }
            _ => return Ok(false),
        };
        let Ok(Value::MutableU16 { id, role }) = self.raw_local(state, source.local.as_usize())
        else {
            return Ok(false);
        };
        if !matches!(state.memory.mutable_u16[id].phase, Phase::Retained { .. }) {
            return Ok(false);
        }
        state.flow.require_unarmed()?;
        self.mutable_retained_operand(body, state, source.local.as_usize(), id, &role)?;
        let original = self
            .mutable_owner_certificate(state.memory.mutable_u16[id].certificate)?
            .original;
        if !matches!(role, MutableU16Role::Child { .. })
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || state.addresses[destination.local.as_usize()].is_some()
            || !match body.local_decls[destination.local].ty.kind() {
                ty::Ref(_, inner, rustc_hir::Mutability::Not) if !fake => {
                    matches!(inner.kind(), ty::Slice(element) if *element == original)
                }
                ty::RawPtr(inner, rustc_hir::Mutability::Not) if fake => {
                    matches!(inner.kind(), ty::Slice(element) if *element == original)
                }
                _ => false,
            }
        {
            return Err(self.retained_error("retained readonly witness requires exact shared view"));
        }
        let mut work = Work(0);
        let statement = self.retained_original_statement(
            body,
            std::ptr::from_ref(occurrence) as usize,
            &mut work,
        )?;
        if !matches!(statement, StatementKind::Assign(pair)
            if pair.0 == destination && std::ptr::eq(&pair.1, value))
        {
            return Err(self.retained_error("retained shared view lacks actual assignment"));
        }
        work.charge(self, state.memory.owned_regions.len())?;
        work.charge(self, state.memory.mutable_u16.len().saturating_mul(5))?;
        if state.memory.storage_slots().saturating_add(2) > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained metadata exceeds existing storage budget".into(),
            ));
        }
        work.charge(self, state.missing_places.entries().len())?;
        let consumed = state
            .missing_places
            .entries()
            .iter()
            .filter_map(|(owner, missing)| missing.is_empty().then_some(*owner))
            .collect::<std::collections::BTreeSet<_>>();
        let generation = state.memory.mutable_u16[id].generation;
        // Bound the actual descriptor detach, witness copy/filter and new pair publication
        // before Rc::make_mut can clone the branch-local backing vector.
        work.charge(self, state.memory.mutable_u16.len())?;
        let Phase::Retained { metadata, .. } = &state.memory.mutable_u16[id].phase else {
            unreachable!()
        };
        work.charge(self, metadata.len().saturating_mul(2).saturating_add(2))?;
        let Phase::Retained { metadata, .. } =
            &mut Rc::make_mut(&mut state.memory.mutable_u16)[id].phase
        else {
            unreachable!()
        };
        metadata.retain(|&(local, _)| {
            local != destination.local.as_usize() && !consumed.contains(&local)
        });
        metadata.push((
            destination.local.as_usize(),
            std::ptr::from_ref(occurrence) as usize,
        ));
        self.write(
            state,
            destination,
            Value::MutableU16 {
                id,
                role: MutableU16Role::ChildMetadata { generation },
            },
        )?;
        Ok(true)
    }

    pub(super) fn mutable_retained_extent(
        &self,
        id: usize,
        backing: &super::mutable_u16::Backing,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let Phase::Retained {
            certificate,
            length,
            ..
        } = &backing.phase
        else {
            return Ok(None);
        };
        self.validate_mutable_retained(id, backing)?;
        let issued = self.mutable_retained.borrow();
        let origin = &issued[*certificate];
        let ordered = self.terms.apply(
            Op::BvUnsignedLe,
            &[origin.start.clone(), origin.end.clone()],
        )?;
        let fits = self.terms.apply(
            Op::BvUnsignedLe,
            &[origin.end.clone(), origin.capacity.clone()],
        )?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let bytes = self.mutable_owner_certificate(backing.certificate)?.bytes;
        let maximum = u128::MAX >> (128 - bits);
        let maximum = if bytes == 0 {
            maximum
        } else {
            (maximum >> 1) / u128::from(bytes)
        };
        let allocation_valid = self.terms.apply(
            Op::BvUnsignedLe,
            &[
                origin.capacity.clone(),
                self.terms.bit_vector(maximum, bits)?,
            ],
        )?;
        let valid = self.terms.apply(Op::And, &[ordered, fits])?;
        let valid = self.terms.apply(Op::And, &[valid, allocation_valid])?;
        let mut denied = conditions.to_vec();
        denied.push(symbolic::not(&valid));
        if self.feasible(&denied)? {
            return Err(self.retained_error("retained view current extent is not established"));
        }
        Ok(Some(Value::Int {
            expression: length.clone(),
            bits: u32::from(self.tcx.sess.target.pointer_width),
            signed: false,
        }))
    }

    pub(super) fn mutable_retained_index(
        &self,
        id: usize,
        backing: &super::mutable_u16::Backing,
        index: Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Some(length) = self.mutable_retained_extent(id, backing, conditions)? else {
            return Ok(index);
        };
        self.memory_bounds(&index, &length, conditions)?;
        let Phase::Retained { offset, .. } = &backing.phase else {
            unreachable!()
        };
        let absolute = symbolic::binary(
            &self.terms,
            "add",
            index,
            Value::Int {
                expression: offset.clone(),
                bits: u32::from(self.tcx.sess.target.pointer_width),
                signed: false,
            },
        )?;
        self.memory_bounds(&absolute, &backing.length, conditions)?;
        Ok(absolute)
    }

    pub(super) fn mutable_retained_call(
        &mut self,
        state: &State,
        call: ChildCall<'_, 'tcx>,
    ) -> Result<Option<(BasicBlock, State)>, String> {
        let ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            site,
            ..
        } = call;
        if state.memory.mutable_u16.len() != 1
            || state.memory.mutable_hierarchy.is_some()
            || pure_comparison_templates::definition_key(instance.def_id())
                != "DefId(core::slice::index::{impl#1}::index_mut)"
            || args.len() != 2
            || !destination.projection.is_empty()
        {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        if !matches!(args[0].node, Operand::Move(_)) {
            return Err(self.retained_error("retained view requires consuming exact receiver"));
        }
        let mut work = Work(0);
        let body_rc = self.retained_body(body, &mut work)?;
        let Some(target) = target else {
            return Ok(None);
        };
        let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
            return Ok(None);
        };
        let Ok(Value::MutableU16 {
            id,
            role: MutableU16Role::Child { generation },
        }) = self.raw_local(state, source.local.as_usize())
        else {
            return Ok(None);
        };
        let next_block = body
            .basic_blocks
            .get(target)
            .ok_or("retained normal target is unavailable")?;
        work.charge(self, next_block.statements.len())?;
        let mut candidate = None;
        let mut observed = false;
        for statement in &next_block.statements {
            let StatementKind::Assign(pair) = &statement.kind else {
                continue;
            };
            match &pair.1 {
                Rvalue::Ref(_, BorrowKind::Mut { .. }, p)
                    if p.local == destination.local
                        && p.projection.as_ref() == [ProjectionElem::Deref]
                        && pair.0.projection.is_empty() =>
                {
                    candidate = Some((pair.0.local, std::ptr::from_ref(&statement.kind) as usize));
                }
                Rvalue::Ref(_, BorrowKind::Shared, p)
                    if candidate.is_some_and(|(carrier, _)| p.local == carrier)
                        && p.projection.as_ref() == [ProjectionElem::Deref] =>
                {
                    observed = true;
                }
                _ => {}
            }
        }
        // Exact immediate handoff stays in the existing function interval protocol.
        let Some((carrier, stage)) = candidate.filter(|_| observed) else {
            return Ok(None);
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let original = self
            .mutable_owner_certificate(backing.certificate)?
            .original;
        if self.specification(instance)?.is_some()
            || !self.configured_contracts(instance)?.is_empty()
        {
            return Err(self.retained_error(
                "retained Range configured contracts require separate observations",
            ));
        }
        if !self.certify_retained_range_family(instance, original)? {
            return Ok(None);
        }
        self.mutable_u16_staging_tip(body, state, source.local.as_usize(), id, generation)?;

        let terminator = body
            .basic_blocks
            .get(block)
            .ok_or("retained actual Call block is unavailable")?
            .terminator();
        let TerminatorKind::Call {
            func,
            args: actual,
            destination: actual_dest,
            target: actual_target,
            ..
        } = &terminator.kind
        else {
            return Err("retained view requires actual Call".into());
        };
        let ty::FnDef(def, generic) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("retained view original FnDef missing".into());
        };
        if self.resolve_function_item(*def, generic.skip_binder())? != instance
            || !std::ptr::eq(actual.as_ref(), args)
            || *actual_dest != destination
            || *actual_target != Some(target)
            || !source.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || carrier.as_usize() <= body.arg_count
            || carrier == destination.local
            || state.addresses[destination.local.as_usize()].is_some()
            || state.addresses[carrier.as_usize()].is_some()
            || !self.mutable_owner_type(body.local_decls[carrier].ty, original)
            || !self.mutable_owner_type(body.local_decls[destination.local].ty, original)
            || backing.interval.is_some()
            || backing.hierarchy.is_some()
        {
            return Err(self.retained_error("retained view actual Call or private type differs"));
        }
        if state.memory.storage_slots().saturating_add(8) > MAX_INPUT_VALUES
            || self
                .mutable_retained
                .borrow()
                .len()
                .saturating_add(self.mutable_u16_staging.borrow().len())
                .saturating_add(self.mutable_u16_frames.borrow().len())
                >= MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "retained view exceeds existing storage/certificate budget".into(),
            ));
        }
        self.retained_exclusive_receiver(state, source.local.as_usize())?;
        let allocation = backing.allocation;
        let certificate = backing.certificate;
        let capacity = backing.length.clone();
        let mut next = state.clone();
        if matches!(args[0].node, Operand::Move(_)) {
            next.missing_places
                .consume(source.local.as_usize(), Vec::new())?;
        }
        let range = self
            .evaluate_operand(site.0, body, &mut next, &args[1].node)?
            .materialize()?;
        let range_ty = args[1].node.ty(&body.local_decls, self.tcx);
        let ty::Adt(def, args) = range_ty.kind() else {
            return Err("retained original Range missing".into());
        };
        if self.tcx.lang_items().get(LangItem::Range) != Some(def.did())
            || args.type_at(0) != self.tcx.types.usize
            || !matches!(&range,Value::Adt{name,variant:0,fields,..}
                if *name == self.tcx.def_path_str(def.did()) && fields.len()==2)
        {
            return Err(self.retained_error("retained view original Range schema differs"));
        }
        let start = range.field("start")?;
        let end = range.field("end")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [&start, &end, &capacity] {
            let (term, width, signed) = bound.integer()?;
            if width != bits || signed || !term.belongs_to(&self.terms) {
                return Err(
                    self.retained_error("retained view endpoints require target usize Context")
                );
            }
        }
        let safe = self.terms.apply(
            Op::And,
            &[
                symbolic::binary(&self.terms, "le", start.clone(), end.clone())?.boolean()?,
                symbolic::binary(&self.terms, "le", end.clone(), capacity.clone())?.boolean()?,
            ],
        )?;
        self.require(
            site.0,
            site.1,
            &next.conditions,
            &safe,
            ObligationKind::PanicSafety,
            "retained mutable Range requires start <= end <= original length".into(),
        )?;
        next.conditions.push(safe);
        let offset = start.integer()?.0;
        let length = symbolic::binary(&self.terms, "sub", end.clone(), start.clone())?
            .integer()?
            .0;
        let mut issued = self.mutable_retained.borrow_mut();
        let key = issued.len();
        issued.push(Certificate {
            body: Rc::downgrade(&body_rc),
            backing: id,
            allocation,
            original: certificate,
            generation,
            call: block,
            occurrence: std::ptr::from_ref(&terminator.kind) as usize,
            intermediate: destination.local.as_usize(),
            carrier: carrier.as_usize(),
            stage,
            start: offset.clone(),
            end: end.integer()?.0,
            capacity: capacity.integer()?.0,
        });
        drop(issued);
        Rc::make_mut(&mut next.memory.mutable_u16)[id].phase = Phase::Retained {
            certificate: key,
            carrier: destination.local.as_usize(),
            offset,
            length,
            metadata: Vec::new(),
        };
        self.write(
            &mut next,
            destination,
            Value::MutableU16 {
                id,
                role: MutableU16Role::Child { generation },
            },
        )?;
        self.validate_mutable_retained(id, &next.memory.mutable_u16[id])?;
        self.record_model(
            instance.def_id(),
            "certified typed Range; exclusive same-frame retained lease, current backing",
        );
        #[cfg(test)]
        println!("retained paid Call nodes={}", work.0);
        Ok(Some((target, next)))
    }

    pub(super) fn mutable_retained_stage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Ok(false);
        };
        let Ok(Value::MutableU16 {
            id,
            role: MutableU16Role::Child { generation },
        }) = self.raw_local(state, source.local.as_usize())
        else {
            return Ok(false);
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let Phase::Retained {
            certificate,
            carrier,
            ..
        } = &backing.phase
        else {
            return Ok(false);
        };
        state.flow.require_unarmed()?;
        self.validate_mutable_retained(id, backing)?;
        let issued = self.mutable_retained.borrow();
        let origin = &issued[*certificate];
        if *carrier != origin.intermediate
            || source.local.as_usize() != origin.intermediate
            || destination.local.as_usize() != origin.carrier
            || !destination.projection.is_empty()
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || origin.stage != std::ptr::from_ref(occurrence) as usize
            || !origin
                .body
                .upgrade()
                .is_some_and(|held| std::ptr::eq(held.as_ref(), body))
            || generation != backing.generation
        {
            return Err(
                self.retained_error("retained view reborrow requires exact current carrier")
            );
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])?;
        let new_carrier = origin.carrier;
        drop(issued);
        state
            .missing_places
            .consume(source.local.as_usize(), Vec::new())?;
        let Phase::Retained { carrier, .. } =
            &mut Rc::make_mut(&mut state.memory.mutable_u16)[id].phase
        else {
            unreachable!()
        };
        *carrier = new_carrier;
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

    pub(super) fn mutable_retained_release(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        local: Local,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<(), String> {
        let mut work = Work(0);
        work.charge(self, state.memory.mutable_u16.len())?;
        for id in 0..state.memory.mutable_u16.len() {
            let backing = &state.memory.mutable_u16[id];
            let Phase::Retained { carrier, .. } = &backing.phase else {
                continue;
            };
            if *carrier != local.as_usize() {
                continue;
            }
            state.flow.require_unarmed()?;
            self.retained_body(body, &mut Work(0))?;
            self.mutable_retained_frame(body, id, &state.memory)?;
            work.charge(self, body.basic_blocks.len())?;
            let mut original_occurrence = false;
            for block in body.basic_blocks.iter() {
                work.charge(self, block.statements.len())?;
                if block
                    .statements
                    .iter()
                    .any(|s| std::ptr::eq(&s.kind, occurrence))
                {
                    original_occurrence = true;
                    break;
                }
            }
            if !original_occurrence
                || !matches!(occurrence,StatementKind::StorageDead(dead) if *dead==local)
            {
                return Err(self.retained_error("retained release needs original StorageDead"));
            }
            #[cfg(test)]
            println!("retained paid endpoint lookup nodes={}", work.0);
            // Runtime carrier inventory is a separate complete bounded service. This meter
            // never resets application steps or Armed fees; both service payments remain.
            let mut work = Work(0);
            work.charge(self, state.locals.len())?;
            work.charge(self, state.memory.owned_regions.len())?;
            work.charge(self, state.memory.mutable_u16.len().saturating_mul(3))?;
            work.charge(self, state.memory.storage_slots())?;
            work.charge(self, state.missing_places.entries().len())?;
            let mut consumed = std::collections::BTreeSet::new();
            for (owner, missing) in state.missing_places.entries() {
                if missing.is_empty() {
                    work.charge(self, 1)?;
                    consumed.insert(*owner);
                }
            }
            for other in 0..state.locals.len() {
                work.charge(self, 1)?;
                if other == local.as_usize() || consumed.contains(&other) {
                    continue;
                }
                let current = if let Some(allocation) = state.addresses[other] {
                    state.memory.get(allocation).and_then(Option::as_ref)
                } else {
                    state.locals[other].as_ref()
                };
                let Some(value) = current else {
                    continue;
                };
                if matches!(
                    value,
                    Value::MutableU16 {
                        role: MutableU16Role::Root,
                        ..
                    }
                ) {
                    continue;
                }
                if self.mutable_u16_contains_with_work(value, &state.memory, Some(&mut work))? {
                    return Err(self
                        .retained_error("retained release has another executable child carrier"));
                }
            }
            state.missing_places.consume(local.as_usize(), Vec::new())?;
            let current = &mut Rc::make_mut(&mut state.memory.mutable_u16)[id];
            current.generation = current
                .generation
                .checked_add(1)
                .ok_or("retained release generation overflow")?;
            current.phase = Phase::Idle;
            #[cfg(test)]
            println!("retained paid Release nodes={}", work.0);
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "mutable_reborrows_probe.rs"]
mod probe;
