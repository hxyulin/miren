//! Checked single nested whole-u16 child hierarchy with persistent generation and epoch.
use super::*;
use std::rc::Rc;

const ISSUANCE_ENABLED: bool = true;
const INTEGER_HIERARCHY_ENABLED: bool = true;
const DORMANT_CALLS_ENABLED: bool = true;

fn integer_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    INTEGER_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_INTEGER_HIERARCHY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestIntegerHierarchy(bool);

#[cfg(test)]
impl TestIntegerHierarchy {
    fn enable() -> Self {
        Self(TEST_INTEGER_HIERARCHY.with(|value| value.replace(true)))
    }
}

#[cfg(test)]
impl Drop for TestIntegerHierarchy {
    fn drop(&mut self) {
        TEST_INTEGER_HIERARCHY.with(|value| value.set(self.0));
    }
}

fn issuance_enabled() -> bool {
    #[cfg(test)]
    if TEST_ISSUANCE.with(std::cell::Cell::get) {
        return true;
    }
    ISSUANCE_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_ISSUANCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestIssuance(bool);

#[cfg(test)]
impl TestIssuance {
    fn enable() -> Self {
        Self(TEST_ISSUANCE.with(|value| value.replace(true)))
    }
}

#[cfg(test)]
impl Drop for TestIssuance {
    fn drop(&mut self) {
        TEST_ISSUANCE.with(|value| value.set(self.0));
    }
}

#[derive(Clone, Debug)]
struct Origin {
    certificate: usize,
    allocation: usize,
    capacity: Value,
    data_context: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Owner {
    lease: u64,
    parent: u64,
    frames: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Tip {
    frame: usize,
    statement: usize,
    local: usize,
}

#[derive(Debug)]
enum TransitionError {
    Semantics(String),
    Resource(&'static str),
}

impl From<String> for TransitionError {
    fn from(reason: String) -> Self {
        Self::Semantics(reason)
    }
}

impl From<&str> for TransitionError {
    fn from(reason: &str) -> Self {
        Self::Semantics(reason.into())
    }
}

#[derive(Clone, Debug)]
struct Pending {
    lease: u64,
    parent: u64,
    tip: Tip,
}

#[derive(Clone, Debug)]
pub(super) struct Hierarchy {
    origin: Rc<Origin>,
    issued: u64,
    epoch: u64,
    owners: Vec<Owner>,
    pending: Option<Pending>,
}

impl Hierarchy {
    pub(super) fn role_valid(&self, role: &symbolic::MutableU16Role, initialized: bool) -> bool {
        use symbolic::MutableU16Role;
        match role {
            MutableU16Role::Root => {
                if initialized {
                    self.access(0).is_ok()
                } else {
                    self.lifetime(0).is_ok()
                }
            }
            MutableU16Role::HierarchyChild { lease } => {
                if initialized {
                    self.access(*lease).is_ok()
                } else {
                    self.lifetime(*lease).is_ok()
                }
            }
            MutableU16Role::HierarchyMetadata { lease, epoch } => self
                .observe(Metadata {
                    lease: *lease,
                    epoch: *epoch,
                })
                .is_ok(),
            MutableU16Role::Ghost { .. } => true,
            MutableU16Role::Metadata { .. }
            | MutableU16Role::Child { .. }
            | MutableU16Role::ChildMetadata { .. } => false,
        }
    }

    pub(super) fn metadata_epoch(&self, lease: u64) -> Result<u64, String> {
        Ok(self.metadata(lease)?.epoch)
    }

    pub(super) fn storage_slots(&self) -> usize {
        // Dormant origin and counters persist even when the owner stack is empty.
        6usize
            .saturating_add(
                self.owners
                    .iter()
                    .map(|owner| 2 + owner.frames.len())
                    .sum::<usize>(),
            )
            .saturating_add(usize::from(self.pending.is_some()) * 5)
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_hierarchy_disabled_backing(
        &self,
        backing: &super::mutable_u16::Backing,
    ) -> Result<(), String> {
        let Some(hierarchy) = &backing.hierarchy else {
            return Ok(());
        };
        if hierarchy.owners.len() > 2 {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "hierarchy exceeds the single nested-child scope".into(),
            ));
        }
        if backing.interval.is_some()
            || backing.phase != super::mutable_u16_children::Phase::Idle
            || hierarchy.origin.certificate != backing.certificate
            || hierarchy.origin.allocation != backing.allocation
            || hierarchy.origin.capacity.integer()? != backing.length.integer()?
            || !hierarchy.origin.data_context.belongs_to(&self.terms)
            || !backing.data.belongs_to(&self.terms)
            || hierarchy.origin.data_context.sort() != backing.data.sort()
            || !self.mutable_hierarchy_integer_element(
                self.mutable_interval_element(backing.certificate)?,
            )
            || hierarchy.issued < backing.generation
        {
            return Err("disabled hierarchy original owner differs".into());
        }
        let mut parent = 0;
        let mut depth = 0usize;
        for owner in &hierarchy.owners {
            depth = depth.saturating_add(owner.frames.len());
            if owner.lease == 0
                || owner.lease > hierarchy.issued
                || owner.lease <= parent
                || owner.parent != parent
                || owner.frames.is_empty()
                || depth > MAX_INPUT_DEPTH
                || owner.frames.iter().any(|id| {
                    self.mutable_u16_frames
                        .borrow()
                        .get(*id)
                        .is_none_or(|weak| weak.upgrade().is_none())
                })
            {
                return Err("disabled hierarchy lineage differs".into());
            }
            parent = owner.lease;
        }
        if hierarchy.pending.as_ref().is_some_and(|pending| {
            pending.lease != hierarchy.issued
                || pending.lease <= pending.parent
                || pending.parent != parent
                || hierarchy.epoch == 0
                || pending.tip.local == 0
                || pending.tip.statement == 0
                || self
                    .mutable_u16_frames
                    .borrow()
                    .get(pending.tip.frame)
                    .is_none_or(|weak| weak.upgrade().is_none())
        }) {
            return Err("disabled hierarchy pending identity differs".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn mutable_hierarchy_source(
        &self,
        body: &Body<'tcx>,
        state: &State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<(), String> {
        let mut work = body
            .local_decls
            .len()
            .saturating_add(body.basic_blocks.len());
        if work > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy compiler facts exceed existing work budget".into(),
            ));
        }
        if body.coroutine.is_some() || body.spread_arg.is_some() || body.tainted_by_errors.is_some()
        {
            return Err("hierarchy original Body is outside bounded domain".into());
        }
        let mut actual = false;
        for block in body.basic_blocks.iter() {
            work = work.saturating_add(block.statements.len());
            if work > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "hierarchy compiler facts exceed existing work budget".into(),
                ));
            }
            actual |= block
                .statements
                .iter()
                .any(|s| std::ptr::eq(&s.kind, occurrence));
        }
        if !actual
            || !matches!(occurrence, StatementKind::Assign(assignment)
            if assignment.0 == destination && std::ptr::eq(&assignment.1, value))
        {
            return Err("hierarchy requires actual Assignment occurrence".into());
        }
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Err("hierarchy requires exact RefMut".into());
        };
        let Value::MutableU16 {
            id,
            role: symbolic::MutableU16Role::Child { generation },
        } = self.raw_local(state, source.local.as_usize())?
        else {
            return Err("hierarchy requires current Child source".into());
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let super::mutable_u16_children::Phase::Active { frames } = &backing.phase else {
            return Err("hierarchy requires active parent".into());
        };
        self.mutable_u16_frame_top(body, frames)?;
        if backing.interval.is_some()
            || backing.generation != generation
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || source.local == destination.local
            || state.addresses[destination.local.as_usize()].is_some()
            || !self.mutable_hierarchy_integer_element(
                self.mutable_interval_element(backing.certificate)?,
            )
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
        {
            return Err("hierarchy original source/type/tip differs".into());
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])
    }
}

impl<'tcx> Engine<'tcx> {
    fn mutable_hierarchy_transition_error(&self, error: TransitionError) -> String {
        match error {
            TransitionError::Semantics(reason) => {
                self.categorized_error(UnknownCategory::Semantics, reason)
            }
            TransitionError::Resource(reason) => {
                self.categorized_error(UnknownCategory::ResourceLimit, reason.into())
            }
        }
    }

    fn mutable_hierarchy_namespace(&self, memory: &Memory) -> Result<(), String> {
        let Some(id) = memory.mutable_hierarchy else {
            return Ok(());
        };
        let backing = self.mutable_u16_backing(id, memory)?;
        if backing.hierarchy.is_none() {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "hierarchy namespace has no issued backing".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn mutable_hierarchy_call(
        &mut self,
        state: &mut State,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        // Disabled routing performs no role observation, Body scan or term construction.
        if !issuance_enabled() && state.memory.mutable_hierarchy.is_none() {
            return Ok(None);
        }
        self.mutable_hierarchy_namespace(&state.memory)?;
        if state.memory.mutable_hierarchy.is_none()
            && !self.mutable_hierarchy_route(state, &call)?
        {
            return Ok(None);
        }
        if self.tcx.lang_items().get(LangItem::SliceLen) == Some(call.instance.def_id())
            || super::super::identity::is_panic_call(self.tcx, call.instance.def_id())
            || self.is_core_panic_helper(call.instance.def_id())
        {
            return Ok(None);
        }
        if DORMANT_CALLS_ENABLED
            && let Some(results) = self.mutable_hierarchy_dormant_call(state, &call)?
        {
            return Ok(Some(results));
        }
        self.mutable_hierarchy_call_transaction(state, call)
    }

    fn mutable_hierarchy_dormant_call(
        &mut self,
        state: &mut State,
        call: &super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let Some(id) = state.memory.mutable_hierarchy else {
            return Ok(None);
        };
        self.mutable_hierarchy_namespace(&state.memory)?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let before = backing
            .hierarchy
            .as_ref()
            .ok_or("dormant hierarchy missing")?
            .clone();
        if !before.owners.is_empty() || before.pending.is_some() {
            return Ok(None);
        }
        let data = backing.data.clone();
        if call.args.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "dormant hierarchy arguments exceed existing certificate budget".into(),
            ));
        }
        let instance = call.instance;
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
        {
            return Ok(None);
        }
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != call.args.len()
            || signature
                .inputs()
                .iter()
                .any(|t| !self.mutable_hierarchy_primitive(*t))
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive(signature.output()))
        {
            return Ok(None);
        }
        self.mutable_u16_body_budget(call.body)?;
        self.mutable_u16_register_current_frame(call.body)?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &call.body.basic_blocks[call.block].terminator().kind
        else {
            return Err("dormant hierarchy requires actual Call".into());
        };
        if call.body.basic_blocks[call.block].is_cleanup
            || call.site.0 != call.body.source.def_id()
            || call.site.1
                != call.body.basic_blocks[call.block]
                    .terminator()
                    .source_info
                    .span
            || args.as_ptr() != call.args.as_ptr()
            || args.len() != call.args.len()
            || *destination != call.destination
            || *target != call.target
            || target.is_none()
            || !destination.projection.is_empty()
            || destination.ty(&call.body.local_decls, self.tcx).ty != signature.output()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
            || !self.configured_contracts(instance)?.is_empty()
        {
            return Err("dormant hierarchy original Call/normal edge differs".into());
        }
        let ty::FnDef(definition, generic) = func.ty(&call.body.local_decls, self.tcx).kind()
        else {
            return Err("dormant hierarchy requires original function Item".into());
        };
        if self.resolve_function_item(*definition, generic.skip_binder())? != instance {
            return Err("dormant hierarchy selected Instance differs".into());
        }
        for (operand, original) in args.iter().zip(signature.inputs()) {
            if operand.node.ty(&call.body.local_decls, self.tcx) != *original {
                return Err("dormant hierarchy primitive original operand type differs".into());
            }
            if let Operand::Copy(place) | Operand::Move(place) = &operand.node {
                self.mutable_hierarchy_dormant_operand(call.body, state, *place, *original)?;
            }
        }
        // Body availability/schema precede existing builtin priority. No new summary is issued.
        let selected = self.instantiated_body(instance)?;
        self.mutable_u16_body_budget(&selected)?;
        if selected.arg_count != args.len()
            || selected.return_ty() != signature.output()
            || selected
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, t)| {
                    self.tcx
                        .erase_and_anonymize_regions(selected.local_decls[local].ty)
                        != *t
                })
            || selected.basic_blocks.iter().any(|block| {
                block.is_cleanup
                    || match &block.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err("dormant hierarchy selected Body/schema/unwind differs".into());
        }
        let mut values = Vec::with_capacity(args.len());
        for (arg, original) in args.iter().zip(signature.inputs()) {
            let value = self.evaluate_operand(call.site.0, call.body, state, &arg.node)?;
            self.mutable_hierarchy_primitive_value(*original, &value, &state.conditions)?;
            values.push(value);
        }
        let results = if let Some(value) =
            self.builtin(call.body, instance, &values, &values, state, call.site.1)?
        {
            vec![Return {
                value,
                conditions: state.conditions.clone(),
                memory: state.memory.clone(),
            }]
        } else {
            self.call_instance(
                instance,
                values,
                state.conditions.clone(),
                state.memory.clone(),
                call.stack,
                call.site,
            )?
        };
        for result in &results {
            self.mutable_hierarchy_primitive_value(
                signature.output(),
                &result.value,
                &result.conditions,
            )?;
            self.mutable_hierarchy_dormant_return(id, &before, &data, &result.memory)?;
        }
        Ok(Some(results))
    }

    fn mutable_hierarchy_dormant_operand(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        self.owned_field_footprint(body, place)?;
        let value = self.place(state, place)?;
        self.mutable_hierarchy_primitive_value(original, &value, &state.conditions)
    }

    fn mutable_hierarchy_primitive_value(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let valid = if original.is_unit() {
            matches!(value, Value::Unit)
                || matches!(value, Value::Tuple(fields) if fields.is_empty())
        } else if original == self.tcx.types.bool {
            matches!(value, Value::Bool(term)
                if term.belongs_to(&self.terms) && term.sort() == &Sort::Bool)
        } else if self.mutable_hierarchy_primitive(original) {
            matches!(value, Value::Int {expression,bits,signed}
                if self.integer_type(original) == Some((*bits,*signed))
                && expression.belongs_to(&self.terms) && expression.sort() == &Sort::BitVec(*bits))
        } else {
            false
        };
        if !valid {
            return Err("dormant hierarchy primitive value/type/context differs".into());
        }
        if original == self.tcx.types.char {
            self.prove_char_value(value, conditions)?;
        }
        Ok(())
    }

    fn mutable_hierarchy_dormant_return(
        &self,
        id: usize,
        before: &Hierarchy,
        data: &Term,
        memory: &Memory,
    ) -> Result<(), String> {
        self.mutable_hierarchy_namespace(memory)?;
        if memory.mutable_hierarchy != Some(id) {
            return Err("dormant primitive Return changed namespace".into());
        }
        let backing = self.mutable_u16_backing(id, memory)?;
        let returned = backing
            .hierarchy
            .as_ref()
            .ok_or("dormant Return lost hierarchy")?;
        if !Rc::ptr_eq(&returned.origin, &before.origin)
            || returned.issued < before.issued
            || returned.epoch < before.epoch
            || !returned.owners.is_empty()
            || returned.pending.is_some()
            || backing.data != *data
        {
            return Err("dormant primitive Return changed origin/counters/data/state".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_route(
        &mut self,
        state: &State,
        call: &super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<bool, String> {
        // Only original whole-u16 Root/pending-root calls may select a new namespace.
        // Routing alone never issues a grant or proves any selected body operation.
        if state.memory.mutable_u16.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy routing exceeds existing backing budget".into(),
            ));
        }
        if state
            .memory
            .mutable_u16
            .iter()
            .any(|b| b.hierarchy.is_some())
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued hierarchy lost its Memory namespace".into(),
            ));
        }
        if state.memory.mutable_u16.is_empty() || call.args.len() > MAX_INPUT_VALUES {
            return Ok(false);
        }
        let Some(original) = call.body.basic_blocks.get(call.block) else {
            return Ok(false);
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &original.terminator().kind
        else {
            return Ok(false);
        };
        if args.as_ptr() != call.args.as_ptr()
            || args.len() != call.args.len()
            || *destination != call.destination
            || *target != call.target
            || target.is_none()
            || !destination.projection.is_empty()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
        {
            return Ok(false);
        }
        let mut source = None;
        for (position, argument) in call.args.iter().enumerate() {
            let (Operand::Copy(place) | Operand::Move(place)) = argument.node else {
                continue;
            };
            let local = place.local.as_usize();
            if !place.projection.is_empty()
                || state.addresses.get(local).is_none_or(Option::is_some)
            {
                continue;
            }
            let Some(Some(Value::MutableU16 { id, role })) = state.locals.get(local) else {
                continue;
            };
            if source.is_some()
                || !matches!(
                    role,
                    symbolic::MutableU16Role::Root | symbolic::MutableU16Role::Child { .. }
                )
                || state.missing_places.check(local, &[]).is_err()
                || !self.mutable_hierarchy_integer_reference(call.body.local_decls[place.local].ty)
            {
                return Ok(false);
            }
            let backing = self.mutable_u16_backing(*id, &state.memory)?;
            if backing.interval.is_some()
                || !self.mutable_hierarchy_integer_element(
                    self.mutable_interval_element(backing.certificate)?,
                )
                || !self.mutable_u16_matches(
                    call.body.local_decls[place.local].ty,
                    *id,
                    &state.memory,
                    true,
                )?
                || self
                    .mutable_hierarchy_bootstrap(call.body, state, place, *id, role)
                    .is_err()
            {
                return Ok(false);
            }
            source = Some(position);
        }
        let Some(position) = source else {
            return Ok(false);
        };
        self.mutable_u16_body_budget(call.body)?;
        let ty::FnDef(definition, generic) = func.ty(&call.body.local_decls, self.tcx).kind()
        else {
            return Ok(false);
        };
        if *definition != call.instance.def_id()
            || self.resolve_function_item(*definition, generic.skip_binder())? != call.instance
        {
            return Ok(false);
        }
        let Some(signature) =
            self.mutable_hierarchy_routing_signature(call.instance, args.len())?
        else {
            return Ok(false);
        };
        if !self.mutable_hierarchy_integer_reference(signature.inputs()[position])
            || signature
                .inputs()
                .iter()
                .enumerate()
                .any(|(i, t)| i != position && !self.mutable_hierarchy_primitive(*t))
            || destination.ty(&call.body.local_decls, self.tcx).ty != signature.output()
            || self.specification(call.instance)?.is_some()
        {
            return Ok(false);
        }
        let selected = self.instantiated_body(call.instance)?;
        self.mutable_hierarchy_selector(&selected, position + 1)
    }

    fn mutable_hierarchy_integer_element(&self, original: Ty<'tcx>) -> bool {
        original == self.tcx.types.u16
            || (integer_hierarchy_enabled()
                && matches!(original.kind(), ty::Int(_) | ty::Uint(_))
                && original != self.tcx.types.u8)
    }

    fn mutable_hierarchy_integer_reference(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, pointee, rustc_hir::Mutability::Mut)
            if matches!(pointee.kind(), ty::Slice(element)
                if self.mutable_hierarchy_integer_element(*element)))
    }

    fn mutable_hierarchy_routing_signature(
        &self,
        instance: ty::Instance<'tcx>,
        count: usize,
    ) -> Result<Option<ty::FnSig<'tcx>>, String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::Fn
        {
            return Ok(None);
        }
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != count
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive(signature.output()))
        {
            return Ok(None);
        }
        Ok(Some(signature))
    }

    fn mutable_hierarchy_call_transaction(
        &mut self,
        state: &mut State,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        use symbolic::MutableU16Role;
        self.mutable_hierarchy_namespace(&state.memory)?;
        let super::mutable_u16_children::ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            stack,
            site,
        } = call;
        self.mutable_u16_body_budget(body)?;
        let TerminatorKind::Call {
            func,
            args: original_args,
            destination: original_destination,
            target: original_target,
            unwind,
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("hierarchy handoff requires actual Call".into());
        };
        if args.as_ptr() != original_args.as_ptr()
            || args.len() != original_args.len()
            || destination != *original_destination
            || target != *original_target
            || !matches!(func.ty(&body.local_decls, self.tcx).kind(), ty::FnDef(d, _)
                if *d == instance.def_id())
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::Fn
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || target.is_none()
            || !destination.projection.is_empty()
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
        {
            return Err("hierarchy handoff original Call/signature differs".into());
        }
        let ty::FnDef(definition, actual_args) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("hierarchy unresolved original callable".into());
        };
        if self.resolve_function_item(*definition, actual_args.skip_binder())? != instance {
            return Err("hierarchy selected Instance differs from original Call".into());
        }
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive(signature.output()))
            || destination.ty(&body.local_decls, self.tcx).ty != signature.output()
        {
            return Err("hierarchy requires synchronous primitive-return Rust Item".into());
        }
        let mut source = None;
        for (position, arg) in args.iter().enumerate() {
            if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                let value = self.raw_local(state, place.local.as_usize())?;
                if self.mutable_u16_contains(&value, &state.memory)? {
                    let Value::MutableU16 { id, role } = value else {
                        return Err("hierarchy argument contains nested authority".into());
                    };
                    if source.is_some()
                        || !place.projection.is_empty()
                        || !matches!(
                            role,
                            MutableU16Role::Root
                                | MutableU16Role::Child { .. }
                                | MutableU16Role::HierarchyChild { .. }
                        )
                    {
                        return Err(self.categorized_error(
                            UnknownCategory::Semantics,
                            "hierarchy duplicate or metadata argument".into(),
                        ));
                    }
                    self.check_local_initialization(state, place.local.as_usize(), &[])?;
                    if state.addresses[place.local.as_usize()].is_some()
                        || !self.mutable_u16_matches(
                            body.local_decls[place.local].ty,
                            id,
                            &state.memory,
                            true,
                        )?
                        || !self.mutable_u16_matches(
                            signature.inputs()[position],
                            id,
                            &state.memory,
                            true,
                        )?
                    {
                        return Err("hierarchy source original type/address differs".into());
                    }
                    source = Some((position, *place, id, role));
                }
            }
        }
        let selected = self.instantiated_body(instance)?;
        self.mutable_u16_body_budget(&selected)?;
        if selected.arg_count != args.len()
            || selected.return_ty() != signature.output()
            || selected.args_iter().zip(signature.inputs()).any(|(l, t)| {
                self.tcx
                    .erase_and_anonymize_regions(selected.local_decls[l].ty)
                    != *t
            })
            || selected.basic_blocks.iter().any(|b| {
                b.is_cleanup
                    || match &b.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err("hierarchy selected Body/schema/unwind differs".into());
        }
        let Some((position, place, id, role)) = source else {
            if signature
                .inputs()
                .iter()
                .any(|t| !self.mutable_hierarchy_primitive(*t))
            {
                return Err("hierarchy scalar frame has nonprimitive argument".into());
            }
            return self.mutable_hierarchy_scalar_call(
                state,
                &selected,
                super::mutable_u16_children::ChildCall {
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
        if signature
            .inputs()
            .iter()
            .enumerate()
            .any(|(i, t)| i != position && !self.mutable_hierarchy_primitive(*t))
            || !self.mutable_hierarchy_integer_element(
                self.mutable_interval_element(state.memory.mutable_u16[id].certificate)?,
            )
        {
            return Err("hierarchy source is not original whole u16".into());
        }
        if matches!(role, MutableU16Role::Root) && matches!(args[position].node, Operand::Move(_)) {
            return Err("hierarchy moved original Root is deferred".into());
        }
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        if backing.interval.is_some() {
            return Err("hierarchy intervals are deferred".into());
        }
        let mut hierarchy = if let Some(h) = &backing.hierarchy {
            h.clone()
        } else {
            if !self.mutable_hierarchy_selector(&selected, position + 1)? {
                return Ok(None);
            }
            self.mutable_hierarchy_bootstrap(body, state, place, id, &role)?;
            Hierarchy::dormant(backing)
        };
        let caller_frame = self.mutable_u16_register_current_frame(body)?;
        let tip = Tip {
            frame: caller_frame,
            statement: std::ptr::from_ref(&body.basic_blocks[block].terminator().kind) as usize,
            local: place.local.as_usize(),
        };
        let lease = match role {
            MutableU16Role::Root => hierarchy
                .issue(
                    0,
                    tip.clone(),
                    state
                        .memory
                        .storage_slots()
                        .saturating_add(usize::from(backing.hierarchy.is_none()) * 6),
                )
                .map_err(|error| self.mutable_hierarchy_transition_error(error))?,
            MutableU16Role::Child { .. } => {
                if backing.hierarchy.is_some() {
                    return Err("legacy child cannot migrate".into());
                }
                hierarchy
                    .issue(
                        0,
                        tip.clone(),
                        state
                            .memory
                            .storage_slots()
                            .saturating_add(hierarchy.storage_slots()),
                    )
                    .map_err(|error| self.mutable_hierarchy_transition_error(error))?
            }
            MutableU16Role::HierarchyChild { lease } => {
                if let Some(pending) = &hierarchy.pending {
                    if pending.lease != lease
                        || pending.tip.local != place.local.as_usize()
                        || pending.tip.frame != caller_frame
                    {
                        return Err("hierarchy Call did not use current pending tip".into());
                    }
                    self.mutable_hierarchy_tip(&hierarchy, body)?;
                    let pending = hierarchy
                        .pending
                        .as_mut()
                        .ok_or("pending tip disappeared")?;
                    pending.tip = tip.clone();
                    lease
                } else {
                    let owner = hierarchy.owners.last().ok_or("hierarchy owner missing")?;
                    self.mutable_u16_frame_top(body, &owner.frames)?;
                    hierarchy
                        .issue(lease, tip.clone(), state.memory.storage_slots())
                        .map_err(|error| self.mutable_hierarchy_transition_error(error))?
                }
            }
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::HierarchyMetadata { .. }
            | MutableU16Role::Ghost { .. } => {
                return Err("hierarchy source lacks owner grant".into());
            }
        };
        let selected_frame = self.mutable_u16_register_frame(&selected)?;
        let ticket = hierarchy
            .enter(
                &tip,
                selected_frame,
                state
                    .memory
                    .storage_slots()
                    .saturating_add(usize::from(backing.hierarchy.is_none()) * 6),
            )
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?;
        self.mutable_hierarchy_charge(state, id, &hierarchy)?;
        // Source/selected/duplicate checks precede every sequential argument effect.
        let mut values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            if i == position {
                if matches!(arg.node, Operand::Move(_)) {
                    state
                        .missing_places
                        .consume(place.local.as_usize(), Vec::new())?;
                }
                values.push(Value::MutableU16 {
                    id,
                    role: MutableU16Role::HierarchyChild { lease },
                });
            } else {
                values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
            }
        }
        for (original, value) in signature.inputs().iter().zip(&values) {
            if *original == self.tcx.types.char {
                self.prove_char_value(value, &state.conditions)?;
            }
        }
        let backing = &mut Rc::make_mut(&mut state.memory.mutable_u16)[id];
        backing.phase = super::mutable_u16_children::Phase::Idle;
        backing.hierarchy = Some(hierarchy);
        state.memory.mutable_hierarchy = Some(id);
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        for result in &mut results {
            if signature.output() == self.tcx.types.char {
                self.prove_char_value(&result.value, &result.conditions)?;
            }
            if result.memory.mutable_hierarchy != Some(id) {
                return Err("returned hierarchy mode disappeared or changed owner".into());
            }
            self.mutable_u16_backing(id, &result.memory)?;
            if self.mutable_u16_contains(&result.value, &result.memory)? {
                return Err("hierarchy returned executable role".into());
            }
            let h = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("returned hierarchy disappeared")?;
            h.release(&ticket)?;
            // Original masks and current updated data remain untouched on release.
        }
        Ok(Some(results))
    }

    fn mutable_hierarchy_primitive(&self, original: Ty<'tcx>) -> bool {
        matches!(
            original.kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)
        )
    }

    fn mutable_hierarchy_selector(
        &self,
        selected: &Body<'tcx>,
        argument: usize,
    ) -> Result<bool, String> {
        self.mutable_u16_body_budget(selected)?;
        let root = rustc_middle::mir::Local::from_usize(argument);
        if argument == 0
            || argument > selected.arg_count
            || selected
                .local_decls
                .get(root)
                .is_none_or(|d| !self.mutable_hierarchy_integer_reference(d.ty))
        {
            return Ok(false);
        }
        for block in selected.basic_blocks.iter() {
            let mut lineage = std::collections::BTreeSet::from([root]);
            for statement in &block.statements {
                match &statement.kind {
                    StatementKind::Assign(a) if a.0.projection.is_empty() => {
                        let follows = matches!(&a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, p)
                            if p.projection.as_ref() == [ProjectionElem::Deref]
                            && lineage.contains(&p.local)
                            && selected.local_decls[p.local].ty == selected.local_decls[root].ty
                            && selected.local_decls[a.0.local].ty == selected.local_decls[root].ty
                            && self.mutable_hierarchy_integer_reference(
                                selected.local_decls[p.local].ty)
                            && self.mutable_hierarchy_integer_reference(
                                selected.local_decls[a.0.local].ty));
                        lineage.remove(&a.0.local);
                        if follows {
                            lineage.insert(a.0.local);
                        }
                    }
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                        lineage.remove(local);
                    }
                    _ => {}
                }
            }
            let TerminatorKind::Call {
                func,
                args,
                target: Some(_),
                unwind,
                ..
            } = &block.terminator().kind
            else {
                continue;
            };
            if !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable) {
                continue;
            }
            let ty::FnDef(definition, generic) = func.ty(&selected.local_decls, self.tcx).kind()
            else {
                continue;
            };
            let instance = self.resolve_function_item(*definition, generic.skip_binder())?;
            let Some(signature) = self.mutable_hierarchy_routing_signature(instance, args.len())?
            else {
                continue;
            };
            let mut receiver = None;
            let mut eligible = true;
            for (position, (operand, original)) in args.iter().zip(signature.inputs()).enumerate() {
                if self.mutable_hierarchy_integer_reference(*original) {
                    let follows = matches!(operand.node, Operand::Copy(p) | Operand::Move(p)
                        if p.projection.is_empty() && lineage.contains(&p.local)
                        && *original == selected.local_decls[root].ty
                        && selected.local_decls[p.local].ty == selected.local_decls[root].ty
                        && self.mutable_hierarchy_integer_reference(
                                selected.local_decls[p.local].ty));
                    if !follows || receiver.replace(position).is_some() {
                        eligible = false;
                    }
                } else if !self.mutable_hierarchy_primitive(*original) {
                    eligible = false;
                }
            }
            if eligible && receiver.is_some() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn mutable_u16_register_current_frame(&self, body: &Body<'tcx>) -> Result<usize, String> {
        let original = self
            .bodies
            .borrow()
            .values()
            .find(|candidate| std::ptr::eq(candidate.as_ref(), body))
            .cloned()
            .ok_or("hierarchy current instantiated Body unavailable")?;
        self.mutable_u16_register_frame(&original)
    }

    fn mutable_hierarchy_charge(
        &self,
        state: &State,
        id: usize,
        next: &Hierarchy,
    ) -> Result<(), String> {
        let old = state.memory.mutable_u16[id]
            .hierarchy
            .as_ref()
            .map_or(0, Hierarchy::storage_slots);
        if state
            .memory
            .storage_slots()
            .saturating_sub(old)
            .saturating_add(next.storage_slots())
            .saturating_add(usize::from(state.memory.mutable_hierarchy.is_none()))
            > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy exceeds existing combined storage budget".into(),
            ));
        }
        Ok(())
    }

    fn mutable_hierarchy_tip(
        &self,
        hierarchy: &Hierarchy,
        body: &Body<'tcx>,
    ) -> Result<(), String> {
        let tip = &hierarchy
            .pending
            .as_ref()
            .ok_or("pending hierarchy missing")?
            .tip;
        self.mutable_u16_frame_top(body, &[tip.frame])?;
        self.mutable_u16_body_budget(body)?;
        if !body.basic_blocks.iter().any(|b| {
            b.statements
                .iter()
                .any(|s| std::ptr::from_ref(&s.kind) as usize == tip.statement)
        }) {
            return Err("hierarchy pending occurrence not in current Body".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_bootstrap(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        id: usize,
        role: &symbolic::MutableU16Role,
    ) -> Result<(), String> {
        match role {
            symbolic::MutableU16Role::Root => self.mutable_u16_role_live(id, role, &state.memory),
            symbolic::MutableU16Role::Child { generation } => {
                self.mutable_u16_staging_tip(body, state, place.local.as_usize(), id, *generation)?;
                let backing = &state.memory.mutable_u16[id];
                let super::mutable_u16_children::Phase::Pending { certificate } = backing.phase
                else {
                    return Err("bootstrap is not original pending root handoff".into());
                };
                let source = self.mutable_u16_original_staging_source(certificate, body)?;
                self.check_local_initialization(state, source, &[])?;
                if !matches!(self.raw_local(state, source)?, Value::MutableU16 { id: other,
                    role: symbolic::MutableU16Role::Root } if other == id)
                {
                    return Err("legacy active child cannot bootstrap hierarchy".into());
                }
                Ok(())
            }
            symbolic::MutableU16Role::Metadata { .. }
            | symbolic::MutableU16Role::ChildMetadata { .. }
            | symbolic::MutableU16Role::HierarchyChild { .. }
            | symbolic::MutableU16Role::HierarchyMetadata { .. }
            | symbolic::MutableU16Role::Ghost { .. } => {
                Err("bootstrap source is not original root handoff".into())
            }
        }
    }
}

impl Hierarchy {
    fn dormant(backing: &super::mutable_u16::Backing) -> Self {
        Self {
            origin: Rc::new(Origin {
                certificate: backing.certificate,
                allocation: backing.allocation,
                capacity: backing.length.clone(),
                data_context: backing.data.clone(),
            }),
            issued: backing.generation,
            epoch: 0,
            owners: Vec::new(),
            pending: None,
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_hierarchy_stage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        if !issuance_enabled() && state.memory.mutable_hierarchy.is_none() {
            return Ok(false);
        }
        self.mutable_hierarchy_namespace(&state.memory)?;
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Ok(false);
        };
        let Value::MutableU16 { id, role } = self.raw_local(state, source.local.as_usize())? else {
            return Ok(false);
        };
        if state.memory.mutable_u16[id].hierarchy.is_none() {
            return Ok(false);
        }
        let lease = match role {
            symbolic::MutableU16Role::Root => 0,
            symbolic::MutableU16Role::HierarchyChild { lease } => lease,
            symbolic::MutableU16Role::Metadata { .. }
            | symbolic::MutableU16Role::Child { .. }
            | symbolic::MutableU16Role::ChildMetadata { .. }
            | symbolic::MutableU16Role::HierarchyMetadata { .. }
            | symbolic::MutableU16Role::Ghost { .. } => {
                return Err("legacy/metadata source cannot stage hierarchy".into());
            }
        };
        self.mutable_u16_body_budget(body)?;
        if !matches!(occurrence, StatementKind::Assign(a)
            if a.0 == destination && std::ptr::eq(&a.1, value))
            || !body.basic_blocks.iter().any(|b| {
                b.statements
                    .iter()
                    .any(|s| std::ptr::eq(&s.kind, occurrence))
            })
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || source.local == destination.local
            || state.addresses[source.local.as_usize()].is_some()
            || state.addresses[destination.local.as_usize()].is_some()
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
        {
            return Err("hierarchy staging original occurrence/type/private source differs".into());
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let mut h = backing
            .hierarchy
            .clone()
            .ok_or("hierarchy staging namespace missing")?;
        let frame = self.mutable_u16_register_current_frame(body)?;
        let next = Tip {
            frame,
            statement: std::ptr::from_ref(occurrence) as usize,
            local: destination.local.as_usize(),
        };
        let next_lease = if let Some(pending) = &h.pending {
            if pending.lease != lease || pending.tip.local != source.local.as_usize() {
                return Err("hierarchy old staging tip cannot advance".into());
            }
            self.mutable_hierarchy_tip(&h, body)?;
            let old = pending.tip.clone();
            h.advance(&old, next, source.local.as_usize())?;
            lease
        } else {
            if let Some(owner) = h.owners.last() {
                self.mutable_u16_frame_top(body, &owner.frames)?;
            } else if lease != 0 {
                return Err("hierarchy source has no current owner".into());
            }
            h.issue(lease, next, state.memory.storage_slots())
                .map_err(|error| self.mutable_hierarchy_transition_error(error))?
        };
        self.mutable_hierarchy_charge(state, id, &h)?;
        Rc::make_mut(&mut state.memory.mutable_u16)[id].hierarchy = Some(h);
        // Sole private destination was authenticated before this ordinary exact write.
        self.write(
            state,
            destination,
            Value::MutableU16 {
                id,
                role: symbolic::MutableU16Role::HierarchyChild { lease: next_lease },
            },
        )?;
        Ok(true)
    }

    pub(super) fn mutable_hierarchy_exit(
        &self,
        body: &Body<'tcx>,
        arguments: &[Value],
        id: usize,
        memory: &Memory,
    ) -> Result<(), String> {
        let backing = self.mutable_u16_backing(id, memory)?;
        let h = backing
            .hierarchy
            .as_ref()
            .ok_or("hierarchy exit namespace missing")?;
        if h.pending.is_some() {
            return Err("pending hierarchy cannot leave frame".into());
        }
        let Some(owner) = h.owners.last() else {
            return Ok(());
        };
        self.mutable_u16_frame_top(body, &owner.frames)?;
        let count = arguments
            .iter()
            .filter(|v| {
                matches!(v,
            Value::MutableU16 { id: other,
                role: symbolic::MutableU16Role::HierarchyChild { lease } }
                if *other == id && *lease == owner.lease)
            })
            .count();
        if count != usize::from(owner.frames.len() == 1) {
            return Err("hierarchy Return lacks exact owning frame argument".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_scalar_call(
        &mut self,
        state: &mut State,
        selected: &Rc<Body<'tcx>>,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let super::mutable_u16_children::ChildCall {
            body,
            instance,
            args,
            stack,
            site,
            ..
        } = call;
        let Some(id) = state.memory.mutable_hierarchy else {
            return Ok(None);
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let before = backing
            .hierarchy
            .as_ref()
            .ok_or("scalar hierarchy namespace missing")?
            .clone();
        if before.owners.is_empty() {
            return Ok(None);
        }
        if before.pending.is_some() {
            return Err("pending hierarchy cannot call scalar".into());
        }
        let owner = before.owners.last().unwrap();
        self.mutable_u16_frame_top(body, &owner.frames)?;
        let depth = before.owners.iter().map(|o| o.frames.len()).sum::<usize>();
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy scalar depth exceeds existing budget".into(),
            ));
        }
        let frame = self.mutable_u16_register_frame(selected)?;
        let mut entered = before.clone();
        entered.owners.last_mut().unwrap().frames.push(frame);
        self.mutable_hierarchy_charge(state, id, &entered)?;
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
        }
        for (local, value) in selected.args_iter().zip(&values) {
            if selected.local_decls[local].ty == self.tcx.types.char {
                self.prove_char_value(value, &state.conditions)?;
            }
        }
        Rc::make_mut(&mut state.memory.mutable_u16)[id].hierarchy = Some(entered.clone());
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        for result in &mut results {
            if selected.return_ty() == self.tcx.types.char {
                self.prove_char_value(&result.value, &result.conditions)?;
            }
            if result.memory.mutable_hierarchy != Some(id) {
                return Err("scalar returned hierarchy mode differs".into());
            }
            self.mutable_u16_backing(id, &result.memory)?;
            if self.mutable_u16_contains(&result.value, &result.memory)? {
                return Err("hierarchy scalar result carries role".into());
            }
            let returned = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("hierarchy scalar returned namespace disappeared")?;
            if !Rc::ptr_eq(&returned.origin, &entered.origin)
                || returned.pending.is_some()
                || returned.issued < entered.issued
                || returned.epoch < entered.epoch
                || returned.owners != entered.owners
            {
                return Err("hierarchy scalar Return changed issuer/prefix/top".into());
            }
            self.mutable_u16_frame_top(selected, &returned.owners.last().unwrap().frames)?;
            returned.owners.last_mut().unwrap().frames.pop();
        }
        Ok(Some(results))
    }
}

#[cfg(test)]
pub(super) fn compiler_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    outer: &Rc<Body<'tcx>>,
    leaf: &Rc<Body<'tcx>>,
    base: &State,
) -> String {
    tests::run(engine, root, outer, leaf, base);
    tests::production_call(engine, root, base, false).unwrap()
}

#[cfg(test)]
pub(super) fn compiler_integer_boundary_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    element: Ty<'tcx>,
    wrong: Ty<'tcx>,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let value = engine
        .mutable_u16_input(element, &mut memory, &mut conditions)
        .unwrap();
    let mut state = State {
        locals: vec![None; root.local_decls.len()],
        addresses: vec![None; root.local_decls.len()],
        missing_places: Default::default(),
        conditions,
        memory,
    };
    state.locals[1] = Some(value);
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: root,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (root.source.def_id(), data.terminator().source_info.span),
    };
    assert_eq!(
        engine.mutable_hierarchy_route(&state, &call()).unwrap(),
        INTEGER_HIERARCHY_ENABLED
    );
    let _scope = TestIntegerHierarchy::enable();
    assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
    for excluded in [
        engine.tcx.types.u8,
        engine.tcx.types.bool,
        engine.tcx.types.char,
        engine.tcx.types.f32,
        engine.tcx.types.f64,
    ] {
        assert!(!engine.mutable_hierarchy_integer_element(excluded));
    }
    let selected = engine.instantiated_body(instance).unwrap();
    assert!(engine.mutable_hierarchy_selector(&selected, 1).unwrap());
    let mut forged = (*selected).clone();
    let wrong_ref = Ty::new_mut_ref(
        engine.tcx,
        engine.tcx.lifetimes.re_erased,
        Ty::new_slice(engine.tcx, wrong),
    );
    for declaration in forged.local_decls.iter_mut().skip(forged.arg_count + 1) {
        if declaration.ty == root.local_decls[rustc_middle::mir::Local::from_usize(1)].ty {
            declaration.ty = wrong_ref;
        }
    }
    assert!(!engine.mutable_hierarchy_selector(&forged, 1).unwrap());
    let mut wrong_memory = Memory::default();
    let mut wrong_conditions = Vec::new();
    let wrong_value = engine
        .mutable_u16_input(wrong, &mut wrong_memory, &mut wrong_conditions)
        .unwrap();
    let mut wrong_state = state.clone();
    wrong_state.memory = wrong_memory;
    wrong_state.conditions = wrong_conditions;
    let source = match args[0].node {
        Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
        _ => unreachable!(),
    };
    wrong_state.locals[source] = Some(wrong_value);
    assert!(
        !engine
            .mutable_hierarchy_route(&wrong_state, &call())
            .unwrap()
    );
    let before = wrong_state.memory.mutable_u16[0].data.clone();
    assert!(
        engine
            .mutable_hierarchy_call(&mut wrong_state, call())
            .unwrap()
            .is_none()
    );
    assert_eq!(wrong_state.memory.mutable_u16[0].data, before);
    let results = engine
        .mutable_hierarchy_call(&mut state, call())
        .unwrap()
        .unwrap();
    assert!(!results.is_empty());
    let leaf_name = if element == engine.tcx.types.i32 {
        "leaf_i32"
    } else {
        "leaf_usize"
    };
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|entry| entry.function == leaf_name)
    );
    for result in results {
        let backing = engine.mutable_u16_backing(0, &result.memory).unwrap();
        assert_eq!(
            engine
                .mutable_interval_element(backing.certificate)
                .unwrap(),
            element
        );
        let hierarchy = backing.hierarchy.as_ref().unwrap();
        assert!(hierarchy.owners.is_empty() && hierarchy.pending.is_none());
        assert!(hierarchy.issued >= 2);
    }
}

#[cfg(test)]
pub(super) fn compiler_production_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    assert!(tests::production_call(engine, root, base, true).is_none());
}

#[cfg(test)]
pub(super) fn compiler_non_candidate_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut state = base.clone();
    if root.local_decls[rustc_middle::mir::Local::from_usize(1)].ty == engine.tcx.types.u16 {
        state.locals[1] = Some(symbolic::integer(&engine.terms, 17, 16, false));
    }
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let before = state.memory.mutable_u16[0].data.clone();
    let slots = state.memory.storage_slots();
    let _scope = TestIssuance::enable();
    assert!(
        engine
            .mutable_hierarchy_call(
                &mut state,
                super::mutable_u16_children::ChildCall {
                    body: root,
                    block,
                    instance,
                    args,
                    destination: *destination,
                    target: *target,
                    stack: &[],
                    site: (root.source.def_id(), data.terminator().source_info.span),
                }
            )
            .unwrap()
            .is_none()
    );
    assert_eq!(state.memory.mutable_hierarchy, None);
    assert!(state.memory.mutable_u16[0].hierarchy.is_none());
    assert_eq!(state.memory.mutable_u16[0].data, before);
    assert_eq!(state.memory.storage_slots(), slots);
}

#[cfg(test)]
fn compiler_dormant_probe<'tcx>(engine: &mut Engine<'tcx>, memory: &Memory, conditions: &[Term]) {
    let definition = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == "root_wrapping"
        })
        .unwrap()
        .to_def_id();
    let root_instance = engine
        .resolve_function_item(definition, engine.tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(root_instance).unwrap();
    let (block, data) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, b)| matches!(b.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&body.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut state = State {
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        missing_places: Default::default(),
        memory: memory.clone(),
        conditions: conditions.to_vec(),
    };
    state.locals[1] = Some(symbolic::integer(&engine.terms, 17, 16, false));
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind {
            let value = engine
                .rvalue(body.source.def_id(), &body, &mut state, &a.1)
                .unwrap();
            engine
                .store_assignment_value(&body, &mut state, a.0, value, &statement.kind)
                .unwrap();
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: &body,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (body.source.def_id(), data.terminator().source_info.span),
    };
    let id = state.memory.mutable_hierarchy.unwrap();
    let backing = &state.memory.mutable_u16[id];
    let before = backing.hierarchy.as_ref().unwrap().clone();
    let data_term = backing.data.clone();
    let mut malformed = call();
    malformed.site.1 = rustc_span::DUMMY_SP;
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let mut malformed = call();
    malformed.site.0 = engine.tcx.lang_items().get(LangItem::SliceLen).unwrap();
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let pair_def = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == "root_pair"
        })
        .unwrap()
        .to_def_id();
    let pair_instance = engine
        .resolve_function_item(pair_def, engine.tcx.mk_args(&[]))
        .unwrap();
    let pair = engine.instantiated_body(pair_instance).unwrap();
    let mut pair_state = State {
        locals: vec![None; pair.local_decls.len()],
        addresses: vec![None; pair.local_decls.len()],
        missing_places: Default::default(),
        conditions: conditions.to_vec(),
        memory: memory.clone(),
    };
    pair_state.locals[1] = Some(Value::Tuple(vec![
        symbolic::integer(&engine.terms, 17, 16, true),
        symbolic::integer(&engine.terms, 17, 16, false),
    ]));
    let pair_local = rustc_middle::mir::Local::from_usize(1);
    let valid_field = Place {
        local: pair_local,
        projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(1),
            engine.tcx.types.u16,
        )]),
    };
    engine
        .mutable_hierarchy_dormant_operand(&pair, &pair_state, valid_field, engine.tcx.types.u16)
        .unwrap();
    let forged_field = Place {
        local: pair_local,
        projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(0),
            engine.tcx.types.u16,
        )]),
    };
    assert!(
        engine
            .mutable_hierarchy_dormant_operand(
                &pair,
                &pair_state,
                forged_field,
                engine.tcx.types.u16
            )
            .is_err()
    );
    let mut malformed = call();
    malformed.target = None;
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let mut consumed = state.clone();
    let (Operand::Move(source) | Operand::Copy(source)) = args[0].node else {
        unreachable!()
    };
    consumed
        .missing_places
        .consume(source.local.as_usize(), Vec::new())
        .unwrap();
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut consumed, &call())
            .is_err()
    );
    let mut wrong_type = state.clone();
    wrong_type.locals[source.local.as_usize()] =
        Some(symbolic::integer(&engine.terms, 17, 16, true));
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut wrong_type, &call())
            .is_err()
    );
    let results = engine
        .mutable_hierarchy_dormant_call(&mut state, &call())
        .unwrap()
        .unwrap();
    assert!(
        state
            .missing_places
            .check(source.local.as_usize(), &[])
            .is_err()
    );
    for result in results {
        assert_eq!(
            result.value.integer().unwrap().0.constant(),
            symbolic::integer(&engine.terms, 18, 16, false)
                .integer()
                .unwrap()
                .0
                .constant()
        );
        engine
            .mutable_hierarchy_dormant_return(id, &before, &data_term, &result.memory)
            .unwrap();
        let mut lost = result.memory.clone();
        lost.mutable_hierarchy = None;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &lost)
                .is_err()
        );
        let mut floor = result.memory.clone();
        Rc::make_mut(&mut floor.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .issued = before.issued - 1;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &floor)
                .is_err()
        );
        let mut epoch = result.memory.clone();
        Rc::make_mut(&mut epoch.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .epoch = before.epoch - 1;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &epoch)
                .is_err()
        );
        let mut origin = result.memory.clone();
        Rc::make_mut(&mut origin.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .origin = Rc::new((*before.origin).clone());
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &origin)
                .is_err()
        );
        let mut dead = result.memory.clone();
        dead.missing_places
            .consume(before.origin.allocation, Vec::new())
            .unwrap();
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &dead)
                .is_err()
        );
    }
}

// Compiler transition tests remain separate from production Call/Return adapters.
pub(super) struct Ticket {
    origin: Rc<Origin>,
    lease: u64,
    issued_floor: u64,
    epoch_floor: u64,
    prefix: Vec<Owner>,
    frame: usize,
}

#[derive(Clone, Copy)]
pub(super) struct Metadata {
    lease: u64,
    epoch: u64,
}

impl Hierarchy {
    #[cfg(test)]
    fn from_parent(backing: &super::mutable_u16::Backing, frame: usize) -> Result<Self, String> {
        if backing.interval.is_some() || backing.generation == 0 {
            return Err("whole existing parent only".into());
        }
        Ok(Self {
            origin: Rc::new(Origin {
                certificate: backing.certificate,
                allocation: backing.allocation,
                capacity: backing.length.clone(),
                data_context: backing.data.clone(),
            }),
            issued: backing.generation,
            epoch: 0,
            owners: vec![Owner {
                lease: backing.generation,
                parent: 0,
                frames: vec![frame],
            }],
            pending: None,
        })
    }

    #[cfg(test)]
    fn current(&self, engine: &Engine<'_>, state: &State) -> Result<(), String> {
        let backing = state.memory.mutable_u16.first().ok_or("backing missing")?;
        if backing.interval.is_some()
            || backing.certificate != self.origin.certificate
            || backing.allocation != self.origin.allocation
            || backing.length.integer()? != self.origin.capacity.integer()?
            || !backing.data.belongs_to(&engine.terms)
            || !self.origin.data_context.belongs_to(&engine.terms)
            || backing.data.sort() != self.origin.data_context.sort()
            || !matches!(
                state.memory.get(backing.allocation),
                Some(Some(Value::Unit))
            )
        {
            return Err("current issued owner differs".into());
        }
        state
            .memory
            .check_projection_initialization(backing.allocation, &[])?;
        for owner in &self.owners {
            if owner.lease > self.issued
                || owner.frames.is_empty()
                || owner.frames.iter().any(|id| {
                    engine
                        .mutable_u16_frames
                        .borrow()
                        .get(*id)
                        .is_none_or(|weak| weak.upgrade().is_none())
                })
            {
                return Err("current live owner lineage differs".into());
            }
        }
        Ok(())
    }

    fn access(&self, lease: u64) -> Result<(), String> {
        if self.pending.is_none() && self.owners.last().map_or(lease == 0, |o| o.lease == lease) {
            Ok(())
        } else {
            Err("suspended or revoked lease".into())
        }
    }

    fn lifetime(&self, lease: u64) -> Result<(), String> {
        if lease == 0 || self.owners.iter().any(|o| o.lease == lease) {
            Ok(())
        } else {
            Err("revoked is not ancestor".into())
        }
    }

    fn metadata(&self, lease: u64) -> Result<Metadata, String> {
        self.access(lease)?;
        Ok(Metadata {
            lease,
            epoch: self.epoch,
        })
    }

    fn observe(&self, metadata: Metadata) -> Result<(), String> {
        self.access(metadata.lease)?;
        if metadata.epoch == self.epoch {
            Ok(())
        } else {
            Err("stale epoch".into())
        }
    }

    fn issue(&mut self, parent: u64, tip: Tip, slots: usize) -> Result<u64, TransitionError> {
        self.access(parent)?;
        if self.owners.len() >= 2 {
            return Err(TransitionError::Semantics(
                "hierarchy exceeds the single nested-child scope".into(),
            ));
        }
        if self.owners.iter().map(|o| o.frames.len()).sum::<usize>() >= MAX_INPUT_DEPTH
            || slots.saturating_add(5) > MAX_INPUT_VALUES
        {
            return Err(TransitionError::Resource(
                "hierarchy cumulative budget/depth",
            ));
        }
        let issued = self.issued.checked_add(1).ok_or(TransitionError::Resource(
            "hierarchy issuer counter exhausted",
        ))?;
        let epoch = self.epoch.checked_add(1).ok_or(TransitionError::Resource(
            "hierarchy epoch counter exhausted",
        ))?;
        self.pending = Some(Pending {
            lease: issued,
            parent,
            tip,
        });
        self.issued = issued;
        self.epoch = epoch;
        Ok(issued)
    }

    fn advance(&mut self, old: &Tip, next: Tip, original_source: usize) -> Result<(), String> {
        let pending = self.pending.as_mut().ok_or("pending missing")?;
        if &pending.tip != old
            || old.frame != next.frame
            || old.local == next.local
            || old.local != original_source
        {
            return Err("old tip/Body cannot advance".into());
        }
        pending.tip = next;
        Ok(())
    }

    fn enter(&mut self, tip: &Tip, frame: usize, slots: usize) -> Result<Ticket, TransitionError> {
        let pending = self.pending.as_ref().ok_or("pending missing")?;
        if &pending.tip != tip || self.owners.last().map_or(0, |o| o.lease) != pending.parent {
            return Err("current pending handoff differs".into());
        }
        if slots.saturating_add(3) > MAX_INPUT_VALUES {
            return Err(TransitionError::Resource(
                "hierarchy handoff exceeds storage budget",
            ));
        }
        let ticket = Ticket {
            origin: self.origin.clone(),
            lease: pending.lease,
            issued_floor: self.issued,
            epoch_floor: self.epoch,
            prefix: self.owners.clone(),
            frame,
        };
        self.owners.push(Owner {
            lease: pending.lease,
            parent: pending.parent,
            frames: vec![frame],
        });
        self.pending = None;
        Ok(ticket)
    }

    fn release(&mut self, ticket: &Ticket) -> Result<(), String> {
        if !Rc::ptr_eq(&self.origin, &ticket.origin)
            || self.pending.is_some()
            || self.issued < ticket.issued_floor
            || self.epoch < ticket.epoch_floor
            || self.owners.len() != ticket.prefix.len() + 1
            || self.owners[..ticket.prefix.len()] != ticket.prefix
            || self
                .owners
                .last()
                .is_none_or(|o| o.lease != ticket.lease || o.frames != [ticket.frame])
        {
            return Err("returned Memory rollback/top/prefix".into());
        }
        let epoch = self.epoch.checked_add(1).ok_or("epoch overflow")?;
        self.owners.pop();
        self.epoch = epoch;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scoped_public_issuance_restores_nested_and_panicking_tests() {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
        {
            let _outer = TestIssuance::enable();
            assert!(issuance_enabled());
            {
                let _inner = TestIssuance::enable();
                assert!(issuance_enabled());
            }
            assert!(issuance_enabled());
        }
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestIssuance::enable();
                assert!(issuance_enabled());
                panic!("test scoped issuer restoration");
            })
            .is_err()
        );
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
    }

    #[test]
    fn scoped_integer_selection_restores_nested_and_panicking_tests() {
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        {
            let _outer = TestIntegerHierarchy::enable();
            assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
            {
                let _inner = TestIntegerHierarchy::enable();
                assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
            }
            assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        }
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestIntegerHierarchy::enable();
                panic!("test issuer restoration");
            })
            .is_err()
        );
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(integer_hierarchy_enabled(), INTEGER_HIERARCHY_ENABLED);
    }

    pub(super) fn production_call<'tcx>(
        engine: &mut Engine<'tcx>,
        root: &Rc<Body<'tcx>>,
        base: &State,
        expected: bool,
    ) -> Option<String> {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        let (block, call) = root
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                matches!(data.terminator().kind, TerminatorKind::Call { .. })
                    .then_some((block, &data.terminator().kind))
            })
            .unwrap();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = call
        else {
            unreachable!()
        };
        let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
            unreachable!()
        };
        let instance = engine
            .resolve_function_item(*definition, generic.skip_binder())
            .unwrap();
        let mut state = base.clone();
        for statement in &root.basic_blocks[block].statements {
            if let StatementKind::Assign(a) = &statement.kind
                && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
            {
                assert!(
                    engine
                        .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                        .unwrap()
                );
            }
        }
        let before = state.memory.mutable_u16[0].data.clone();
        // Preserve the disabled default-route assertion in archived/checkpoint test builds.
        let call = || super::super::mutable_u16_children::ChildCall {
            body: root,
            block,
            instance,
            args,
            destination: *destination,
            target: *target,
            stack: &[],
            site: (
                root.source.def_id(),
                root.basic_blocks[block].terminator().source_info.span,
            ),
        };
        if !ISSUANCE_ENABLED {
            assert!(
                engine
                    .mutable_hierarchy_call(&mut state.clone(), call())
                    .unwrap()
                    .is_none()
            );
        }
        assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
        let selected = engine.instantiated_body(instance).unwrap();
        assert!(engine.mutable_hierarchy_selector(&selected, 1).unwrap());
        for entry in ["scalar", "leaf_len"] {
            let definition = engine
                .tcx
                .iter_local_def_id()
                .find(|d| {
                    engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                        && engine.tcx.item_name(d.to_def_id()).as_str() == entry
                })
                .unwrap()
                .to_def_id();
            let instance = engine
                .resolve_function_item(definition, engine.tcx.mk_args(&[]))
                .unwrap();
            let ordinary = engine.instantiated_body(instance).unwrap();
            assert!(!engine.mutable_hierarchy_selector(&ordinary, 1).unwrap());
        }
        let source = match args[0].node {
            Operand::Copy(place) | Operand::Move(place) => place.local.as_usize(),
            Operand::Constant(_) => unreachable!(),
            Operand::RuntimeChecks(_) => unreachable!(),
        };
        // A routing cache cannot issue authority or recover a missing namespace.
        let mut unissued = state.clone();
        unissued.memory.mutable_hierarchy = Some(0);
        assert!(
            engine
                .mutable_hierarchy_namespace(&unissued.memory)
                .is_err()
        );
        assert!(
            engine
                .mutable_hierarchy_call(&mut unissued, call())
                .is_err()
        );
        let mut wrong = state.clone();
        wrong.memory.mutable_hierarchy = Some(usize::MAX);
        assert!(engine.mutable_hierarchy_call(&mut wrong, call()).is_err());
        let mut consumed = state.clone();
        consumed.missing_places.consume(source, Vec::new()).unwrap();
        assert!(!engine.mutable_hierarchy_route(&consumed, &call()).unwrap());
        let mut active_legacy = state.clone();
        let frame = engine.mutable_u16_register_frame(root).unwrap();
        Rc::make_mut(&mut active_legacy.memory.mutable_u16)[0].phase =
            super::super::mutable_u16_children::Phase::Active {
                frames: vec![frame],
            };
        assert!(
            !engine
                .mutable_hierarchy_route(&active_legacy, &call())
                .unwrap()
        );

        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut consumed, call())
                .is_err()
        );
        let mut ghost = state.clone();
        ghost.locals[source] = Some(Value::Unit);
        assert!(!engine.mutable_hierarchy_route(&ghost, &call()).unwrap());
        for element in [engine.tcx.types.i16, engine.tcx.types.f32] {
            let mut memory = Memory::default();
            let mut conditions = Vec::new();
            let role = engine
                .mutable_u16_input(element, &mut memory, &mut conditions)
                .unwrap();
            let mut other = state.clone();
            other.memory = memory;
            other.conditions = conditions;
            other.locals[source] = Some(role);
            assert!(!engine.mutable_hierarchy_route(&other, &call()).unwrap());
            let _scope = TestIssuance::enable();
            assert!(
                engine
                    .mutable_hierarchy_call(&mut other, call())
                    .unwrap()
                    .is_none()
            );
        }

        let other_args = args.to_vec();
        let mut forged = call();
        forged.args = &other_args;
        assert!(!engine.mutable_hierarchy_route(&state, &forged).unwrap());
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let different = Rc::new((**root).clone());
        let mut forged = call();
        forged.body = &different;
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let mut forged = call();
        forged.target = None;
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let mut forged = call();
        forged.destination = Place::from(rustc_middle::mir::RETURN_PLACE);
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        // Exercise the public Call route and all actual child staging/Return hooks. The scoped
        // test switch changes only issuer selection; the production constant remains false.
        let _issuance = TestIssuance::enable();
        assert!(issuance_enabled());
        for mut noncandidate in [consumed.clone(), active_legacy.clone(), ghost.clone()] {
            assert!(
                engine
                    .mutable_hierarchy_call(&mut noncandidate, call())
                    .unwrap()
                    .is_none()
            );
        }
        let mut forged = call();
        forged.args = &other_args;
        assert!(
            engine
                .mutable_hierarchy_call(&mut state.clone(), forged)
                .unwrap()
                .is_none()
        );
        let mut forged = call();
        forged.target = None;
        assert!(
            engine
                .mutable_hierarchy_call(&mut state.clone(), forged)
                .unwrap()
                .is_none()
        );
        let outcome = engine.mutable_hierarchy_call(&mut state, call());
        if !expected {
            return Some(
                outcome
                    .err()
                    .expect("original is_empty must remain unsupported"),
            );
        }
        let results = outcome.unwrap().unwrap();
        assert!(!results.is_empty());
        let mut observed_current_store = false;
        for result in results {
            assert!(matches!(result.value, Value::Unit));
            assert_eq!(result.memory.mutable_hierarchy, Some(0));
            let backing = &result.memory.mutable_u16[0];
            observed_current_store |= backing.data != before;
            compiler_dormant_probe(engine, &result.memory, &result.conditions);
            let h = backing.hierarchy.as_ref().unwrap();
            assert!(h.owners.is_empty() && h.pending.is_none());
            assert!(h.issued >= 3 && h.epoch >= 6);
            assert!(h.role_valid(&symbolic::MutableU16Role::Root, true));
            assert!(!h.role_valid(&symbolic::MutableU16Role::Child { generation: 1 }, true));
            assert!(!h.role_valid(
                &symbolic::MutableU16Role::HierarchyChild { lease: h.issued },
                false
            ));
            assert!(!h.role_valid(
                &symbolic::MutableU16Role::HierarchyMetadata { lease: 0, epoch: 0 },
                true
            ));
            engine.mutable_hierarchy_namespace(&result.memory).unwrap();
            let mut absent = result.memory.clone();
            absent.mutable_hierarchy = None;
            assert!(engine.mutable_u16_backing(0, &absent).is_err());
            let mut cache_lost = state.clone();
            cache_lost.memory = absent.clone();
            assert!(
                engine
                    .mutable_hierarchy_route(&cache_lost, &call())
                    .is_err()
            );
            assert!(
                engine
                    .mutable_hierarchy_call(&mut cache_lost, call())
                    .is_err()
            );
            let mut wrong = result.memory.clone();
            wrong.mutable_hierarchy = Some(usize::MAX);
            assert!(engine.mutable_hierarchy_namespace(&wrong).is_err());
            let clone = result.memory.clone();
            assert_eq!(clone.storage_slots(), result.memory.storage_slots());
            assert_eq!(clone.mutable_hierarchy, Some(0));
            let mut grown = clone.clone();
            grown.push(Some(Value::Unit));
            assert_eq!(grown.storage_slots(), clone.storage_slots() + 1);
            let mut reopened = h.clone();
            let old_epoch = reopened.epoch;
            let old_issued = reopened.issued;
            let tip = Tip {
                frame: 0,
                statement: 1,
                local: 1,
            };
            reopened
                .issue(0, tip, result.memory.storage_slots())
                .unwrap();
            assert!(reopened.epoch > old_epoch && reopened.issued > old_issued);
            assert!(!reopened.role_valid(&symbolic::MutableU16Role::Root, true));
            assert!(reopened.role_valid(&symbolic::MutableU16Role::Root, false));
            assert!(!reopened.role_valid(
                &symbolic::MutableU16Role::HierarchyMetadata {
                    lease: 0,
                    epoch: old_epoch
                },
                false,
            ));
            assert!(backing.data.belongs_to(&engine.terms));
            assert_eq!(backing.data.sort(), before.sort());
        }
        assert!(
            observed_current_store,
            "normal Return must retain actual child Store data"
        );
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function.contains("scalar"))
        );
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function.contains("leaf"))
        );
        None
    }

    pub(super) fn run<'tcx>(
        engine: &mut Engine<'tcx>,
        root: &Rc<Body<'tcx>>,
        outer: &Rc<Body<'tcx>>,
        leaf: &Rc<Body<'tcx>>,
        base: &State,
    ) {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        let root_frame = engine.mutable_u16_register_frame(root).unwrap();
        let outer_frame = engine.mutable_u16_register_frame(outer).unwrap();
        let leaf_frame = engine.mutable_u16_register_frame(leaf).unwrap();
        let statement = outer
            .basic_blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find(|s| {
                matches!(&s.kind, StatementKind::Assign(a)
                if matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _)))
            })
            .unwrap();
        let StatementKind::Assign(assignment) = &statement.kind else {
            unreachable!()
        };
        let Rvalue::Ref(_, _, source) = &assignment.1 else {
            unreachable!()
        };
        let mut state = State {
            locals: vec![None; outer.local_decls.len()],
            addresses: vec![None; outer.local_decls.len()],
            missing_places: Default::default(),
            conditions: base.conditions.clone(),
            memory: base.memory.clone(),
        };
        state.locals[source.local.as_usize()] = Some(Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::Child { generation: 1 },
        });
        {
            let backing = &mut Rc::make_mut(&mut state.memory.mutable_u16)[0];
            backing.generation = 1;
            backing.phase = super::super::mutable_u16_children::Phase::Active {
                frames: vec![outer_frame],
            };
        }
        engine
            .mutable_hierarchy_source(outer, &state, assignment.0, &assignment.1, &statement.kind)
            .unwrap();
        let mut consumed = state.clone();
        consumed
            .missing_places
            .consume(source.local.as_usize(), Vec::new())
            .unwrap();
        assert!(
            engine
                .mutable_hierarchy_source(
                    outer,
                    &consumed,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let different = Rc::new((**outer).clone());
        assert!(
            engine
                .mutable_hierarchy_source(
                    &different,
                    &state,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let mut wrong_role = state.clone();
        wrong_role.locals[source.local.as_usize()] = Some(Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::Root,
        });
        assert!(
            engine
                .mutable_hierarchy_source(
                    outer,
                    &wrong_role,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let mut hierarchy =
            Hierarchy::from_parent(&state.memory.mutable_u16[0], outer_frame).unwrap();
        let outer_ticket = Ticket {
            origin: hierarchy.origin.clone(),
            lease: 1,
            issued_floor: 1,
            epoch_floor: 0,
            prefix: Vec::new(),
            frame: outer_frame,
        };
        let old_parent_meta = hierarchy.metadata(1).unwrap();
        let first = Tip {
            frame: outer_frame,
            statement: &statement.kind as *const _ as usize,
            local: assignment.0.local.as_usize(),
        };
        let lease = hierarchy
            .issue(
                1,
                first.clone(),
                state.memory.storage_slots() + hierarchy.storage_slots(),
            )
            .unwrap();
        assert_eq!(lease, 2);
        assert!(hierarchy.access(1).is_err());
        hierarchy.lifetime(1).unwrap();
        let next_statement = outer
            .basic_blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find(|s| {
                matches!(&s.kind, StatementKind::Assign(a)
                if matches!(&a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                    if place.local.as_usize() == first.local))
            })
            .unwrap();
        let StatementKind::Assign(next_assignment) = &next_statement.kind else {
            unreachable!()
        };
        let next = Tip {
            frame: outer_frame,
            statement: &next_statement.kind as *const _ as usize,
            local: next_assignment.0.local.as_usize(),
        };
        hierarchy
            .advance(&first, next.clone(), first.local)
            .unwrap();
        assert!(
            hierarchy
                .advance(&first, next.clone(), first.local)
                .is_err()
        );
        assert!(
            hierarchy
                .enter(
                    &first,
                    leaf_frame,
                    state.memory.storage_slots() + hierarchy.storage_slots()
                )
                .is_err()
        );
        let ticket = hierarchy
            .enter(
                &next,
                leaf_frame,
                state.memory.storage_slots() + hierarchy.storage_slots(),
            )
            .unwrap();
        let child_meta = hierarchy.metadata(2).unwrap();
        // Actual graph modes distinguish a suspended ancestor from current access.
        let mut graph = state.clone();
        graph.memory.mutable_hierarchy = Some(0);
        {
            let backing = &mut Rc::make_mut(&mut graph.memory.mutable_u16)[0];
            backing.phase = super::super::mutable_u16_children::Phase::Idle;
            backing.hierarchy = Some(hierarchy.clone());
        }
        engine.mutable_hierarchy_namespace(&graph.memory).unwrap();
        let ancestor = Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::HierarchyChild { lease: 1 },
        };
        assert!(engine.validate_tracked_value(&ancestor, &graph).is_err());
        Engine::mutable_hierarchy_test_lifetime_graph(&ancestor, &graph).unwrap();
        let current = Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::HierarchyChild { lease: 2 },
        };
        engine.validate_tracked_value(&current, &graph).unwrap();
        let mut revoked = graph.clone();
        Rc::make_mut(&mut revoked.memory.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap()
            .release(&ticket)
            .unwrap();
        assert!(Engine::mutable_hierarchy_test_lifetime_graph(&current, &revoked).is_err());
        let mut absent = graph.clone();
        absent.memory.mutable_hierarchy = None;
        assert!(Engine::mutable_hierarchy_test_lifetime_graph(&ancestor, &absent).is_err());
        assert!(
            Engine::validate_reference_graph(&current, &graph, Some(1), &mut Vec::new()).is_err()
        );

        let mut rolled = hierarchy.clone();
        rolled.issued = ticket.issued_floor - 1;
        assert!(rolled.release(&ticket).is_err());
        let mut rolled = hierarchy.clone();
        rolled.epoch = ticket.epoch_floor - 1;
        assert!(rolled.release(&ticket).is_err());
        let mut wrong_origin = hierarchy.clone();
        wrong_origin.origin = Rc::new((*hierarchy.origin).clone());
        assert!(wrong_origin.release(&ticket).is_err());
        let mut wrong_prefix = hierarchy.clone();
        wrong_prefix.owners[0].frames = vec![root_frame];
        assert!(wrong_prefix.release(&ticket).is_err());
        let mut early = hierarchy.clone();
        early.owners.last_mut().unwrap().frames.push(outer_frame);
        assert!(early.release(&ticket).is_err());
        hierarchy.current(engine, &state).unwrap();
        Rc::make_mut(&mut state.memory.mutable_u16)[0].hierarchy = Some(hierarchy.clone());
        let slots = state.memory.storage_slots();
        assert!(slots >= hierarchy.storage_slots());
        assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
        assert!(!super::super::mutable_u16_children::role_live(
            &state.memory.mutable_u16[0],
            &symbolic::MutableU16Role::Child { generation: 2 }
        ));
        assert!(
            engine
                .validate_tracked_value(
                    state.locals[source.local.as_usize()].as_ref().unwrap(),
                    &state
                )
                .is_err()
        );
        hierarchy.release(&ticket).unwrap();
        hierarchy.access(1).unwrap();
        assert!(hierarchy.lifetime(2).is_err());
        assert!(hierarchy.observe(old_parent_meta).is_err());
        assert!(hierarchy.observe(child_meta).is_err());
        let second = hierarchy.issue(1, first.clone(), slots).unwrap();
        assert_eq!(second, 3);
        let second_ticket = hierarchy.enter(&first, leaf_frame, slots).unwrap();
        hierarchy.release(&second_ticket).unwrap();
        hierarchy.release(&outer_ticket).unwrap();
        assert!(hierarchy.owners.is_empty());
        assert_eq!(hierarchy.issued, 3);
        hierarchy.access(0).unwrap();
        let dormant_meta = hierarchy.metadata(0).unwrap();
        let dormant_epoch = hierarchy.epoch;
        Rc::make_mut(&mut state.memory.mutable_u16)[0].hierarchy = Some(hierarchy.clone());
        let dormant_slots = state.memory.storage_slots();
        assert_eq!(hierarchy.storage_slots(), 6);
        let mut branch = state.memory.clone();
        let h = Rc::make_mut(&mut branch.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap();
        let next_root_tip = Tip {
            frame: root_frame,
            statement: first.statement,
            local: first.local,
        };
        assert_eq!(h.issue(0, next_root_tip.clone(), dormant_slots).unwrap(), 4);
        let next_ticket = h
            .enter(&next_root_tip, outer_frame, dormant_slots + 5)
            .unwrap();
        h.release(&next_ticket).unwrap();
        assert!(h.observe(dormant_meta).is_err());
        assert_eq!(
            state.memory.mutable_u16[0]
                .hierarchy
                .as_ref()
                .unwrap()
                .epoch,
            dormant_epoch
        );
        assert_eq!(
            state.memory.mutable_u16[0]
                .hierarchy
                .as_ref()
                .unwrap()
                .issued,
            3
        );
        assert_eq!(branch.mutable_u16[0].hierarchy.as_ref().unwrap().issued, 4);
        assert!(matches!(
            hierarchy.issue(0, first.clone(), MAX_INPUT_VALUES),
            Err(TransitionError::Resource(_))
        ));
        let mut exhausted = hierarchy.clone();
        exhausted.issued = u64::MAX;
        assert!(matches!(
            exhausted.issue(0, first.clone(), 0),
            Err(TransitionError::Resource(_))
        ));

        assert_eq!(hierarchy.issued, 3);
        let held = Rc::new((**leaf).clone());
        let expired_id = engine.mutable_u16_register_frame(&held).unwrap();
        drop(held);
        let mut expired = hierarchy.clone();
        expired.owners.push(Owner {
            lease: 3,
            parent: 0,
            frames: vec![expired_id],
        });
        assert!(expired.current(engine, &state).is_err());
        assert!(
            consumed
                .missing_places
                .check(source.local.as_usize(), &[])
                .is_err()
        );
        // No producer or graph validation above clears the original parent source mask.
    }
}
