//! Actual compiler destruction frames. Private views grant no ordinary raw access.
use super::*;
#[path = "signature.rs"]
mod signature;
use crate::symbolic::MemoryProjection;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    OuterGlue,
    PublicDrop,
    InnerGlue,
    InnerDrop,
    SizedPartial,
    PartialHost,
    PartialInline,
    Bounds,
    Slice,
    Child,
    Helper,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Iterator,
    Inner,
    DataSized,
    DataUnsized,
    RawWhole,
    MaybeElement,
    RemainingElement,
    RawRemainingMaybe,
    RemainingMaybe,
    RawRemainingT,
    RemainingT,
    Element(usize),
}
#[derive(Clone, Debug)]
pub(in crate::proof) struct View {
    owner: usize,
    entry: Rc<()>,
    role: Role,
}
pub(in crate::proof) struct Invocation<'tcx> {
    owner: usize,
    identity: Identity,
    entry: Rc<()>,
    evidence: BodyEvidence<'tcx>,
    kind: Kind,
    front: usize,
    back: usize,
    words: Option<Rc<Vec<steps::Word>>>,
}
fn local(place: Place<'_>, expected: usize) -> bool {
    place.local.as_usize() == expected && place.projection.is_empty()
}
fn path(place: Place<'_>, root: usize, fields: &[usize]) -> bool {
    place.local.as_usize() == root
        && place.projection.first() == Some(&ProjectionElem::Deref)
        && place.projection.len() == fields.len() + 1
        && place.projection[1..].iter().zip(fields).all(|(part, field)|
            matches!(part,ProjectionElem::Field(index,_) if index.as_usize()==*field))
}
fn copied(operand: &Operand<'_>, source: usize) -> bool {
    matches!(operand,Operand::Copy(place) if local(*place,source))
}
fn receiver(kind: Kind) -> Role {
    match kind {
        Kind::OuterGlue | Kind::PublicDrop => Role::Iterator,
        Kind::InnerGlue | Kind::InnerDrop => Role::Inner,
        Kind::SizedPartial => Role::DataSized,
        Kind::PartialHost | Kind::PartialInline => Role::DataUnsized,
        Kind::Slice => Role::RemainingT,
        Kind::Bounds | Kind::Child | Kind::Helper => Role::DataUnsized,
    }
}
impl<'tcx> Invocation<'tcx> {
    fn check(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &State,
    ) -> Result<(), String> {
        state.flow.require_unarmed()?;
        self.check_memory(engine, body, &state.memory, &state.conditions)
    }
    fn check_memory(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<(), String> {
        self.evidence.current(engine)?;
        pay(engine, memory.initialized_owners.len() + 8)?;
        if !Rc::ptr_eq(body, &self.evidence.current) {
            return Err("IntoIter destruction current frame Body differs".into());
        }
        pay(engine, memory.missing_places.entries().len() + 1)?;
        memory.missing_places.check(self.owner, &[])?;
        let physical = engine.array_iterator_certificate(&self.identity)?;
        let (iterator, initialized_element, count) = (
            physical.iterator,
            physical.initialized_element,
            physical.count,
        );
        let (footprint, original) = engine
            .typed_memory_evidence(memory, self.owner, &[])?
            .ok_or("IntoIter destruction original owner type evidence unavailable")?;
        if original != iterator || !footprint.is_empty() {
            return Err("IntoIter destruction original owner storage differs".into());
        }
        let Some(Value::OwnedArrayIterator {
            identity,
            payload: Some(payload),
        }) = memory.get(self.owner).and_then(Option::as_ref)
        else {
            return Err("IntoIter destruction sole owner is absent".into());
        };
        if identity.view.is_some()
            || identity.original != TransportType::Iterator
            || identity.certificate != self.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &self.identity.seal)
            || !Rc::ptr_eq(&identity.entry, &self.identity.entry)
            || payload.front != self.front
            || payload.back != self.back
            || payload.len() != count
        {
            return Err("IntoIter destruction owner/cursor identity differs".into());
        }
        pay(engine, payload.len() + 3)?;
        let progress = payload
            .dropping
            .as_ref()
            .ok_or("IntoIter destruction active phase is absent")?;
        if !Rc::ptr_eq(&progress.entry, &self.entry) {
            return Err("IntoIter destruction phase belongs to another invocation".into());
        }
        progress.validate(payload)?;
        if matches!(self.kind, Kind::Child | Kind::Helper) {
            let lease = progress
                .leased
                .as_ref()
                .ok_or("IntoIter child frame lacks its sole element lease")?;
            let (fields, original) = engine
                .typed_memory_evidence(memory, lease.allocation, &[])?
                .ok_or("IntoIter child lease original type evidence unavailable")?;
            if !fields.is_empty()
                || original != initialized_element
                || lease.allocation == self.owner
                || memory
                    .get(lease.allocation)
                    .and_then(Option::as_ref)
                    .is_none()
            {
                return Err("IntoIter child lease typed allocation differs".into());
            }
            memory.missing_places.check(lease.allocation, &[])?;
            let value = memory
                .get(lease.allocation)
                .and_then(Option::as_ref)
                .ok_or("IntoIter child lease initialized payload absent")?;
            steps::validate_element(engine, initialized_element, value, conditions, 0, &mut 0)?;
        }
        if let Some(words) = &self.words
            && steps::observe_payload_memory(engine, memory, self.owner)? != **words
        {
            return Err(
                "IntoIter suspended destruction payload changed during child/helper".into(),
            );
        }
        Ok(())
    }
    fn view(&self, engine: &mut Engine<'tcx>, role: Role) -> Result<Value, String> {
        // Distinct creation allowance: Identity and entry Rc clones plus private inline view/value.
        // Validation and eventual destination publication retain their independent payments.
        pay(engine, 20)?;
        #[cfg(test)]
        CONSTRUCTIONS.with(|events| events.borrow_mut().push("view"));
        let mut identity = self.identity.clone();
        identity.original = TransportType::Inner;
        identity.view = Some(PrivateView::Drop(View {
            owner: self.owner,
            entry: self.entry.clone(),
            role,
        }));
        Ok(Value::OwnedArrayIterator {
            identity,
            payload: None,
        })
    }
    fn role(&self, engine: &mut Engine<'tcx>, state: &State, index: usize) -> Result<Role, String> {
        // Borrow only the exact private local. No speculative clone of an unsupported guest
        // container occurs; the existing creation allowance remains separate from these checks.
        pay(engine, 20 + state.missing_places.entries().len())?;
        if state.addresses.get(index) != Some(&None) {
            return Err(
                "IntoIter destruction private role local is addressed or unavailable".into(),
            );
        }
        state.missing_places.check(index, &[])?;
        let Some(Value::OwnedArrayIterator {
            identity,
            payload: None,
        }) = state.locals.get(index).and_then(Option::as_ref)
        else {
            return Err("IntoIter destruction private metadata is absent".into());
        };
        let Some(PrivateView::Drop(view)) = &identity.view else {
            return Err("IntoIter destruction metadata belongs to another protocol".into());
        };
        if view.owner != self.owner
            || !Rc::ptr_eq(&view.entry, &self.entry)
            || identity.certificate != self.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &self.identity.seal)
            || !Rc::ptr_eq(&identity.entry, &self.identity.entry)
        {
            return Err("IntoIter destruction metadata owner/entry differs".into());
        }
        Ok(view.role)
    }
    fn require_role(
        &self,
        engine: &mut Engine<'tcx>,
        state: &State,
        index: usize,
        role: Role,
    ) -> Result<(), String> {
        if self.role(engine, state, index)? != role {
            return Err("IntoIter destruction metadata role differs".into());
        }
        Ok(())
    }
}
fn schema<'tcx>(
    engine: &mut Engine<'tcx>,
    evidence: &BodyEvidence<'tcx>,
    kind: Kind,
    identity: &Identity,
) -> Result<(), String> {
    let body = &evidence.current;
    pay(engine, body.local_decls.len() + body.basic_blocks.len() + 4)?;
    let (locals, statements): (usize, &[usize]) = match kind {
        Kind::OuterGlue | Kind::InnerGlue => (4, &[1, 0]),
        Kind::PublicDrop => (5, &[0, 2, 0, 1]),
        Kind::InnerDrop => (5, &[4, 2]),
        Kind::SizedPartial => (4, &[2, 1]),
        Kind::PartialHost => (20, &[4, 4, 2, 18, 5, 2, 2]),
        Kind::PartialInline => (22, &[4, 4, 2, 17, 7, 1, 4, 2, 1]),
        Kind::Slice => (8, &[2, 0, 2, 1]),
        Kind::Bounds | Kind::Child | Kind::Helper => return Ok(()),
    };
    if body.local_decls.len() != locals
        || body.basic_blocks.len() != statements.len()
        || !body.return_ty().is_unit()
        || body.arg_count
            != if matches!(
                kind,
                Kind::SizedPartial | Kind::PartialHost | Kind::PartialInline
            ) {
                2
            } else {
                1
            }
        || body
            .basic_blocks
            .iter()
            .zip(statements)
            .any(|(block, count)| block.is_cleanup || block.statements.len() != *count)
    {
        return Err("IntoIter destruction exact original frame schema differs".into());
    }
    let physical = engine.array_iterator_certificate(identity)?;
    let maybe = match physical.storage_array.kind() {
        ty::Array(element, _) => *element,
        _ => return Err("IntoIter destruction original MaybeUninit array differs".into()),
    };
    let expected = match kind {
        Kind::OuterGlue | Kind::PublicDrop => physical.iterator,
        Kind::InnerGlue | Kind::InnerDrop => physical.sized_inner,
        Kind::SizedPartial => physical.storage_array,
        Kind::PartialHost | Kind::PartialInline => Ty::new_slice(engine.tcx, maybe),
        Kind::Slice => Ty::new_slice(engine.tcx, physical.initialized_element),
        Kind::Bounds | Kind::Child | Kind::Helper => unreachable!(),
    };
    if !matches!(body.local_decls[Local::from_usize(1)].ty.kind(),
        ty::Ref(_,pointee,rustc_hir::Mutability::Mut) if *pointee==expected)
    {
        return Err("IntoIter destruction original receiver type differs".into());
    }
    Ok(())
}
fn scalar(engine: &Engine<'_>, state: &State, index: usize) -> Result<usize, String> {
    let Value::Int {
        expression,
        bits,
        signed: false,
    } = engine.local(state, index)?
    else {
        return Err("IntoIter destruction cursor is not original usize".into());
    };
    if bits != u32::from(engine.tcx.sess.target.pointer_width)
        || !expression.belongs_to(&engine.terms)
        || expression.sort() != &miren::smt::Sort::BitVec(bits)
    {
        return Err("IntoIter destruction cursor type/context differs".into());
    }
    match symbolic::constant(&expression) {
        Some(symbolic::Constant::BitVec { value, .. }) => usize::try_from(value)
            .map_err(|_| "IntoIter destruction cursor exceeds host usize".into()),
        _ => Err("IntoIter destruction cursor is not concrete".into()),
    }
}
impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn array_iterator_drop_arguments(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        arguments: &[Value],
        memory: &Memory,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        if matches!(invocation.kind, Kind::Bounds | Kind::Child | Kind::Helper) {
            return Ok(false);
        }
        self.array_iterator_drop_no_observations(invocation.evidence.instance)?;
        pay(self, arguments.len() + 8)?;
        invocation.check_memory(self, body, memory, &[])?;
        let Some(Value::OwnedArrayIterator {
            identity,
            payload: None,
        }) = arguments.first()
        else {
            return Err("IntoIter destruction argument lacks private metadata".into());
        };
        let Some(PrivateView::Drop(view)) = &identity.view else {
            return Err("IntoIter destruction argument uses another private protocol".into());
        };
        if arguments.len() != body.arg_count
            || view.owner != invocation.owner
            || !Rc::ptr_eq(&view.entry, &invocation.entry)
            || identity.certificate != invocation.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &invocation.identity.seal)
            || !Rc::ptr_eq(&identity.entry, &invocation.identity.entry)
            || view.role != receiver(invocation.kind)
        {
            return Err("IntoIter destruction actual argument identity/role differs".into());
        }
        Ok(true)
    }
    fn array_iterator_drop_no_observations(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if self.specification(instance)?.is_some()
            || self
                .configured_contracts(instance)?
                .iter()
                .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
            || self.foreign_rust_target(instance)?.is_some()
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "IntoIter private destruction contract/adapter observations are unsupported".into(),
            ));
        }
        Ok(())
    }
    fn array_iterator_drop_execute(
        &mut self,
        invocation: Invocation<'tcx>,
        arguments: Vec<Value>,
        state: &State,
        conditions: Vec<Term>,
        stack: &[DefId],
    ) -> Result<Vec<Return>, String> {
        if !state.memory.incoming_byte_roots.is_empty()
            || !state.memory.startup_values.is_empty()
            || !state.memory.isolated_static_types.is_empty()
            || !state.memory.startup_overwritten.is_empty()
            || !state.memory.static_uninitialized.is_empty()
        {
            return Err("IntoIter active Drop auxiliary Memory clone domain unsupported".into());
        }
        let masks = clone_work::masks(self, &state.memory.missing_places)?;
        pay(self, 24 + stack.len())?;
        let memory = state.memory.clone_with_iterator_drop_masks(masks);
        let instance = invocation.evidence.instance;
        let chain = stack.iter().copied().chain([instance.def_id()]).collect();
        let previous = std::mem::replace(&mut self.call_chain, chain);
        #[cfg(test)]
        let (before_execution, kind) = (self.steps, invocation.kind);
        let result = self.execute_body_with_protocol(
            array_drop_glue::Frame::destruction(instance, invocation),
            arguments,
            conditions,
            memory,
            stack,
            activation_flow::Flow::Unarmed,
        );
        #[cfg(test)]
        if std::env::var_os("MIREN_INTOITER_DROP_WORK_TRACE").is_some() {
            println!(
                "Drop work execute={kind:?} before={before_execution} after={}",
                self.steps
            );
        }
        if result.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        result
    }
    pub(in crate::proof) fn array_iterator_drop_place(
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
        let value = self.raw_local(state, place.local.as_usize())?;
        if !matches!(value, Value::OwnedArrayIterator { .. }) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        pay(self, 10)?;
        if !Rc::ptr_eq(body, &self.instantiated_body(caller)?) {
            return Err("IntoIter destruction actual caller Body differs".into());
        }
        let original = body.local_decls[place.local].ty;
        let value = self.local(state, place.local.as_usize())?;
        self.validate_array_iterator_value(original, &value)?;
        let Value::OwnedArrayIterator {
            identity,
            payload: Some(payload),
        } = value
        else {
            unreachable!()
        };
        let instance = ty::Instance::resolve_drop_glue(self.tcx, original);
        let evidence = compiler_evidence::load_drop(self, instance)?;
        schema(self, &evidence, Kind::OuterGlue, &identity)?;
        self.array_iterator_drop_no_observations(instance)?;
        pay(self, 8)?;
        let memory_work = memory_cow_work(self, &state.memory)?;
        pay(self, memory_work)?;
        let argument = self
            .borrow_array_iterator_owner(body, state, *place)?
            .ok_or("IntoIter destruction actual whole owner borrow unavailable")?;
        let Value::Reference {
            allocation,
            projection,
            ..
        } = argument
        else {
            unreachable!()
        };
        if !projection.is_empty() {
            return Err("IntoIter destruction whole owner has a suffix".into());
        }
        let entry = Rc::new(());
        let invocation = Invocation {
            owner: allocation,
            identity,
            entry: entry.clone(),
            evidence,
            kind: Kind::OuterGlue,
            front: payload.front,
            back: payload.back,
            words: None,
        };
        let Some(Value::OwnedArrayIterator {
            payload: Some(actual),
            ..
        }) = &mut state.memory[allocation]
        else {
            unreachable!()
        };
        actual.dropping = Some(Progress {
            next: actual.front,
            leased: None,
            entry,
        });
        let argument = invocation.view(self, Role::Iterator)?;
        let conditions = clone_conditions(self, &state.conditions)?;
        let results =
            self.array_iterator_drop_execute(invocation, vec![argument], state, conditions, stack)?;
        let mut branches = Vec::new();
        for result in results {
            pay(self, 8 + state.memory.initialized_owners.len())?;
            continuation_work(self, state)?;
            let mut branch =
                self.adopt_flow_return(state, result.conditions, result.memory, result.flow)?;
            let Some(Value::OwnedArrayIterator {
                payload: Some(actual),
                ..
            }) = &branch.memory[allocation]
            else {
                return Err("IntoIter completed destruction owner is absent".into());
            };
            let progress = actual
                .dropping
                .as_ref()
                .ok_or("IntoIter completed phase is absent")?;
            progress.validate(actual)?;
            if progress.next != actual.back || progress.leased.is_some() {
                return Err("IntoIter cannot retire undestroyed remaining slots".into());
            }
            let mut masks = clone_work::masks(self, &branch.memory.missing_places)?;
            consume_mask(self, &mut masks, allocation)?;
            let memory_work = memory_cow_work(self, &branch.memory)?;
            pay(
                self,
                memory_work + 8 + 5 * branch.memory.initialized_owners.len(),
            )?;
            branch.memory.missing_places = masks;
            branch.memory.retire_initialized_owner(allocation);
            branch.memory[allocation] = None;
            branch.addresses[place.local.as_usize()] = None;
            branch.locals[place.local.as_usize()] = None;
            branch.constant_receipts.invalidate(*place);
            pay(self, 1)?;
            if branches.len() >= MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "IntoIter Drop branch results exceed existing 512-node limit".into(),
                ));
            }
            branches.push(branch);
        }
        Ok(Some(branches))
    }
    pub(in crate::proof) fn array_iterator_drop_return(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
    ) -> Result<(), String> {
        if let Some(invocation) = invocation {
            invocation.check(self, body, state)?;
        }
        Ok(())
    }
    pub(in crate::proof) fn array_iterator_drop_escape(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        value: &Value,
        state: &State,
        incoming: usize,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        invocation.check(self, body, state)?;
        if matches!(invocation.kind, Kind::Child | Kind::Helper) {
            if !matches!(
                value,
                Value::Unit | Value::Bool(_) | Value::Int { .. } | Value::Float { .. }
            ) {
                return Err("IntoIter child helper result transport remains unsupported".into());
            }
        } else if !matches!(value, Value::Unit) || !body.return_ty().is_unit() {
            return Err("IntoIter private destruction cannot return metadata or ownership".into());
        }
        pay(self, 2)?;
        self.return_value(value.clone(), state, incoming)?;
        self.validate_incoming_frame_escape_with_iterator(state, incoming, invocation.owner)?;
        Ok(true)
    }
}
impl<'tcx> Engine<'tcx> {
    fn array_iterator_drop_actual_call(
        &mut self,
        callee: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if matches!(callee.def, ty::InstanceKind::Item(id)
            if matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
        {
            signature::check(self, callee)?;
        }
        if self.foreign_rust_target(callee)?.is_some()
            || self.specification(callee)?.is_some_and(|spec| {
                spec.trusted || spec.storage_effect.is_some() || spec.returns_alias.is_some()
            })
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "IntoIter active Drop summary/foreign adapter remains unsupported".into(),
            ));
        }
        Ok(())
    }
    pub(in crate::proof) fn array_iterator_drop_call_gate(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        function: &Operand<'tcx>,
    ) -> Result<(), String> {
        let Some(invocation) = invocation else {
            return Ok(());
        };
        invocation.check(self, body, state)?;
        pay(self, 3)?;
        if !matches!(function, Operand::Constant(_))
            || !matches!(
                function.ty(&body.local_decls, self.tcx).kind(),
                ty::FnDef(..)
            )
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "IntoIter active Drop indirect call/early adapter remains unsupported".into(),
            ));
        }
        Ok(())
    }
    pub(in crate::proof) fn array_iterator_drop_call(
        &mut self,
        parent: Option<&Invocation<'tcx>>,
        site: (ty::Instance<'tcx>, BasicBlock),
        body: &Rc<Body<'tcx>>,
        callee: ty::Instance<'tcx>,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<Return>>, String> {
        let Some(parent) = parent else {
            return Ok(None);
        };
        parent.check(self, body, state)?;
        if matches!(parent.kind, Kind::Bounds | Kind::Child | Kind::Helper) {
            if !matches!(callee.def,
                ty::InstanceKind::Item(id)
                    if matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
                && !matches!(
                    callee.def,
                    ty::InstanceKind::Intrinsic(_)
                        | ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_)))
                )
            {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "IntoIter active Drop resolved adapter remains unsupported".into(),
                ));
            }
            self.array_iterator_drop_actual_call(callee)?;
            return Ok(None);
        }
        if site.0 != parent.evidence.instance {
            return Err("IntoIter destruction caller differs".into());
        }
        let TerminatorKind::Call {
            func,
            args,
            target: Some(_),
            ..
        } = &body.basic_blocks[site.1].terminator().kind
        else {
            return Err("IntoIter destruction requires its actual normal Call".into());
        };
        let Operand::Constant(function) = func else {
            return Err("IntoIter destruction Call lacks original function item".into());
        };
        let ty::FnDef(id, arguments) = function.const_.ty().kind() else {
            return Err("IntoIter destruction callee type differs".into());
        };
        pay(self, 4 + arguments.skip_binder().len())?;
        if self.resolve_function_item(*id, arguments.skip_binder())? != callee {
            return Err("IntoIter destruction actual resolved callee differs".into());
        }
        let (kind, source, role) = match (parent.kind, site.1.as_usize()) {
            (Kind::OuterGlue, 0) => (Kind::PublicDrop, 2, Role::Iterator),
            (Kind::PublicDrop, 1) => (Kind::InnerGlue, 4, Role::Inner),
            (Kind::InnerGlue, 0) => (Kind::InnerDrop, 2, Role::Inner),
            (Kind::InnerDrop, 0) => (Kind::SizedPartial, 2, Role::DataSized),
            (Kind::SizedPartial, 0) => (
                if self.tcx.sess.target.llvm_target == "thumbv7em-none-eabihf" {
                    Kind::PartialInline
                } else {
                    Kind::PartialHost
                },
                3,
                Role::DataUnsized,
            ),
            (Kind::PartialHost | Kind::PartialInline, 1) => (Kind::Bounds, 7, Role::DataUnsized),
            (Kind::PartialHost, 4) => (Kind::Slice, 19, Role::RemainingT),
            _ => return Err("IntoIter destruction unexpected core Call occurrence".into()),
        };
        let evidence = match callee.def {
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_))) => {
                compiler_evidence::load_drop(self, callee)?
            }
            ty::InstanceKind::Item(_) => compiler_evidence::load_item(self, callee)?,
            _ => return Err("IntoIter destruction callee adapter is unsupported".into()),
        };
        schema(self, &evidence, kind, &parent.identity)?;
        let mut invocation = Invocation {
            owner: parent.owner,
            identity: parent.identity.clone(),
            entry: parent.entry.clone(),
            evidence,
            kind,
            front: parent.front,
            back: parent.back,
            words: parent.words.clone(),
        };
        let mut values = Vec::new();
        pay(self, args.len() * 4 + 8)?;
        if kind == Kind::Bounds {
            let words = steps::observe_payload(self, state, parent.owner)?;
            pay(self, 1)?;
            invocation.words = Some(Rc::new(words));
            if args.len() != 2 {
                return Err("IntoIter destruction bounds arity differs".into());
            }
            for argument in args {
                let value = self.evaluate_operand(site.0.def_id(), body, state, &argument.node)?;
                let Value::Int {
                    expression,
                    bits,
                    signed: false,
                } = &value
                else {
                    return Err(
                        "IntoIter destruction bounds arguments require original usize".into(),
                    );
                };
                if *bits != u32::from(self.tcx.sess.target.pointer_width)
                    || !expression.belongs_to(&self.terms)
                    || expression.sort() != &miren::smt::Sort::BitVec(*bits)
                {
                    return Err("IntoIter destruction bounds argument sort/context differs".into());
                }
                values.push(value);
            }
            let conditions = clone_conditions(self, &state.conditions)?;
            state.conditions = self.call_preconditions(
                callee,
                &values,
                conditions,
                &state.memory,
                (
                    site.0.def_id(),
                    body.basic_blocks[site.1].terminator().source_info.span,
                ),
            )?;
        } else {
            self.array_iterator_drop_no_observations(callee)?;
            parent.require_role(self, state, source, role)?;
            if args.is_empty()
                || !matches!(&args[0].node,Operand::Move(place) if local(*place,source))
            {
                return Err("IntoIter destruction forwarding operand differs".into());
            }
            values.push(invocation.view(self, receiver(kind))?);
            let mut masks = clone_work::masks(self, &state.missing_places)?;
            consume_mask(self, &mut masks, source)?;
            state.missing_places = masks;
            state
                .constant_receipts
                .invalidate(Place::from(Local::from_usize(source)));
            if args.len() == 2 {
                values.push(self.evaluate_operand(site.0.def_id(), body, state, &args[1].node)?);
            }
            if values.len() != args.len() {
                return Err("IntoIter destruction forwarding arity differs".into());
            }
        }
        let conditions = clone_conditions(self, &state.conditions)?;
        self.array_iterator_drop_execute(invocation, values, state, conditions, stack)
            .map(Some)
    }
    fn array_iterator_drop_usize(&mut self, value: usize) -> Result<Value, String> {
        pay(self, 12)?; // Actual integer metadata/Context term creation, before interning.
        #[cfg(test)]
        CONSTRUCTIONS.with(|events| events.borrow_mut().push("usize"));
        Ok(symbolic::integer(
            &self.terms,
            value as u128,
            u32::from(self.tcx.sess.target.pointer_width),
            false,
        ))
    }
    fn array_iterator_drop_range_value(
        &mut self,
        original: Ty<'tcx>,
        front: usize,
        back: usize,
    ) -> Result<Value, String> {
        const NAME: &str = "core::ops::index_range::IndexRange";
        // Bounded original descriptor lookup/identity/field planning before constructed allocation.
        pay(
            self,
            24 + "IndexRange".len() + "index_range".len() + "ops".len() + "core".len(),
        )?;
        let ty::Adt(definition, arguments) = original.kind() else {
            return Err("IntoIter alive original type is not its core IndexRange".into());
        };
        let index_module = self
            .tcx
            .opt_parent(definition.did())
            .ok_or("IntoIter alive original type has no module parent")?;
        let ops_module = self
            .tcx
            .opt_parent(index_module)
            .ok_or("IntoIter alive original index module has no parent")?;
        let root = self
            .tcx
            .opt_parent(ops_module)
            .ok_or("IntoIter alive original ops module has no parent")?;
        let core = self
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("IntoIter alive core identity unavailable")?
            .krate;
        if definition.did().krate != core
            || !arguments.is_empty()
            || !definition.is_struct()
            || definition.variants().len() != 1
            || definition.non_enum_variant().fields.len() != 2
            || self.tcx.item_name(definition.did()).as_str() != "IndexRange"
            || self.tcx.def_kind(index_module) != DefKind::Mod
            || self.tcx.item_name(index_module).as_str() != "index_range"
            || self.tcx.def_kind(ops_module) != DefKind::Mod
            || self.tcx.item_name(ops_module).as_str() != "ops"
            || root.index != rustc_span::def_id::CRATE_DEF_INDEX
            || self.tcx.crate_name(core).as_str() != "core"
        {
            return Err("IntoIter alive original core nominal identity differs".into());
        }
        for (field, expected) in definition
            .non_enum_variant()
            .fields
            .iter()
            .zip(["start", "end"])
        {
            pay(self, 4 + expected.len())?;
            if field.name.as_str() != expected
                || field.ty(self.tcx, arguments).skip_norm_wip() != self.tcx.types.usize
            {
                return Err("IntoIter alive original core field name/type differs".into());
            }
        }
        // Vec header/two slots; nominal name allocation/bytes; Value::Adt metadata; field Vec,
        // two String headers + Value moves + exact start/end bytes; AdtFields Rc allocation;
        // constructed's bounded variant/Option/layout reads. Term creation is separately prepaid.
        pay(
            self,
            3 + NAME.len() + 1 + 6 + 1 + 2 * (3 + 5) + 5 + 3 + 2 + 12,
        )?;
        let start = self.array_iterator_drop_usize(front)?;
        let end = self.array_iterator_drop_usize(back)?;
        #[cfg(test)]
        CONSTRUCTIONS.with(|events| events.borrow_mut().push("constructed"));
        self.constructed(original, 0, vec![start, end])
    }
    pub(in crate::proof) fn array_iterator_drop_statement(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        location: Location,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        invocation.check(self, body, state)?;
        let StatementKind::Assign(pair) =
            &body.basic_blocks[location.block].statements[location.statement_index].kind
        else {
            return Ok(false);
        };
        let (destination, rvalue) = (&pair.0, &pair.1);
        if matches!(invocation.kind, Kind::Bounds | Kind::Child | Kind::Helper) {
            if matches!(
                rvalue,
                Rvalue::RawPtr(..)
                    | Rvalue::Cast(
                        CastKind::Transmute
                            | CastKind::BoxDerefTransmute
                            | CastKind::PointerWithExposedProvenance
                            | CastKind::PointerExposeProvenance
                            | CastKind::PtrToPtr,
                        ..
                    )
            ) {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "IntoIter child Drop physical address operations remain unsupported".into(),
                ));
            }
            if let Rvalue::BinaryOp(_, operands) = rvalue
                && [&operands.0, &operands.1].iter().any(|operand| {
                    matches!(
                        operand.ty(&body.local_decls, self.tcx).kind(),
                        ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..)
                    )
                })
            {
                return Err(self.categorized_error(
                    UnknownCategory::Semantics,
                    "IntoIter child Drop pointer comparisons remain unsupported".into(),
                ));
            }
            return Ok(false);
        }
        let b = location.block.as_usize();
        let o = location.statement_index;
        let mut value = None;
        match invocation.kind {
            Kind::OuterGlue | Kind::InnerGlue if b == 0 && o == 0 => {
                invocation.require_role(self, state, 1, receiver(invocation.kind))?;
                if !matches!(
                        rvalue, Rvalue::Ref(_,BorrowKind::Mut{..},place) if path(*place,1,&[]))
                {
                    return Err("IntoIter destruction glue reborrow differs".into());
                }
                value = Some(invocation.view(self, receiver(invocation.kind))?);
            }
            Kind::PublicDrop if b == 1 && o == 1 => {
                invocation.require_role(self, state, 1, Role::Iterator)?;
                if !matches!(
                        rvalue, Rvalue::Ref(_,BorrowKind::Mut{..},place) if path(*place,1,&[0,0]))
                {
                    return Err("IntoIter destruction ManuallyDrop projection differs".into());
                }
                value = Some(invocation.view(self, Role::Inner)?);
            }
            Kind::InnerDrop if b == 0 && o == 1 => {
                invocation.require_role(self, state, 1, Role::Inner)?;
                if !matches!(
                        rvalue, Rvalue::Ref(_,BorrowKind::Mut{..},place) if path(*place,1,&[1]))
                {
                    return Err("IntoIter destruction data projection differs".into());
                }
                value = Some(invocation.view(self, Role::DataSized)?);
            }
            Kind::InnerDrop if b == 0 && o == 3 => {
                invocation.require_role(self, state, 1, Role::Inner)?;
                if !matches!(
                        rvalue, Rvalue::Use(Operand::Copy(place),_) if path(*place,1,&[0]))
                {
                    return Err("IntoIter destruction alive projection differs".into());
                }
                let physical = self.array_iterator_certificate(&invocation.identity)?;
                let original = exact_field(self, physical.sized_inner, 0)?;
                value = Some(self.array_iterator_drop_range_value(
                    original,
                    invocation.front,
                    invocation.back,
                )?);
            }
            Kind::SizedPartial if b == 0 && o == 1 => {
                invocation.require_role(self, state, 1, Role::DataSized)?;
                if !matches!(
                        rvalue, Rvalue::Cast(CastKind::PointerCoercion(
                    ty::adjustment::PointerCoercion::Unsize,_),operand,_)
                    if copied(operand,1))
                {
                    return Err("IntoIter destruction data Unsize differs".into());
                }
                value = Some(invocation.view(self, Role::DataUnsized)?);
            }
            Kind::PartialHost | Kind::PartialInline => {
                invocation.require_role(self, state, 1, Role::DataUnsized)?;
                if b == 0 && o == 3 {
                    if !matches!(
                        rvalue, Rvalue::RawPtr(RawPtrKind::Mut,place) if path(*place,1,&[]))
                    {
                        return Err(
                            "IntoIter destruction original raw MaybeUninit slice differs".into(),
                        );
                    }
                    value = Some(invocation.view(self, Role::RawWhole)?);
                } else if b == 1 && o == 3 {
                    if !matches!(
                        rvalue, Rvalue::UnaryOp(UnOp::PtrMetadata,operand) if copied(operand,1))
                    {
                        return Err("IntoIter destruction physical slice metadata differs".into());
                    }
                    let count = self.array_iterator_certificate(&invocation.identity)?.count;
                    value = Some(self.array_iterator_drop_usize(count)?);
                } else if b == 3 && o == 7 {
                    invocation.require_role(self, state, 5, Role::RawWhole)?;
                    if !matches!(
                        rvalue, Rvalue::Cast(CastKind::PtrToPtr,operand,_) if copied(operand,5))
                    {
                        return Err("IntoIter destruction raw element cast differs".into());
                    }
                    value = Some(invocation.view(self, Role::MaybeElement)?);
                } else if b == 3 && o == 9 {
                    invocation.require_role(self, state, 15, Role::MaybeElement)?;
                    if scalar(self, state, 10)? != invocation.front
                        || !matches!(
                        rvalue, Rvalue::BinaryOp(BinOp::Offset,operands)
                            if copied(&operands.0,15)&&copied(&operands.1,10))
                    {
                        return Err("IntoIter destruction raw range offset differs".into());
                    }
                    value = Some(invocation.view(self, Role::RemainingElement)?);
                } else if b == 3 && o == 10 {
                    invocation.require_role(self, state, 16, Role::RemainingElement)?;
                    if scalar(self, state, 12)? != invocation.back - invocation.front
                        || !matches!(
                        rvalue, Rvalue::Aggregate(kind,operands)
                            if matches!(kind.as_ref(),
                                AggregateKind::RawPtr(_,rustc_hir::Mutability::Mut))
                            && operands.len()==2
                            && copied(&operands.raw[0],16)&&copied(&operands.raw[1],12))
                    {
                        return Err(
                            "IntoIter destruction exact remaining fat pointer differs".into()
                        );
                    }
                    value = Some(invocation.view(self, Role::RawRemainingMaybe)?);
                } else if b == 3 && o == 15 {
                    invocation.require_role(self, state, 4, Role::RawRemainingMaybe)?;
                    if !matches!(
                        rvalue, Rvalue::Ref(_,BorrowKind::Mut{..},place) if path(*place,4,&[]))
                    {
                        return Err(
                            "IntoIter destruction remaining MaybeUninit reborrow differs".into(),
                        );
                    }
                    value = Some(invocation.view(self, Role::RemainingMaybe)?);
                } else if b == 4 && o == 1 {
                    invocation.require_role(self, state, 3, Role::RemainingMaybe)?;
                    if !matches!(
                        rvalue, Rvalue::RawPtr(RawPtrKind::Mut,place) if path(*place,3,&[]))
                    {
                        return Err("IntoIter destruction remaining raw slice differs".into());
                    }
                    value = Some(invocation.view(self, Role::RawRemainingMaybe)?);
                } else if b == 4 && o == 2 {
                    invocation.require_role(self, state, 18, Role::RawRemainingMaybe)?;
                    if !matches!(
                        rvalue, Rvalue::Cast(CastKind::PtrToPtr,operand,_) if copied(operand,18))
                    {
                        return Err("IntoIter destruction initialized slice cast differs".into());
                    }
                    value = Some(invocation.view(self, Role::RawRemainingT)?);
                } else if invocation.kind == Kind::PartialHost && b == 4 && o == 4 {
                    invocation.require_role(self, state, 17, Role::RawRemainingT)?;
                    if !matches!(
                        rvalue, Rvalue::Ref(_,BorrowKind::Mut{..},place) if path(*place,17,&[]))
                    {
                        return Err(
                            "IntoIter destruction initialized slice reborrow differs".into()
                        );
                    }
                    value = Some(invocation.view(self, Role::RemainingT)?);
                } else if invocation.kind == Kind::PartialInline && b == 7 && o == 0 {
                    invocation.require_role(self, state, 17, Role::RawRemainingT)?;
                    let index = scalar(self, state, 19)?;
                    if index >= invocation.back - invocation.front
                        || !matches!(
                        rvalue, Rvalue::RawPtr(RawPtrKind::Mut,place)
                            if place.local.as_usize()==17&&place.projection.as_ref()
                                ==[ProjectionElem::Deref,
                                    ProjectionElem::Index(Local::from_usize(19))])
                    {
                        return Err(
                            "IntoIter destruction inline raw element occurrence differs".into()
                        );
                    }
                    value = Some(invocation.view(self, Role::Element(invocation.front + index))?);
                }
            }
            Kind::Slice if b == 0 && o == 0 => {
                invocation.require_role(self, state, 1, Role::RemainingT)?;
                if !matches!(
                        rvalue, Rvalue::UnaryOp(UnOp::PtrMetadata,operand) if copied(operand,1))
                {
                    return Err("IntoIter destruction slice loop metadata differs".into());
                }
                value = Some(self.array_iterator_drop_usize(invocation.back - invocation.front)?);
            }
            Kind::Slice if b == 2 && o == 0 => {
                invocation.require_role(self, state, 1, Role::RemainingT)?;
                let index = scalar(self, state, 3)?;
                if index >= invocation.back - invocation.front
                    || !matches!(
                        rvalue, Rvalue::RawPtr(RawPtrKind::Mut,place)
                        if place.local.as_usize()==1&&place.projection.as_ref()
                            ==[ProjectionElem::Deref,ProjectionElem::Index(Local::from_usize(3))])
                {
                    return Err("IntoIter destruction slice raw element occurrence differs".into());
                }
                value = Some(invocation.view(self, Role::Element(invocation.front + index))?);
            }
            Kind::OuterGlue
            | Kind::PublicDrop
            | Kind::InnerGlue
            | Kind::InnerDrop
            | Kind::SizedPartial
            | Kind::Bounds
            | Kind::Slice
            | Kind::Child
            | Kind::Helper => {}
        }
        let Some(value) = value else { return Ok(false) };
        if !destination.projection.is_empty()
            || state.addresses[destination.local.as_usize()].is_some()
        {
            return Err("IntoIter private destruction metadata cannot gain guest storage".into());
        }
        pay(self, 8)?;
        state.locals[destination.local.as_usize()] = Some(value);
        state
            .missing_places
            .initialize(destination.local.as_usize(), &[]);
        state.constant_receipts.invalidate(*destination);
        Ok(true)
    }
    pub(in crate::proof) fn array_iterator_drop_element(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        block: BasicBlock,
        stack: &[DefId],
    ) -> Result<Option<Vec<State>>, String> {
        let Some(invocation) = invocation else {
            return Ok(None);
        };
        invocation.check(self, body, state)?;
        if !matches!(invocation.kind, Kind::Slice | Kind::PartialInline) {
            return Ok(None);
        }
        let (expected, local_index, cursor) = if invocation.kind == Kind::Slice {
            (2, 6, 3)
        } else {
            (7, 20, 19)
        };
        let TerminatorKind::Drop { place, .. } = &body.basic_blocks[block].terminator().kind else {
            return Ok(None);
        };
        if block.as_usize() != expected
            || place.local.as_usize() != local_index
            || place.projection.as_ref() != [ProjectionElem::Deref]
        {
            return Err("IntoIter remaining Drop actual element occurrence differs".into());
        }
        let Role::Element(index) = invocation.role(self, state, local_index)? else {
            return Err("IntoIter remaining Drop pending raw element marker differs".into());
        };
        if scalar(self, state, cursor)? != index - invocation.front + 1 {
            return Err("IntoIter remaining Drop advanced compiler cursor differs".into());
        }
        if invocation.kind == Kind::PartialInline {
            let scope = body.basic_blocks[block].terminator().source_info.scope;
            let inline = body.source_scopes[scope]
                .inlined
                .as_ref()
                .ok_or("IntoIter inline Drop original source scope is unavailable")?;
            let element = self
                .array_iterator_certificate(&invocation.identity)?
                .initialized_element;
            if inline.0
                != ty::Instance::resolve_drop_glue(self.tcx, Ty::new_slice(self.tcx, element))
            {
                return Err(
                    "IntoIter inline Drop original resolved source Instance differs".into(),
                );
            }
        }
        let original = place.ty(&body.local_decls, self.tcx).ty;
        let element = self
            .array_iterator_certificate(&invocation.identity)?
            .initialized_element;
        if original != element {
            return Err("IntoIter child original Drop type differs".into());
        }
        let child = ty::Instance::resolve_drop_glue(self.tcx, element);
        let evidence = compiler_evidence::load_drop(self, child)?;
        self.array_iterator_drop_actual_call(child)?;
        let Some(Value::OwnedArrayIterator {
            payload: Some(payload),
            ..
        }) = &state.memory[invocation.owner]
        else {
            unreachable!()
        };
        let progress = payload.dropping.as_ref().unwrap();
        if progress.next != index || progress.leased.is_some() {
            return Err("IntoIter child Drop source slot was already leased or retired".into());
        }
        let value = payload
            .slots
            .get(index)
            .and_then(Option::as_ref)
            .ok_or("IntoIter child Drop source slot is uninitialized")?;
        steps::validate_element(self, element, value, &state.conditions, 0, &mut 0)?;
        if state.memory.storage_slots().saturating_add(2) > memory::MAX_ALLOCATIONS
            || state.memory.initialized_owners.len() >= MAX_INPUT_VALUES
            || self.initialized_type_count() >= MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter child lease exceeds existing storage/type limits".into(),
            ));
        }
        // Prepay actual sole-slot Vec COW, allocation Vec COW/growth and type/Owner publication.
        let mut owned = 2 + payload.len();
        let mut nodes = 0;
        for value in payload.slots.iter().flatten() {
            owned += steps::value_clone_work(self, value, 0, &mut nodes)?;
        }
        let memory_work = memory_cow_work(self, &state.memory)?;
        pay(
            self,
            owned
                + memory_work
                + 20
                + 5 * state.memory.initialized_owners.len()
                + 3 * self.initialized_type_count(),
        )?;
        let allocation = state.memory.len();
        let Some(Value::OwnedArrayIterator {
            payload: Some(payload),
            ..
        }) = &mut state.memory[invocation.owner]
        else {
            unreachable!()
        };
        let value = Rc::make_mut(&mut payload.slots)[index]
            .take()
            .ok_or("IntoIter child slot was consumed during admission")?;
        payload.dropping.as_mut().unwrap().leased = Some(Lease { index, allocation });
        state.memory.push(Some(value));
        let witness = ElementWitness {
            owner: invocation.owner,
            identity: invocation.identity.clone(),
            entry: invocation.entry.clone(),
            body: BodyEvidence {
                instance: invocation.evidence.instance,
                current: body.clone(),
            },
            block,
            index,
            original: element,
        };
        self.bind_iterator_element_storage(&witness, state, allocation)?;
        let argument = Value::Reference {
            allocation,
            projection: Vec::new(),
            mutable: true,
        };
        let conditions = clone_conditions(self, &state.conditions)?;
        let conditions = self.call_preconditions(
            child,
            std::slice::from_ref(&argument),
            conditions,
            &state.memory,
            (
                invocation.evidence.instance.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        let words = steps::observe_payload(self, state, invocation.owner)?;
        pay(self, 1)?;
        let child_frame = Invocation {
            owner: invocation.owner,
            identity: invocation.identity.clone(),
            entry: invocation.entry.clone(),
            evidence,
            kind: Kind::Child,
            front: invocation.front,
            back: invocation.back,
            words: Some(Rc::new(words)),
        };
        let results = self.array_iterator_drop_execute(
            child_frame,
            vec![argument],
            state,
            conditions,
            stack,
        )?;
        let mut branches = Vec::new();
        for result in results {
            if !matches!(result.value, Value::Unit) {
                return Err("IntoIter actual child Drop returned ownership or metadata".into());
            }
            continuation_work(self, state)?;
            let mut branch =
                self.adopt_flow_return(state, result.conditions, result.memory, result.flow)?;
            invocation.check(self, body, &branch)?;
            witness.element(self, &branch, allocation)?;
            let mut masks = clone_work::masks(self, &branch.memory.missing_places)?;
            consume_mask(self, &mut masks, allocation)?;
            let memory_work = memory_cow_work(self, &branch.memory)?;
            pay(
                self,
                memory_work + 8 + 5 * branch.memory.initialized_owners.len(),
            )?;
            branch.memory.missing_places = masks;
            branch.memory.retire_initialized_owner(allocation);
            branch.memory[allocation] = None;
            let Some(Value::OwnedArrayIterator {
                payload: Some(payload),
                ..
            }) = &mut branch.memory[invocation.owner]
            else {
                unreachable!()
            };
            let progress = payload.dropping.as_mut().unwrap();
            progress.leased = None;
            progress.next = index + 1;
            payload.dropping.as_ref().unwrap().validate(payload)?;
            branch.locals[local_index] = None;
            let mut masks = clone_work::masks(self, &branch.missing_places)?;
            consume_mask(self, &mut masks, local_index)?;
            branch.missing_places = masks;
            branch
                .constant_receipts
                .invalidate(Place::from(Local::from_usize(local_index)));
            pay(self, 1)?;
            if branches.len() >= MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "IntoIter Drop branch results exceed existing 512-node limit".into(),
                ));
            }
            branches.push(branch);
        }
        Ok(Some(branches))
    }
}

/// Issued only at the authenticated real loop Drop after the source slot has moved once.
pub(in crate::proof) struct ElementWitness<'tcx> {
    owner: usize,
    identity: Identity,
    entry: Rc<()>,
    body: BodyEvidence<'tcx>,
    block: BasicBlock,
    index: usize,
    original: Ty<'tcx>,
}
impl<'tcx> ElementWitness<'tcx> {
    pub(in crate::proof) fn element(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        allocation: usize,
    ) -> Result<Ty<'tcx>, String> {
        state.flow.require_unarmed()?;
        let cached = engine.bodies.borrow();
        if cached
            .get(&self.body.instance)
            .is_none_or(|body| !Rc::ptr_eq(body, &self.body.current))
        {
            return Err("IntoIter element issuer current Body was replaced".into());
        }
        let physical = engine.array_iterator_certificate(&self.identity)?;
        if self.original != physical.initialized_element {
            return Err("IntoIter element issuer original type differs".into());
        }
        let TerminatorKind::Drop { place, .. } =
            &self.body.current.basic_blocks[self.block].terminator().kind
        else {
            return Err("IntoIter element issuer lacks actual Drop occurrence".into());
        };
        if place.ty(&self.body.current.local_decls, engine.tcx).ty != self.original {
            return Err("IntoIter element issuer actual Drop pointee differs".into());
        }
        let Some(Value::OwnedArrayIterator {
            payload: Some(payload),
            identity,
        }) = state.memory.get(self.owner).and_then(Option::as_ref)
        else {
            return Err("IntoIter element issuer owner absent".into());
        };
        let progress = payload
            .dropping
            .as_ref()
            .ok_or("IntoIter element issuer active phase absent")?;
        let lease = progress
            .leased
            .as_ref()
            .ok_or("IntoIter element issuer sole lease absent")?;
        if identity.certificate != self.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &self.identity.seal)
            || !Rc::ptr_eq(&progress.entry, &self.entry)
            || lease.index != self.index
            || lease.allocation != allocation
            || allocation == self.owner
            || state
                .memory
                .get(allocation)
                .and_then(Option::as_ref)
                .is_none()
        {
            return Err("IntoIter element issuer lease/owner identity differs".into());
        }
        progress.validate(payload)?;
        Ok(self.original)
    }
}
impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn array_iterator_drop_helper_execute(
        &mut self,
        parent: &Invocation<'tcx>,
        body: &Rc<Body<'tcx>>,
        callee: ty::Instance<'tcx>,
        values: Vec<Value>,
        state: &State,
        call: (&[DefId], (DefId, Span)),
    ) -> Result<Vec<Return>, String> {
        let (stack, site) = call;
        parent.check(self, body, state)?;
        if !matches!(parent.kind, Kind::Child | Kind::Helper) {
            return Err("IntoIter element helper has no active child invocation".into());
        }
        self.array_iterator_drop_actual_call(callee)?;
        let evidence = match callee.def {
            ty::InstanceKind::Item(id)
                if matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) =>
            {
                compiler_evidence::load_item(self, callee)?
            }
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_))) => {
                compiler_evidence::load_drop(self, callee)?
            }
            _ => return Err("IntoIter element helper adapter remains unsupported".into()),
        };
        let conditions = clone_conditions(self, &state.conditions)?;
        let conditions =
            self.call_preconditions(callee, &values, conditions, &state.memory, site)?;
        pay(self, 10)?;
        let invocation = Invocation {
            owner: parent.owner,
            identity: parent.identity.clone(),
            entry: parent.entry.clone(),
            evidence,
            kind: Kind::Helper,
            front: parent.front,
            back: parent.back,
            words: parent.words.clone(),
        };
        self.array_iterator_drop_execute(invocation, values, state, conditions, stack)
    }
    pub(in crate::proof) fn array_iterator_drop_child_frame<'a>(
        &self,
        invocation: Option<&'a Invocation<'tcx>>,
    ) -> Option<&'a Invocation<'tcx>> {
        invocation.filter(|frame| matches!(frame.kind, Kind::Child | Kind::Helper))
    }
}

fn clone_conditions(engine: &mut Engine<'_>, conditions: &[Term]) -> Result<Vec<Term>, String> {
    pay(engine, conditions.len() + 1)?;
    Ok(conditions.to_vec())
}

fn memory_cow_work(engine: &mut Engine<'_>, memory: &Memory) -> Result<usize, String> {
    pay(engine, memory.len() + 1)?;
    let mut owned = 2 + memory.len();
    let mut nodes = 0;
    for value in memory.iter().flatten() {
        owned += transport_clone_work(engine, value, &mut nodes)?;
    }
    Ok(owned)
}
fn transport_clone_work(
    engine: &mut Engine<'_>,
    value: &Value,
    nodes: &mut usize,
) -> Result<usize, String> {
    pay(engine, 1)?;
    *nodes += 1;
    if *nodes > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter Drop transport clone exceeds existing 512-node limit".into(),
        ));
    }
    match value {
        Value::OwnedArrayIterator { .. } => Ok(32), // Identity/views/progress and shared slots Rc.
        Value::Reference { projection, .. } => {
            if projection.len() > MAX_INPUT_DEPTH {
                return Err("IntoIter Drop reference clone exceeds depth16 limit".into());
            }
            for part in projection {
                pay(engine, 1)?;
                match part {
                    MemoryProjection::Field(_) | MemoryProjection::Variant(_) => {}
                    MemoryProjection::Index(_)
                    | MemoryProjection::TypedIndex { .. }
                    | MemoryProjection::Slice { .. }
                    | MemoryProjection::Chunks { .. } => {
                        return Err(
                            "IntoIter Drop owning reference projection clone unsupported".into(),
                        );
                    }
                }
            }
            Ok(8 + 2 * projection.len())
        }
        _ => steps::value_clone_work(engine, value, 0, nodes),
    }
}
fn consume_mask(
    engine: &mut Engine<'_>,
    masks: &mut initialized_places::MissingPlaces,
    owner: usize,
) -> Result<(), String> {
    pay(engine, 2 * masks.entries().len() + 4)?;
    masks.consume(owner, Vec::new())
}
fn continuation_work(engine: &mut Engine<'_>, state: &State) -> Result<(), String> {
    state.flow.require_unarmed()?;
    if state.locals.len() > MAX_INPUT_VALUES
        || state.addresses.len() > MAX_INPUT_VALUES
        || state.constant_receipts.len() > MAX_INPUT_VALUES
    {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter Drop continuation clone exceeds existing 512-node limit".into(),
        ));
    }
    pay(engine, state.locals.len() + 1)?;
    let mut work =
        8 + state.locals.len() + state.addresses.len() + 8 * state.constant_receipts.len();
    let mut nodes = 0;
    for value in state.locals.iter().flatten() {
        work += transport_clone_work(engine, value, &mut nodes)?;
    }
    work += clone_work::mask_clone_work(engine, &state.missing_places)?;
    pay(engine, work)
}
impl Engine<'_> {
    pub(in crate::proof) fn array_iterator_drop_adopt_work(
        &mut self,
        invocation: Option<&Invocation<'_>>,
        state: &State,
    ) -> Result<(), String> {
        if invocation.is_some() {
            continuation_work(self, state)?;
        }
        Ok(())
    }
}

#[cfg(test)]
std::thread_local! {
    static CONSTRUCTIONS: std::cell::RefCell<Vec<&'static str>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
pub(in crate::proof::array_iterator_constructors) fn controls<'tcx>(
    engine: &mut Engine<'tcx>,
    body: &Rc<Body<'tcx>>,
    value: &Value,
    memory: &Memory,
) {
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: initialized_places::MissingPlaces::default(),
        conditions: Vec::new(),
        memory: memory.clone(),
    };
    state.locals[0] = Some(value.clone());
    let reference = engine
        .borrow_array_iterator_owner(body, &mut state, Place::from(Local::from_usize(0)))
        .unwrap()
        .unwrap();
    let Value::Reference {
        allocation: owner, ..
    } = reference
    else {
        panic!("actual original typed owner storage")
    };
    let Value::OwnedArrayIterator {
        identity,
        payload: Some(payload),
    } = value
    else {
        panic!("actual constructor owner")
    };
    let entry = Rc::new(());
    let glue = ty::Instance::resolve_drop_glue(engine.tcx, body.return_ty());
    let evidence = compiler_evidence::load_drop(engine, glue).unwrap();
    let invocation = Invocation {
        owner,
        identity: identity.clone(),
        entry: entry.clone(),
        evidence,
        kind: Kind::OuterGlue,
        front: payload.front,
        back: payload.back,
        words: None,
    };
    let Some(Value::OwnedArrayIterator {
        payload: Some(payload),
        ..
    }) = &mut state.memory[owner]
    else {
        panic!("typed constructor owner")
    };
    payload.dropping = Some(Progress {
        next: payload.front,
        leased: None,
        entry,
    });
    let current = invocation.evidence.current.clone();
    invocation.check(engine, &current, &state).unwrap();
    let original_inner = engine
        .array_iterator_certificate(identity)
        .unwrap()
        .sized_inner;
    let original_range = exact_field(engine, original_inner, 0).unwrap();
    let full_limit = engine.limits.max_steps;
    let header = 24 + "IndexRange".len() + "index_range".len() + "ops".len() + "core".len();
    let field_plan = 4 + 5 + 4 + 3;
    let range =
        3 + "core::ops::index_range::IndexRange".len() + 1 + 6 + 1 + 2 * (3 + 5) + 5 + 3 + 2 + 12;
    for (mode, permitted) in [(0, 19), (1, 11), (2, header + field_plan + range - 1)] {
        CONSTRUCTIONS.with(|events| events.borrow_mut().clear());
        let before = engine.steps;
        engine.limits.max_steps = before + permitted;
        let result = match mode {
            0 => invocation.view(engine, Role::Iterator),
            1 => engine.array_iterator_drop_usize(31),
            2 => engine.array_iterator_drop_range_value(original_range, 0, 2),
            _ => unreachable!(),
        };
        assert!(
            result
                .unwrap_err()
                .contains("shared execution step limit reached")
        );
        assert!(engine.steps > engine.limits.max_steps);
        CONSTRUCTIONS.with(|events| assert!(events.borrow().is_empty()));
        engine.limits.max_steps = full_limit;
    }
    CONSTRUCTIONS.with(|events| events.borrow_mut().clear());
    let value = engine
        .array_iterator_drop_range_value(original_range, 0, 2)
        .unwrap();
    let Value::Adt { name, fields, .. } = value else {
        panic!("actual original core range")
    };
    assert_eq!(name, "core::ops::index_range::IndexRange");
    assert_eq!(fields[0].0, "start");
    assert_eq!(fields[1].0, "end");
    CONSTRUCTIONS.with(|events| assert_eq!(*events.borrow(), ["usize", "usize", "constructed"]));
    CONSTRUCTIONS.with(|events| events.borrow_mut().clear());
    assert!(
        engine
            .array_iterator_drop_range_value(engine.tcx.types.u16, 0, 2)
            .is_err()
    );
    CONSTRUCTIONS.with(|events| assert!(events.borrow().is_empty()));
    let initialized_element = engine
        .array_iterator_certificate(identity)
        .unwrap()
        .initialized_element;
    assert!(
        engine
            .array_iterator_drop_range_value(initialized_element, 0, 2)
            .is_err()
    );
    CONSTRUCTIONS.with(|events| assert!(events.borrow().is_empty()));
    let sibling = state.clone();
    for change in 0..8 {
        let mut hostile = state.clone();
        match change {
            0 => {
                hostile.memory[owner] = None;
            }
            1 => {
                hostile
                    .memory
                    .missing_places
                    .consume(owner, Vec::new())
                    .unwrap();
            }
            2 => {
                hostile.memory.retire_initialized_owner(owner);
            }
            3..=7 => {
                let Some(Value::OwnedArrayIterator {
                    identity,
                    payload: Some(payload),
                }) = &mut hostile.memory[owner]
                else {
                    unreachable!()
                };
                match change {
                    3 => payload.front += 1,
                    4 => payload.dropping.as_mut().unwrap().entry = Rc::new(()),
                    5 => Rc::make_mut(&mut payload.slots)[0] = None,
                    6 => identity.entry = Rc::new(()),
                    7 => {
                        payload.dropping.as_mut().unwrap().leased = Some(Lease {
                            index: payload.front,
                            allocation: owner,
                        })
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        assert!(
            invocation.check(engine, &current, &hostile).is_err(),
            "hostile {change}"
        );
        invocation.check(engine, &current, &sibling).unwrap();
    }
    let changed_body = Rc::new(current.as_ref().clone());
    assert!(invocation.check(engine, &changed_body, &state).is_err());
    engine.bodies.borrow_mut().insert(glue, changed_body);
    assert!(invocation.check(engine, &current, &state).is_err());
    engine.bodies.borrow_mut().insert(glue, current.clone());
    invocation.check(engine, &current, &state).unwrap();
    let duplicate = || Invocation {
        owner: invocation.owner,
        identity: invocation.identity.clone(),
        entry: invocation.entry.clone(),
        evidence: BodyEvidence {
            instance: invocation.evidence.instance,
            current: invocation.evidence.current.clone(),
        },
        kind: invocation.kind,
        front: invocation.front,
        back: invocation.back,
        words: invocation.words.clone(),
    };
    let mut other_invocation = duplicate();
    other_invocation.owner = usize::MAX;
    assert!(other_invocation.check(engine, &current, &state).is_err());
    other_invocation = duplicate();
    other_invocation.entry = Rc::new(());
    assert!(other_invocation.check(engine, &current, &state).is_err());
    let configured = Invocation {
        words: Some(Rc::new(Vec::new())),
        ..duplicate()
    };
    assert!(configured.check(engine, &current, &state).is_err());
    // Authenticate the actual host slice frame or ARM inline partial-drop element occurrence.
    let mut loop_evidence = compiler_evidence::load_drop(engine, glue).unwrap();
    loop {
        if loop_evidence
            .current
            .basic_blocks
            .iter()
            .any(|block| matches!(block.terminator().kind, TerminatorKind::Drop { .. }))
        {
            break;
        }
        let mut next = None;
        for block in loop_evidence.current.basic_blocks.iter() {
            if let TerminatorKind::Call {
                func: Operand::Constant(function),
                ..
            } = &block.terminator().kind
            {
                let ty::FnDef(id, args) = function.const_.ty().kind() else {
                    unreachable!()
                };
                let callee = engine
                    .resolve_function_item(*id, args.skip_binder())
                    .unwrap();
                if engine.tcx.item_name(callee.def_id()).as_str() != "precondition_check" {
                    next = Some(callee);
                }
            }
        }
        let next = next.expect("actual next destruction Call");
        loop_evidence = match next.def {
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_))) => {
                compiler_evidence::load_drop(engine, next).unwrap()
            }
            ty::InstanceKind::Item(_) => compiler_evidence::load_item(engine, next).unwrap(),
            _ => panic!("actual destruction evidence adapter"),
        };
    }
    let (block, original) = loop_evidence
        .current
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let TerminatorKind::Drop { place, .. } = data.terminator().kind else {
                return None;
            };
            Some((
                block,
                place.ty(&loop_evidence.current.local_decls, engine.tcx).ty,
            ))
        })
        .unwrap();
    let allocation = state.memory.len();
    let Some(Value::OwnedArrayIterator {
        payload: Some(payload),
        ..
    }) = &mut state.memory[owner]
    else {
        unreachable!()
    };
    let element = Rc::make_mut(&mut payload.slots)[0].take().unwrap();
    payload.dropping.as_mut().unwrap().leased = Some(Lease {
        index: 0,
        allocation,
    });
    state.memory.push(Some(element));
    let witness = ElementWitness {
        owner,
        identity: identity.clone(),
        entry: invocation.entry.clone(),
        body: loop_evidence,
        block,
        index: 0,
        original,
    };
    engine
        .bind_iterator_element_storage(&witness, &mut state, allocation)
        .unwrap();
    let child_glue = ty::Instance::resolve_drop_glue(engine.tcx, original);
    let child_evidence = compiler_evidence::load_drop(engine, child_glue).unwrap();
    let words = steps::observe_payload(engine, &state, owner).unwrap();
    let child = Invocation {
        owner,
        identity: identity.clone(),
        entry: invocation.entry.clone(),
        evidence: child_evidence,
        kind: Kind::Child,
        front: invocation.front,
        back: invocation.back,
        words: Some(Rc::new(words)),
    };
    let child_body = child.evidence.current.clone();
    child.check(engine, &child_body, &state).unwrap();
    let (call_block, actual_child) = child_body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            let TerminatorKind::Call {
                func: Operand::Constant(function),
                ..
            } = &data.terminator().kind
            else {
                return None;
            };
            let ty::FnDef(id, arguments) = function.const_.ty().kind() else {
                return None;
            };
            Some((
                block,
                engine
                    .resolve_function_item(*id, arguments.skip_binder())
                    .unwrap(),
            ))
        })
        .expect("actual typed element DropGlue to destructor Call");
    let prior_limit = engine.limits.max_steps;
    let prior_cache = engine.call_signatures.borrow().len();
    let before = engine.steps;
    engine.limits.max_steps = before + 7;
    assert!(
        signature::check(engine, actual_child)
            .unwrap_err()
            .contains("shared execution step limit reached")
    );
    assert!(engine.steps > engine.limits.max_steps);
    assert_eq!(engine.call_signatures.borrow().len(), prior_cache);
    engine.limits.max_steps = prior_limit;
    signature::check(engine, actual_child).unwrap();
    let original_signature = engine.call_poly_signature(actual_child).unwrap();
    let entries = engine.proof.body_entries.len();
    for mutation in 0..5 {
        let poisoned = match mutation {
            0 => original_signature.map_bound(|s| s.set_safety(rustc_hir::Safety::Unsafe)),
            1 => original_signature.map_bound(|s| ty::FnSig {
                fn_sig_kind: s
                    .fn_sig_kind
                    .set_abi(rustc_abi::ExternAbi::C { unwind: false }),
                ..s
            }),
            2 => ty::Binder::bind_with_vars(
                original_signature.skip_binder(),
                engine
                    .tcx
                    .mk_bound_variable_kinds(&[ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon)]),
            ),
            3 | 4 => original_signature.map_bound(|s| {
                let mut types = s.inputs_and_output.to_vec();
                let selected = if mutation == 3 { 0 } else { types.len() - 1 };
                types[selected] = engine.tcx.types.u8;
                ty::FnSig {
                    inputs_and_output: engine.tcx.mk_type_list(&types),
                    ..s
                }
            }),
            _ => unreachable!(),
        };
        assert_ne!(poisoned, original_signature);
        engine
            .call_signatures
            .borrow_mut()
            .insert(actual_child, poisoned);
        let before = engine.steps;
        let mut hostile = state.clone();
        let error = engine
            .array_iterator_drop_call(
                Some(&child),
                (child_glue, call_block),
                &child_body,
                actual_child,
                &mut hostile,
                &[],
            )
            .err()
            .unwrap();
        assert!(
            error.contains("cached/original full signature differs"),
            "{error}"
        );
        assert!(engine.steps > before);
        assert_eq!(engine.proof.body_entries.len(), entries);
        child.check(engine, &child_body, &state).unwrap();
        engine
            .call_signatures
            .borrow_mut()
            .insert(actual_child, original_signature);
    }
    assert!(
        engine
            .array_iterator_drop_call(
                Some(&child),
                (child_glue, call_block),
                &child_body,
                actual_child,
                &mut state,
                &[],
            )
            .unwrap()
            .is_none()
    );
    for change in 0..6 {
        let mut hostile = state.clone();
        match change {
            0 => hostile.memory[allocation] = None,
            1 => hostile.memory[allocation] = Some(Value::Unit),
            2 => hostile.memory.retire_initialized_owner(allocation),
            3 => hostile
                .memory
                .missing_places
                .consume(allocation, Vec::new())
                .unwrap(),
            4 | 5 => {
                let Some(Value::Adt { fields, .. }) = &mut hostile.memory[allocation] else {
                    unreachable!()
                };
                let foreign = Context::default();
                fields[0].1 = if change == 4 {
                    symbolic::integer(&foreign, 11, 16, false)
                } else {
                    Value::Int {
                        expression: engine.terms.boolean(true),
                        bits: 16,
                        signed: false,
                    }
                };
            }
            _ => unreachable!(),
        }
        assert!(
            child.check(engine, &child_body, &hostile).is_err(),
            "lease hostile {change}"
        );
        child.check(engine, &child_body, &state).unwrap();
    }
    let replacement = Rc::new(child_body.as_ref().clone());
    engine.bodies.borrow_mut().insert(child_glue, replacement);
    assert!(child.check(engine, &child_body, &state).is_err());
    engine.bodies.borrow_mut().insert(child_glue, child_body);
    assert!(witness.element(engine, &state, owner).is_err());
}

pub(in crate::proof::array_iterator_constructors) fn authenticate_callable<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<(), String> {
    signature::check(engine, instance).map(|_| ())
}

pub(in crate::proof::array_iterator_constructors) fn authenticated_signature<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ty::PolyFnSig<'tcx>, String> {
    pay(engine, 1)?; // New Box immutable return service; existing callable gate fees stay intact.
    signature::check(engine, instance)
}
