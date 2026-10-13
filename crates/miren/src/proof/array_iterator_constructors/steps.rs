//! Actual public/inner iterator frames; metadata never grants generic raw or projection access.
use super::*;
use rustc_middle::mir::{BorrowKind, Location, RawPtrKind};

mod evidence;
pub(in crate::proof) use evidence::Evidence;
use evidence::{load_evidence, schema};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Direction {
    Front,
    Back,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrameKind {
    Public,
    Inner,
    BoundsHelper,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Public,
    Sized,
    Unsized,
    Data,
    MaybePointer,
    ElementPointer,
}
#[derive(Clone, Debug)]
pub(in crate::proof) struct View {
    owner: usize,
    entry: Rc<()>,
    role: Role,
}
#[derive(Clone, Debug)]
pub(in crate::proof) struct Pending {
    pub(super) index: usize,
    entry: Rc<()>,
}
#[derive(PartialEq)]
enum Word {
    Slot(bool),
    Unit,
    Bool(Term),
    Integer(Term, u32, bool),
    Float(Term, u32, Option<Term>),
    Array(usize),
    Tuple(usize),
    Adt(String, usize, bool, u128, usize),
    Field(String),
}
struct Lease<'tcx> {
    owner: usize,
    parent: BodyEvidence<'tcx>,
    callee: ty::Instance<'tcx>,
    block: BasicBlock,
    entry: Rc<()>,
    front: usize,
    back: usize,
    pending: usize,
    words: Vec<Word>,
}
fn observe_word(
    engine: &mut Engine<'_>,
    value: &Value,
    depth: usize,
    words: &mut Vec<Word>,
) -> Result<(), String> {
    pay(engine, 1)?;
    if depth > MAX_INPUT_DEPTH || words.len() >= MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter pending lease observation exceeds existing node/depth bounds".into(),
        ));
    }
    pay(engine, 2)?; // Prepay one shallow word clone and its vector entry before construction.
    let word = match value {
        Value::Unit => Word::Unit,
        Value::Bool(term)
            if term.belongs_to(&engine.terms) && term.sort() == &miren::smt::Sort::Bool =>
        {
            Word::Bool(term.clone())
        }
        Value::Int {
            expression,
            bits,
            signed,
        } if expression.belongs_to(&engine.terms)
            && expression.sort() == &miren::smt::Sort::BitVec(*bits) =>
        {
            Word::Integer(expression.clone(), *bits, *signed)
        }
        Value::Float {
            expression,
            bits,
            raw_bits,
        } if expression.belongs_to(&engine.terms)
            && raw_bits
                .as_ref()
                .is_none_or(|bits| bits.belongs_to(&engine.terms)) =>
        {
            let expected = match bits {
                32 => miren::smt::Sort::Float {
                    exponent: 8,
                    significand: 24,
                },
                64 => miren::smt::Sort::Float {
                    exponent: 11,
                    significand: 53,
                },
                _ => return Err("IntoIter pending lease float width is unsupported".into()),
            };
            if expression.sort() != &expected {
                return Err("IntoIter pending lease float sort differs".into());
            }
            if raw_bits.is_some() {
                characters::validate_float_encoding(&engine.terms, value, *bits)?;
            }
            Word::Float(expression.clone(), *bits, raw_bits.clone())
        }
        Value::Tuple(fields) => Word::Tuple(fields.len()),
        Value::Elements(fields) => Word::Array(fields.len()),
        Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } => {
            pay(engine, name.len() + 1)?;
            Word::Adt(
                name.clone(),
                *variant,
                *is_option,
                *discriminant,
                fields.len(),
            )
        }
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
        | Value::Uninitialized
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::RawPointer { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Bytes { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. } => {
            return Err(
                "IntoIter pending lease requires retained pure typed payload observations".into(),
            );
        }
    };
    words.push(word);
    match value {
        Value::Tuple(fields) => {
            for value in fields {
                observe_word(engine, value, depth + 1, words)?;
            }
        }
        Value::Elements(fields) => {
            for value in fields {
                observe_word(engine, value, depth + 1, words)?;
            }
        }
        Value::Adt { fields, .. } => {
            for (name, value) in fields {
                if words.len() >= MAX_INPUT_VALUES {
                    return Err("IntoIter pending lease field budget exceeded".into());
                }
                pay(engine, name.len() + 3)?;
                words.push(Word::Field(name.clone()));
                observe_word(engine, value, depth + 1, words)?;
            }
        }
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
        | Value::Uninitialized
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::RawPointer { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Bytes { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Unit => {}
    }
    Ok(())
}
pub(super) fn value_clone_work(
    engine: &mut Engine<'_>,
    value: &Value,
    depth: usize,
    nodes: &mut usize,
) -> Result<usize, String> {
    pay(engine, 1)?;
    *nodes += 1;
    if depth > MAX_INPUT_DEPTH || *nodes > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter COW value clone exceeds existing node/depth bounds".into(),
        ));
    }
    match value {
        Value::Input(_) => Ok(4), // InputShape Rc, slot, Term and inline Value discriminant.
        Value::Bool(_) | Value::Int { .. } | Value::Float { .. } | Value::Unit => Ok(5),
        Value::Elements(_) => Ok(2), // Shared immutable Elements handle; no element cloning.
        Value::Adt { name, .. } => Ok(name.len() + 7), // Name allocation and shallow AdtFields Rc.
        Value::Tuple(fields) => {
            let mut owned = 2 + fields.len();
            for value in fields {
                owned = owned
                    .checked_add(value_clone_work(engine, value, depth + 1, nodes)?)
                    .ok_or("IntoIter COW tuple clone work overflow")?;
            }
            Ok(owned)
        }
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
        | Value::Uninitialized
        | Value::MaybeUninit { .. }
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::RawPointer { .. }
        | Value::TrackedPointer { .. }
        | Value::RawSlice { .. }
        | Value::Bytes { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::FunctionPointer { .. }
        | Value::Function => Err("IntoIter COW clone payload domain is unsupported".into()),
    }
}
fn validate_element<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    value: &Value,
    conditions: &[Term],
    depth: usize,
    nodes: &mut usize,
) -> Result<(), String> {
    pay(engine, 1)?;
    *nodes += 1;
    if depth > MAX_INPUT_DEPTH || *nodes > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter yielded element exceeds existing typed node/depth bounds".into(),
        ));
    }
    match (original.kind(), value) {
        (ty::Bool, Value::Bool(term))
            if term.belongs_to(&engine.terms) && term.sort() == &miren::smt::Sort::Bool =>
        {
            Ok(())
        }
        (
            ty::Int(_) | ty::Uint(_),
            Value::Int {
                expression,
                bits,
                signed,
            },
        ) if expression.belongs_to(&engine.terms)
            && expression.sort() == &miren::smt::Sort::BitVec(*bits)
            && *signed == matches!(original.kind(), ty::Int(_))
            && u64::from(*bits) == engine.static_layout(original)?.size.bits() =>
        {
            Ok(())
        }
        (ty::Char, Value::Int { .. }) => {
            pay(engine, conditions.len() + 12)?;
            engine.prove_char_value(value, conditions)
        }
        (
            ty::Float(_),
            Value::Float {
                expression,
                bits,
                raw_bits,
            },
        ) if expression.belongs_to(&engine.terms)
            && raw_bits
                .as_ref()
                .is_none_or(|term| term.belongs_to(&engine.terms))
            && u64::from(*bits) == engine.static_layout(original)?.size.bits() =>
        {
            let expected = match bits {
                32 => miren::smt::Sort::Float {
                    exponent: 8,
                    significand: 24,
                },
                64 => miren::smt::Sort::Float {
                    exponent: 11,
                    significand: 53,
                },
                _ => return Err("IntoIter float element width is unsupported".into()),
            };
            if expression.sort() != &expected {
                return Err("IntoIter float element sort differs from original type".into());
            }
            if raw_bits.is_some() {
                characters::validate_float_encoding(&engine.terms, value, *bits)?;
            }
            Ok(())
        }
        (ty::Tuple(types), Value::Unit) if types.is_empty() => Ok(()),
        (ty::Tuple(types), Value::Tuple(fields)) if types.len() == fields.len() => {
            for (original, value) in types.iter().zip(fields) {
                validate_element(engine, original, value, conditions, depth + 1, nodes)?;
            }
            Ok(())
        }
        (ty::Array(original, count), Value::Elements(fields))
            if count.try_to_target_usize(engine.tcx) == Some(fields.len() as u64) =>
        {
            for value in fields {
                validate_element(engine, *original, value, conditions, depth + 1, nodes)?;
            }
            Ok(())
        }
        (
            ty::Adt(def, args),
            Value::Adt {
                name,
                variant,
                is_option,
                discriminant,
                fields,
            },
        ) if def.is_struct()
            && !def.is_union()
            && *variant == 0
            && !*is_option
            && *discriminant == 0
            && *name == engine.tcx.def_path_str(def.did())
            && fields.len() == def.non_enum_variant().fields.len() =>
        {
            for (field, (name, value)) in def.non_enum_variant().fields.iter().zip(fields.iter()) {
                if field.name.as_str() != name {
                    return Err("IntoIter yielded original field name differs".into());
                }
                pay(engine, 3)?;
                let original = engine
                    .tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        field.ty(engine.tcx, args),
                    )
                    .map_err(|error| {
                        format!("IntoIter yielded field type unavailable: {error:?}")
                    })?;
                validate_element(engine, original, value, conditions, depth + 1, nodes)?;
            }
            Ok(())
        }
        _ => Err("IntoIter yielded value differs from original pure element type/context".into()),
    }
}
fn observe_payload(
    engine: &mut Engine<'_>,
    state: &State,
    owner: usize,
) -> Result<Vec<Word>, String> {
    let Value::OwnedArrayIterator {
        payload: Some(payload),
        ..
    } = state
        .memory
        .get(owner)
        .and_then(Option::as_ref)
        .ok_or("IntoIter lease owner is absent")?
    else {
        return Err("IntoIter lease requires sole original owner".into());
    };
    pay(engine, payload.len() + 1)?;
    let mut words = Vec::new();
    for slot in payload.slots.iter() {
        if words.len() >= MAX_INPUT_VALUES {
            return Err("IntoIter pending lease slot budget exceeded".into());
        }
        pay(engine, 2)?;
        words.push(Word::Slot(slot.is_some()));
        if let Some(value) = slot {
            observe_word(engine, value, 0, &mut words)?;
        }
    }
    Ok(words)
}
impl<'tcx> Lease<'tcx> {
    fn check(
        &self,
        engine: &mut Engine<'tcx>,
        invocation: &Invocation<'tcx>,
        state: &State,
    ) -> Result<(), String> {
        self.parent.current(engine)?;
        if self.owner != invocation.owner
            || invocation.kind != FrameKind::BoundsHelper
            || self.block.as_usize() != 6
            || self.callee != invocation.evidence.instance
            || !Rc::ptr_eq(&self.entry, &invocation.entry)
        {
            return Err("IntoIter bounds lease parent/callee/occurrence differs".into());
        }
        pay(engine, 7)?;
        let TerminatorKind::Call {
            func: Operand::Constant(function),
            args,
            target: Some(target),
            destination,
            ..
        } = &self.parent.current.basic_blocks[self.block]
            .terminator()
            .kind
        else {
            return Err("IntoIter bounds lease original parent Call differs".into());
        };
        let ty::FnDef(id, generic) = function.const_.ty().kind() else {
            return Err("IntoIter bounds lease original helper FnDef differs".into());
        };
        if engine.resolve_function_item(*id, generic.skip_binder())? != self.callee
            || args.len() != 2
            || target.as_usize() != 7
            || !local(*destination, 17)
            || !matches!(&args[0].node, Operand::Copy(place) if local(*place, 13))
            || !matches!(&args[1].node, Operand::Move(place) if local(*place, 18))
        {
            return Err("IntoIter bounds lease original helper occurrence differs".into());
        }
        let Some(Value::OwnedArrayIterator {
            payload: Some(payload),
            ..
        }) = state.memory.get(invocation.owner).and_then(Option::as_ref)
        else {
            return Err("IntoIter bounds lease original owner disappeared".into());
        };
        if payload.front != self.front
            || payload.back != self.back
            || payload.pending.as_ref().is_none_or(|pending| {
                pending.index != self.pending || !Rc::ptr_eq(&pending.entry, &self.entry)
            })
        {
            return Err("IntoIter bounds helper changed suspended cursor/yield state".into());
        }
        if observe_payload(engine, state, invocation.owner)? != self.words {
            return Err("IntoIter bounds helper changed suspended original slot payload".into());
        }
        Ok(())
    }
}
pub(in crate::proof) struct Invocation<'tcx> {
    owner: usize,
    identity: Identity,
    entry: Rc<()>,
    evidence: BodyEvidence<'tcx>,
    direction: Direction,
    kind: FrameKind,
    lease: Option<Lease<'tcx>>,
}
fn local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}
fn copied(operand: &Operand<'_>, index: usize) -> bool {
    matches!(operand, Operand::Copy(place) if local(*place,index))
}
fn field_path(place: Place<'_>, root: usize, fields: &[usize]) -> bool {
    place.local.as_usize()==root && place.projection.first()==Some(&ProjectionElem::Deref)
        && place.projection.len()==1+fields.len()
        && place.projection[1..].iter().zip(fields).all(|(part, expected)|
            matches!(part,ProjectionElem::Field(index,_) if index.as_usize()==*expected))
}
fn assignment<'a, 'tcx>(
    body: &'a Body<'tcx>,
    block: usize,
    index: usize,
    destination: usize,
) -> Result<&'a Rvalue<'tcx>, String> {
    let statement = &body.basic_blocks[BasicBlock::from_usize(block)].statements[index];
    let StatementKind::Assign(pair) = &statement.kind else {
        return Err("IntoIter step schema lacks exact assignment".into());
    };
    if !local(pair.0, destination) {
        return Err("IntoIter step schema destination differs".into());
    }
    Ok(&pair.1)
}
impl<'tcx> Invocation<'tcx> {
    fn check(
        &self,
        engine: &mut Engine<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        allow_pending: bool,
    ) -> Result<(), String> {
        self.evidence.current(engine)?;
        if !Rc::ptr_eq(body, &self.evidence.current) {
            return Err("IntoIter step current Body/invocation differs".into());
        }
        state.flow.require_unarmed()?;
        let physical = engine.array_iterator_certificate(&self.identity)?;
        state.memory.missing_places.check(self.owner, &[])?;
        let (_, original) = engine
            .typed_memory_evidence(&state.memory, self.owner, &[])?
            .ok_or("IntoIter step owner lacks original type evidence")?;
        if original != physical.iterator {
            return Err("IntoIter step owner original type differs".into());
        }
        let Some(Value::OwnedArrayIterator {
            identity,
            payload: Some(payload),
        }) = state.memory.get(self.owner).and_then(Option::as_ref)
        else {
            return Err("IntoIter step sole owner storage is unavailable".into());
        };
        if identity.view.is_some()
            || identity.original != TransportType::Iterator
            || identity.certificate != self.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &self.identity.seal)
            || !Rc::ptr_eq(&identity.entry, &self.identity.entry)
        {
            return Err("IntoIter step owner identity/context differs".into());
        }
        payload.validate(physical.count, allow_pending)?;
        if payload
            .pending
            .as_ref()
            .is_some_and(|pending| !Rc::ptr_eq(&pending.entry, &self.entry))
        {
            return Err("IntoIter pending yield belongs to another invocation".into());
        }
        Ok(())
    }
    fn view(&self, role: Role) -> Value {
        let mut identity = self.identity.clone();
        identity.original = TransportType::Inner;
        identity.view = Some(View {
            owner: self.owner,
            entry: self.entry.clone(),
            role,
        });
        Value::OwnedArrayIterator {
            identity,
            payload: None,
        }
    }
    fn local_view(
        &self,
        engine: &Engine<'tcx>,
        state: &State,
        index: usize,
        role: Role,
    ) -> Result<(), String> {
        let Value::OwnedArrayIterator {
            identity,
            payload: None,
        } = engine.local(state, index)?
        else {
            return Err("IntoIter step private metadata local differs".into());
        };
        let view = identity
            .view
            .ok_or("IntoIter step private metadata is absent")?;
        if view.owner != self.owner
            || view.role != role
            || !Rc::ptr_eq(&view.entry, &self.entry)
            || identity.certificate != self.identity.certificate
            || !Rc::ptr_eq(&identity.seal, &self.identity.seal)
        {
            return Err("IntoIter step metadata owner/role/invocation differs".into());
        }
        Ok(())
    }
}
impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn borrow_array_iterator_owner(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if !place.projection.is_empty() {
            return Ok(None);
        }
        let original = body.local_decls[place.local].ty;
        let value = self.local(state, place.local.as_usize())?;
        if !matches!(value, Value::OwnedArrayIterator { .. }) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        self.validate_array_iterator_value(original, &value)?;
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        pay(self, state.memory.initialized_owners.len() + 3)?;
        self.preflight_owned_type_storage(body, state, place)?;
        let reference = self.borrow_typed(body, state, place, true)?;
        self.bind_owned_type_storage(body, state, place)?;
        Ok(Some(reference))
    }

    fn array_iterator_bounds_call(
        &mut self,
        parent: &Invocation<'tcx>,
        site: (ty::Instance<'tcx>, BasicBlock),
        body: &Rc<Body<'tcx>>,
        callee: ty::Instance<'tcx>,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Vec<Return>, String> {
        let (caller, block) = site;
        parent.check(self, body, state, true)?;
        if caller != parent.evidence.instance
            || parent.kind != FrameKind::Inner
            || block.as_usize() != 6
            || !matches!(
                callee.def,
                ty::InstanceKind::Item(id) if self.tcx.def_kind(id) == DefKind::Fn
            )
            || self.tcx.item_name(callee.def_id()).as_str() != "precondition_check"
        {
            return Err("IntoIter bounds lease lacks original scalar helper Call".into());
        }
        let physical = self.array_iterator_certificate(&parent.identity)?;
        let ty::Adt(core, _) = physical.iterator.kind() else {
            unreachable!()
        };
        if callee.def_id().krate != core.did().krate {
            return Err("IntoIter bounds lease helper core identity differs".into());
        }
        let TerminatorKind::Call {
            func,
            args,
            target: Some(target),
            destination,
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("IntoIter bounds lease real Call is absent".into());
        };
        let Operand::Constant(function) = func else {
            return Err("IntoIter bounds callee is not original FnDef".into());
        };
        let ty::FnDef(id, generic) = function.const_.ty().kind() else {
            unreachable!()
        };
        if self.resolve_function_item(*id, generic.skip_binder())? != callee
            || args.len() != 2
            || target.as_usize() != 7
            || !local(*destination, 17)
            || !matches!(&args[0].node,Operand::Copy(place) if local(*place,13))
            || !matches!(&args[1].node,Operand::Move(place) if local(*place,18))
        {
            return Err("IntoIter bounds lease arguments/normal continuation differ".into());
        }
        let signature = self.call_signature(callee)?;
        if signature.inputs() != [self.tcx.types.usize, self.tcx.types.usize]
            || !signature.output().is_unit()
        {
            return Err("IntoIter bounds lease original scalar signature differs".into());
        }
        if self.specification(callee)?.is_some_and(|spec| spec.trusted)
            || self.foreign_rust_target(callee)?.is_some()
        {
            return Err("IntoIter bounds lease adapters are unsupported".into());
        }
        let values = args
            .iter()
            .map(|arg| self.operand(caller.def_id(), body, state, &arg.node))
            .collect::<Result<Vec<_>, _>>()?;
        let conditions = self.call_preconditions(
            callee,
            &values,
            state.conditions.clone(),
            &state.memory,
            (
                caller.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        let evidence = load_evidence(self, callee)?;
        let Value::OwnedArrayIterator {
            payload: Some(payload),
            ..
        } = state.memory[parent.owner].as_ref().unwrap()
        else {
            unreachable!()
        };
        let pending = payload
            .pending
            .as_ref()
            .ok_or("IntoIter bounds lease has no pending slot")?;
        let (front, back, index) = (payload.front, payload.back, pending.index);
        let words = observe_payload(self, state, parent.owner)?;
        pay(self, 8)?;
        let lease = Lease {
            owner: parent.owner,
            parent: BodyEvidence {
                instance: parent.evidence.instance,
                current: parent.evidence.current.clone(),
            },
            callee,
            block,
            entry: parent.entry.clone(),
            front,
            back,
            pending: index,
            words,
        };
        let invocation = Invocation {
            owner: parent.owner,
            identity: parent.identity.clone(),
            entry: parent.entry.clone(),
            evidence,
            direction: parent.direction,
            kind: FrameKind::BoundsHelper,
            lease: Some(lease),
        };
        for arg in args {
            self.evaluate_operand(caller.def_id(), body, state, &arg.node)?;
        }
        let frame = array_drop_glue::Frame::step(callee, invocation);
        let chain = stack.iter().copied().chain([callee.def_id()]).collect();
        let previous = std::mem::replace(&mut self.call_chain, chain);
        let result = self.execute_body_with_protocol(
            frame,
            values,
            conditions,
            state.memory.clone(),
            stack,
            activation_flow::Flow::Unarmed,
        );
        if result.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        result
    }
    pub(in crate::proof) fn array_iterator_step_frame_escape(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        value: &Value,
        state: &State,
        incoming: usize,
    ) -> Result<bool, String> {
        let Some(invocation) =
            invocation.filter(|invocation| invocation.kind == FrameKind::BoundsHelper)
        else {
            return Ok(false);
        };
        if !matches!(value, Value::Unit) || !body.return_ty().is_unit() {
            return Err("IntoIter bounds lease cannot publish owner or pointer metadata".into());
        }
        invocation.check(self, body, state, true)?;
        invocation
            .lease
            .as_ref()
            .ok_or("IntoIter bounds lease is absent")?
            .check(self, invocation, state)?;
        self.return_value(value.clone(), state, incoming)?;
        self.validate_incoming_frame_escape_with_iterator(state, incoming, invocation.owner)?;
        Ok(true)
    }
    pub(in crate::proof) fn array_iterator_step_call(
        &mut self,
        parent: Option<&Invocation<'tcx>>,
        site: (ty::Instance<'tcx>, BasicBlock),
        body: &Rc<Body<'tcx>>,
        callee: ty::Instance<'tcx>,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<Return>>, String> {
        let (caller, block) = site;
        if let Some(parent) = parent
            && parent.kind == FrameKind::Inner
            && block.as_usize() == 6
        {
            return self
                .array_iterator_bounds_call(parent, site, body, callee, state, stack)
                .map(Some);
        }
        if !matches!(callee.def,ty::InstanceKind::Item(id)
            if self.tcx.def_kind(id)==DefKind::AssocFn)
        {
            return Ok(None);
        }
        let signature = self.call_signature(callee)?;
        let name = self.tcx.item_name(callee.def_id());
        let direction = match name.as_str() {
            "next" => Direction::Front,
            "next_back" => Direction::Back,
            _ => return Ok(None),
        };
        let [receiver] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Ref(_, pointee, rustc_hir::Mutability::Mut) = receiver.kind() else {
            return Ok(None);
        };
        let ty::Adt(def, _) = pointee.kind() else {
            return Ok(None);
        };
        let is_public = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("ArrayIntoIter"))
            == Some(def.did());
        if !is_public && parent.is_none() {
            return Ok(None);
        }
        if is_public {
            let ty::Adt(_, args) = pointee.kind() else {
                unreachable!()
            };
            if !args
                .type_at(0)
                .needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
            {
                return Ok(None); // Existing no-drop iterator route remains literal.
            }
        }
        let TerminatorKind::Call {
            args,
            target: Some(target),
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("IntoIter step has no real normal Call".into());
        };
        let [argument] = args.as_ref() else {
            return Err("IntoIter step receiver arity differs".into());
        };
        let (owner, identity, entry, kind) = if is_public {
            let value = self.operand(caller.def_id(), body, state, &argument.node)?;
            let Value::Reference {
                allocation,
                projection,
                mutable: true,
            } = value
            else {
                return Err("IntoIter step requires tracked whole mutable receiver".into());
            };
            if !projection.is_empty() {
                return Err("IntoIter step projected receiver is unsupported".into());
            }
            let Some(Value::OwnedArrayIterator {
                identity,
                payload: Some(payload),
            }) = state.memory.get(allocation).and_then(Option::as_ref)
            else {
                return Ok(None);
            };
            self.validate_array_iterator_value(
                *pointee,
                state.memory[allocation].as_ref().unwrap(),
            )?;
            payload.validate(self.array_iterator_certificate(identity)?.count, false)?;
            (allocation, identity.clone(), Rc::new(()), FrameKind::Public)
        } else {
            let parent = parent.unwrap();
            parent.check(self, body, state, false)?;
            if parent.kind != FrameKind::Public
                || block.as_usize() != 0
                || target.as_usize() != 1
                || direction != parent.direction
                || caller != parent.evidence.instance
                || !matches!(&argument.node,Operand::Move(place) if local(*place,2))
            {
                return Err("IntoIter inner step lacks actual public forwarding occurrence".into());
            }
            parent.local_view(self, state, 2, Role::Unsized)?;
            (
                parent.owner,
                parent.identity.clone(),
                parent.entry.clone(),
                FrameKind::Inner,
            )
        };
        state.flow.require_unarmed()?;
        let physical = self.array_iterator_certificate(&identity)?;
        let element = physical.initialized_element;
        let ty::Adt(core, _) = physical.iterator.kind() else {
            unreachable!()
        };
        let ty::Adt(inner, _) = physical.sized_inner.kind() else {
            unreachable!()
        };
        if callee.def_id().krate != core.did().krate
            || (kind == FrameKind::Inner && def.did() != inner.did())
        {
            return Err("IntoIter step original core method/wrapper identity differs".into());
        }
        let implementation = self.tcx.parent(callee.def_id());
        if kind == FrameKind::Public {
            if !matches!(
                self.tcx.def_kind(implementation),
                DefKind::Impl { of_trait: true }
            ) {
                return Err("IntoIter step is not its actual trait implementation".into());
            }
            let trait_id = self
                .tcx
                .impl_trait_ref(implementation)
                .instantiate(self.tcx, callee.args)
                .skip_norm_wip()
                .def_id;
            let expected = if direction == Direction::Front {
                "Iterator"
            } else {
                "DoubleEndedIterator"
            };
            if trait_id.krate != core.did().krate
                || self.tcx.item_name(trait_id).as_str() != expected
            {
                return Err("IntoIter step original iterator trait differs".into());
            }
        } else if !matches!(
            self.tcx.def_kind(implementation),
            DefKind::Impl { of_trait: false }
        ) {
            return Err("IntoIter inner step is not its actual inherent implementation".into());
        }
        if self.specification(callee)?.is_some_and(|spec| spec.trusted)
            || self.foreign_rust_target(callee)?.is_some()
        {
            return Err("IntoIter step trusted/foreign adapter is unsupported".into());
        }
        let evidence = load_evidence(self, callee)?;
        schema(self, &evidence, kind, direction, element)?;
        let invocation = Invocation {
            owner,
            identity,
            entry,
            evidence,
            direction,
            kind,
            lease: None,
        };
        let role = if kind == FrameKind::Public {
            Role::Public
        } else {
            Role::Unsized
        };
        let value = invocation.view(role);
        let conditions = if kind == FrameKind::Public {
            let original = self.operand(caller.def_id(), body, state, &argument.node)?;
            self.call_preconditions(
                callee,
                &[original],
                state.conditions.clone(),
                &state.memory,
                (
                    caller.def_id(),
                    body.basic_blocks[block].terminator().source_info.span,
                ),
            )?
        } else {
            self.array_iterator_no_observations(callee)?;
            state.conditions.clone()
        };
        if let Operand::Move(place) = &argument.node {
            if kind == FrameKind::Public {
                self.evaluate_operand(caller.def_id(), body, state, &argument.node)?;
            } else {
                if state.addresses[place.local.as_usize()].is_some() {
                    return Err("IntoIter forwarding metadata gained guest storage".into());
                }
                let mut masks = clone_work::masks(self, &state.missing_places)?;
                masks.consume(place.local.as_usize(), Vec::new())?;
                state.missing_places = masks;
                state.constant_receipts.invalidate(*place);
            }
        }
        let frame = array_drop_glue::Frame::step(callee, invocation);
        let chain = stack.iter().copied().chain([callee.def_id()]).collect();
        let previous = std::mem::replace(&mut self.call_chain, chain);
        let results = self.execute_body_with_protocol(
            frame,
            vec![value],
            conditions,
            state.memory.clone(),
            stack,
            activation_flow::Flow::Unarmed,
        );
        if results.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone())
        }
        self.call_chain = previous;
        results.map(Some)
    }
    fn array_iterator_no_observations(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if self
            .configured_contracts(instance)?
            .iter()
            .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
            || self.specification(instance)?.is_some()
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "IntoIter private step contract observations are unsupported".into(),
            ));
        }
        Ok(())
    }
    pub(in crate::proof) fn array_iterator_ordinary_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &mut Vec<Value>,
        state: &State,
        stack: &[DefId],
        site: (DefId, Span),
    ) -> Result<Option<Vec<Return>>, String> {
        if !matches!(instance.def,ty::InstanceKind::Item(id)
            if id.is_local()&&matches!(self.tcx.def_kind(id),DefKind::Fn|DefKind::AssocFn))
            || !values
                .iter()
                .any(|value| matches!(value, Value::OwnedArrayIterator { .. }))
        {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || self.foreign_rust_target(instance)?.is_some()
        {
            return Ok(None);
        }
        let body = self.instantiated_body(instance)?;
        if !self.array_iterator_unused_arguments(
            instance,
            &body,
            values,
            &state.memory,
            &state.conditions,
        )? {
            return Ok(None);
        }
        // Local Rust Items have their actual body. Bypass unused library observations entirely;
        // never pass an empty or placeholder vector into a model or a contract service.
        let actual = std::mem::take(values);
        self.call_instance(
            instance,
            actual,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )
        .map(Some)
    }
    pub(in crate::proof) fn array_iterator_unused_arguments(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        arguments: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<bool, String> {
        if !arguments
            .iter()
            .any(|value| matches!(value, Value::OwnedArrayIterator { .. }))
        {
            return Ok(false);
        }
        if self.specification(instance)?.is_some()
            || self
                .configured_contracts(instance)?
                .iter()
                .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
        {
            // Existing contract snapshot service retains its conservative refusal.
            return Ok(false);
        }
        if arguments.len() != body.arg_count {
            return Err("IntoIter unused observation argument arity differs".into());
        }
        for (local, value) in body.args_iter().zip(arguments) {
            if let Value::OwnedArrayIterator {
                identity,
                payload: Some(payload),
            } = value
            {
                self.validate_array_iterator_value(body.local_decls[local].ty, value)?;
                let element = self
                    .array_iterator_certificate(identity)?
                    .initialized_element;
                let mut nodes = 0_usize;
                for value in payload.iter() {
                    validate_element(self, element, value, conditions, 0, &mut nodes)?;
                }
            } else if matches!(value, Value::OwnedArrayIterator { .. }) {
                return Err("IntoIter invocation metadata cannot enter an ordinary helper".into());
            } else if self.contains_array_iterator(value)? {
                return Ok(false); // Nested containers and mixed private observations are separate.
            } else {
                self.typed_coroutine_snapshots(
                    &[body.local_decls[local].ty],
                    std::slice::from_ref(value),
                    memory,
                    conditions,
                )?;
            }
        }
        // Only unbound input bookkeeping is omitted; executable values remain present.
        self.validate_owned_call_arguments(arguments, memory)?;
        Ok(true)
    }
    pub(in crate::proof) fn array_iterator_step_arguments(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        arguments: &[Value],
        memory: &Memory,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        if invocation.kind == FrameKind::BoundsHelper {
            invocation.evidence.current(self)?;
            if !Rc::ptr_eq(body, &invocation.evidence.current) || arguments.len() != 2 {
                return Err("IntoIter bounds helper body/arity differs".into());
            }
            for value in arguments {
                match value {
                    Value::Int {
                        expression,
                        bits,
                        signed: false,
                    } if *bits == u32::from(self.tcx.sess.target.pointer_width)
                        && expression.belongs_to(&self.terms) => {}
                    _ => {
                        return Err(
                            "IntoIter bounds helper arguments are not original usize scalars"
                                .into(),
                        );
                    }
                }
            }
            return Ok(false); // Scalar snapshots/contracts remain ordinary.
        }
        self.array_iterator_no_observations(invocation.evidence.instance)?;
        invocation.evidence.current(self)?;
        if !Rc::ptr_eq(body, &invocation.evidence.current) || arguments.len() != 1 {
            return Err("IntoIter step body/argument count differs".into());
        }
        let state = State {
            locals: vec![None, Some(arguments[0].clone())],
            addresses: vec![None; 2],
            missing_places: initialized_places::MissingPlaces::default(),
            constant_receipts: constant_reference_receipts::Slots::default(),
            conditions: Vec::new(),
            memory: memory.clone(),
            flow: activation_flow::Flow::Unarmed,
        };
        invocation.check(self, body, &state, false)?;
        invocation.local_view(
            self,
            &state,
            1,
            if invocation.kind == FrameKind::Public {
                Role::Public
            } else {
                Role::Unsized
            },
        )?;
        Ok(true)
    }
    pub(in crate::proof) fn array_iterator_step_return(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &State,
    ) -> Result<(), String> {
        if let Some(invocation) = invocation {
            invocation.check(
                self,
                body,
                state,
                invocation.kind == FrameKind::BoundsHelper,
            )?;
            if let Some(lease) = &invocation.lease {
                lease.check(self, invocation, state)?;
            }
        }
        Ok(())
    }
    pub(in crate::proof) fn array_iterator_step_statement(
        &mut self,
        invocation: Option<&Invocation<'tcx>>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        location: Location,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        if invocation.kind == FrameKind::BoundsHelper {
            return Ok(false);
        }
        invocation.check(self, body, state, true)?;
        let StatementKind::Assign(pair) =
            &body.basic_blocks[location.block].statements[location.statement_index].kind
        else {
            return Ok(false);
        };
        let (destination, rvalue) = (&pair.0, &pair.1);
        let block = location.block.as_usize();
        let ordinal = location.statement_index;
        let role = if invocation.kind == FrameKind::Public {
            Role::Public
        } else {
            Role::Unsized
        };
        invocation.local_view(self, state, 1, role)?;
        let physical = self.array_iterator_certificate(&invocation.identity)?;
        let count = physical.count;
        let mut result = None;
        if invocation.kind == FrameKind::Public {
            if block == 0 && ordinal == 2 {
                if !matches!(
                    rvalue,
                    Rvalue::Ref(_, BorrowKind::Mut { .. }, place) if field_path(*place, 1, &[0, 0])
                ) {
                    return Err("IntoIter step public receiver projection differs".into());
                }
                result = Some(invocation.view(Role::Sized));
            } else if block == 0 && ordinal == 3 {
                invocation.local_view(self, state, 3, Role::Sized)?;
                result = Some(invocation.view(Role::Unsized));
            }
        } else {
            let Value::OwnedArrayIterator {
                payload: Some(payload),
                ..
            } = state.memory[invocation.owner].as_ref().unwrap()
            else {
                unreachable!()
            };
            if matches!(rvalue,Rvalue::Use(Operand::Copy(place),_) if
                field_path(*place,1,&[0,0])||field_path(*place,1,&[0,1]))
            {
                let Rvalue::Use(Operand::Copy(place), _) = rvalue else {
                    unreachable!()
                };
                let index = if field_path(*place, 1, &[0, 0]) {
                    payload.front
                } else {
                    payload.back
                };
                result = Some(symbolic::integer(
                    &self.terms,
                    index as u128,
                    u32::from(self.tcx.sess.target.pointer_width),
                    false,
                ));
            } else if !destination.projection.is_empty()
                && field_path(
                    *destination,
                    1,
                    &[
                        0,
                        if invocation.direction == Direction::Front {
                            0
                        } else {
                            1
                        },
                    ],
                )
            {
                let expected = if invocation.direction == Direction::Front {
                    (4, 1)
                } else {
                    (4, 2)
                };
                if (block, ordinal) != expected
                    || payload.pending.is_some()
                    || payload.front == payload.back
                {
                    return Err(
                        "IntoIter cursor store has no unique initialized outgoing slot".into(),
                    );
                }
                let Rvalue::Use(operand, _) = rvalue else {
                    return Err("IntoIter cursor store differs".into());
                };
                let value =
                    self.operand(invocation.evidence.instance.def_id(), body, state, operand)?;
                let integer = value.integer()?.0.constant();
                let new = if invocation.direction == Direction::Front {
                    payload.front + 1
                } else {
                    payload.back - 1
                };
                if integer != Some(miren::smt::Constant::BitVec(new as u128)) {
                    return Err("IntoIter real cursor update differs from bounded interval".into());
                }
                let masks = if let Operand::Move(place) = operand {
                    let mut masks = clone_work::masks(self, &state.missing_places)?;
                    masks.consume(place.local.as_usize(), Vec::new())?;
                    Some((masks, *place))
                } else {
                    None
                };
                pay(self, 3)?;
                let Value::OwnedArrayIterator {
                    payload: Some(payload),
                    ..
                } = state.memory[invocation.owner].as_mut().unwrap()
                else {
                    unreachable!()
                };
                let outgoing = if invocation.direction == Direction::Front {
                    payload.front
                } else {
                    new
                };
                if invocation.direction == Direction::Front {
                    payload.front = new
                } else {
                    payload.back = new
                };
                payload.pending = Some(Pending {
                    index: outgoing,
                    entry: invocation.entry.clone(),
                });
                if let Some((masks, place)) = masks {
                    state.missing_places = masks;
                    state.constant_receipts.invalidate(place);
                }
                return Ok(true);
            } else if matches!(
                rvalue,
                Rvalue::Ref(_, BorrowKind::Shared, place) if field_path(*place, 1, &[1])
            ) {
                result = Some(invocation.view(Role::Data));
            } else if matches!(rvalue,Rvalue::Use(operand,_) if copied(operand,4)) {
                invocation.local_view(self, state, 4, Role::Data)?;
                result = Some(invocation.view(Role::Data));
            } else if matches!(
                rvalue,
                Rvalue::UnaryOp(UnOp::PtrMetadata, operand) if copied(operand, 4)
            ) {
                invocation.local_view(self, state, 4, Role::Data)?;
                result = Some(symbolic::integer(
                    &self.terms,
                    count as u128,
                    u32::from(self.tcx.sess.target.pointer_width),
                    false,
                ));
            } else if matches!(rvalue,Rvalue::RawPtr(RawPtrKind::Const,place) if
                place.local.as_usize()==4&&matches!(place.projection.as_ref(),
                    [ProjectionElem::Deref,ProjectionElem::Index(index)] if index.as_usize()==13))
            {
                invocation.local_view(self, state, 4, Role::Data)?;
                let Some(pending) = &payload.pending else {
                    return Err("IntoIter raw witness has no pending yield".into());
                };
                let index = self.local(state, 13)?.integer()?.0.constant();
                if index != Some(miren::smt::Constant::BitVec(pending.index as u128)) {
                    return Err("IntoIter raw witness index differs from outgoing slot".into());
                }
                result = Some(invocation.view(Role::MaybePointer));
            } else if matches!(
                rvalue,
                Rvalue::Cast(CastKind::PtrToPtr, operand, _) if copied(operand, 16)
            ) {
                invocation.local_view(self, state, 16, Role::MaybePointer)?;
                result = Some(invocation.view(Role::ElementPointer));
            } else if matches!(rvalue,Rvalue::Use(Operand::Copy(place),_) if
                place.local.as_usize()==22&&place.projection.as_ref()==[ProjectionElem::Deref])
            {
                if (block, ordinal) != (9, 2) || !local(*destination, 14) {
                    return Err("IntoIter owning read differs from actual bb9 occurrence".into());
                }
                invocation.local_view(self, state, 22, Role::ElementPointer)?;
                let Some(pending) = &payload.pending else {
                    return Err("IntoIter raw read witness was consumed".into());
                };
                let index = pending.index;
                let element = self
                    .array_iterator_certificate(&invocation.identity)?
                    .initialized_element;
                let value = payload.slots[index]
                    .as_ref()
                    .ok_or("IntoIter outgoing slot was consumed")?;
                validate_element(self, element, value, &state.conditions, 0, &mut 0)?;
                self.validate_tracked_value(value, state)?;
                if state.addresses[14].is_some()
                    || state.locals[14].is_some()
                    || body.local_decls[Local::from_usize(14)].ty != element
                {
                    return Err(
                        "IntoIter owning read destination is not its fresh original local".into(),
                    );
                }
                let clone_work = if Rc::strong_count(&payload.slots) > 1 {
                    let mut nodes = 0_usize;
                    let mut owned = 1 + payload.len();
                    for slot in payload.slots.iter().flatten() {
                        owned = owned
                            .checked_add(value_clone_work(self, slot, 0, &mut nodes)?)
                            .ok_or("IntoIter slot COW clone work overflow")?;
                    }
                    owned
                } else {
                    0
                };
                pay(self, clone_work + count + 5)?;
                let Value::OwnedArrayIterator {
                    payload: Some(payload),
                    ..
                } = state.memory[invocation.owner].as_mut().unwrap()
                else {
                    unreachable!()
                };
                let value = Rc::make_mut(&mut payload.slots)[index]
                    .take()
                    .ok_or("IntoIter outgoing slot was consumed")?;
                payload.pending = None;
                // The shared write service's exact empty-projection root branch is infallible
                // after fresh-local/type preflight; all allocations/fees precede the take.
                self.write_typed(body, state, *destination, value)?;
                return Ok(true);
            }
        }
        if let Some(value) = result {
            pay(self, 2)?;
            self.store_assignment_value_inner(
                body,
                state,
                *destination,
                value,
                &body.basic_blocks[location.block].statements[ordinal].kind,
            )?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}
#[cfg(test)]
mod tests;
