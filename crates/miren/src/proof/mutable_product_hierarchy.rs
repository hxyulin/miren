//! Exclusive whole-product lineage. Source evidence never substitutes for an owner lease.
use super::*;
use crate::proof::mutable_u16::{Backing, Storage};
use rustc_middle::mir::BasicBlock;
use symbolic::MutableU16Role;

#[path = "mutable_product_hierarchy/signature.rs"]
mod signature;

#[path = "mutable_product_hierarchy/work.rs"]
mod work;

pub(in crate::proof) struct Source<'tcx> {
    instance: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
}

struct PreparedCall<'a, 'tcx> {
    body: &'a Body<'tcx>,
    block: BasicBlock,
    instance: ty::Instance<'tcx>,
    args: &'a [rustc_span::Spanned<Operand<'tcx>>],
    stack: &'a [DefId],
    site: (DefId, Span),
    signature: ty::FnSig<'tcx>,
    selected: Rc<Body<'tcx>>,
    selected_frame: usize,
}

struct OwnerCall<'tcx> {
    caller_frame: usize,
    position: usize,
    place: Place<'tcx>,
    id: usize,
    role: MutableU16Role,
}

// Every credit is charged to the ordinary shared counter before this record is published.
// Credits are consumed before guard work, never refunded and never carried to a new instruction.
pub(in crate::proof) struct Access<'tcx> {
    body: usize,
    frame: usize,
    occurrence: usize,
    owner: usize,
    origin: usize,
    issued: u64,
    epoch: u64,
    columns: usize,
    owners: usize,
    frames: usize,
    masks: usize,
    remaining: usize,
    descriptors: usize,
    original: Ty<'tcx>,
    failed: bool,
}

fn require_service(engine: &Engine<'_>) -> Result<(), String> {
    if engine.mutable_product_failed.get() {
        return Err("failed mutable product service cannot continue".into());
    }
    Ok(())
}

pub(in crate::proof) fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    if engine.mutable_product_failed.get() {
        return Err("failed mutable product service cannot continue".into());
    }
    #[cfg(test)]
    if count != 0 {
        work_controls::payment(engine);
    }
    engine.steps = engine.steps.checked_add(count).ok_or_else(|| {
        engine.mutable_product_failed.set(true);
        engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "mutable product hierarchy work overflow".into(),
        )
    })?;
    if engine.steps > engine.limits.max_steps {
        engine.mutable_product_failed.set(true);
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "mutable product hierarchy shared execution step limit reached".into(),
        ));
    }
    Ok(())
}

fn source<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<Source<'tcx>, String> {
    let signature = signature::check(engine, instance).inspect_err(|_| {
        engine.mutable_product_failed.set(true);
    })?;
    source_with_signature(engine, instance, signature)
}

fn source_with_signature<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
) -> Result<Source<'tcx>, String> {
    let result = source_with_signature_inner(engine, instance, signature);
    if result.is_err() {
        engine.mutable_product_failed.set(true);
    }
    result
}

fn source_with_signature_inner<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
) -> Result<Source<'tcx>, String> {
    pay(engine, 2)?;
    let body = match super::super::function_tables::source::borrowed(engine, instance)? {
        Some(body) => body,
        None => array_iterator_constructors::steps::authenticated_helper_body(engine, instance)?,
    };
    pay(engine, 6 + body.arg_count)?;
    let callable = engine.tcx.instantiate_bound_regions_with_erased(signature);
    if body.source.instance != instance.def
        || body.arg_count != callable.inputs().len()
        || body.return_ty() != callable.output()
        || body
            .args_iter()
            .zip(callable.inputs())
            .any(|(local, original)| {
                engine
                    .tcx
                    .erase_and_anonymize_regions(body.local_decls[local].ty)
                    != *original
            })
    {
        return Err("mutable product hierarchy original signature/Body locals differ".into());
    }
    pay(engine, 4)?;
    Ok(Source {
        instance,
        body,
        signature,
    })
}

fn is_product(hierarchy: &Hierarchy) -> bool {
    matches!(hierarchy.origin.data_context, Storage::Product(_))
}

impl<'tcx> Engine<'tcx> {
    // These bounds describe only newly introduced lineage/source guards. Existing product
    // representation and expression validators keep their ordinary behavior and work policy.
    pub(in crate::proof) fn mutable_product_access_begin(
        &mut self,
        body: &Body<'tcx>,
        occurrence: usize,
        memory: &Memory,
        guards: usize,
    ) -> Result<(), String> {
        let result = self.mutable_product_access_begin_inner(body, occurrence, memory, guards);
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    fn mutable_product_access_begin_inner(
        &mut self,
        body: &Body<'tcx>,
        occurrence: usize,
        memory: &Memory,
        guards: usize,
    ) -> Result<(), String> {
        if self.mutable_product_failed.get()
            || self
                .mutable_product_access
                .borrow()
                .as_ref()
                .is_some_and(|access| access.failed)
        {
            return Err("failed mutable product hierarchy instruction cannot continue".into());
        }
        *self.mutable_product_access.borrow_mut() = None;
        let Some(id) = memory.mutable_hierarchy else {
            return Ok(());
        };
        let Some(hierarchy) = memory
            .mutable_u16
            .get(id)
            .and_then(|backing| backing.hierarchy.as_ref())
        else {
            return Ok(());
        };
        if !is_product(hierarchy) {
            return Ok(());
        }
        pay_body_visits(self, body, 1)?;
        // A whole-Body pointer denotes the actual frame entry/returned-memory observation.
        // Every instruction scope otherwise names a current original statement or terminator.
        let actual_occurrence = occurrence == std::ptr::from_ref(body) as usize
            || body.basic_blocks.iter().any(|block| {
                occurrence == std::ptr::from_ref(&block.terminator().kind) as usize
                    || block
                        .statements
                        .iter()
                        .any(|statement| occurrence == std::ptr::from_ref(&statement.kind) as usize)
            });
        if !actual_occurrence {
            return Err("product instruction occurrence is not in its current Body".into());
        }
        pay(self, 10)?;
        let Storage::Product(columns) = &hierarchy.origin.data_context else {
            unreachable!()
        };
        let masks = memory.missing_places.entries().len();
        if guards > MAX_INPUT_VALUES
            || columns.len() > MAX_INPUT_VALUES
            || hierarchy.owners.len() > MAX_INPUT_DEPTH
            || masks > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable product hierarchy instruction inventory exceeds existing bounds".into(),
            ));
        }
        pay(self, hierarchy.owners.len())?;
        let frames = hierarchy.owners.iter().try_fold(0usize, |total, owner| {
            total
                .checked_add(owner.frames.len())
                .ok_or("mutable product frame count overflow")
        })?;
        if frames > MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable product hierarchy frame depth exceeds existing bound".into(),
            ));
        }
        // One guard performs origin/header comparisons, each column sort/Context check,
        // complete lineage/pending validation, held source/cache checks and owner masks.
        pay(self, 4)?;
        let original = self
            .mutable_integer_types
            .get(hierarchy.origin.certificate)
            .ok_or("product instruction original type certificate absent")?
            .original;
        let descriptor = work::descriptor_work(self, original)?;
        let descriptors = guards
            .checked_mul(4)
            .ok_or("product descriptor allowance overflow")?;
        if descriptors > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "product descriptor service inventory exceeds existing512 bound".into(),
            ));
        }
        let storage_work = memory_storage_work(self, memory)?;
        let per_guard = 48
            + 4 * columns.len()
            + 12 * hierarchy.owners.len()
            + 16 * frames
            + 3 * masks
            + 4 * storage_work;
        let work = guards
            .checked_mul(per_guard)
            .ok_or("mutable product guard allowance overflow")?;
        let registry = self.mutable_product_sources.borrow().len();
        if registry > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable product source registry exceeds existing bound".into(),
            ));
        }
        pay(self, registry + work + descriptor * descriptors + 28)?;
        let frame = self
            .mutable_product_sources
            .borrow()
            .iter()
            .find_map(|(frame, source)| std::ptr::eq(source.body.as_ref(), body).then_some(*frame))
            .ok_or("product instruction has no authenticated full Instance source")?;
        *self.mutable_product_access.borrow_mut() = Some(Access {
            body: std::ptr::from_ref(body) as usize,
            frame,
            occurrence,
            owner: id,
            origin: Rc::as_ptr(&hierarchy.origin) as usize,
            issued: hierarchy.issued,
            epoch: hierarchy.epoch,
            columns: columns.len(),
            owners: hierarchy.owners.len(),
            frames,
            masks,
            remaining: guards,
            descriptors,
            original,
            failed: false,
        });
        Ok(())
    }

    pub(in crate::proof) fn mutable_product_descriptor_guard(
        &self,
        id: usize,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        let mut scope = self.mutable_product_access.borrow_mut();
        let Some(access) = scope.as_mut() else {
            return Ok(()); // The unchanged scalar/direct Product path has no new lineage scope.
        };
        if access.failed || self.mutable_product_failed.get() || access.descriptors == 0 {
            access.failed = true;
            self.mutable_product_failed.set(true);
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "product descriptor instruction allowance is unavailable".into(),
            ));
        }
        access.descriptors -= 1;
        if access.owner != id || access.original != original {
            access.failed = true;
            self.mutable_product_failed.set(true);
            return Err(
                "product descriptor original type changed after instruction planning".into(),
            );
        }
        Ok(())
    }

    pub(in crate::proof) fn mutable_product_hierarchy_frame(
        &self,
        body: &Body<'tcx>,
        id: usize,
        role: &MutableU16Role,
        memory: &Memory,
        backing: &Backing,
    ) -> Result<(), String> {
        if memory
            .mutable_u16
            .get(id)
            .is_none_or(|current| !std::ptr::eq(current, backing))
        {
            return Err("product frame backing is not current Memory".into());
        }
        let h = backing
            .hierarchy
            .as_ref()
            .ok_or("product frame hierarchy is absent")?;
        if !matches!(
            role,
            MutableU16Role::Root
                | MutableU16Role::HierarchyChild { .. }
                | MutableU16Role::HierarchyMetadata { .. }
        ) || !h.role_valid(role, true)
        {
            return Err(
                "product frame role is suspended/revoked or lacks current metadata epoch".into(),
            );
        }
        let scope = self.mutable_product_access.borrow();
        if scope
            .as_ref()
            .is_none_or(|access| access.body != std::ptr::from_ref(body) as usize)
        {
            return Err("product observer instruction Body differs".into());
        }
        if let Some(owner) = h.owners.last() {
            self.mutable_u16_frame_top(body, &owner.frames)?;
        }
        Ok(())
    }

    pub(in crate::proof) fn mutable_product_access_end(&self, failed: bool) {
        let mut access = self.mutable_product_access.borrow_mut();
        if failed {
            if let Some(access) = access.as_mut() {
                access.failed = true;
                self.mutable_product_failed.set(true);
            }
        } else {
            *access = None;
        }
    }

    pub(in crate::proof) fn mutable_product_hierarchy_live(
        &self,
        id: usize,
        backing: &Backing,
        memory: &Memory,
    ) -> Result<(), String> {
        let result = self.mutable_product_hierarchy_guard(id, backing, memory);
        if result.is_err() {
            self.mutable_product_access_end(true);
        }
        result
    }

    fn mutable_product_hierarchy_guard(
        &self,
        id: usize,
        backing: &Backing,
        memory: &Memory,
    ) -> Result<(), String> {
        let hierarchy = backing
            .hierarchy
            .as_ref()
            .ok_or("product hierarchy is absent")?;
        let Storage::Product(witnesses) = &hierarchy.origin.data_context else {
            return Err("product owner cannot use scalar hierarchy origin".into());
        };
        let Storage::Product(columns) = &backing.data else {
            return Err("product hierarchy needs typed column storage".into());
        };
        {
            let mut scope = self.mutable_product_access.borrow_mut();
            let access = scope
                .as_mut()
                .ok_or("product hierarchy guard lacks instruction payment")?;
            // Consume before any repeated lineage, current-source or column validation.
            if access.failed || access.remaining == 0 {
                access.failed = true;
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable product hierarchy instruction guard allowance exhausted".into(),
                ));
            }
            access.remaining -= 1;
            if access.owner != id
                || access.origin != Rc::as_ptr(&hierarchy.origin) as usize
                || access.issued != hierarchy.issued
                || access.epoch != hierarchy.epoch
                || access.columns != witnesses.len()
                || access.owners != hierarchy.owners.len()
                || access.masks != memory.missing_places.entries().len()
                || access.occurrence == 0
            {
                access.failed = true;
                return Err("product hierarchy instruction binding changed".into());
            }
        }
        if memory.mutable_hierarchy != Some(id)
            || backing.interval.is_some()
            || backing.phase != super::super::mutable_u16_children::Phase::Idle
            || hierarchy.origin.certificate != backing.certificate
            || hierarchy.origin.allocation != backing.allocation
            || hierarchy.origin.capacity.integer()? != backing.length.integer()?
            || hierarchy.issued < backing.generation
            || columns.len() != witnesses.len()
        {
            return Err("product hierarchy typed origin/generation differs".into());
        }
        hierarchy
            .lineage_depth()
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?;
        memory.check_projection_initialization(backing.allocation, &[])?;
        if !matches!(memory.get(backing.allocation), Some(Some(Value::Unit))) {
            return Err("product hierarchy owner anchor is unavailable".into());
        }
        for (column, witness) in columns.iter().zip(witnesses) {
            if !column.belongs_to(&self.terms)
                || !witness.belongs_to(&self.terms)
                || column.sort() != witness.sort()
            {
                return Err("product hierarchy typed column Context/sort differs".into());
            }
        }
        let sources = self.mutable_product_sources.borrow();
        let bodies = self.bodies.borrow();
        let signatures = self.call_signatures.borrow();
        let scope_frame = self
            .mutable_product_access
            .borrow()
            .as_ref()
            .ok_or("product instruction scope disappeared")?
            .frame;
        let scope_source = sources
            .get(&scope_frame)
            .ok_or("product instruction source was not issued")?;
        if bodies
            .get(&scope_source.instance)
            .is_none_or(|body| !Rc::ptr_eq(body, &scope_source.body))
            || signatures
                .get(&scope_source.instance)
                .is_some_and(|current| *current != scope_source.signature)
        {
            return Err("product instruction original/current source binding differs".into());
        }
        let mut frames = 0usize;
        for owner in &hierarchy.owners {
            for frame in &owner.frames {
                frames += 1;
                let source = sources
                    .get(frame)
                    .ok_or("product hierarchy frame source was not issued")?;
                let original = self
                    .mutable_u16_frames
                    .borrow()
                    .get(*frame)
                    .and_then(std::rc::Weak::upgrade)
                    .ok_or("product hierarchy frame source expired")?;
                if !Rc::ptr_eq(&original, &source.body)
                    || bodies
                        .get(&source.instance)
                        .is_none_or(|body| !Rc::ptr_eq(body, &source.body))
                    || signatures
                        .get(&source.instance)
                        .is_some_and(|current| *current != source.signature)
                {
                    return Err(
                        "product hierarchy current Body/Instance/full signature differs".into(),
                    );
                }
            }
        }
        if self
            .mutable_product_access
            .borrow()
            .as_ref()
            .is_none_or(|access| access.frames != frames)
        {
            return Err("product hierarchy instruction frame inventory changed".into());
        }
        Ok(())
    }
}

fn hierarchy_clone_work(engine: &mut Engine<'_>, hierarchy: &Hierarchy) -> Result<usize, String> {
    pay(engine, 4)?;
    if hierarchy.owners.len() > MAX_INPUT_VALUES {
        return Err("product hierarchy clone owner inventory exceeds existing bound".into());
    }
    pay(engine, hierarchy.owners.len() + 4)?;
    let mut work = 8usize + hierarchy.owners.len() + usize::from(hierarchy.pending.is_some()) * 5;
    let mut frames = 0usize;
    for owner in &hierarchy.owners {
        frames = frames
            .checked_add(owner.frames.len())
            .ok_or("product frame count overflow")?;
        if frames > MAX_INPUT_VALUES {
            return Err("product hierarchy clone frame inventory exceeds existing bound".into());
        }
        work = work
            .checked_add(6 + owner.frames.len())
            .ok_or("product hierarchy clone overflow")?;
    }
    Ok(work)
}

fn memory_storage_work(engine: &mut Engine<'_>, memory: &Memory) -> Result<usize, String> {
    pay(engine, 8)?;
    if memory.len() > MAX_INPUT_VALUES
        || memory.owned_regions.len() > MAX_INPUT_VALUES
        || memory.initialized_owners.len() > MAX_INPUT_VALUES
        || memory.mutable_u16.len() != 1
    {
        return Err("product storage-slot catalogue exceeds existing scope/bounds".into());
    }
    let mut work = 24 + memory.owned_regions.len() + 4 * memory.mutable_u16.len();
    pay(engine, 4 * memory.mutable_u16.len())?;
    for backing in memory.mutable_u16.iter() {
        if backing.interval.is_some() {
            return Err("product hierarchy storage has an unsupported interval catalogue".into());
        }
        if let Some(hierarchy) = &backing.hierarchy {
            work += hierarchy_clone_work(engine, hierarchy)?;
        }
    }
    Ok(work)
}

fn pay_body_visits(engine: &mut Engine<'_>, body: &Body<'_>, visits: usize) -> Result<(), String> {
    pay(engine, 4)?;
    if body.basic_blocks.len() > MAX_INPUT_VALUES || body.local_decls.len() > MAX_INPUT_VALUES {
        return Err("product Body outer inventory exceeds existing bound".into());
    }
    pay(engine, body.basic_blocks.len() + 4)?;
    let statements = body.basic_blocks.iter().try_fold(0usize, |total, block| {
        total
            .checked_add(block.statements.len())
            .ok_or("product Body statement count overflow")
    })?;
    let count = body.local_decls.len() + body.basic_blocks.len() + statements;
    if count > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "product hierarchy Body visits exceed existing inventory bound".into(),
        ));
    }
    pay(
        engine,
        visits
            .checked_mul(count + 8)
            .ok_or("product Body visit allowance overflow")?,
    )
}

fn pay_backing_cow(engine: &mut Engine<'_>, memory: &Memory) -> Result<(), String> {
    pay(engine, 2)?;
    if Rc::strong_count(&memory.mutable_u16) == 1 {
        return Ok(());
    }
    if memory.mutable_u16.len() > MAX_INPUT_VALUES {
        return Err("product COW backing inventory exceeds existing bound".into());
    }
    pay(engine, memory.mutable_u16.len() * 8 + 4)?;
    let mut work = 0usize;
    for backing in memory.mutable_u16.iter() {
        if matches!(&backing.data, Storage::Product(columns) if columns.len() > MAX_INPUT_VALUES) {
            return Err("product COW column inventory exceeds existing bound".into());
        }
        work += match &backing.data {
            Storage::Scalar(_) => 1,
            Storage::Product(columns) => columns.len(),
        };
        if let Some(hierarchy) = &backing.hierarchy {
            work = work
                .checked_add(hierarchy_clone_work(engine, hierarchy)?)
                .ok_or("product COW work overflow")?;
        }
        work += match &backing.phase {
            super::super::mutable_u16_children::Phase::Idle => 1,
            super::super::mutable_u16_children::Phase::Pending { .. } => 2,
            super::super::mutable_u16_children::Phase::Active { frames } => {
                if frames.len() > MAX_INPUT_VALUES {
                    return Err("product COW legacy frame inventory exceeds existing bound".into());
                }
                3 + frames.len()
            }
            super::super::mutable_u16_children::Phase::Retained { metadata, .. } => {
                if metadata.len() > MAX_INPUT_VALUES {
                    return Err("product COW retained metadata exceeds existing bound".into());
                }
                8 + 2 * metadata.len()
            }
        };
    }
    pay(engine, work)
}

fn register_source<'tcx>(engine: &mut Engine<'tcx>, source: Source<'tcx>) -> Result<usize, String> {
    pay(engine, 4)?;
    let frames = engine.mutable_u16_frames.borrow().len();
    if frames >= MAX_INPUT_VALUES {
        return Err("product source frame inventory exceeds existing bound".into());
    }
    pay(engine, frames + 12)?;
    let frame = engine.activation_register_frame(&source.body, &activation_flow::Flow::Unarmed)?;
    let count = engine.mutable_product_sources.borrow().len();
    if count >= MAX_INPUT_VALUES && !engine.mutable_product_sources.borrow().contains_key(&frame) {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "product hierarchy source registry exceeds existing bound".into(),
        ));
    }
    pay(engine, count + 8)?;
    if let Some(prior) = engine.mutable_product_sources.borrow().get(&frame)
        && (prior.instance != source.instance
            || prior.signature != source.signature
            || !Rc::ptr_eq(&prior.body, &source.body))
    {
        return Err("product hierarchy frame source registration differs".into());
    }
    engine
        .mutable_product_sources
        .borrow_mut()
        .insert(frame, source);
    Ok(frame)
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn mutable_product_hierarchy_active(&self, memory: &Memory) -> bool {
        memory
            .mutable_hierarchy
            .and_then(|id| memory.mutable_u16.get(id))
            .and_then(|backing| backing.hierarchy.as_ref())
            .is_some_and(is_product)
    }

    pub(in crate::proof) fn mutable_product_hierarchy_stage(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        if !self.mutable_product_hierarchy_active(&state.memory)
            || !matches!(value, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            return Ok(false);
        }
        state.flow.require_unarmed()?;
        pay_body_visits(self, body, 4)?;
        let id = state
            .memory
            .mutable_hierarchy
            .ok_or("product hierarchy owner namespace missing")?;
        let h = state.memory.mutable_u16[id]
            .hierarchy
            .as_ref()
            .ok_or("product hierarchy is absent")?;
        pay(self, h.owners.len())?;
        let clone_work = hierarchy_clone_work(self, h)? + 48;
        pay(self, clone_work)?;
        pay_backing_cow(self, &state.memory)?;
        self.mutable_hierarchy_stage(body, state, destination, value, occurrence)
    }
}

fn primitive<'tcx>(engine: &Engine<'tcx>, original: Ty<'tcx>) -> bool {
    original.is_unit() || engine.mutable_u16_primitive(original)
}

fn primitive_value<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    value: &Value,
    conditions: &[Term],
) -> Result<(), String> {
    pay(engine, 6)?;
    if original.is_unit() {
        if matches!(value, Value::Unit) {
            return Ok(());
        }
        return Err("product helper Unit value differs".into());
    }
    if original == engine.tcx.types.char {
        return engine.prove_char_value(value, conditions);
    }
    if let Some(float) = engine.float_type(original) {
        return engine.prove_float_pair(value, float, conditions);
    }
    engine.mutable_hierarchy_primitive_value(original, value, conditions)
}

fn nested_candidate<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<bool, String> {
    pay(engine, 6)?;
    if !matches!(instance.def, ty::InstanceKind::Item(id)
        if engine.tcx.def_kind(id) == DefKind::Fn)
        || !engine.tcx.is_mir_available(instance.def_id())
    {
        return Ok(false);
    }
    // The immutable original is a routing inventory only. It cannot authenticate a current
    // Body or produce permission; admission below independently validates both full sources.
    let original = engine.tcx.instance_mir(instance.def);
    pay_body_visits(engine, original, 1)?;
    Ok(original.basic_blocks.iter().any(|block| {
        block.statements.iter().any(|statement| {
            matches!(&statement.kind,
            StatementKind::Assign(assignment)
            if matches!(&assignment.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, source)
                if source.projection.as_ref() == [ProjectionElem::Deref]))
        }) && matches!(block.terminator().kind, TerminatorKind::Call { .. })
    }))
}

impl<'tcx> Engine<'tcx> {
    fn product_catalogue_eligible(&mut self, memory: &Memory) -> Result<bool, String> {
        require_service(self)?;
        // This routing node precedes Product admission. Its ordinary shared-budget failure
        // cannot fail a Product service that has not been selected or observed yet.
        self.steps = self.steps.checked_add(1).ok_or_else(|| {
            self.categorized_error(
                UnknownCategory::ResourceLimit,
                "symbolic execution step limit reached".into(),
            )
        })?;
        if self.steps > self.limits.max_steps {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "symbolic execution step limit reached".into(),
            ));
        }
        let result = self.product_catalogue_eligible_inner(memory);
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    fn product_catalogue_eligible_inner(&mut self, memory: &Memory) -> Result<bool, String> {
        // One fixed eligibility node reads only catalogue/variant/certificate headers.
        // It scans no arguments, types, columns, hierarchy owners or source records.
        let retained = self.mutable_product_access.borrow().is_some()
            || !self.mutable_product_sources.borrow().is_empty();
        if memory.mutable_u16.is_empty() {
            if retained || memory.mutable_hierarchy.is_some() {
                return Err("product source/access state outlived its empty catalogue".into());
            }
            return Ok(false);
        }
        if memory.mutable_u16.len() != 1 {
            return Ok(true); // The normal complete paid service handles multi-backing catalogues.
        }
        let backing = &memory.mutable_u16[0];
        let certificate = self
            .mutable_integer_types
            .get(backing.certificate)
            .ok_or("product eligibility original certificate is absent")?;
        let product = matches!(backing.data, Storage::Product(_))
            || matches!(
                certificate.codec,
                super::super::mutable_u16::ElementCodec::Product(_)
            )
            || !matches!(
                certificate.original.kind(),
                ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char
            )
            || backing.hierarchy.as_ref().is_some_and(is_product);
        if product {
            if matches!(backing.data, Storage::Scalar(_)) {
                return Err("product certificate/origin cannot use Scalar storage".into());
            }
            return Ok(true);
        }
        if retained {
            return Err("product source/access state cannot become a Scalar catalogue".into());
        }
        if let Some(hierarchy) = &backing.hierarchy
            && hierarchy.origin.certificate != backing.certificate
        {
            return Err("scalar eligibility hierarchy certificate differs".into());
        }
        if memory.mutable_hierarchy.is_some_and(|id| id != 0) {
            return Err("scalar eligibility namespace is outside its catalogue".into());
        }
        Ok(false)
    }
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn mutable_product_hierarchy_call(
        &mut self,
        caller: ty::Instance<'tcx>,
        state: &mut State,
        call: super::super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        require_service(self)?;
        if !self.product_catalogue_eligible(&state.memory)? {
            return Ok(None);
        }
        let result = self.mutable_product_hierarchy_call_inner(caller, state, call);
        if result.is_err() {
            self.mutable_product_failed.set(true);
            self.mutable_product_access_end(true);
        }
        result
    }

    fn mutable_product_hierarchy_call_inner(
        &mut self,
        caller: ty::Instance<'tcx>,
        state: &mut State,
        call: super::super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        // Classification is an actual new service even when it selects the ordinary route.
        // Charge its bounded complete argument-header scan before touching current values.
        pay(self, 4)?;
        if call.args.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "product handoff argument classification exceeds existing inventory bound".into(),
            ));
        }
        pay(self, 8 + 2 * call.args.len())?;
        let active = self.mutable_product_hierarchy_active(&state.memory);
        let mut owner = None;
        // Borrowed variant/header classification carries no permission and copies no payload.
        for (position, argument) in call.args.iter().enumerate() {
            let (Operand::Copy(place) | Operand::Move(place)) = argument.node else {
                continue;
            };
            let local = place.local.as_usize();
            let value = match state.addresses.get(local).copied().flatten() {
                Some(allocation) => state.memory.get(allocation).and_then(Option::as_ref),
                None => state.locals.get(local).and_then(Option::as_ref),
            };
            let Some(Value::MutableU16 { id, role }) = value else {
                continue;
            };
            if !matches!(
                state
                    .memory
                    .mutable_u16
                    .get(*id)
                    .map(|backing| &backing.data),
                Some(Storage::Product(_))
            ) {
                continue;
            }
            pay(self, 8)?;
            if owner.is_some() {
                return Err("product hierarchy duplicate owner argument".into());
            }
            if matches!(role, MutableU16Role::Ghost { .. }) {
                return Err("detached Product Ghost cannot enter a hierarchy call".into());
            }
            owner = Some((position, place, *id, role.clone()));
        }
        if !active && (owner.is_none() || !nested_candidate(self, call.instance)?) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        pay(self, call.args.len() + 12)?;
        let super::super::mutable_u16_children::ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            stack,
            site,
        } = call;
        pay_body_visits(self, body, 3)?;
        let TerminatorKind::Call {
            func,
            args: actual,
            destination: actual_destination,
            target: actual_target,
            unwind,
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("product handoff requires actual Call".into());
        };
        let ty::FnDef(definition, arguments) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("product handoff requires original direct FnDef".into());
        };
        let panic = crate::identity::is_panic_call(self.tcx, instance.def_id())
            || self.is_core_panic_helper(instance.def_id());
        if args.as_ptr() != actual.as_ptr()
            || args.len() != actual.len()
            || destination != *actual_destination
            || target != *actual_target
            || (target.is_none() && !panic)
            || !destination.projection.is_empty()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || !matches!(instance.def, ty::InstanceKind::Item(id) if id == *definition)
            || !matches!(
                self.tcx.def_kind(*definition),
                DefKind::Fn | DefKind::AssocFn
            )
            || self.resolve_function_item(*definition, arguments.skip_binder())? != instance
            || caller.def_id() != body.source.def_id()
            || site.0 != caller.def_id()
            || site.1 != body.basic_blocks[block].terminator().source_info.span
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
        {
            return Err("product handoff original Call/Instance/occurrence differs".into());
        }
        let original_signature = signature::check(self, instance)?;
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(original_signature);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || (!primitive(self, signature.output()) && !(panic && signature.output().is_never()))
            || (!panic && destination.ty(&body.local_decls, self.tcx).ty != signature.output())
        {
            return Err(
                "product hierarchy needs safe synchronous primitive-return Rust callable".into(),
            );
        }
        pay(self, args.len() + 6)?;
        for (argument, original) in args.iter().zip(signature.inputs()) {
            if self
                .tcx
                .erase_and_anonymize_regions(argument.node.ty(&body.local_decls, self.tcx))
                != *original
            {
                return Err("product hierarchy original argument type differs".into());
            }
        }
        let models = self.configured_contracts(instance)?.is_empty();
        if active && models && (self.mutable_metadata_operation(instance) || panic) {
            let id = state
                .memory
                .mutable_hierarchy
                .ok_or("product model namespace absent")?;
            self.mutable_product_backing(id, &state.memory)?;
            return Ok(None);
        }
        if target.is_none() {
            return Err("product hierarchy has no supported normal helper return edge".into());
        }
        if owner.is_none() {
            if signature
                .inputs()
                .iter()
                .any(|original| !primitive(self, *original))
            {
                return Err("product hierarchy helper has unsupported incoming argument".into());
            }
            // Exact primitive bit models execute inline in this State and create no frame.
            if models
                && self
                    .float_bits_operation(instance.def_id(), instance.args, signature)
                    .is_some()
            {
                let id = state
                    .memory
                    .mutable_hierarchy
                    .ok_or("product model namespace absent")?;
                self.mutable_product_backing(id, &state.memory)?;
                return Ok(None);
            }
        }
        let selected = source_with_signature(self, instance, original_signature)?;
        let caller_source = source(self, caller)?;
        if !std::ptr::eq(caller_source.body.as_ref(), body) {
            return Err("product handoff caller original/current Body differs".into());
        }
        if owner.is_none()
            && models
            && let Some(result) =
                self.product_root_wrapping_add(state, instance, args, signature, &selected.body)?
        {
            return Ok(Some(vec![result]));
        }
        let caller_frame = register_source(self, caller_source)?;
        let selected_body = selected.body.clone();
        let selected_frame = register_source(self, selected)?;
        let prepared = PreparedCall {
            body,
            block,
            instance,
            args,
            stack,
            site,
            signature,
            selected: selected_body,
            selected_frame,
        };
        if let Some((position, place, id, role)) = owner {
            self.product_owner_call(
                state,
                prepared,
                OwnerCall {
                    caller_frame,
                    position,
                    place,
                    id,
                    role,
                },
            )
        } else {
            self.product_primitive_call(state, prepared)
        }
    }

    fn product_owner_call(
        &mut self,
        state: &mut State,
        prepared: PreparedCall<'_, 'tcx>,
        owner: OwnerCall<'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let PreparedCall {
            body,
            block,
            instance,
            args,
            stack,
            site,
            signature,
            selected,
            selected_frame,
        } = prepared;
        let OwnerCall {
            caller_frame,
            position,
            place,
            id,
            role,
        } = owner;
        if !place.projection.is_empty()
            || state.addresses[place.local.as_usize()].is_some()
            || state.memory.mutable_u16.len() != 1
            || signature
                .inputs()
                .iter()
                .enumerate()
                .any(|(i, original)| i != position && !primitive(self, *original))
        {
            return Err(
                "product handoff needs one direct whole owner and primitive arguments".into(),
            );
        }
        if state.memory.mutable_u16[id].hierarchy.is_none() {
            pay(self, 4)?;
            let original = self
                .mutable_integer_types
                .get(state.memory.mutable_u16[id].certificate)
                .ok_or("cold product handoff type certificate absent")?
                .original;
            let descriptor = work::descriptor_work(self, original)?;
            // Two original type matches, backing validation, and the original Root/Pending
            // bootstrap observers precede the first lineage instruction scope.
            pay(self, descriptor * 8 + 24)?;
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)?
            || !self.mutable_u16_matches(signature.inputs()[position], id, &state.memory, true)?
        {
            return Err("product handoff original owner type differs".into());
        }
        self.mutable_product_unbound_contracts(instance)?;
        let backing = self.mutable_product_backing(id, &state.memory)?;
        let mut hierarchy = if let Some(hierarchy) = &backing.hierarchy {
            pay(self, hierarchy.owners.len())?;
            let clone_work = hierarchy_clone_work(self, hierarchy)?;
            pay(self, clone_work)?;
            hierarchy.clone()
        } else {
            pay_body_visits(self, body, 4)?;
            self.mutable_hierarchy_bootstrap(body, state, place, id, &role)?;
            let Storage::Product(columns) = &backing.data else {
                unreachable!()
            };
            pay(self, 14 + columns.len())?;
            Hierarchy {
                origin: Rc::new(Origin {
                    certificate: backing.certificate,
                    allocation: backing.allocation,
                    capacity: backing.length.clone(),
                    data_context: Storage::Product(columns.clone()),
                }),
                issued: backing.generation,
                epoch: 0,
                owners: Vec::new(),
                pending: None,
            }
        };
        let tip = Tip {
            frame: caller_frame,
            statement: std::ptr::from_ref(&body.basic_blocks[block].terminator().kind) as usize,
            local: place.local.as_usize(),
        };
        pay(self, 40 + hierarchy.owners.len() * 12)?;
        let storage_work = memory_storage_work(self, &state.memory)?;
        pay(self, storage_work + hierarchy.owners.len() + 8)?;
        let slots = state.memory.storage_slots()
            + usize::from(backing.hierarchy.is_none()) * hierarchy.storage_slots();
        let lease = match role {
            MutableU16Role::Root | MutableU16Role::Child { .. } => {
                if backing.hierarchy.is_some() && !matches!(role, MutableU16Role::Root) {
                    return Err("active legacy product child cannot migrate".into());
                }
                if matches!(role, MutableU16Role::Root)
                    && matches!(args[position].node, Operand::Move(_))
                {
                    return Err("product hierarchy root Move transport remains unsupported".into());
                }
                hierarchy
                    .issue(0, tip.clone(), slots)
                    .map_err(|error| self.mutable_hierarchy_transition_error(error))?
            }
            MutableU16Role::HierarchyChild { lease } => {
                if let Some(pending) = &hierarchy.pending {
                    if pending.lease != lease
                        || pending.tip.local != place.local.as_usize()
                        || pending.tip.frame != caller_frame
                    {
                        return Err("product handoff does not use current pending tip".into());
                    }
                    self.mutable_hierarchy_tip(&hierarchy, body)?;
                    hierarchy
                        .pending
                        .as_mut()
                        .ok_or("product pending disappeared")?
                        .tip = tip.clone();
                    lease
                } else {
                    self.mutable_u16_frame_top(
                        body,
                        &hierarchy
                            .owners
                            .last()
                            .ok_or("product owner lineage missing")?
                            .frames,
                    )?;
                    hierarchy
                        .issue(lease, tip.clone(), slots)
                        .map_err(|error| self.mutable_hierarchy_transition_error(error))?
                }
            }
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::HierarchyMetadata { .. }
            | MutableU16Role::Ghost { .. } => {
                return Err("product metadata has no child handoff permission".into());
            }
        };
        pay(self, hierarchy.owners.len())?;
        let clone_work = hierarchy_clone_work(self, &hierarchy)? + 20;
        pay(self, clone_work)?;
        let ticket = hierarchy
            .enter(&tip, selected_frame, slots)
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?;
        pay(
            self,
            hierarchy.owners.len() + state.memory.mutable_u16.len() * 6 + 12,
        )?;
        pay(self, 3 * storage_work + 3 * hierarchy.owners.len() + 16)?;
        self.mutable_hierarchy_charge(state, id, &hierarchy)?;
        pay(self, args.len() + 4)?;
        let mut values = Vec::with_capacity(args.len());
        for (index, argument) in args.iter().enumerate() {
            if index == position {
                if matches!(argument.node, Operand::Move(_)) {
                    pay(self, state.missing_places.entries().len() + 4)?;
                    state
                        .missing_places
                        .consume(place.local.as_usize(), Vec::new())?;
                }
                values.push(Value::MutableU16 {
                    id,
                    role: MutableU16Role::HierarchyChild { lease },
                });
            } else {
                let value = self.evaluate_operand(site.0, body, state, &argument.node)?;
                primitive_value(self, signature.inputs()[index], &value, &state.conditions)?;
                values.push(value);
            }
        }
        pay_backing_cow(self, &state.memory)?;
        let backing = &mut Rc::make_mut(&mut state.memory.mutable_u16)[id];
        backing.phase = super::super::mutable_u16_children::Phase::Idle;
        backing.hierarchy = Some(hierarchy);
        state.memory.mutable_hierarchy = Some(id);
        self.mutable_product_access_begin(
            &selected,
            std::ptr::from_ref(selected.as_ref()) as usize,
            &state.memory,
            16 + 4 * args.len(),
        )?;
        pay(
            self,
            state.conditions.len() + state.memory.missing_places.entries().len() * 3 + 12,
        )?;
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        for result in &mut results {
            self.mutable_product_access_begin(
                &selected,
                std::ptr::from_ref(selected.as_ref()) as usize,
                &result.memory,
                16,
            )?;
            primitive_value(self, signature.output(), &result.value, &result.conditions)?;
            if result.memory.mutable_hierarchy != Some(id)
                || self.mutable_u16_contains(&result.value, &result.memory)?
            {
                return Err("product Return changed owner namespace or escaped a role".into());
            }
            self.mutable_product_backing(id, &result.memory)?;
            pay_backing_cow(self, &result.memory)?;
            pay(
                self,
                24 + ticket.prefix.len() * 6
                    + ticket
                        .prefix
                        .iter()
                        .map(|owner| owner.frames.len())
                        .sum::<usize>(),
            )?;
            let hierarchy = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("product Return lost hierarchy")?;
            hierarchy.release(&ticket)?;
        }
        self.mutable_product_access_begin(
            body,
            std::ptr::from_ref(&body.basic_blocks[block].terminator().kind) as usize,
            &state.memory,
            16,
        )?;
        Ok(Some(results))
    }
}

impl<'tcx> Engine<'tcx> {
    fn product_root_wrapping_add(
        &mut self,
        state: &mut State,
        instance: ty::Instance<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        signature: ty::FnSig<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<Option<Return>, String> {
        let id = state
            .memory
            .mutable_hierarchy
            .ok_or("product root model namespace absent")?;
        let backing = self.mutable_product_backing(id, &state.memory)?;
        let hierarchy = backing
            .hierarchy
            .as_ref()
            .ok_or("product root model lineage absent")?;
        if !hierarchy.owners.is_empty() || hierarchy.pending.is_some() {
            return Ok(None);
        }
        pay_body_visits(self, body, 1)?;
        pay(self, 16)?;
        let core = self
            .tcx
            .lang_items()
            .get(LangItem::SliceLen)
            .map(|id| id.krate);
        let parent = self.tcx.parent(instance.def_id());
        if core != Some(instance.def_id().krate)
            || self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            || self.tcx.def_kind(parent) != (DefKind::Impl { of_trait: false })
            || self.tcx.item_name(instance.def_id()).as_str() != "wrapping_add"
            || args.len() != 2
            || signature.inputs() != [signature.output(), signature.output()]
            || self.integer_type(signature.output()).is_none()
            || self
                .tcx
                .type_of(parent)
                .instantiate(self.tcx, instance.args)
                .skip_norm_wip()
                != signature.output()
            || body.local_decls.len() != 3
            || body.basic_blocks.len() != 1
        {
            return Ok(None);
        }
        let block = &body.basic_blocks[rustc_middle::mir::START_BLOCK];
        if block.is_cleanup
            || block.statements.len() != 1
            || !matches!(block.terminator().kind, TerminatorKind::Return)
        {
            return Ok(None);
        }
        let StatementKind::Assign(assignment) = &block.statements[0].kind else {
            return Ok(None);
        };
        let Rvalue::BinaryOp(BinOp::Add, operands) = &assignment.1 else {
            return Ok(None);
        };
        let (Operand::Copy(left), Operand::Copy(right)) = &**operands else {
            return Ok(None);
        };
        if assignment.0.local.as_usize() != 0
            || !assignment.0.projection.is_empty()
            || left.local.as_usize() != 1
            || !left.projection.is_empty()
            || right.local.as_usize() != 2
            || !right.projection.is_empty()
        {
            return Ok(None);
        }
        // The entire independently authenticated Body has one primitive Add and Return.
        // No storage observation, destructor, callback, auxiliary frame or reference is modeled.
        self.mutable_product_vector_work(&state.memory, 2)?;
        let caller_frame = self
            .mutable_product_access
            .borrow()
            .as_ref()
            .ok_or("product root model lacks paid caller instruction")?
            .frame;
        let caller = self
            .mutable_product_sources
            .borrow()
            .get(&caller_frame)
            .ok_or("product root model lacks authenticated caller")?
            .instance;
        let caller_body = self
            .mutable_product_sources
            .borrow()
            .get(&caller_frame)
            .ok_or("product root model caller disappeared")?
            .body
            .clone();
        let mut values = Vec::with_capacity(2);
        for (argument, original) in args.iter().zip(signature.inputs()) {
            let value =
                self.evaluate_operand(caller.def_id(), &caller_body, state, &argument.node)?;
            primitive_value(self, *original, &value, &state.conditions)?;
            values.push(value);
        }
        pay(self, 24)?;
        let right = values.pop().ok_or("product root Add rhs absent")?;
        let left = values.pop().ok_or("product root Add lhs absent")?;
        let value = symbolic::binary(&self.terms, "add", left, right)?;
        primitive_value(self, signature.output(), &value, &state.conditions)?;
        self.mutable_product_switch_work(state, 1)?;
        let name_work = self.mutable_product_frame_name_work(instance, &state.memory)?;
        pay(self, 4)?;
        if self.proof.models.len() > MAX_INPUT_VALUES {
            return Err("product root model registry exceeds existing bound".into());
        }
        // Equal-length String comparisons are bounded by this newly planned model name.
        let name_bound = name_work + 128;
        pay(self, name_bound * (self.proof.models.len() + 1))?;
        self.record_model(
            instance.def_id(),
            "original full MIR: primitive wrapping Add then Return",
        );
        Ok(Some(Return {
            value,
            conditions: state.conditions.clone(),
            memory: state.memory.clone(),
            flow: activation_flow::Flow::Unarmed,
        }))
    }

    fn product_primitive_call(
        &mut self,
        state: &mut State,
        prepared: PreparedCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let PreparedCall {
            body,
            block,
            instance,
            args,
            stack,
            site,
            signature,
            selected,
            selected_frame,
        } = prepared;
        let id = state
            .memory
            .mutable_hierarchy
            .ok_or("product helper lacks owner namespace")?;
        let backing = self.mutable_product_backing(id, &state.memory)?;
        let before = backing
            .hierarchy
            .as_ref()
            .ok_or("product helper hierarchy is absent")?;
        if before.pending.is_some() || before.owners.is_empty() {
            return Err("product helper lacks a current suspended owning invocation".into());
        }
        self.mutable_u16_frame_top(body, &before.owners.last().unwrap().frames)?;
        pay(self, before.owners.len())?;
        let clone_work = hierarchy_clone_work(self, before)? * 2 + 16;
        pay(self, clone_work)?;
        let before = before.clone();
        let Storage::Product(columns) = &backing.data else {
            unreachable!()
        };
        pay(self, columns.len() + 4)?;
        let data = columns.clone();
        let depth = before
            .lineage_depth()
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?;
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "product helper exceeds existing frame depth".into(),
            ));
        }
        let mut entered = before.clone();
        pay(self, 8 + entered.owners.last().unwrap().frames.len())?;
        entered
            .owners
            .last_mut()
            .unwrap()
            .frames
            .push(selected_frame);
        pay(
            self,
            entered.owners.len() + state.memory.mutable_u16.len() * 6 + 12,
        )?;
        self.mutable_hierarchy_charge(state, id, &entered)?;
        pay(self, args.len() + 4)?;
        let mut values = Vec::with_capacity(args.len());
        for (argument, original) in args.iter().zip(signature.inputs()) {
            let value = self.evaluate_operand(site.0, body, state, &argument.node)?;
            primitive_value(self, *original, &value, &state.conditions)?;
            values.push(value);
        }
        pay_backing_cow(self, &state.memory)?;
        Rc::make_mut(&mut state.memory.mutable_u16)[id].hierarchy = Some(entered.clone());
        self.mutable_product_access_begin(
            &selected,
            std::ptr::from_ref(selected.as_ref()) as usize,
            &state.memory,
            16 + 4 * args.len(),
        )?;
        pay(
            self,
            state.conditions.len() + state.memory.missing_places.entries().len() * 3 + 12,
        )?;
        let mut results = self.call_instance(
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            stack,
            site,
        )?;
        for result in &mut results {
            self.mutable_product_access_begin(
                &selected,
                std::ptr::from_ref(selected.as_ref()) as usize,
                &result.memory,
                16,
            )?;
            primitive_value(self, signature.output(), &result.value, &result.conditions)?;
            let returned = self.mutable_product_backing(id, &result.memory)?;
            let h = returned
                .hierarchy
                .as_ref()
                .ok_or("product helper Return lost lineage")?;
            let clone_work = hierarchy_clone_work(self, &entered)? + data.len() + 16;
            pay(self, clone_work)?;
            if result.memory.mutable_hierarchy != Some(id)
                || !Rc::ptr_eq(&h.origin, &before.origin)
                || h.issued != before.issued
                || h.epoch != before.epoch
                || h.pending.is_some()
                || h.owners != entered.owners
                || returned.data != Storage::Product(data.clone())
                || self.mutable_u16_contains(&result.value, &result.memory)?
            {
                return Err(
                    "product helper Return changed owner/data/ancestry or escaped role".into(),
                );
            }
            pay_backing_cow(self, &result.memory)?;
            let current = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("product helper Return lost owning invocation")?;
            current
                .owners
                .last_mut()
                .ok_or("product helper Return lost current leaf")?
                .frames
                .pop();
        }
        self.mutable_product_access_begin(
            body,
            std::ptr::from_ref(&body.basic_blocks[block].terminator().kind) as usize,
            &state.memory,
            16,
        )?;
        Ok(Some(results))
    }
}

#[cfg(test)]
#[path = "mutable_product_hierarchy/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "mutable_product_hierarchy/work_controls.rs"]
pub(in crate::proof) mod work_controls;

#[cfg(test)]
pub(in crate::proof) fn niche_codec_signature<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ty::PolyFnSig<'tcx>, String> {
    signature::check_niche(engine, instance)
}
