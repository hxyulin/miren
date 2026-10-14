//! Paid actual instruction receipts for niche leaves; no owner permission is issued here.
use super::nonzero_niches::mutable_codec::{self as codec, Prepared, Session, Site, Use};
use super::*;
use rustc_middle::mir::BasicBlock;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

pub(super) struct Registry<'tcx> {
    current: RefCell<Option<Scope<'tcx>>>,
    failed: Cell<bool>,
    frames: Rc<RefCell<Vec<Rc<Frame>>>>,
}
impl Default for Registry<'_> {
    fn default() -> Self {
        Self {
            current: RefCell::new(None),
            failed: Cell::new(false),
            frames: Rc::new(RefCell::new(Vec::new())),
        }
    }
}
struct Leaf<'tcx> {
    place: Place<'tcx>,
    operand: usize,
    path: Vec<usize>,
    site: Site<'tcx>,
    prepared: Option<Prepared<'tcx>>,
}
struct Scope<'tcx> {
    body: Rc<Body<'tcx>>,
    instance: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    frame: Option<Rc<Frame>>,
    conditions: Vec<Term>,
    token: Term,
    remaining: usize,
    #[cfg(test)]
    deny_replan: bool,
    #[cfg(test)]
    denied_replan_work: Option<usize>,
    body_bound: usize,
    signature_bound: usize,
    value_work: usize,
    backing: Rc<Vec<super::mutable_u16::Backing>>,
    cow_ready: bool,
    leaves: Vec<Leaf<'tcx>>,
}

fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    engine.steps.checked_add_commit(count).ok_or_else(|| {
        engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "niche instruction work overflow".into(),
        )
    })?;
    if engine.steps.used() > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "niche instruction shared step limit reached".into(),
        ));
    }
    Ok(())
}

struct Frame {
    alive: Cell<bool>,
    pending: Cell<Option<BasicBlock>>,
}
pub(super) struct FrameGuard {
    frames: Rc<RefCell<Vec<Rc<Frame>>>>,
    frame: Rc<Frame>,
}
impl Drop for FrameGuard {
    fn drop(&mut self) {
        self.frame.alive.set(false);
        let Ok(mut frames) = self.frames.try_borrow_mut() else {
            // Invalidating the frame revokes every outstanding receipt even when a hostile
            // observer holds the registry. The next acquisition prunes this dead frame.
            return;
        };
        if frames
            .last()
            .is_some_and(|frame| Rc::ptr_eq(frame, &self.frame))
        {
            frames.pop();
        }
    }
}

fn leaves<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    path: &mut Vec<usize>,
    output: &mut Vec<(Ty<'tcx>, Vec<usize>)>,
    depth: usize,
    nodes: &mut usize,
) -> Result<(), String> {
    pay(engine, 16)?;
    *nodes += 1;
    if depth >= 16 || *nodes > 512 || output.len() >= 512 {
        return Err("niche instruction traversal exceeds bounded graph".into());
    }
    match original.kind() {
        ty::Tuple(fields) => {
            for (index, original) in fields.iter().enumerate() {
                path.push(index);
                leaves(engine, original, path, output, depth + 1, nodes)?;
                path.pop();
            }
        }
        ty::Array(element, count) => {
            let count = count
                .try_to_target_usize(engine.tcx)
                .ok_or("niche instruction original array count unavailable")?;
            if count > 128 {
                return Err("niche instruction original array exceeds128".into());
            }
            for index in 0..count as usize {
                path.push(index);
                leaves(engine, *element, path, output, depth + 1, nodes)?;
                path.pop();
            }
        }
        ty::Adt(def, args) if def.is_struct() && def.did().is_local() => {
            for (index, field) in def.non_enum_variant().fields.iter().enumerate() {
                pay(engine, 8)?;
                let original = field.ty(engine.tcx, args).skip_norm_wip();
                path.push(index);
                leaves(engine, original, path, output, depth + 1, nodes)?;
                path.pop();
            }
        }
        ty::Adt(def, _) if def.is_enum() => {
            // Only exact certified leaf receipts can be issued; arbitrary sums fail prepare.
            pay(engine, path.len() + 8)?;
            output.push((original, path.clone()));
        }
        _ => {}
    }
    Ok(())
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn niche_plan_work(&mut self, count: usize) -> Result<(), String> {
        pay(self, count)
    }
    pub(super) fn niche_backing_cow(&self, memory: &Memory) -> Result<(), String> {
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot publish backing COW".into());
        }
        let mut current = self
            .niche_ledger
            .current
            .try_borrow_mut()
            .map_err(|_| "niche backing ledger borrowed")?;
        let scope = current
            .as_mut()
            .ok_or("niche backing COW needs paid actual scope")?;
        if !scope.cow_ready || !Rc::ptr_eq(&scope.backing, &memory.mutable_u16) {
            self.niche_ledger.failed.set(true);
            return Err("niche prepaid full backing COW differs or already consumed".into());
        }
        scope.cow_ready = false;
        Ok(())
    }

    pub(super) fn niche_root_storage_work(&mut self, leaves: usize) -> Result<(), String> {
        if leaves > 512
            || self.mutable_integer_types.len() >= MAX_INPUT_VALUES
            || !self.niche_origins.is_empty()
        {
            return Err("niche root storage publication exceeds bounded fresh input".into());
        }
        pay(
            self,
            leaves * 128 + self.mutable_integer_types.len() * 8 + 192,
        )
    }

    fn niche_current_frame(&self) -> Result<Option<Rc<Frame>>, String> {
        let frames = self
            .niche_ledger
            .frames
            .try_borrow()
            .map_err(|_| "niche frame registry borrowed")?;
        if frames.len() > MAX_INPUT_DEPTH {
            return Err("niche current frame catalogue exceeds prepaid depth16".into());
        }
        Ok(frames.last().filter(|frame| frame.alive.get()).cloned())
    }
    pub(super) fn niche_frame_begin(
        &mut self,
        memory: &Memory,
    ) -> Result<Option<FrameGuard>, String> {
        if !self.niche_memory(memory) {
            return Ok(None);
        }
        let count = self
            .niche_ledger
            .frames
            .try_borrow()
            .map_err(|_| "niche frame registry borrowed")?
            .len();
        if count > MAX_INPUT_DEPTH {
            return Err("niche frame inventory exceeds existing depth16".into());
        }
        pay(self, count * 4 + 16)?;
        let mut frames = self
            .niche_ledger
            .frames
            .try_borrow_mut()
            .map_err(|_| "niche frame registry borrowed")?;
        frames.retain(|frame| frame.alive.get());
        if frames.len() >= MAX_INPUT_DEPTH {
            return Err("niche live frames exceed existing depth16".into());
        }
        let frame = Rc::new(Frame {
            alive: Cell::new(true),
            pending: Cell::new(None),
        });
        frames.push(frame.clone());
        Ok(Some(FrameGuard {
            frames: self.niche_ledger.frames.clone(),
            frame,
        }))
    }
    pub(super) fn niche_resume_call(
        &mut self,
        body: &Body<'tcx>,
        state: &State,
    ) -> Result<(), String> {
        if !self.niche_memory(&state.memory) {
            return Ok(());
        }
        let block = self
            .niche_ledger
            .frames
            .try_borrow()
            .map_err(|_| "niche frame registry borrowed")?
            .last()
            .filter(|frame| frame.alive.get())
            .and_then(|frame| frame.pending.get())
            .ok_or("niche caller Call boundary absent")?;
        let count = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche Body registry borrowed")?
            .len();
        if count > 128 {
            return Err("niche Body catalogue exceeds ordinary128 cap".into());
        }
        pay(self, count + 8)?;
        let instance = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche Body registry borrowed")?
            .iter()
            .find_map(|(instance, current)| {
                std::ptr::eq(current.as_ref(), body).then_some(*instance)
            })
            .ok_or("niche caller current Body absent")?;
        if !matches!(
            &body.basic_blocks[block].terminator().kind,
            TerminatorKind::Call { .. }
        ) {
            return Err("niche caller adoption needs actual Call".into());
        }
        self.niche_scope(instance, body, &state.memory, &state.conditions, Vec::new())
    }
    pub(super) fn niche_destination_scope(
        &mut self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        if !self.niche_memory(&state.memory) {
            return Ok(());
        }
        let block = self
            .niche_ledger
            .frames
            .try_borrow()
            .map_err(|_| "niche frame registry borrowed")?
            .last()
            .filter(|frame| frame.alive.get())
            .and_then(|frame| frame.pending.get())
            .ok_or("niche caller continuation absent")?;
        let count = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche Body registry borrowed")?
            .len();
        if count > 128 {
            return Err("niche Body catalogue exceeds ordinary128 cap".into());
        }
        pay(self, count + 8)?;
        let instance = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche Body registry borrowed")?
            .iter()
            .find_map(|(instance, current)| {
                std::ptr::eq(current.as_ref(), body).then_some(*instance)
            })
            .ok_or("niche caller Body not authenticated")?;
        if !matches!(&body.basic_blocks[block].terminator().kind,
            TerminatorKind::Call { destination, .. } if *destination == place)
        {
            return Err("niche writeback is not actual caller Call destination".into());
        }
        self.niche_terminator_scope(instance, body, state, block, true)
    }

    pub(super) fn niche_memory(&self, memory: &Memory) -> bool {
        memory
            .mutable_u16
            .iter()
            .any(|backing| self.niche_origins.contains_key(&backing.certificate))
    }
    pub(super) fn niche_scope_end(&self, failed: bool) {
        match self.niche_ledger.current.try_borrow_mut() {
            Ok(mut current) => {
                current.take();
            }
            Err(_) => {
                self.niche_ledger.failed.set(true);
            }
        }
        if failed && !self.niche_origins.is_empty() {
            self.niche_ledger.failed.set(true);
        }
    }
    fn niche_scope(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        memory: &Memory,
        conditions: &[Term],
        occurrences: Vec<(Place<'tcx>, usize, Site<'tcx>)>,
    ) -> Result<(), String> {
        if !self.niche_memory(memory) {
            return Ok(());
        }
        match self.niche_ledger.current.try_borrow_mut() {
            Ok(mut current) => {
                current.take();
            }
            Err(_) => {
                self.niche_ledger.failed.set(true);
                return Err("niche instruction ledger borrowed".into());
            }
        }
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot continue".into());
        }
        let result = (|| {
            let body_count = self
                .bodies
                .try_borrow()
                .map_err(|_| "niche Body registry borrowed")?
                .len();
            if body_count > 128 {
                return Err("niche Body catalogue exceeds ordinary128 cap".into());
            }
            pay(self, body_count + 32)?;
            let signature = mutable_hierarchy::products::niche_codec_signature(self, instance)?;
            let owned = self.instantiated_body(instance)?;
            pay(self, 32 + conditions.len() + occurrences.len() * 16)?;
            if !std::ptr::eq(owned.as_ref(), body) {
                return Err("niche actual Body differs".into());
            }
            let count = self
                .call_signatures
                .try_borrow()
                .map_err(|_| "niche signature registry borrowed")?
                .len();
            if count > 256 {
                return Err("niche signature catalogue exceeds ordinary256 cap".into());
            }
            pay(self, count + 16)?;
            let mut signatures = self
                .call_signatures
                .try_borrow_mut()
                .map_err(|_| "niche signature registry borrowed")?;
            if count < 256 {
                signatures.insert(instance, signature);
            }
            drop(signatures);
            if self.niche_origins.len() > 1 {
                return Err("niche origins exceed one-shot root input bound".into());
            }
            // Planning facts are immutable and paid at authentic root construction. Price only
            // this bounded origin catalogue lookup; current certificate comparisons stay separate.
            pay(self, self.niche_origins.len() + 8)?;
            let compare = self
                .niche_origins
                .values()
                .try_fold(0usize, |sum, origin| {
                    sum.checked_add(origin.compare_work())
                        .ok_or("niche comparison work overflow")
                })?;
            let occurrence_count = occurrences.len();
            let session = Rc::new(Session::default());
            let mut prepared = Vec::new();
            for (place, operand, site) in occurrences {
                if place
                    .projection
                    .iter()
                    .any(|part| matches!(part, ProjectionElem::Downcast(..)))
                {
                    // Local enum payload reads stay with existing enum semantics. Owner payload
                    // destinations will still fail typed product projection before publication.
                    continue;
                }
                let root = place.ty(&owned.local_decls, self.tcx).ty;
                let mut inventory = Vec::new();
                leaves(self, root, &mut Vec::new(), &mut inventory, 0, &mut 0)?;
                for (original, path) in inventory {
                    let issued = if path.is_empty() {
                        codec::prepare(self, &session, original, site, conditions)?
                    } else {
                        codec::prepare_traversal(
                            self,
                            &session,
                            original,
                            site,
                            conditions,
                            (root, &path),
                        )?
                    };
                    if let Some(issued) = issued {
                        if prepared.len() >= 512 {
                            return Err("niche whole instruction leaf inventory exceeds512".into());
                        }
                        pay(self, 16)?;
                        prepared.push(Leaf {
                            place,
                            operand,
                            path,
                            site,
                            prepared: Some(issued),
                        });
                    }
                }
            }
            // Codec preparation can legitimately acquire additional source entries. Bound the
            // actual inventories only after preparation, and refuse uncovered growth before any
            // later source lookup. A new actual instruction or caller scope reprices its entries.
            let body_bound = self
                .bodies
                .try_borrow()
                .map_err(|_| "niche Body registry borrowed")?
                .len();
            let signature_bound = self
                .call_signatures
                .try_borrow()
                .map_err(|_| "niche signature registry borrowed")?
                .len();
            if body_bound > 128 || signature_bound > 256 {
                return Err("niche source inventory exceeds ordinary catalogue caps".into());
            }
            let remaining = 64usize;
            let per_slot = compare
                .checked_add(2 * (body_bound + signature_bound) + 2 * MAX_INPUT_DEPTH + 16)
                .ok_or("niche source comparison reservation overflow")?;
            let compare_work = remaining
                .checked_mul(per_slot)
                .and_then(|work| work.checked_add(64))
                .ok_or("niche comparison reservation overflow")?;
            pay(self, compare_work)?;
            let receipt_work = prepared
                .len()
                .checked_mul(24)
                .and_then(|work| work.checked_add(conditions.len() + 32))
                .ok_or("niche actual receipt lookup plan overflow")?;
            let per_occurrence = if occurrence_count == 0 {
                0
            } else {
                // Immutable construction facts omit repeated schema traversal, while actual
                // occurrences, receipt lookups and value constructors retain their charges.
                pay(self, self.niche_origins.len() + 8)?;
                self.niche_origins
                    .values()
                    .try_fold(0usize, |sum, origin| {
                        sum.checked_add(origin.value_work(receipt_work)?)
                            .ok_or_else(|| "niche actual value plan overflow".to_owned())
                    })?
            };
            let value_work = occurrence_count
                .checked_mul(per_occurrence)
                .ok_or("niche actual occurrence value plan overflow")?;
            pay(self, value_work)?;
            let cow_work = mutable_hierarchy::products::niche_backing_clone_plan(self, memory)?;
            pay(self, cow_work)?;
            let scope = Scope {
                body: owned,
                instance,
                signature,
                frame: self.niche_current_frame()?,
                conditions: conditions.to_vec(),
                token: self.terms.boolean(true),
                remaining,
                #[cfg(test)]
                deny_replan: false,
                #[cfg(test)]
                denied_replan_work: None,
                body_bound,
                signature_bound,
                value_work,
                backing: memory.mutable_u16.clone(),
                cow_ready: true,
                leaves: prepared,
            };
            *self
                .niche_ledger
                .current
                .try_borrow_mut()
                .map_err(|_| "niche instruction ledger borrowed")? = Some(scope);
            Ok(())
        })();
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    pub(super) fn niche_entry_scope(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<(), String> {
        self.niche_scope(instance, body, memory, conditions, Vec::new())
    }
    pub(super) fn niche_statement_scope(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        state: &State,
        actual: &StatementKind<'tcx>,
    ) -> Result<(), String> {
        if !self.niche_memory(&state.memory) {
            return Ok(());
        }
        let mut found = None;
        if body.basic_blocks.len() > MAX_INPUT_VALUES {
            return Err("niche statement Body block inventory exceeds512".into());
        }
        pay(self, body.basic_blocks.len() + 8)?;
        let statements = body.basic_blocks.iter().try_fold(0usize, |sum, block| {
            sum.checked_add(block.statements.len())
                .ok_or("niche statement inventory overflow")
        })?;
        if statements > MAX_INPUT_VALUES {
            return Err("niche statement Body inventory exceeds512".into());
        }
        pay(self, body.basic_blocks.len() + statements + 8)?;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            if let Some(statement) = data
                .statements
                .iter()
                .position(|item| std::ptr::eq(&item.kind, actual))
            {
                found = Some((block, statement));
                break;
            }
        }
        let (block, statement) = found.ok_or("niche statement occurrence absent")?;
        let count = match actual {
            StatementKind::Assign(assignment) => match &assignment.1 {
                Rvalue::Aggregate(_, operands) => operands.len() + 1,
                _ => 2,
            },
            _ => 0,
        };
        if count > 512 {
            return Err("niche statement operand inventory exceeds512".into());
        }
        pay(self, count * 16 + 8)?;
        let mut occurrences = Vec::with_capacity(count);
        if let StatementKind::Assign(assignment) = actual {
            occurrences.push((
                assignment.0,
                usize::MAX,
                Site {
                    instance,
                    block,
                    statement,
                    ordinal: 0,
                    terminator: false,
                    kind: Use::Encode,
                },
            ));
            let operands = match &assignment.1 {
                Rvalue::Use(operand, _) => vec![(0, operand)],
                Rvalue::Aggregate(_, operands) => operands.iter().enumerate().collect(),
                _ => Vec::new(),
            };
            for (ordinal, operand) in operands {
                if let Operand::Copy(place) | Operand::Move(place) = operand {
                    occurrences.push((
                        *place,
                        std::ptr::from_ref(operand) as usize,
                        Site {
                            instance,
                            block,
                            statement,
                            ordinal,
                            terminator: false,
                            kind: Use::Decode,
                        },
                    ));
                }
            }
        }
        self.niche_scope(
            instance,
            body,
            &state.memory,
            &state.conditions,
            occurrences,
        )
    }
    pub(super) fn niche_terminator_scope(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        state: &State,
        block: BasicBlock,
        destination_only: bool,
    ) -> Result<(), String> {
        if !self.niche_memory(&state.memory) {
            return Ok(());
        }
        if matches!(
            &body.basic_blocks[block].terminator().kind,
            TerminatorKind::TailCall { .. }
        ) {
            // The interpreter does not execute TailCall. Refuse before issuing reusable
            // caller-frame receipts, including self tail calls with identical source IDs.
            self.niche_scope_end(true);
            return Err("niche owner TailCall execution unsupported".into());
        }
        if let Some(frame) = self.niche_current_frame()? {
            frame.pending.set(Some(block));
        }
        let count = match &body.basic_blocks[block].terminator().kind {
            TerminatorKind::Call { args, .. } => args.len() + 1,
            _ => 0,
        };
        if count > 512 {
            return Err("niche Call operand inventory exceeds512".into());
        }
        pay(self, count * 16 + 8)?;
        let mut occurrences = Vec::with_capacity(count);
        match &body.basic_blocks[block].terminator().kind {
            TerminatorKind::Call {
                args, destination, ..
            } => {
                occurrences.push((
                    *destination,
                    usize::MAX,
                    Site {
                        instance,
                        block,
                        statement: 0,
                        ordinal: 0,
                        terminator: true,
                        kind: Use::Encode,
                    },
                ));
                if !destination_only {
                    for (ordinal, operand) in args.iter().enumerate() {
                        if let Operand::Copy(place) | Operand::Move(place) = &operand.node {
                            occurrences.push((
                                *place,
                                std::ptr::from_ref(&operand.node) as usize,
                                Site {
                                    instance,
                                    block,
                                    statement: 0,
                                    ordinal,
                                    terminator: true,
                                    kind: Use::Decode,
                                },
                            ));
                        }
                    }
                }
            }
            TerminatorKind::TailCall { args, .. } => {
                for (ordinal, operand) in args.iter().enumerate() {
                    if let Operand::Copy(place) | Operand::Move(place) = &operand.node {
                        occurrences.push((
                            *place,
                            std::ptr::from_ref(&operand.node) as usize,
                            Site {
                                instance,
                                block,
                                statement: 0,
                                ordinal,
                                terminator: true,
                                kind: Use::Decode,
                            },
                        ));
                    }
                }
            }
            _ => {}
        }
        self.niche_scope(
            instance,
            body,
            &state.memory,
            &state.conditions,
            occurrences,
        )
    }
    fn niche_source_replan(&mut self, bodies: usize, signatures: usize) -> Result<(), String> {
        let active = self
            .niche_ledger
            .current
            .try_borrow()
            .map_err(|_| "niche source scope borrowed during acquisition")?;
        let Some(scope) = active.as_ref() else {
            return Ok(());
        };
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot acquire source work".into());
        }
        let old_bodies = scope.body_bound;
        let old_signatures = scope.signature_bound;
        let remaining = scope.remaining;
        #[cfg(test)]
        let deny_replan = scope.deny_replan;
        drop(active);
        let current_bodies = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche Body registry borrowed during acquisition")?
            .len();
        let current_signatures = self
            .call_signatures
            .try_borrow()
            .map_err(|_| "niche signature registry borrowed during acquisition")?
            .len();
        if current_bodies > old_bodies || current_signatures > old_signatures {
            return Err(
                "niche acquisition cannot cover preexisting unplanned source growth".into(),
            );
        }
        let body_bound = current_bodies
            .checked_add(bodies)
            .ok_or("niche pending Body inventory overflow")?
            .max(old_bodies);
        let signature_bound = current_signatures
            .checked_add(signatures)
            .ok_or("niche pending signature inventory overflow")?
            .max(old_signatures);
        if body_bound > 128 || signature_bound > 256 {
            return Err("niche source acquisition exceeds ordinary catalogue caps".into());
        }
        let work = (body_bound - old_bodies)
            .checked_add(signature_bound - old_signatures)
            .and_then(|work| work.checked_mul(2))
            .and_then(|work| work.checked_mul(remaining))
            .ok_or("niche remaining source reservation overflow")?;
        #[cfg(test)]
        if deny_replan && work != 0 {
            self.niche_ledger
                .current
                .borrow_mut()
                .as_mut()
                .unwrap()
                .denied_replan_work = Some(work);
            self.limits.max_steps = self.steps.used().checked_add(work - 1).unwrap();
        }
        if work != 0 {
            pay(self, work)?;
        }
        let mut active = self
            .niche_ledger
            .current
            .try_borrow_mut()
            .map_err(|_| "niche source scope borrowed at acquisition publication")?;
        let scope = active
            .as_mut()
            .ok_or("niche source scope disappeared during acquisition")?;
        scope.body_bound = body_bound;
        scope.signature_bound = signature_bound;
        Ok(())
    }
    fn niche_acquisition_selected(&self) -> Result<bool, String> {
        let result = self.niche_acquisition_selected_inner();
        if result.is_err() && !self.niche_origins.is_empty() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    fn niche_acquisition_selected_inner(&self) -> Result<bool, String> {
        let selected = self
            .niche_ledger
            .current
            .try_borrow()
            .map_err(|_| "niche scope borrowed during acquisition selection")?
            .is_some();
        if selected
            && self
                .mutable_product_access
                .try_borrow()
                .map_err(|_| "Product scope borrowed during niche acquisition selection")?
                .is_some()
        {
            self.niche_ledger.failed.set(true);
            return Err("simultaneous Product/niche source acquisition is unsupported".into());
        }
        Ok(selected)
    }
    pub(super) fn niche_call_signature_prepare(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if !self.niche_acquisition_selected()? {
            return Ok(());
        }
        let result = (|| {
            self.niche_source_inventory_guard()?;
            let count = self
                .call_signatures
                .try_borrow()
                .map_err(|_| "niche signature registry borrowed")?
                .len();
            pay(self, count + 8)?;
            let present = self
                .call_signatures
                .try_borrow()
                .map_err(|_| "niche signature registry borrowed")?
                .contains_key(&instance);
            let actual = mutable_hierarchy::products::niche_codec_signature(self, instance)?;
            if present || count >= 256 {
                return Ok(());
            }
            self.niche_source_replan(0, 1)?;
            pay(self, 8)?;
            self.call_signatures
                .try_borrow_mut()
                .map_err(|_| "niche signature registry borrowed at publication")?
                .insert(instance, actual);
            Ok(())
        })();
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    pub(super) fn niche_length_body(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<Rc<Body<'tcx>>, String> {
        if !self.niche_acquisition_selected()? {
            return self.instantiated_body(instance);
        }
        let result = (|| {
            self.niche_source_inventory_guard()?;
            let count = self
                .bodies
                .try_borrow()
                .map_err(|_| "niche Body registry borrowed")?
                .len();
            pay(self, count + 8)?;
            let present = self
                .bodies
                .try_borrow()
                .map_err(|_| "niche Body registry borrowed")?
                .contains_key(&instance);
            if !present {
                self.niche_source_replan(1, 0)?;
            }
            self.instantiated_body(instance)
        })();
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    pub(super) fn niche_value_work(&self, count: usize) -> Result<(), String> {
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot construct values".into());
        }
        let mut current = self
            .niche_ledger
            .current
            .try_borrow_mut()
            .map_err(|_| "niche value ledger borrowed")?;
        let scope = current
            .as_mut()
            .ok_or("niche value needs paid current scope")?;
        let Some(remaining) = scope.value_work.checked_sub(count) else {
            self.niche_ledger.failed.set(true);
            return Err("niche value construction reservation exhausted".into());
        };
        scope.value_work = remaining;
        Ok(())
    }
    pub(super) fn niche_source_inventory_guard(&self) -> Result<(), String> {
        let result = self.niche_source_inventory_guard_inner();
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    fn niche_source_inventory_guard_inner(&self) -> Result<(), String> {
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot validate source inventory".into());
        }
        let active = self
            .niche_ledger
            .current
            .try_borrow()
            .map_err(|_| "niche instruction ledger borrowed")?;
        let scope = active
            .as_ref()
            .ok_or("niche source inventory needs paid current scope")?;
        let bodies = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche current Body registry borrowed")?;
        let signatures = self
            .call_signatures
            .try_borrow()
            .map_err(|_| "niche current signature registry borrowed")?;
        if bodies.len() > scope.body_bound || signatures.len() > scope.signature_bound {
            return Err(
                "niche originating source catalogue exceeds prepaid actual inventory".into(),
            );
        }
        Ok(())
    }
    pub(super) fn niche_certificate_work(&self, id: usize) -> Result<(), String> {
        let result = self.niche_certificate_work_inner(id);
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    fn niche_certificate_work_inner(&self, _: usize) -> Result<(), String> {
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot consume descriptor work".into());
        }
        let mut active = self
            .niche_ledger
            .current
            .try_borrow_mut()
            .map_err(|_| "niche instruction ledger borrowed")?;
        let scope = active
            .as_mut()
            .ok_or("niche owner needs paid actual observation scope")?;
        if scope.remaining == 0 {
            return Err("niche descriptor comparison slots exhausted".into());
        }
        scope.remaining -= 1;
        let bodies = self
            .bodies
            .try_borrow()
            .map_err(|_| "niche current Body registry borrowed")?;
        let signatures = self
            .call_signatures
            .try_borrow()
            .map_err(|_| "niche current signature registry borrowed")?;
        if bodies.len() > scope.body_bound || signatures.len() > scope.signature_bound {
            return Err("niche current source catalogue exceeds prepaid actual inventory".into());
        }
        let current_frame = self.niche_current_frame()?;
        if scope.frame.as_ref().is_some_and(|frame| {
            !frame.alive.get()
                || current_frame
                    .as_ref()
                    .is_none_or(|current| !Rc::ptr_eq(frame, current))
        }) || !scope.token.belongs_to(&self.terms)
            || bodies
                .get(&scope.instance)
                .is_none_or(|body| !Rc::ptr_eq(body, &scope.body))
            || signatures
                .get(&scope.instance)
                .is_some_and(|signature| *signature != scope.signature)
        {
            return Err("niche current instruction binding differs".into());
        }
        Ok(())
    }
    pub(super) fn niche_leaf(
        &self,
        state: &State,
        place: Place<'tcx>,
        path: &[usize],
        kind: Use,
    ) -> Result<(Prepared<'tcx>, Site<'tcx>), String> {
        let result = self.niche_leaf_inner(state, place, path, kind);
        if result.is_err() {
            self.niche_ledger.failed.set(true);
        }
        result
    }
    fn niche_leaf_inner(
        &self,
        state: &State,
        place: Place<'tcx>,
        path: &[usize],
        kind: Use,
    ) -> Result<(Prepared<'tcx>, Site<'tcx>), String> {
        if self.niche_ledger.failed.get() {
            return Err("failed niche execution cannot consume leaf receipt".into());
        }
        let mut active = self
            .niche_ledger
            .current
            .try_borrow_mut()
            .map_err(|_| "niche instruction ledger borrowed")?;
        let scope = active
            .as_mut()
            .ok_or("niche leaf needs actual instruction receipt")?;
        let lookup = scope
            .leaves
            .len()
            .checked_mul(24)
            .and_then(|work| work.checked_add(scope.conditions.len() + 32))
            .ok_or("niche receipt lookup reservation overflow")?;
        scope.value_work = scope
            .value_work
            .checked_sub(lookup)
            .ok_or("niche receipt lookup reservation exhausted")?;
        let current_frame = self.niche_current_frame()?;
        if scope.frame.as_ref().is_none_or(|frame| {
            !frame.alive.get()
                || current_frame
                    .as_ref()
                    .is_none_or(|current| !Rc::ptr_eq(frame, current))
        }) || scope.conditions != state.conditions
        {
            return Err("niche current conditions differ".into());
        }
        let operand = if kind == Use::Encode {
            usize::MAX
        } else {
            self.niche_operand.get()
        };
        let leaf = scope
            .leaves
            .iter_mut()
            .find(|leaf| {
                leaf.place == place
                    && leaf.path == path
                    && leaf.site.kind == kind
                    && leaf.operand == operand
            })
            .ok_or("niche actual operand ordinal/path receipt absent")?;
        let prepared = leaf
            .prepared
            .take()
            .ok_or("niche leaf receipt already consumed")?;
        Ok((prepared, leaf.site))
    }
}

#[cfg(test)]
#[path = "mutable_product_niche_owner_probe.rs"]
mod owner_probe;
