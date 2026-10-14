//! Exact real-call IntoIter constructor frames with one owned payload and private metadata.
//! Normal return and destination publication use existing typed owned-value storage services.
//! Actual element transfer needs an explicit larger budget; remaining Drop and inlining stay open.
use super::*;
use rustc_middle::mir::{BasicBlock, CastKind, Local, MirPhase, RuntimePhase};
use std::rc::Rc;
#[path = "array_iterator_clone_work.rs"]
mod clone_work;
mod compiler_evidence;
pub(super) mod drops;
pub(super) mod steps;

const MAX_ELEMENTS: u64 = 128;

/// Sole branch-local owned storage; immutable compiler identity is held separately.
#[derive(Clone, Debug)]
pub struct Payload {
    pub(super) slots: Rc<Vec<Option<Value>>>,
    pub(super) front: usize,
    pub(super) back: usize,
    pub(super) pending: Option<steps::Pending>,
    pub(super) dropping: Option<drops::Progress>,
    pub(super) retired: bool,
}
impl Payload {
    fn new(elements: symbolic::Elements) -> Self {
        let back = elements.len();
        Self {
            slots: Rc::new(elements.into_iter().map(Some).collect()),
            front: 0,
            back,
            pending: None,
            dropping: None,
            retired: false,
        }
    }
    pub(super) fn len(&self) -> usize {
        self.slots.len()
    }
    pub(super) fn iter(&self) -> impl Iterator<Item = &Value> {
        self.slots.iter().filter_map(Option::as_ref)
    }
    pub(super) fn validate(&self, count: usize, allow_pending: bool) -> Result<(), String> {
        if self.retired || self.slots.len() != count || self.front > self.back || self.back > count
        {
            return Err("IntoIter owned cursor/slot cardinality or retirement differs".into());
        }
        if self.pending.is_some() && !allow_pending {
            return Err("IntoIter pending yield cannot leave its actual invocation".into());
        }
        if let Some(progress) = &self.dropping {
            progress.validate(self)?;
            return Err("IntoIter active destruction cannot leave its actual invocation".into());
        }
        for (index, slot) in self.slots.iter().enumerate() {
            let alive = (self.front..self.back).contains(&index);
            let pending = self
                .pending
                .as_ref()
                .is_some_and(|pending| pending.index == index);
            if alive && pending || slot.is_some() != (alive || pending) {
                return Err("IntoIter initialized slots differ from alive/pending interval".into());
            }
        }
        Ok(())
    }
}

pub(super) struct PhysicalTypes<'tcx> {
    identity: Rc<()>,
    context: Term,
    issuer: BodyEvidence<'tcx>,
    iterator: Ty<'tcx>,
    manually_drop: Ty<'tcx>,
    sized_inner: Ty<'tcx>,
    storage_array: Ty<'tcx>,
    initialized_element: Ty<'tcx>,
    count: usize,
    data_offset: u64,
    element_size: u64,
    owner_size: u64,
}

struct BodyEvidence<'tcx> {
    instance: ty::Instance<'tcx>,
    current: Rc<Body<'tcx>>,
}

fn pay(engine: &mut Engine<'_>, operations: usize) -> Result<(), String> {
    let next = match engine.steps.checked_add(operations) {
        Some(next) => next,
        None => {
            engine.steps = usize::MAX;
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter operation count overflow".into(),
            ));
        }
    };
    engine.steps = next;
    if next > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter shared execution step limit reached".into(),
        ));
    }
    Ok(())
}

fn exact_field<'tcx>(
    engine: &mut Engine<'tcx>,
    owner: Ty<'tcx>,
    index: usize,
) -> Result<Ty<'tcx>, String> {
    pay(engine, 3)?;
    let ty::Adt(def, args) = owner.kind() else {
        return Err("IntoIter physical wrapper is not its original ADT".into());
    };
    if !def.is_struct() || def.repr().packed() {
        return Err("IntoIter physical wrapper is not an unpacked struct".into());
    }
    let field = def
        .non_enum_variant()
        .fields
        .raw
        .get(index)
        .ok_or("IntoIter physical wrapper field is unavailable")?;
    engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            field.ty(engine.tcx, args),
        )
        .map_err(|error| format!("IntoIter original FieldTy unavailable: {error:?}"))
}

fn source_identity<'tcx>(body: &Body<'tcx>, instance: ty::Instance<'tcx>) -> Result<(), String> {
    if body.source.instance != instance.def || body.source.promoted.is_some() {
        return Err("IntoIter compiler Body source Instance or promoted identity differs".into());
    }
    Ok(())
}

fn step_debug_equal<'tcx>(
    engine: &mut Engine<'_>,
    a: &rustc_middle::mir::StmtDebugInfos<'tcx>,
    b: &rustc_middle::mir::StmtDebugInfos<'tcx>,
) -> Result<bool, String> {
    pay(engine, 1 + a.len())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    Ok(a.as_slice()
        .iter()
        .zip(b.as_slice())
        .all(|(a, b)| match (a, b) {
            (
                rustc_middle::mir::StmtDebugInfo::AssignRef(a, ap),
                rustc_middle::mir::StmtDebugInfo::AssignRef(b, bp),
            ) => a == b && ap == bp,
            (
                rustc_middle::mir::StmtDebugInfo::InvalidAssign(a),
                rustc_middle::mir::StmtDebugInfo::InvalidAssign(b),
            ) => a == b,
            _ => false,
        }))
}
impl<'tcx> BodyEvidence<'tcx> {
    fn load(engine: &mut Engine<'tcx>, instance: ty::Instance<'tcx>) -> Result<Self, String> {
        pay(engine, 2)?;
        match instance.def {
            ty::InstanceKind::Item(id) => {
                if !engine.tcx.is_mir_available(id) {
                    return Err(engine.categorized_error(
                        UnknownCategory::MissingCompilerEvidence,
                        engine.missing_body_reason(id),
                    ));
                }
            }
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, _)) => {}
            _ => {
                return Err(engine.categorized_error(
                    UnknownCategory::MissingCompilerEvidence,
                    "IntoIter certificate does not admit an intrinsic or other Body adapter".into(),
                ));
            }
        }
        let raw = engine.tcx.instance_mir(instance.def);
        source_identity(raw, instance)?;
        let owned = clone_work::body(engine, raw)?;
        let cached = engine.bodies.borrow().contains_key(&instance);
        if !cached {
            pay(engine, owned)?; // Actual uncached current Body owned clone.
            pay(engine, owned)?; // Owned-structure fold bound; opaque queries are not priced here.
        }
        let current = engine.instantiated_body(instance)?;
        source_identity(&current, instance)?;
        pay(engine, 1 + raw.local_decls.len() + raw.basic_blocks.len())?;
        pay(engine, owned)?; // Independent raw Body clone, paid before allocation.
        pay(engine, owned)?; // Distinct owned-structure normalization/fold bound.
        let original = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, raw.clone()),
            )
            .map_err(|error| format!("IntoIter raw compiler substitution failed: {error:?}"))?;
        if original.coroutine.is_some()
            || current.coroutine.is_some()
            || original.tainted_by_errors.is_some()
            || current.tainted_by_errors.is_some()
            || original.spread_arg.is_some()
            || current.spread_arg.is_some()
            || original.arg_count != current.arg_count
            || original.span != current.span
            || original.phase != current.phase
            || original.local_decls.len() != current.local_decls.len()
            || original.basic_blocks.len() != current.basic_blocks.len()
        {
            return Err("IntoIter original/current Body header differs".into());
        }
        for (a, b) in original.local_decls.iter().zip(current.local_decls.iter()) {
            pay(engine, 3)?;
            if a.ty != b.ty || a.mutability != b.mutability || a.source_info != b.source_info {
                return Err("IntoIter original/current local type or source differs".into());
            }
        }
        for (a, b) in original
            .basic_blocks
            .iter()
            .zip(current.basic_blocks.iter())
        {
            pay(engine, 4)?;
            if !a.terminator().attributes.is_empty()
                || !b.terminator().attributes.is_empty()
                || a.is_cleanup != b.is_cleanup
                || a.statements.len() != b.statements.len()
                || a.terminator().kind != b.terminator().kind
                || a.terminator().source_info != b.terminator().source_info
            {
                return Err("IntoIter original/current block or terminator differs".into());
            }
            for (a, b) in a.statements.iter().zip(&b.statements) {
                pay(engine, 4)?;
                if a.kind != b.kind
                    || a.source_info != b.source_info
                    || !a.debuginfos.is_empty()
                    || !b.debuginfos.is_empty()
                {
                    return Err("IntoIter original/current statement or source differs".into());
                }
            }
        }
        Ok(Self { instance, current })
    }

    fn current(&self, engine: &mut Engine<'tcx>) -> Result<(), String> {
        pay(engine, 2)?;
        let cache = engine.bodies.borrow();
        let cached = cache
            .get(&self.instance)
            .ok_or("IntoIter admitted current Body is no longer cached")?;
        if !Rc::ptr_eq(&self.current, cached) {
            return Err("IntoIter admitted current Body was replaced".into());
        }
        source_identity(&self.current, self.instance)
    }
}

fn local(place: Place<'_>, index: usize) -> bool {
    place.local == Local::from_usize(index) && place.projection.is_empty()
}
fn assignment<'a, 'tcx>(
    body: &'a Body<'tcx>,
    index: usize,
    destination: usize,
) -> Result<&'a Rvalue<'tcx>, String> {
    let statement = body.basic_blocks[BasicBlock::from_usize(0)]
        .statements
        .get(index)
        .ok_or("IntoIter constructor assignment is missing")?;
    let StatementKind::Assign(pair) = &statement.kind else {
        return Err("IntoIter constructor operation is not its exact assignment".into());
    };
    if !local(pair.0, destination) {
        return Err("IntoIter constructor assignment destination differs".into());
    }
    Ok(&pair.1)
}

fn aggregate<'a, 'tcx>(
    engine: &mut Engine<'tcx>,
    value: &'a Rvalue<'tcx>,
    original: Ty<'tcx>,
    statement: usize,
    evidence: &BodyEvidence<'tcx>,
) -> Result<&'a rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>, String> {
    let Rvalue::Aggregate(kind, operands) = value else {
        return Err("IntoIter constructor lacks exact aggregate transport".into());
    };
    let AggregateKind::Adt(id, variant, args, user, active) = kind.as_ref() else {
        return Err("IntoIter constructor aggregate is not its original ADT".into());
    };
    if variant.as_usize() != 0
        || active.is_some()
        || Ty::new_adt(engine.tcx, engine.tcx.adt_def(*id), args) != original
    {
        return Err("IntoIter constructor aggregate identity or arguments differ".into());
    }
    if user.is_some() {
        authenticate_residual_user(engine, evidence, statement, value)?;
    }
    Ok(operands)
}

fn authenticate_residual_user<'tcx>(
    engine: &mut Engine<'tcx>,
    evidence: &BodyEvidence<'tcx>,
    statement: usize,
    value: &Rvalue<'tcx>,
) -> Result<(), String> {
    evidence.current(engine)?;
    pay(engine, 10)?;
    let body = &evidence.current;
    let raw = engine.tcx.instance_mir(evidence.instance.def);
    source_identity(body, evidence.instance)?;
    source_identity(raw, evidence.instance)?;
    if body.phase != MirPhase::Runtime(RuntimePhase::Optimized)
        || raw.phase != body.phase
        || !body.user_type_annotations.is_empty()
        || !raw.user_type_annotations.is_empty()
    {
        return Err("IntoIter residual user annotation phase or tables differ".into());
    }
    let current = body.basic_blocks[BasicBlock::from_usize(0)]
        .statements
        .get(statement)
        .ok_or("IntoIter current aggregate statement is missing")?;
    let original = raw.basic_blocks[BasicBlock::from_usize(0)]
        .statements
        .get(statement)
        .ok_or("IntoIter original aggregate statement is missing")?;
    let (StatementKind::Assign(current), StatementKind::Assign(original)) =
        (&current.kind, &original.kind)
    else {
        return Err("IntoIter residual user annotation assignment differs".into());
    };
    if !current.0.projection.is_empty() || original.0 != current.0 || current.1 != *value {
        return Err(
            "IntoIter residual user annotation destination or current occurrence differs".into(),
        );
    }
    let Rvalue::Aggregate(kind, operands) = &original.1 else {
        return Err("IntoIter residual user annotation original aggregate is missing".into());
    };
    if !matches!(kind.as_ref(), AggregateKind::Adt(_, _, _, Some(_), None)) {
        return Err("IntoIter residual user annotation original role differs".into());
    }
    // Clone only this bounded constructor Rvalue, including its real aggregate Box and operand Vec.
    // Exact normalized equality covers DefId, variant, generic arguments, user index, active field
    // and every operand. Rendering is never used as an equality check.
    pay(engine, 3 + 3 * operands.len())?;
    pay(engine, 4 + 3 * operands.len())?;
    let normalized = evidence
        .instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            engine.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(engine.tcx, original.1.clone()),
        )
        .map_err(|error| format!("IntoIter original aggregate substitution failed: {error:?}"))?;
    if normalized != *value {
        return Err("IntoIter residual user annotation original occurrence differs".into());
    }
    Ok(())
}

fn constant_usize<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: &Operand<'tcx>,
    expected: u128,
) -> Result<(), String> {
    let Operand::Constant(value) = value else {
        return Err("IntoIter range bound is not its original compiler constant".into());
    };
    let width = rustc_abi::Size::from_bits(u64::from(tcx.sess.target.pointer_width));
    if value.const_.ty() != tcx.types.usize
        || value
            .const_
            .try_eval_scalar_int(tcx, ty::TypingEnv::fully_monomorphized())
            .filter(|value| value.size() == width)
            .map(|value| value.to_bits(width))
            != Some(expected)
    {
        return Err("IntoIter compiler range bound differs".into());
    }
    Ok(())
}

impl<'tcx> PhysicalTypes<'tcx> {
    fn constructor(
        engine: &mut Engine<'tcx>,
        evidence: &BodyEvidence<'tcx>,
    ) -> Result<Self, String> {
        evidence.current(engine)?;
        let body = &evidence.current;
        pay(engine, 5)?;
        if body.arg_count != 1
            || body.local_decls.len() != 6
            || body.basic_blocks.len() != 1
            || body.basic_blocks[BasicBlock::from_usize(0)]
                .statements
                .len()
                != 13
            || !matches!(
                body.basic_blocks[BasicBlock::from_usize(0)]
                    .terminator()
                    .kind,
                TerminatorKind::Return
            )
        {
            return Err("IntoIter complete constructor schema differs".into());
        }
        let iterator = body.local_decls[Local::from_usize(0)].ty;
        let ty::Adt(def, args) = iterator.kind() else {
            return Err("IntoIter constructor result is not its compiler ADT".into());
        };
        if engine
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("ArrayIntoIter"))
            != Some(def.did())
            || args.len() != 2
        {
            return Err("IntoIter constructor result lacks exact compiler identity".into());
        }
        let callee = evidence.instance.def_id();
        let parent = engine.tcx.parent(callee);
        if callee.krate != def.did().krate
            || engine.tcx.def_kind(callee) != DefKind::AssocFn
            || engine.tcx.item_name(callee).as_str() != "into_iter"
            || !matches!(
                engine.tcx.def_kind(parent),
                DefKind::Impl { of_trait: true }
            )
            || Some(
                engine
                    .tcx
                    .impl_trait_ref(parent)
                    .instantiate(engine.tcx, evidence.instance.args)
                    .skip_norm_wip()
                    .def_id,
            ) != engine
                .tcx
                .get_diagnostic_item(rustc_span::Symbol::intern("IntoIterator"))
        {
            return Err(
                "IntoIter constructor lacks actual core IntoIterator method identity".into(),
            );
        }
        let initialized_element = args.type_at(0);
        if !initialized_element.is_freeze(engine.tcx, ty::TypingEnv::fully_monomorphized()) {
            return Err("IntoIter constructor interior-mutable payloads are unsupported".into());
        }
        let count = args
            .const_at(1)
            .try_to_target_usize(engine.tcx)
            .ok_or("IntoIter original count is not concrete")?;
        if count > MAX_ELEMENTS {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter exceeds original 128-element limit".into(),
            ));
        }
        let input = body.local_decls[Local::from_usize(1)].ty;
        if !matches!(input.kind(), ty::Array(element, length)
            if *element == initialized_element
                && length.try_to_target_usize(engine.tcx) == Some(count))
        {
            return Err("IntoIter constructor input original T/N differs".into());
        }
        let manually_drop = exact_field(engine, iterator, 0)?;
        let ty::Adt(drop, _) = manually_drop.kind() else {
            return Err("IntoIter inner storage lacks ManuallyDrop".into());
        };
        if engine.tcx.lang_items().get(LangItem::ManuallyDrop) != Some(drop.did()) {
            return Err("IntoIter inner storage lacks compiler ManuallyDrop identity".into());
        }
        let sized_inner = exact_field(engine, manually_drop, 0)?;
        let range = exact_field(engine, sized_inner, 0)?;
        let storage_array = exact_field(engine, sized_inner, 1)?;
        let ty::Array(storage_element, length) = storage_array.kind() else {
            return Err("IntoIter physical data is not its original MaybeUninit array".into());
        };
        if length.try_to_target_usize(engine.tcx) != Some(count) {
            return Err("IntoIter physical data count differs".into());
        }
        let ty::Adt(union, union_args) = storage_element.kind() else {
            return Err("IntoIter physical element is not MaybeUninit".into());
        };
        if engine.tcx.lang_items().get(LangItem::MaybeUninit) != Some(union.did())
            || !union.is_union()
            || union_args.len() != 1
            || union_args.type_at(0) != initialized_element
        {
            return Err("IntoIter physical MaybeUninit payload differs".into());
        }
        pay(engine, 8)?;
        for (original, fields) in [
            (iterator, 1),
            (manually_drop, 1),
            (sized_inner, 2),
            (range, 2),
        ] {
            let ty::Adt(def, _) = original.kind() else {
                unreachable!()
            };
            if def.non_enum_variant().fields.len() != fields {
                return Err("IntoIter original physical wrapper field cardinality differs".into());
            }
        }
        let owner_layout = engine.static_layout(iterator)?;
        let drop_layout = engine.static_layout(manually_drop)?;
        let physical = engine.static_layout(*storage_element)?;
        let payload = engine.static_layout(initialized_element)?;
        let inner = engine.static_layout(sized_inner)?;
        if physical.size != payload.size
            || physical.align != payload.align
            || storage_element.needs_drop(engine.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err("IntoIter physical MaybeUninit payload layout differs".into());
        }
        // An inhabited payload is still checked at the genuine intrinsic occurrence during next.
        let Rvalue::Cast(CastKind::Transmute, Operand::Copy(source), target) =
            assignment(body, 1, 2)?
        else {
            return Err("IntoIter constructor lacks exact array transmute transport".into());
        };
        if !local(*source, 1) || *target != storage_array {
            return Err("IntoIter constructor transmute source or destination differs".into());
        }
        pay(engine, 13)?;
        for (position, id, live) in [
            (0, 2, true),
            (2, 3, true),
            (3, 4, true),
            (6, 4, false),
            (7, 5, true),
            (10, 5, false),
            (11, 3, false),
            (12, 2, false),
        ] {
            let kind = &body.basic_blocks[BasicBlock::from_usize(0)].statements[position].kind;
            if !matches!(kind, StatementKind::StorageLive(local) if live && local.as_usize() == id)
                && !matches!(kind, StatementKind::StorageDead(local)
                    if !live && local.as_usize() == id)
            {
                return Err("IntoIter constructor storage lifetime schedule differs".into());
            }
        }
        for (index, original) in [
            (2, storage_array),
            (3, sized_inner),
            (4, range),
            (5, manually_drop),
        ] {
            if body.local_decls[Local::from_usize(index)].ty != original {
                return Err("IntoIter constructor temporary original type differs".into());
            }
        }
        let bounds = aggregate(engine, assignment(body, 4, 4)?, range, 4, evidence)?;
        if bounds.len() != 2
            || exact_field(engine, range, 0)? != engine.tcx.types.usize
            || exact_field(engine, range, 1)? != engine.tcx.types.usize
        {
            return Err("IntoIter compiler IndexRange shape differs".into());
        }
        constant_usize(engine.tcx, &bounds.raw[0], 0)?;
        constant_usize(engine.tcx, &bounds.raw[1], u128::from(count))?;
        let inner_fields = aggregate(engine, assignment(body, 5, 3)?, sized_inner, 5, evidence)?;
        if inner_fields.len() != 2
            || !matches!(&inner_fields.raw[0], Operand::Copy(place) if local(*place, 4))
            || !matches!(&inner_fields.raw[1], Operand::Copy(place) if local(*place, 2))
        {
            return Err("IntoIter constructor inner ownership transport differs".into());
        }
        let drop_fields = aggregate(engine, assignment(body, 8, 5)?, manually_drop, 8, evidence)?;
        if drop_fields.len() != 1
            || !matches!(&drop_fields.raw[0], Operand::Copy(place) if local(*place, 3))
        {
            return Err("IntoIter constructor ManuallyDrop transport differs".into());
        }
        let result = aggregate(engine, assignment(body, 9, 0)?, iterator, 9, evidence)?;
        if result.len() != 1 || !matches!(&result.raw[0], Operand::Move(place) if local(*place, 5))
        {
            return Err("IntoIter constructor result ownership transport differs".into());
        }
        pay(engine, 6)?;
        Ok(Self {
            identity: Rc::new(()),
            context: engine.terms.boolean(false),
            issuer: BodyEvidence {
                instance: evidence.instance,
                current: evidence.current.clone(),
            },
            iterator,
            manually_drop,
            sized_inner,
            storage_array,
            initialized_element,
            count: count as usize,
            data_offset: owner_layout
                .fields
                .offset(0)
                .bytes()
                .checked_add(drop_layout.fields.offset(0).bytes())
                .and_then(|offset| offset.checked_add(inner.fields.offset(1).bytes()))
                .ok_or("IntoIter physical data offset overflow")?,
            element_size: payload.size.bytes(),
            owner_size: owner_layout.size.bytes(),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TransferKind {
    Move,
    TerminalCopy,
}

struct ConstructorSource<'a, 'tcx> {
    caller: ty::Instance<'tcx>,
    body: &'a Rc<Body<'tcx>>,
    block: BasicBlock,
    moved: Place<'tcx>,
    constructor: ty::Instance<'tcx>,
    kind: TransferKind,
}

impl<'a, 'tcx> ConstructorSource<'a, 'tcx> {
    fn capture(
        engine: &mut Engine<'tcx>,
        caller: ty::Instance<'tcx>,
        body: &'a Rc<Body<'tcx>>,
        block: BasicBlock,
        constructor: ty::Instance<'tcx>,
        physical: &PhysicalTypes<'tcx>,
    ) -> Result<Self, String> {
        pay(engine, 5)?;
        source_identity(body, caller)?;
        let original = BodyEvidence::load(engine, caller)?;
        if !Rc::ptr_eq(body, &original.current) {
            return Err("IntoIter constructor caller is not its current Body".into());
        }
        let data = body
            .basic_blocks
            .get(block)
            .ok_or("IntoIter actual caller block is missing")?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &data.terminator().kind
        else {
            return Err("IntoIter constructor source is not an actual Call occurrence".into());
        };
        let callable = func.ty(&body.local_decls, engine.tcx);
        let ty::FnDef(id, generic) = callable.kind() else {
            return Err("IntoIter constructor source lacks compiler FnDef".into());
        };
        if engine.resolve_function_item(*id, generic.skip_binder())? != constructor
            || args.len() != 1
            || target.is_none()
            || destination.ty(&body.local_decls, engine.tcx).ty != physical.iterator
        {
            return Err("IntoIter actual Call Instance, result or arity differs".into());
        }
        let (moved, kind) = match args[0].node {
            Operand::Move(place) => (place, TransferKind::Move),
            Operand::Copy(place) => {
                terminal_copy_forwarder(engine, caller, body, block, place, *destination)?;
                (place, TransferKind::TerminalCopy)
            }
            Operand::Constant(_) | Operand::RuntimeChecks(_) => {
                return Err("IntoIter constructor source is not a captured owner place".into());
            }
        };
        let source = moved.ty(&body.local_decls, engine.tcx).ty;
        pay(engine, 3)?;
        let signature = engine.call_signature(constructor)?;
        if signature.inputs() != [source] || signature.output() != physical.iterator {
            return Err("IntoIter constructor original by-value signature differs".into());
        }
        if !matches!(source.kind(), ty::Array(element, count)
            if *element == physical.initialized_element
                && count.try_to_target_usize(engine.tcx) == Some(physical.count as u64))
        {
            return Err("IntoIter actual moved source original element/count differs".into());
        }
        Ok(Self {
            caller,
            body,
            block,
            moved,
            constructor,
            kind,
        })
    }

    fn recheck(
        &self,
        engine: &mut Engine<'tcx>,
        physical: &PhysicalTypes<'tcx>,
    ) -> Result<(), String> {
        let actual = Self::capture(
            engine,
            self.caller,
            self.body,
            self.block,
            self.constructor,
            physical,
        )?;
        if actual.moved != self.moved || actual.kind != self.kind {
            return Err("IntoIter prepared Move occurrence differs".into());
        }
        Ok(())
    }
}

fn terminal_copy_forwarder<'tcx>(
    engine: &mut Engine<'tcx>,
    caller: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    source: Place<'tcx>,
    destination: Place<'tcx>,
) -> Result<(), String> {
    pay(engine, 12)?;
    if body.phase != MirPhase::Runtime(RuntimePhase::Optimized)
        || block.as_usize() != 0
        || body.arg_count != 1
        || body.local_decls.len() != 2
        || body.basic_blocks.len() != 2
        || !local(source, 1)
        || !local(destination, 0)
        || !body.basic_blocks[block].statements.is_empty()
        || body.basic_blocks.iter().any(|data| data.is_cleanup)
    {
        return Err("IntoIter Copy source lacks exact terminal forwarder schema".into());
    }
    let TerminatorKind::Call {
        target: Some(target),
        unwind,
        ..
    } = &body.basic_blocks[block].terminator().kind
    else {
        return Err("IntoIter Copy source lacks normal Call edge".into());
    };
    if target.as_usize() != 1
        || *unwind != rustc_middle::mir::UnwindAction::Unreachable
        || !body.basic_blocks[*target].statements.is_empty()
        || !matches!(
            body.basic_blocks[*target].terminator().kind,
            TerminatorKind::Return
        )
    {
        return Err("IntoIter Copy source has post-transfer use or unwind edge".into());
    }
    let original = source.ty(&body.local_decls, engine.tcx).ty;
    pay(engine, 4)?;
    let signature = engine.call_signature(caller)?;
    if signature.inputs() != [original]
        || signature.output() != body.local_decls[destination.local].ty
        || engine
            .tcx
            .type_is_copy_modulo_regions(ty::TypingEnv::fully_monomorphized(), original)
        || !matches!(original.kind(), ty::Array(_, _))
    {
        return Err("IntoIter Copy source is not exact non-Copy by-value input".into());
    }
    // The independent full raw/current Body comparison in capture proves these same two blocks,
    // operands and source identity under the original requested Instance and substitutions.
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TransportType {
    Storage,
    Inner,
    ManuallyDrop,
    Iterator,
}

#[derive(Clone, Debug)]
enum PrivateView {
    Step(steps::View),
    Drop(drops::View),
}

#[derive(Clone, Debug)]
pub struct Identity {
    certificate: usize,
    seal: Rc<()>,
    entry: Rc<()>,
    original: TransportType,
    view: Option<PrivateView>,
}

pub(super) struct Invocation {
    certificate: usize,
    entry: Rc<()>,
}

impl<'tcx> Engine<'tcx> {
    fn array_iterator_certificate(
        &self,
        identity: &Identity,
    ) -> Result<&PhysicalTypes<'tcx>, String> {
        let certificate = self
            .array_iterator_types
            .get(identity.certificate)
            .ok_or("IntoIter compiler certificate is unavailable")?;
        let cache = self.bodies.borrow();
        let cached = cache
            .get(&certificate.issuer.instance)
            .ok_or("IntoIter retained compiler Body is no longer cached")?;
        if !Rc::ptr_eq(&certificate.identity, &identity.seal)
            || !Rc::ptr_eq(&certificate.identity, &identity.entry)
            || !certificate.context.belongs_to(&self.terms)
            || !Rc::ptr_eq(&certificate.issuer.current, cached)
        {
            return Err("IntoIter compiler certificate namespace or current Body differs".into());
        }
        Ok(certificate)
    }

    pub(super) fn validate_array_iterator_value(
        &self,
        original: Ty<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        self.validate_constructor_transport(original, value, None)
    }

    fn validate_constructor_transport(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        invocation: Option<&Invocation>,
    ) -> Result<(), String> {
        let Value::OwnedArrayIterator { identity, payload } = value else {
            return Ok(());
        };
        let certificate = self.array_iterator_certificate(identity)?;
        if identity.view.is_some() {
            return Err("IntoIter private step view requires its actual invocation".into());
        }
        if identity.original != TransportType::Iterator {
            let invocation =
                invocation.ok_or("IntoIter partial transport requires actual invocation")?;
            if identity.certificate != invocation.certificate
                || !Rc::ptr_eq(&identity.entry, &invocation.entry)
            {
                return Err("IntoIter partial transport belongs to another invocation".into());
            }
        }
        let expected = match identity.original {
            TransportType::Storage => certificate.storage_array,
            TransportType::Inner => certificate.sized_inner,
            TransportType::ManuallyDrop => certificate.manually_drop,
            TransportType::Iterator => certificate.iterator,
        };
        let owns_payload = matches!(
            identity.original,
            TransportType::Storage | TransportType::Iterator
        );
        if original != expected
            || payload.is_some() != owns_payload
            || payload
                .as_ref()
                .is_some_and(|data| data.len() != certificate.count)
        {
            return Err("IntoIter transport original type or payload cardinality differs".into());
        }
        if let Some(data) = payload {
            data.validate(certificate.count, false)?;
            if identity.original == TransportType::Storage
                && (data.front != 0 || data.back != certificate.count)
            {
                return Err(
                    "IntoIter constructor storage must retain every initialized slot".into(),
                );
            }
        }
        Ok(())
    }

    pub(super) fn array_iterator_constructor_call(
        &mut self,
        caller: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        constructor: ty::Instance<'tcx>,
        state: &mut State,
        stack: &[DefId],
    ) -> Result<Option<Vec<Return>>, String> {
        if !matches!(constructor.def, ty::InstanceKind::Item(id)
            if self.tcx.def_kind(id) == DefKind::AssocFn)
        {
            return Ok(None);
        }
        let signature = self.call_signature(constructor)?;
        let ty::Adt(def, args) = signature.output().kind() else {
            return Ok(None);
        };
        if self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("ArrayIntoIter"))
            != Some(def.did())
            || !args
                .type_at(0)
                .needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
            || self.tcx.item_name(constructor.def_id()).as_str() != "into_iter"
        {
            return Ok(None);
        }
        if !args
            .type_at(0)
            .is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Ok(None); // Existing conservative Drop-element route retains its refusal.
        }
        state.flow.require_unarmed()?;
        if self
            .specification(constructor)?
            .is_some_and(|specification| specification.trusted)
        {
            return Ok(None);
        }
        if self.foreign_rust_target(constructor)?.is_some() {
            return Err("IntoIter constructor foreign adapter is unsupported".into());
        }
        let evidence = BodyEvidence::load(self, constructor)?;
        let physical = PhysicalTypes::constructor(self, &evidence)?;
        let source = ConstructorSource::capture(self, caller, body, block, constructor, &physical)?;
        let operand = match source.kind {
            TransferKind::Move => Operand::Move(source.moved),
            TransferKind::TerminalCopy => Operand::Copy(source.moved),
        };
        let Value::Elements(payload) = self.operand(caller.def_id(), body, state, &operand)? else {
            return Err("IntoIter constructor requires retained owned elements".into());
        };
        if payload.len() != physical.count {
            return Err("IntoIter source cardinality differs from original array".into());
        }
        for value in &payload {
            if !payload_domain(self, value, 0)? {
                return Ok(None); // Ordinary Drop-element refusal; source is not consumed yet.
            }
        }
        let conditions = self.call_preconditions(
            constructor,
            &[Value::Elements(payload.clone())],
            state.conditions.clone(),
            &state.memory,
            (
                caller.def_id(),
                body.basic_blocks[block].terminator().source_info.span,
            ),
        )?;
        let fields = self.owned_field_footprint(body, source.moved)?;
        let address = state.addresses[source.moved.local.as_usize()];
        if let Some(allocation) = address {
            let (_, original) = self
                .typed_memory_evidence(&state.memory, allocation, &[])?
                .ok_or("IntoIter source allocation lacks original type evidence")?;
            if original != body.local_decls[source.moved.local].ty {
                return Err("IntoIter source allocation original type differs".into());
            }
        }
        let ledger = if address.is_some() {
            &state.memory.missing_places
        } else {
            &state.missing_places
        };
        let work = ledger
            .entries()
            .iter()
            .try_fold(1_usize, |sum, (_, path)| sum.checked_add(1 + path.len()))
            .ok_or("IntoIter source ledger work overflow")?;
        pay(self, work + fields.len() + 3)?;
        let mut consumed = clone_work::masks(self, ledger)?;
        consumed.consume(address.unwrap_or(source.moved.local.as_usize()), fields)?;
        if self.array_iterator_types.len() >= MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter compiler certificates exceed 512 entries".into(),
            ));
        }
        source.recheck(self, &physical)?;
        let certificate = self.array_iterator_types.len();
        let entry = physical.identity.clone();
        self.array_iterator_types.push(physical);
        state.constant_receipts.invalidate(source.moved);
        if address.is_some() {
            state.memory.missing_places = consumed;
        } else {
            state.missing_places = consumed;
        }
        let invocation = Invocation { certificate, entry };
        let frame = array_drop_glue::Frame::constructor(constructor, invocation);
        let chain = stack
            .iter()
            .copied()
            .chain([constructor.def_id()])
            .collect();
        let previous = std::mem::replace(&mut self.call_chain, chain);
        let result = self.execute_body_with_protocol(
            frame,
            vec![Value::Elements(payload)],
            conditions,
            state.memory.clone(),
            stack,
            activation_flow::Flow::Unarmed,
        );
        if result.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        result.map(Some)
    }

    pub(super) fn array_iterator_constructor_statement(
        &mut self,
        invocation: Option<&Invocation>,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &mut State,
        location: rustc_middle::mir::Location,
    ) -> Result<bool, String> {
        let Some(invocation) = invocation else {
            return Ok(false);
        };
        pay(self, 4)?;
        let certificate = self
            .array_iterator_types
            .get(invocation.certificate)
            .ok_or("IntoIter frame certificate is unavailable")?;
        if instance != certificate.issuer.instance
            || !Rc::ptr_eq(body, &certificate.issuer.current)
            || location.block.as_usize() != 0
            || location.statement_index >= 13
        {
            return Err("IntoIter constructor frame or actual statement differs".into());
        }
        let ordinal = location.statement_index;
        #[cfg(test)]
        EVENTS.with(|events| events.borrow_mut().push(ordinal));
        if matches!(ordinal, 0 | 2 | 3 | 4 | 6 | 7 | 10 | 11 | 12) {
            return Ok(false);
        }
        let (destination, original) = match ordinal {
            1 => (2, TransportType::Storage),
            5 => (3, TransportType::Inner),
            8 => (5, TransportType::ManuallyDrop),
            9 => (0, TransportType::Iterator),
            _ => return Err("IntoIter private constructor transport ordinal differs".into()),
        };
        let identity = Identity {
            certificate: invocation.certificate,
            seal: certificate.identity.clone(),
            entry: invocation.entry.clone(),
            original,
            view: None,
        };
        if ordinal != 1 {
            let (source, expected) = match ordinal {
                5 => (2, TransportType::Storage),
                8 => (3, TransportType::Inner),
                9 => (5, TransportType::ManuallyDrop),
                _ => return Err("IntoIter internal source ordinal differs".into()),
            };
            self.check_local_initialization(state, source, &[])?;
            let Value::OwnedArrayIterator {
                identity: current, ..
            } = self.local(state, source)?
            else {
                return Err("IntoIter internal transport source is unavailable".into());
            };
            if current.view.is_some()
                || current.original != expected
                || current.certificate != invocation.certificate
                || !Rc::ptr_eq(&current.entry, &invocation.entry)
            {
                return Err("IntoIter internal transport source identity differs".into());
            }
        }
        let payload = if ordinal == 1 {
            let Value::Elements(data) = self.local(state, 1)? else {
                return Err("IntoIter constructor incoming original array was replaced".into());
            };
            if data.len() != certificate.count {
                return Err("IntoIter constructor input length differs".into());
            }
            let mut masks = clone_work::masks(self, &state.missing_places)?;
            masks.consume(1, Vec::new())?;
            state.missing_places = masks;
            state.locals[1] = None;
            if data.is_shared() {
                let mut owned = 1_usize;
                let mut nodes = 0_usize;
                for value in &data {
                    owned = owned
                        .checked_add(steps::value_clone_work(self, value, 0, &mut nodes)?)
                        .ok_or("IntoIter source payload clone work overflow")?;
                }
                pay(self, owned)?;
            }
            pay(self, data.len() + 2)?;
            Some(Payload::new(data))
        } else if ordinal == 9 {
            self.check_local_initialization(state, 2, &[])?;
            let Some(Value::OwnedArrayIterator {
                identity: current,
                payload: Some(_),
            }) = &state.locals[2]
            else {
                return Err("IntoIter constructor sole payload was lost".into());
            };
            if current.view.is_some()
                || current.original != TransportType::Storage
                || !Rc::ptr_eq(&current.entry, &invocation.entry)
                || current.certificate != invocation.certificate
            {
                return Err("IntoIter constructor payload belongs to another frame".into());
            }
            let mut masks = clone_work::masks(self, &state.missing_places)?;
            masks.consume(2, Vec::new())?;
            masks.consume(5, Vec::new())?;
            let Some(Value::OwnedArrayIterator { payload, .. }) = state.locals[2].take() else {
                unreachable!()
            };
            state.missing_places = masks;
            state.locals[5] = None;
            payload
        } else {
            None
        };
        let value = Value::OwnedArrayIterator { identity, payload };
        self.validate_constructor_transport(
            body.local_decls[Local::from_usize(destination)].ty,
            &value,
            Some(invocation),
        )?;
        self.store_assignment_value_inner(
            body,
            state,
            Place::from(Local::from_usize(destination)),
            value,
            &body.basic_blocks[location.block].statements[ordinal].kind,
        )?;
        Ok(true)
    }
}

fn payload_domain(engine: &mut Engine<'_>, value: &Value, depth: usize) -> Result<bool, String> {
    pay(engine, 1)?;
    if depth > MAX_INPUT_DEPTH {
        return Err("IntoIter payload nesting exceeds 16".into());
    }
    match value {
        Value::Adt { fields, .. } => {
            for (_, value) in fields {
                if !payload_domain(engine, value, depth + 1)? {
                    return Ok(false);
                }
            }
        }
        Value::Tuple(fields) => {
            for value in fields {
                if !payload_domain(engine, value, depth + 1)? {
                    return Ok(false);
                }
            }
        }
        Value::Elements(fields) => {
            for value in fields {
                if !payload_domain(engine, value, depth + 1)? {
                    return Ok(false);
                }
            }
        }
        Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Unit => {}
        Value::Enum { .. }
        | Value::Uninitialized
        | Value::Bytes { .. }
        | Value::RawPointer { .. }
        | Value::Reference { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::StaticView { .. }
        | Value::FunctionPointer { .. }
        | Value::Function
        | Value::StaticText
        | Value::FormatArguments
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedArrayIterator { .. }
        | Value::StaticSlice { .. }
        | Value::SliceIterator { .. }
        | Value::MaybeUninit { .. }
        | Value::RawSlice { .. }
        | Value::TrackedPointer { .. }
        | Value::OwnedSnapshot(_)
        | Value::MetadataPointer(_)
        | Value::DebugReference { .. }
        | Value::TraitObject { .. } => {
            return Ok(false);
        }
    }
    Ok(true)
}

impl Engine<'_> {
    pub(super) fn array_iterator_return(&self, value: &Value) -> Result<(), String> {
        let Value::OwnedArrayIterator { identity, payload } = value else {
            return Err("expected an authenticated IntoIter owner".into());
        };
        let certificate = self.array_iterator_certificate(identity)?;
        if identity.view.is_some()
            || identity.original != TransportType::Iterator
            || payload
                .as_ref()
                .is_none_or(|data| data.len() != certificate.count)
        {
            return Err("IntoIter constructor metadata cannot return or escape".into());
        }
        payload
            .as_ref()
            .unwrap()
            .validate(certificate.count, false)?;
        if certificate
            .data_offset
            .checked_add(
                certificate
                    .element_size
                    .saturating_mul(certificate.count as u64),
            )
            .is_none_or(|end| end > certificate.owner_size)
        {
            return Err("IntoIter physical payload exceeds original owner layout".into());
        }
        Ok(())
    }
}

impl Engine<'_> {
    pub(super) fn contains_array_iterator(&self, value: &Value) -> Result<bool, String> {
        let mut queue = vec![(value, 0_usize)];
        let mut nodes = 0_usize;
        while let Some((value, depth)) = queue.pop() {
            nodes += 1;
            if depth >= MAX_INPUT_DEPTH || nodes + queue.len() > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "IntoIter ownership graph exceeds existing node/depth budget".into(),
                ));
            }
            match value {
                Value::OwnedArrayIterator { .. } => return Ok(true),
                Value::Adt { fields, .. } => {
                    queue.extend(fields.iter().map(|(_, value)| (value, depth + 1)))
                }
                Value::Tuple(fields) => queue.extend(fields.iter().map(|value| (value, depth + 1))),
                Value::Elements(fields) => {
                    queue.extend(fields.iter().map(|value| (value, depth + 1)))
                }
                Value::Enum {
                    discriminant,
                    variants,
                    ..
                } => {
                    queue.push((discriminant, depth + 1));
                    queue.extend(variants.iter().map(|value| (value, depth + 1)));
                }
                Value::Input(_)
                | Value::Bool(_)
                | Value::Int { .. }
                | Value::Float { .. }
                | Value::Unit
                | Value::Uninitialized
                | Value::Bytes { .. }
                | Value::RawPointer { .. }
                | Value::Reference { .. }
                | Value::Cell { .. }
                | Value::Atomic { .. }
                | Value::LocalAtomic { .. }
                | Value::CompositeSlice { .. }
                | Value::ScalarSlice { .. }
                | Value::StaticView { .. }
                | Value::FunctionPointer { .. }
                | Value::Function
                | Value::StaticText
                | Value::FormatArguments
                | Value::MutableU16 { .. }
                | Value::OwnedRegion { .. }
                | Value::StaticSlice { .. }
                | Value::SliceIterator { .. }
                | Value::MaybeUninit { .. }
                | Value::RawSlice { .. }
                | Value::TrackedPointer { .. }
                | Value::OwnedSnapshot(_)
                | Value::MetadataPointer(_)
                | Value::DebugReference { .. }
                | Value::TraitObject { .. } => {}
            }
        }
        Ok(false)
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn contains_array_iterator_type(&self, original: Ty<'tcx>) -> Result<bool, String> {
        let mut queue = vec![(original, 0_usize)];
        let mut nodes = 0_usize;
        let iterator = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("ArrayIntoIter"));
        while let Some((original, depth)) = queue.pop() {
            nodes += 1;
            if depth >= MAX_INPUT_DEPTH || nodes + queue.len() > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "IntoIter ownership type graph exceeds existing node/depth budget".into(),
                ));
            }
            match original.kind() {
                ty::Adt(def, args) => {
                    if Some(def.did()) == iterator {
                        return Ok(true);
                    }
                    for field in def.all_fields() {
                        let original = self
                            .tcx
                            .try_normalize_erasing_regions(
                                ty::TypingEnv::fully_monomorphized(),
                                field.ty(self.tcx, args),
                            )
                            .map_err(|error| {
                                format!("IntoIter ownership field normalization failed: {error:?}")
                            })?;
                        queue.push((original, depth + 1));
                    }
                }
                ty::Tuple(fields) => {
                    queue.extend(fields.iter().map(|original| (original, depth + 1)))
                }
                ty::Array(element, _) => queue.push((*element, depth + 1)),
                ty::Closure(_, args) => queue.extend(
                    args.as_closure()
                        .upvar_tys()
                        .iter()
                        .map(|original| (original, depth + 1)),
                ),
                ty::CoroutineClosure(..) => {
                    return Err(
                        "IntoIter ownership through coroutine closure is unsupported".into(),
                    );
                }
                ty::Coroutine(_, args) => queue.extend(
                    args.as_coroutine()
                        .upvar_tys()
                        .iter()
                        .map(|original| (original, depth + 1)),
                ),
                _ => {}
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
std::thread_local! {
    static EVENTS: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub(in crate::proof) fn clone_value_work(
    engine: &mut Engine<'_>,
    value: &Value,
    depth: usize,
    nodes: &mut usize,
) -> Result<usize, String> {
    steps::value_clone_work(engine, value, depth, nodes)
}
pub(in crate::proof) fn clone_masks(
    engine: &mut Engine<'_>,
    masks: &initialized_places::MissingPlaces,
) -> Result<initialized_places::MissingPlaces, String> {
    clone_work::masks(engine, masks)
}

// Pure bounded field planners; these wrappers grant no iterator or source authority.
pub(in crate::proof) fn statement_fields_work(
    engine: &mut Engine<'_>,
    statement: &rustc_middle::mir::Statement<'_>,
) -> Result<usize, String> {
    clone_work::step_statement(engine, statement)
}

pub(in crate::proof) fn terminator_fields_work(
    engine: &mut Engine<'_>,
    terminator: &rustc_middle::mir::Terminator<'_>,
) -> Result<usize, String> {
    clone_work::step_terminator(engine, terminator)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn options() -> VerificationOptions {
        VerificationOptions {
            all_failures: false,
            induction: false,
            startup: false,
            isolated_startup: false,
            async_entry: false,
            limits: miren::AnalysisLimits::default(),
        }
    }

    fn controls(tcx: TyCtxt<'_>) {
        let caller = tcx
            .mir_keys(())
            .iter()
            .copied()
            .find(|id| {
                tcx.def_kind(id.to_def_id()) == DefKind::Fn
                    && tcx.item_name(id.to_def_id()).as_str() == "constructor_move"
            })
            .unwrap();
        let caller = ty::Instance::mono(tcx, caller.to_def_id());
        let config = miren::ContractConfig::default();
        let mut engine = Engine::new(tcx, &config, options());
        let body = engine.instantiated_body(caller).unwrap();
        if let Ok(path) = std::env::var("MIREN_INTOITER_RUNTIME_TRACE") {
            let path = std::path::PathBuf::from(path);
            std::fs::create_dir_all(&path).unwrap();
            let label = format!(
                "{:?}-{}-{:?}",
                tcx.sess.opts.optimize,
                tcx.sess.target.pointer_width,
                tcx.sess.opts.unstable_opts.mir_opt_level
            );
            std::fs::write(
                path.join(format!("{label}-caller.mir")),
                format!(
                    "raw compiler caller:\n{:#?}\ncurrent instantiated caller:\n{:#?}",
                    tcx.instance_mir(caller.def),
                    body
                ),
            )
            .unwrap();
            let original = body.return_ty();
            let ty::Adt(_, args) = original.kind() else {
                panic!("original IntoIter result")
            };
            let array = Ty::new_array(tcx, args.type_at(0), 2);
            let trait_id = tcx
                .get_diagnostic_item(rustc_span::Symbol::intern("IntoIterator"))
                .unwrap();
            let method = tcx
                .associated_items(trait_id)
                .in_definition_order()
                .find(|method| method.name().as_str() == "into_iter")
                .unwrap();
            let constructor = engine
                .resolve_function_item(method.def_id, tcx.mk_args(&[array.into()]))
                .unwrap();
            let current = engine.instantiated_body(constructor).unwrap();
            std::fs::write(
                path.join(format!("{label}-constructor.mir")),
                format!(
                    concat!(
                        "Instance={constructor:?}\nraw compiler constructor:\n{:#?}",
                        "\ncurrent instantiated constructor:\n{current:#?}"
                    ),
                    tcx.instance_mir(constructor.def),
                    constructor = constructor,
                    current = current
                ),
            )
            .unwrap();
        }
        let ty::Adt(stamp, _) = body.local_decls[Local::from_usize(1)].ty.kind() else {
            panic!("actual original Stamp type")
        };
        let argument = |engine: &Engine<'_>, number| Value::Adt {
            name: tcx.def_path_str(stamp.did()),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![(
                "0".into(),
                symbolic::integer(&engine.terms, number, 16, false),
            )]
            .into(),
        };
        EVENTS.with(|events| events.borrow_mut().clear());
        let input = vec![argument(&engine, 11), argument(&engine, 22)];
        let executed = engine.execute(caller, input, Vec::new(), Memory::default(), &[]);
        if !body
            .basic_blocks
            .iter()
            .any(|block| matches!(block.terminator().kind, TerminatorKind::Call { .. }))
        {
            assert!(executed.err().unwrap().contains("unsupported transmute"));
            assert!(engine.array_iterator_types.is_empty());
            EVENTS.with(|events| assert!(events.borrow().is_empty()));
            println!("actual inlined constructor remains UNKNOWN at caller transmute");
            return;
        }
        let results = executed.unwrap();
        assert_eq!(results.len(), 1);
        EVENTS.with(|events| assert_eq!(*events.borrow(), (0..13).collect::<Vec<_>>()));
        let result = &results[0];
        engine.array_iterator_return(&result.value).unwrap();
        let Value::OwnedArrayIterator {
            identity,
            payload: Some(data),
        } = &result.value
        else {
            panic!("actual owning constructor return")
        };
        assert_eq!(data.len(), 2);
        for (value, expected) in data.iter().zip([11, 22]) {
            let Value::Adt { fields, .. } = value else {
                panic!("original Stamp payload")
            };
            assert_eq!(
                fields[0].1.integer().unwrap().0.constant(),
                Some(miren::smt::Constant::BitVec(expected))
            );
        }
        let mut branch = result.memory.clone();
        branch.push(Some(result.value.clone()));
        let mut independent = branch.clone();
        independent[branch.len() - 1] = None;
        assert!(branch[branch.len() - 1].is_some());
        let mut foreign = identity.clone();
        foreign.entry = Rc::new(());
        assert!(
            engine
                .array_iterator_return(&Value::OwnedArrayIterator {
                    identity: foreign,
                    payload: Some(data.clone()),
                })
                .unwrap_err()
                .contains("namespace or current Body")
        );
        let mut metadata = identity.clone();
        metadata.original = TransportType::Inner;
        assert!(
            engine
                .array_iterator_return(&Value::OwnedArrayIterator {
                    identity: metadata,
                    payload: None,
                })
                .unwrap_err()
                .contains("metadata cannot return")
        );
        assert!(
            engine
                .validate_array_iterator_value(tcx.types.u16, &result.value)
                .is_err()
        );
        let certificate = &engine.array_iterator_types[identity.certificate];
        let iterator_ty = certificate.iterator;
        let mut diagnostic_options = options();
        diagnostic_options.limits.max_steps = 30_000;
        let mut diagnostic_evidence = Engine::new(tcx, &config, diagnostic_options);
        drops::core_evidence_controls(&mut diagnostic_evidence, iterator_ty);
        let mut protocol_options = options();
        protocol_options.limits.max_steps = 60_000;
        let mut protocol_engine = Engine::new(tcx, &config, protocol_options);
        let protocol_body = protocol_engine.instantiated_body(caller).unwrap();
        let protocol_arguments = vec![
            argument(&protocol_engine, 11),
            argument(&protocol_engine, 22),
        ];
        let protocol_results = protocol_engine
            .execute(
                caller,
                protocol_arguments,
                Vec::new(),
                Memory::default(),
                &[],
            )
            .unwrap();
        if std::env::var_os("MIREN_INTOITER_DROP_WORK_TRACE").is_some() {
            println!(
                "Drop work target={} opt={:?} constructor_move={}",
                tcx.sess.target.llvm_target, tcx.sess.opts.optimize, protocol_engine.steps
            );
            for name in ["constructor", "remaining_drop_unknown", "next_unknown"] {
                let selected = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == name
                    })
                    .unwrap();
                let selected = ty::Instance::mono(tcx, selected.to_def_id());
                let mut profile_options = options();
                profile_options.limits.max_steps = 60_000;
                let mut profile = Engine::new(tcx, &config, profile_options);
                let input =
                    Value::Elements(vec![argument(&profile, 11), argument(&profile, 22)].into());
                let result =
                    profile.execute(selected, vec![input], Vec::new(), Memory::default(), &[]);
                println!(
                    "Drop work root={name} target={} opt={:?} cumulative={} normal={}",
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                    profile.steps,
                    result.is_ok()
                );
                assert!(result.is_ok(), "{name}: {:?}", result.err());
            }
        }
        drops::protocol_controls(
            &mut protocol_engine,
            &protocol_body,
            &protocol_results[0].value,
            &protocol_results[0].memory,
        );
        let glue = ty::Instance::resolve_drop_glue(tcx, iterator_ty);
        let before_evidence = engine.array_iterator_step_evidence.len();
        let glue_evidence = compiler_evidence::load_drop(&mut engine, glue).unwrap();
        assert_eq!(
            engine.array_iterator_step_evidence.len(),
            before_evidence + 1
        );
        let cached_evidence = compiler_evidence::load_drop(&mut engine, glue).unwrap();
        assert!(Rc::ptr_eq(&glue_evidence.current, &cached_evidence.current));
        assert_eq!(
            engine.array_iterator_step_evidence.len(),
            before_evidence + 1
        );
        let replaced = Rc::new(glue_evidence.current.as_ref().clone());
        engine.bodies.borrow_mut().insert(glue, replaced);
        assert!(
            compiler_evidence::load_drop(&mut engine, glue)
                .err()
                .unwrap()
                .contains("cache was replaced")
        );
        engine
            .bodies
            .borrow_mut()
            .insert(glue, glue_evidence.current.clone());
        let cached = engine.array_iterator_step_evidence.pop().unwrap();
        assert_eq!(cached.instance, glue);
        let mut changed = glue_evidence.current.as_ref().clone();
        changed.basic_blocks.as_mut()[BasicBlock::from_usize(0)].statements[0].kind =
            StatementKind::Nop;
        engine.bodies.borrow_mut().insert(glue, Rc::new(changed));
        assert!(
            compiler_evidence::load_drop(&mut engine, glue)
                .err()
                .unwrap()
                .contains("original/current statement differs")
        );
        assert_eq!(engine.array_iterator_step_evidence.len(), before_evidence);
        engine
            .bodies
            .borrow_mut()
            .insert(glue, glue_evidence.current);
        engine.array_iterator_step_evidence.push(cached);
        // Compiler DropGlue evidence grants no execution or permission to escape an active owner.
        let certificate = &engine.array_iterator_types[identity.certificate];
        // Active destruction is not ordinary iterator transport, even when its phase-specific
        // initialized-slot invariant is valid. These are hostile host states, not guest proofs.
        for (next, leased) in [(0, None), (0, Some(0)), (1, None), (2, None)] {
            let mut active = data.clone();
            for (index, slot) in Rc::make_mut(&mut active.slots).iter_mut().enumerate() {
                if index < next || leased == Some(index) {
                    *slot = None;
                }
            }
            active.dropping = Some(drops::Progress {
                next,
                leased: leased.map(|index| drops::Lease {
                    index,
                    allocation: 42,
                }),
                entry: Rc::new(()),
            });
            let value = Value::OwnedArrayIterator {
                identity: identity.clone(),
                payload: Some(active),
            };
            assert!(
                engine
                    .array_iterator_return(&value)
                    .unwrap_err()
                    .contains("active destruction cannot leave")
            );
            assert!(
                engine
                    .validate_array_iterator_value(certificate.iterator, &value)
                    .unwrap_err()
                    .contains("active destruction cannot leave")
            );
            assert!(engine.snapshot(&value, &result.memory, &[], 0).is_err());
        }
        let mut missing_payload = identity.clone();
        missing_payload.original = TransportType::Iterator;
        assert!(
            engine
                .validate_array_iterator_value(
                    certificate.iterator,
                    &Value::OwnedArrayIterator {
                        identity: missing_payload,
                        payload: None
                    }
                )
                .is_err()
        );
        let mut partial = identity.clone();
        partial.original = TransportType::Storage;
        let partial = Value::OwnedArrayIterator {
            identity: partial,
            payload: Some(data.clone()),
        };
        assert!(
            engine
                .validate_array_iterator_value(certificate.storage_array, &partial)
                .unwrap_err()
                .contains("requires actual invocation")
        );
        assert!(engine.snapshot(&partial, &result.memory, &[], 0).is_err());

        let other = Engine::new(tcx, &config, options());
        assert!(other.array_iterator_return(&result.value).is_err());
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; body.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: initialized_places::MissingPlaces::default(),
            conditions: Vec::new(),
            addresses: vec![None; body.local_decls.len()],
            memory: result.memory.clone(),
        };
        state.locals[0] = Some(result.value.clone());
        assert_eq!(
            engine
                .operand(
                    caller.def_id(),
                    &body,
                    &state,
                    &Operand::Copy(Place::from(Local::from_usize(0)))
                )
                .unwrap_err(),
            "IntoIter executable Copy is unsupported"
        );
        let _ = engine
            .evaluate_operand(
                caller.def_id(),
                &body,
                &mut state,
                &Operand::Move(Place::from(Local::from_usize(0))),
            )
            .unwrap();
        assert!(engine.local(&state, 0).is_err());
        let mut configured = config.clone();
        configured.functions.push(
            serde_json::from_value(serde_json::json!({
                "function": external::canonical_name(tcx, caller.def_id()), "ensures": ["true"]
            }))
            .unwrap(),
        );
        let mut contract_engine = Engine::new(tcx, &configured, options());
        let contract_arguments = vec![
            argument(&contract_engine, 11),
            argument(&contract_engine, 22),
        ];
        assert!(
            contract_engine
                .execute(
                    caller,
                    contract_arguments,
                    Vec::new(),
                    Memory::default(),
                    &[]
                )
                .err()
                .unwrap()
                .contains("private frame-bound metadata snapshot")
        );
        let constructor = engine.array_iterator_types[identity.certificate]
            .issuer
            .instance;
        let mut precondition = config.clone();
        precondition.functions.push(serde_json::from_value(serde_json::json!({
            "function": external::canonical_name(tcx, constructor.def_id()), "requires": ["false"]
        })).unwrap());
        let mut precondition_engine = Engine::new(tcx, &precondition, options());
        let input = vec![
            argument(&precondition_engine, 11),
            argument(&precondition_engine, 22),
        ];
        assert!(
            precondition_engine
                .execute(caller, input, Vec::new(), Memory::default(), &[])
                .is_err()
        );
        assert!(
            precondition_engine
                .proof
                .obligations
                .iter()
                .any(|obligation| obligation.status == ProofStatus::Refuted
                    && obligation.kind == ObligationKind::CallPrecondition)
        );
        assert!(
            precondition_engine
                .proof
                .body_entries
                .iter()
                .all(|entry| entry.function != tcx.def_path_str(constructor.def_id()))
        );
        assert!(precondition_engine.array_iterator_types.is_empty());
        // Clone payment is separate from inspection/comparison and must refuse before allocation.
        let raw = tcx.instance_mir(constructor.def);
        let mut inventory = Engine::new(tcx, &config, options());
        let start = inventory.steps;
        let owned = clone_work::body(&mut inventory, raw).unwrap();
        let planning = inventory.steps - start;
        assert!(owned > raw.local_decls.len() + raw.basic_blocks.len());
        let mut budget = options();
        budget.limits.max_steps =
            2 + planning + 1 + raw.local_decls.len() + raw.basic_blocks.len() + owned - 1;
        let mut exhausted = Engine::new(tcx, &config, budget);
        let retained = engine.instantiated_body(constructor).unwrap();
        exhausted
            .bodies
            .borrow_mut()
            .insert(constructor, retained.clone());
        assert!(
            BodyEvidence::load(&mut exhausted, constructor)
                .err()
                .unwrap()
                .contains("shared execution step limit reached")
        );
        assert!(Rc::ptr_eq(
            exhausted.bodies.borrow().get(&constructor).unwrap(),
            &retained
        ));
        assert!(exhausted.array_iterator_types.is_empty());
        let mut ledger = initialized_places::MissingPlaces::default();
        ledger
            .consume(
                42,
                vec![initialized_places::Step::Field(0); MAX_INPUT_DEPTH],
            )
            .unwrap();
        let mut mask_budget = options();
        mask_budget.limits.max_steps = 2 + 1 + 3 + MAX_INPUT_DEPTH - 1;
        let mut mask_engine = Engine::new(tcx, &config, mask_budget);
        assert!(
            clone_work::masks(&mut mask_engine, &ledger)
                .err()
                .unwrap()
                .contains("shared execution step limit reached")
        );
        assert_eq!(
            ledger.entries(),
            &[(
                42,
                vec![initialized_places::Step::Field(0); MAX_INPUT_DEPTH]
            )]
        );
        // Change the genuine current constructor Body; raw compiler evidence must reject it.
        let constructor = engine.array_iterator_types[identity.certificate]
            .issuer
            .instance;
        let mut mutant = engine
            .instantiated_body(constructor)
            .unwrap()
            .as_ref()
            .clone();
        mutant.basic_blocks.as_mut()[BasicBlock::from_usize(0)].statements[5].kind =
            StatementKind::Nop;
        engine
            .bodies
            .borrow_mut()
            .insert(constructor, Rc::new(mutant));
        assert!(engine.array_iterator_return(&result.value).is_err());
        assert!(
            BodyEvidence::load(&mut engine, constructor)
                .err()
                .unwrap()
                .contains("statement or source differs")
        );
        println!(concat!(
            "IntoIter real 13-statement constructor/normal Return, ",
            "payload, Move and hostile controls passed"
        ));
    }

    #[test]
    fn actual_constructor_transport_preserves_one_payload_and_normal_return() {
        struct Check(bool);
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                controls(tcx);
                self.0 = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-intoiter-constructors-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("guest.rs");
        std::fs::write(
            &source,
            include_str!("../../../../tests/fixtures/array_iterator_constructors.rs"),
        )
        .unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for level in [0, 2] {
                let mut args = vec![
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Cpanic=abort".into(),
                    "-Coverflow-checks=yes".into(),
                    "-Zmir-opt-level=0".into(),
                    format!("-Copt-level={level}"),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                    "--sysroot".into(),
                    env!("MIREN_SYSROOT").into(),
                ];
                if let Some(target) = target {
                    args.extend(["--target".into(), target.into()]);
                }
                let mut check = Check(false);
                rustc_driver::run_compiler(&args, &mut check);
                assert!(check.0);
                if std::env::var_os("MIREN_INTOITER_RUNTIME_TRACE").is_some() {
                    args.retain(|argument| argument != "-Zmir-opt-level=0");
                    let mut default = Check(false);
                    rustc_driver::run_compiler(&args, &mut default);
                    assert!(default.0);
                }
            }
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}

// Shared bounded clone planners; they issue no iterator or function-pointer authority.
