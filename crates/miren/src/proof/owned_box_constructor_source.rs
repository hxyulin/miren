//! Constructor-only source certificates. No Box owner, payload receiver or Drop success is issued.
use super::*;
use owned_box_templates::BoxTemplateFamily;
use std::rc::Rc;

const MAX_BLOCKS: usize = 128;
const MAX_OPERATIONS: usize = 512;
const ENCODING_BYTES: usize = MAX_OPERATIONS * 128;

pub(super) struct RawWitness<'tcx> {
    instance: ty::Instance<'tcx>,
    raw: &'tcx Body<'tcx>,
    family: BoxTemplateFamily,
}
impl<'tcx> RawWitness<'tcx> {
    pub(super) fn check_raw(&self, raw: &Body<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(self.raw, raw) || raw.source.instance != self.instance.def {
            return Err("Box constructor source witness original Body differs".into());
        }
        Ok(())
    }
    pub(super) fn check_instance(&self, instance: ty::Instance<'tcx>) -> Result<(), String> {
        if instance != self.instance {
            return Err("Box constructor source witness full Instance differs".into());
        }
        Ok(())
    }
}
struct Part<'tcx> {
    raw: RawWitness<'tcx>,
    current: Rc<Body<'tcx>>,
}
pub(super) struct Certificate<'tcx> {
    payload: Ty<'tcx>,
    constructor: ty::Instance<'tcx>,
    layout: owned_box_payloads::ZeroLayout,
    context: Term,
    parts: Vec<Part<'tcx>>,
}
fn pay(engine: &mut Engine<'_>, work: usize) -> Result<(), String> {
    let next = engine.steps.checked_add_commit(work).ok_or_else(|| {
        engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box constructor source work overflow".into(),
        )
    })?;

    if next > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box constructor source shared execution step limit reached".into(),
        ));
    }
    Ok(())
}
fn bounds(engine: &mut Engine<'_>, raw: &Body<'_>) -> Result<(), String> {
    pay(engine, raw.basic_blocks.len() + raw.local_decls.len() + 4)?;
    if raw.basic_blocks.len() > MAX_BLOCKS || raw.local_decls.len() > MAX_OPERATIONS {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box constructor source exceeds inherited template dimensions".into(),
        ));
    }
    let mut operations = 0usize;
    let mut operands = 0usize;
    for block in raw.basic_blocks.iter() {
        pay(engine, block.statements.len() + 1)?;
        operations = operations
            .checked_add(block.statements.len() + 1)
            .ok_or("Box constructor source operation count overflow")?;
        for statement in &block.statements {
            if let StatementKind::Assign(assignment) = &statement.kind
                && let Rvalue::Aggregate(_, values) = &assignment.1
            {
                operands = operands
                    .checked_add(values.len())
                    .ok_or("Box constructor source operand count overflow")?;
            }
        }
        if let TerminatorKind::Call { args, .. } = &block.terminator().kind {
            operands = operands
                .checked_add(args.len())
                .ok_or("Box constructor source operand count overflow")?;
        }
    }
    if operations > MAX_OPERATIONS || operands > MAX_OPERATIONS {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "Box constructor source exceeds inherited operation/operand bounds".into(),
        ));
    }
    Ok(())
}
fn raw_witness<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<RawWitness<'tcx>, String> {
    pay(engine, 8)?;
    if !matches!(instance.def,ty::InstanceKind::Item(id)
        if matches!(engine.tcx.def_kind(id),DefKind::Fn|DefKind::AssocFn))
        || !engine.tcx.is_mir_available(instance.def_id())
    {
        return Err(engine.categorized_error(
            UnknownCategory::MissingCompilerEvidence,
            engine.missing_body_reason(instance.def_id()),
        ));
    }
    array_iterator_constructors::authenticated_box_callable(engine, instance)?;
    if engine.specification(instance)?.is_some()
        || !engine.configured_contracts(instance)?.is_empty()
        || engine.foreign_rust_target(instance)?.is_some()
    {
        return Err(
            "Box constructor source contracts/summary/foreign views remain unsupported".into(),
        );
    }
    let core = engine
        .tcx
        .lang_items()
        .sized_trait()
        .ok_or("Box core identity missing")?
        .krate;
    let alloc = engine
        .tcx
        .lang_items()
        .owned_box()
        .ok_or("Box lang identity missing")?
        .krate;
    if instance.def_id().krate != core && instance.def_id().krate != alloc {
        return Err("Box constructor source is outside actual core/alloc".into());
    }
    let raw = engine.tcx.instance_mir(instance.def);
    bounds(engine, raw)?;
    // Conservative separate materialization envelope for the bounded canonical template encoder.
    // Its line buffers and joined/normalized strings are not compiler instruction counts.
    pay(engine, 4 * ENCODING_BYTES + 64)?;
    let definition = pure_comparison_templates::owned_definition_key(instance.def_id());
    let encoded =
        pure_comparison_templates::encode_template_with_alloc(engine.tcx, raw, core, Some(alloc))?;
    pay(engine, encoded.len() + definition.len() + 4)?;
    let family = owned_box_templates::constructor_family(&definition, &encoded)
        .ok_or("Box constructor source differs from its complete original family")?;
    Ok(RawWitness {
        instance,
        raw,
        family,
    })
}
fn local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}
fn forward(args: &[rustc_span::Spanned<Operand<'_>>], index: usize) -> Result<(), String> {
    if !matches!(args.first().map(|a|&a.node),
        Some(Operand::Copy(place)|Operand::Move(place)) if local(*place,index))
    {
        return Err("Box constructor delegate lost its exact original local".into());
    }
    Ok(())
}
pub(super) fn prepare<'tcx>(
    engine: &mut Engine<'tcx>,
    constructor: ty::Instance<'tcx>,
) -> Result<Certificate<'tcx>, String> {
    pay(engine, 32 + constructor.args.len())?;
    if engine
        .tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
        != Some(constructor.def_id())
        || constructor.args.len() != 1
    {
        return Err("Box constructor source requires its exact selected Box::new Instance".into());
    }
    let payload = constructor.args.type_at(0);
    let ty::Adt(def, _) = payload.kind() else {
        return Err("Box constructor source requires a local fieldless payload".into());
    };
    if !def.did().is_local()
        || !def.is_struct()
        || def.repr().packed()
        || !def.non_enum_variant().fields.is_empty()
        || !payload.is_freeze(engine.tcx, ty::TypingEnv::fully_monomorphized())
        || !payload.needs_drop(engine.tcx, ty::TypingEnv::fully_monomorphized())
    {
        return Err("Box constructor source fieldless Freeze/custom Drop domain differs".into());
    }
    let original_box = engine.original_box_type(payload)?;
    let layout = owned_box_payloads::ZeroLayout::for_type(engine.tcx, payload)?;
    let mut pending = vec![(constructor, BoxTemplateFamily::BoxNew)];
    let mut parts = Vec::new();
    while let Some((instance, expected)) = pending.pop() {
        pay(engine, parts.len() + 4)?;
        if parts
            .iter()
            .any(|part: &Part<'tcx>| part.raw.instance == instance)
        {
            return Err("Box constructor source has a repeated/recursive delegate".into());
        }
        if parts.len() >= MAX_OPERATIONS {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "Box constructor source graph exceeds inherited 512-node limit".into(),
            ));
        }
        let witness = raw_witness(engine, instance)?;
        if witness.family != expected {
            return Err("Box constructor source selected a different delegate family".into());
        }
        let current = array_iterator_constructors::authenticated_box_constructor_source(
            engine, instance, &witness,
        )?;
        if instance == constructor
            && (current.return_ty() != original_box
                || current.arg_count != 1
                || current.local_decls[rustc_middle::mir::Local::from_usize(1)].ty != payload)
        {
            return Err("Box constructor original argument/output policy differs".into());
        }
        for index in owned_box_templates::constructor_blocks(expected, layout)? {
            pay(
                engine,
                current.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(*index)]
                    .statements
                    .len()
                    + 3,
            )?;
            let block = &current.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(*index)];
            if block
                .statements
                .iter()
                .any(|s| matches!(s.kind, StatementKind::Intrinsic(_)))
            {
                return Err("Box constructor reached an unproved Assume".into());
            }
            if let TerminatorKind::Call {
                func,
                args,
                target: Some(_),
                ..
            } = &block.terminator().kind
            {
                let child = match (expected, *index) {
                    (BoxTemplateFamily::BoxNew, 0) => {
                        pay(engine, 32)?;
                        owned_box_templates::compiler_zero_layout(
                            engine.tcx,
                            &args[0].node,
                            layout,
                        )?;
                        BoxTemplateFamily::BoxNewUninit
                    }
                    (BoxTemplateFamily::BoxNewUninit, 0) => {
                        forward(args, 1)?;
                        BoxTemplateFamily::GlobalAllocate
                    }
                    (BoxTemplateFamily::GlobalAllocate, 8) => {
                        forward(args, 19)?;
                        BoxTemplateFamily::NonNullPrecondition
                    }
                    _ => return Err("Box constructor reached an unexpected Call".into()),
                };
                let ty::FnDef(id, arguments) = func.ty(&current.local_decls, engine.tcx).kind()
                else {
                    return Err("Box constructor delegate is not an actual FnDef".into());
                };
                pay(engine, arguments.skip_binder().len() + 8)?;
                let next = engine.resolve_function_item(*id, arguments.skip_binder())?;
                pay(engine, pending.len() + 3)?;
                pending.push((next, child));
            }
        }
        pay(engine, parts.len() + 3)?;
        parts.push(Part {
            raw: witness,
            current,
        });
    }
    if parts.len() != 4 || layout.alignment() == 0 || !layout.alignment().is_power_of_two() {
        return Err("Box constructor scalar/complete normal-path obligations differ".into());
    }
    pay(engine, 24)?;
    Ok(Certificate {
        payload,
        constructor,
        layout,
        context: engine.terms.boolean(true),
        parts,
    })
}
impl<'tcx> Certificate<'tcx> {
    pub(super) fn validate(&self, engine: &mut Engine<'tcx>) -> Result<(), String> {
        pay(engine, self.parts.len() + 16)?;
        if !self.context.belongs_to(&engine.terms)
            || self.constructor.args.type_at(0) != self.payload
            || owned_box_payloads::ZeroLayout::for_type(engine.tcx, self.payload)? != self.layout
        {
            return Err("Box constructor certificate type/layout/current Context differs".into());
        }
        for part in &self.parts {
            array_iterator_constructors::authenticated_box_callable(engine, part.raw.instance)?;
            let current = array_iterator_constructors::authenticated_box_constructor_source(
                engine,
                part.raw.instance,
                &part.raw,
            )?;
            if !Rc::ptr_eq(&part.current, &current) {
                return Err("Box constructor certificate current Body was replaced".into());
            }
        }
        Ok(())
    }
}

// Only a preparation/refusal gate until the separate executable Box Drop invocation exists.
pub(super) fn pending_effectful<'tcx>(
    engine: &mut Engine<'tcx>,
    constructor: ty::Instance<'tcx>,
    payload: Ty<'tcx>,
) -> Result<(), String> {
    if !payload.needs_drop(engine.tcx, ty::TypingEnv::fully_monomorphized()) {
        return Ok(());
    }
    pay(engine, 48 + constructor.args.len())?;
    let metadata = owned_box_effect_free_drop::certify_type(engine.tcx, payload)?;
    if !engine.tcx.is_mir_available(metadata.destructor.def_id()) {
        return Ok(());
    }
    let raw = engine.tcx.instance_mir(metadata.destructor.def);
    if owned_box_effect_free_drop::destructor_body(engine.tcx, metadata.destructor, raw, &metadata)
        .is_ok()
    {
        return Ok(());
    }
    let certificate = prepare(engine, constructor)?;
    certificate.validate(engine)?;
    Err(engine.categorized_error(
        UnknownCategory::Semantics,
        "Box constructor is prepared; executable payload Drop invocation remains unsupported"
            .into(),
    ))
}

#[cfg(test)]
#[path = "owned_box_constructor_source_probe.rs"]
mod probe;
