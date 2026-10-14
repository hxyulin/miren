//! Paid, consumed whole-enum leaf codecs. These records grant no owner or Memory permission.
use super::*;
use rustc_middle::mir::{BasicBlock, Operand, Rvalue, StatementKind};
use std::cell::Cell;
use std::rc::Rc;

#[path = "mutable_codec/names.rs"]
mod names;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::proof) enum Use {
    Decode,
    Encode,
}

// The caller owns one instruction session. A refusal cannot be retried within that session.
#[derive(Default)]
pub(in crate::proof) struct Session(Cell<bool>);

// Non-Clone: the precharged operation and source association are consumed together.
pub(in crate::proof) struct Prepared<'tcx> {
    original: Ty<'tcx>,
    consume_names: names::Names<'tcx>,
    schema: Schema,
    instance: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    body: Rc<Body<'tcx>>,
    block: BasicBlock,
    statement: usize,
    occurrence: usize,
    retag: Option<rustc_middle::mir::WithRetag>,
    kind: Use,
    context: Context,
    token: Term,
    conditions: Vec<Term>,
    session: Rc<Session>,
}

fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    engine.steps = engine.steps.checked_add(count).ok_or_else(|| {
        engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "niche codec work overflow".into(),
        )
    })?;
    if engine.steps > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "niche codec shared execution step limit reached".into(),
        ));
    }
    Ok(())
}

fn categorized(engine: &Engine<'_>, reason: String) -> String {
    if engine.unknown_causes.borrow().contains_key(&reason) {
        reason
    } else {
        engine.categorized_error(UnknownCategory::Semantics, reason)
    }
}

struct TypePlan<'a, 'tcx> {
    engine: &'a mut Engine<'tcx>,
    nodes: usize,
    depth: usize,
    error: Option<String>,
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for TypePlan<'_, 'tcx> {
    type Result = std::ops::ControlFlow<()>;
    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if let Err(error) = pay(self.engine, 6) {
            self.error = Some(error);
            return std::ops::ControlFlow::Break(());
        }
        self.nodes += 1;
        if self.nodes > 512 || self.depth >= 16 {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "niche codec original graph exceeds512/depth16".into(),
            ));
            return std::ops::ControlFlow::Break(());
        }
        if let ty::Adt(def, _) = original.kind()
            && let Err(error) = names::path(self.engine, def.did())
        {
            self.error = Some(error);
            return std::ops::ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Tuple(_)
            | ty::Array(..)
            | ty::Adt(..) => original.super_visit_with(self),
            _ => {
                self.error =
                    Some("niche codec raw original graph needs unsupported normalization".into());
                std::ops::ControlFlow::Break(())
            }
        };
        self.depth -= 1;
        result
    }
    fn visit_const(&mut self, original: ty::Const<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if let Err(error) = pay(self.engine, 6) {
            self.error = Some(error);
            return std::ops::ControlFlow::Break(());
        }
        self.nodes += 1;
        if self.nodes > 512 || self.depth >= 16 {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "niche codec constant graph exceeds512/depth16".into(),
            ));
            return std::ops::ControlFlow::Break(());
        }
        if matches!(original.kind(), ty::ConstKind::Value(_)) {
            original.super_visit_with(self)
        } else {
            self.error = Some("niche codec raw constant normalization unsupported".into());
            std::ops::ControlFlow::Break(())
        }
    }
}

fn original_graph<'tcx>(engine: &mut Engine<'tcx>, original: Ty<'tcx>) -> Result<(), String> {
    use ty::TypeVisitable;
    let mut plan = TypePlan {
        engine,
        nodes: 0,
        depth: 0,
        error: None,
    };
    let _ = original.visit_with(&mut plan);
    if let Some(error) = plan.error {
        return Err(error);
    }
    Ok(())
}

fn selected<'tcx>(engine: &mut Engine<'tcx>, original: Ty<'tcx>) -> Result<bool, String> {
    let ty::Adt(def, args) = original.kind() else {
        return Ok(false);
    };
    if !def.is_enum() || def.variants().len() != 2 {
        return Ok(false);
    }
    original_graph(engine, original)?;
    // Original field binding is real work, paid before substitution. This routing service is
    // outside the selected-session failure handler; ordinary sums acquire no niche failure state.
    pay(engine, 8)?;
    let mut payload = None;
    let mut empty = 0;
    for variant in def.variants() {
        if variant.fields.is_empty() {
            empty += 1;
            continue;
        }
        if variant.fields.len() != 1 || payload.is_some() {
            return Ok(false);
        }
        pay(engine, 8)?;
        let actual = variant.fields[FieldIdx::from_usize(0)]
            .ty(engine.tcx, args)
            .skip_norm_wip();
        if matches!(actual.kind(), ty::Adt(nonzero, _)
            if engine.tcx.is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), nonzero.did()))
        {
            payload = Some(actual)
        } else {
            return Ok(false);
        }
    }
    Ok(empty == 1 && payload.is_some())
}

#[derive(Clone, Copy)]
pub(in crate::proof) struct Site<'tcx> {
    instance: ty::Instance<'tcx>,
    block: BasicBlock,
    statement: usize,
    kind: Use,
}

pub(in crate::proof) fn prepare<'tcx>(
    engine: &mut Engine<'tcx>,
    session: &Rc<Session>,
    original: Ty<'tcx>,
    site: Site<'tcx>,
    conditions: &[Term],
) -> Result<Option<Prepared<'tcx>>, String> {
    if !selected(engine, original)? {
        return Ok(None);
    }
    let Site {
        instance,
        block,
        statement,
        kind,
    } = site;
    let result = (|| {
        if session.0.get() {
            return Err("failed niche codec session cannot continue".into());
        }
        pay(engine, 8)?;
        if conditions.len() > 512 {
            return Err("niche codec condition inventory exceeds512".into());
        }
        pay(engine, conditions.len() + 8)?;
        if conditions
            .iter()
            .any(|term| term.sort() != &Sort::Bool || !term.belongs_to(&engine.terms))
        {
            return Err("niche codec conditions differ from current Context".into());
        }
        // Exact enum, NonZero, associated inner/Pat, all layouts, names and fields are a closed
        // compiler service. Prepay each fixed query and every bounded returned-name byte before
        // its real construction; no arbitrary alias normalization is introduced here.
        pay(engine, 512 + 16 * 129 + 128)?;
        let raw = certify_raw(engine.tcx, original)?;
        let prepared_names = names::prepare(engine, &raw)?;
        let consume_names = names::prepare(engine, &raw)?;
        prepared_names.check(&raw)?;
        let schema = schema(engine.tcx, materialize(engine.tcx, raw)?)?;
        if [
            schema.name.as_str(),
            schema.outer_name.as_str(),
            schema.inner_name.as_str(),
            schema.outer_field.as_str(),
            schema.inner_field.as_str(),
            schema.payload_field.as_str(),
            schema.variant_names[0].as_str(),
            schema.variant_names[1].as_str(),
        ]
        .iter()
        .any(|name| name.len() > 128)
        {
            return Err("niche codec schema name exceeds128".into());
        }
        let signature =
            super::super::mutable_hierarchy::products::niche_codec_signature(engine, instance)?;
        let signatures = engine.call_signatures.borrow().len();
        if signatures > 512 {
            return Err("niche codec signature registry exceeds512".into());
        }
        pay(engine, signatures + 16)?;
        engine
            .call_signatures
            .borrow_mut()
            .insert(instance, signature);

        let body = match super::super::function_tables::source::borrowed(engine, instance)? {
            Some(body) => body,
            None => super::super::array_iterator_constructors::steps::authenticated_helper_body(
                engine, instance,
            )?,
        };
        pay(engine, 16)?;
        let actual = body
            .basic_blocks
            .get(block)
            .and_then(|block| block.statements.get(statement))
            .ok_or("niche codec original instruction occurrence absent")?;
        let StatementKind::Assign(assignment) = &actual.kind else {
            return Err("niche codec needs actual whole-enum Assign".into());
        };
        let place = match kind {
            Use::Encode => assignment.0,
            Use::Decode => match &assignment.1 {
                // Exact certified niche values contain integer payloads and no references.
                // Retag Yes is authentic operand metadata, with no reference permission to issue.
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) => *place,
                _ => return Err("niche decode needs actual original whole-enum operand".into()),
            },
        };
        if place.projection.len() > 16 {
            return Err("niche codec original projection exceeds16".into());
        }
        pay(engine, place.projection.len() + 12)?;
        if place.ty(&body.local_decls, engine.tcx).ty != original
            || place
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Downcast(..)))
        {
            return Err("niche codec requires exact original whole enum type".into());
        }
        // Separate receipt/source checks, full schema comparisons, wrapper/value inventory,
        // owned condition vectors, two guarded feasibility queries and term/Value construction.
        // This is paid before any consumed operation; the codec still proves validity itself.
        pay(engine, 256 + 8 * 129 + 4 * conditions.len() + 96)?;
        let occurrence = std::ptr::from_ref(&actual.kind) as usize;
        let retag = match assignment.1 {
            Rvalue::Use(_, retag) => Some(retag),
            _ => None,
        };
        let token = engine.terms.boolean(true);
        Ok(Some(Prepared {
            original,
            consume_names,
            schema,
            instance,
            signature,
            body,
            block,
            statement,
            occurrence,
            retag,
            kind,
            context: engine.terms.clone(),
            token,
            conditions: conditions.to_vec(),
            session: session.clone(),
        }))
    })();
    if result.is_err() {
        session.0.set(true)
    }
    result.map_err(|reason| categorized(engine, reason))
}

impl<'tcx> Prepared<'tcx> {
    fn source(
        &self,
        engine: &Engine<'tcx>,
        site: Site<'tcx>,
        expected: Use,
        conditions: &[Term],
    ) -> Result<(), String> {
        if self.session.0.get()
            || self.kind != expected
            || site.kind != expected
            || site.instance != self.instance
            || site.block != self.block
            || site.statement != self.statement
            || conditions != self.conditions
            || !self.token.belongs_to(&engine.terms)
            || !self.token.belongs_to(&self.context)
        {
            return Err("niche codec consumed kind/Context/session differs".into());
        }
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "niche codec current Body registry is mutably borrowed")?;
        let signatures = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "niche codec full signature registry is mutably borrowed")?;
        if bodies
            .get(&self.instance)
            .is_none_or(|body| !Rc::ptr_eq(body, &self.body))
            || signatures
                .get(&self.instance)
                .is_none_or(|signature| *signature != self.signature)
        {
            return Err("niche codec current Body/full signature association differs".into());
        }
        let actual = self
            .body
            .basic_blocks
            .get(self.block)
            .and_then(|block| block.statements.get(self.statement))
            .ok_or("niche codec current occurrence absent")?;
        if std::ptr::from_ref(&actual.kind) as usize != self.occurrence {
            return Err("niche codec current occurrence differs".into());
        }
        let StatementKind::Assign(assignment) = &actual.kind else {
            return Err("niche codec current Assign absent".into());
        };
        let retag = match assignment.1 {
            Rvalue::Use(_, retag) => Some(retag),
            _ => None,
        };
        if retag != self.retag {
            return Err("niche codec authentic operand retag differs".into());
        }
        let raw = certify_raw(engine.tcx, self.original)?;
        self.consume_names.check(&raw)?;
        let expected = schema(engine.tcx, materialize(engine.tcx, raw)?)?;
        if !self.schema.storage_matches(&expected) {
            return Err("niche codec original compiler schema differs".into());
        }
        Ok(())
    }

    pub(in crate::proof) fn decode(
        self,
        engine: &Engine<'tcx>,
        site: Site<'tcx>,
        conditions: &[Term],
        array: &Term,
        index: &Term,
    ) -> Result<Value, String> {
        let result = (|| {
            self.source(engine, site, Use::Decode, conditions)?;
            self.schema
                .observe(&engine.terms, std::slice::from_ref(array), index, &mut 0)
        })();
        if result.is_err() {
            self.session.0.set(true)
        }
        result.map_err(|reason| categorized(engine, reason))
    }

    pub(in crate::proof) fn encode(
        self,
        engine: &Engine<'tcx>,
        site: Site<'tcx>,
        conditions: &[Term],
        value: &Value,
    ) -> Result<Term, String> {
        let result = (|| {
            self.source(engine, site, Use::Encode, conditions)?;
            self.schema.encode(engine, value, &self.conditions)
        })();
        if result.is_err() {
            self.session.0.set(true)
        }
        result.map_err(|reason| categorized(engine, reason))
    }
}

impl Schema {
    fn storage_matches(&self, expected: &Self) -> bool {
        facts_match(&self.facts)
            && facts_match(&expected.facts)
            && self.name == expected.name
            && self.is_option == expected.is_option
            && self.variant_names == expected.variant_names
            && self.payload_field == expected.payload_field
            && self.outer_name == expected.outer_name
            && self.inner_name == expected.inner_name
            && self.outer_field == expected.outer_field
            && self.inner_field == expected.inner_field
            && self.payload_variant == expected.payload_variant
            && self.tags == expected.tags
            && self.bits == expected.bits
            && self.signed == expected.signed
            && self.facts == expected.facts
    }

    fn variant<'a>(&self, value: &'a Value, variant: usize) -> Result<Option<&'a Value>, String> {
        let Value::Adt {
            name,
            variant: actual,
            is_option,
            discriminant,
            fields,
        } = value
        else {
            return Err("niche codec variant is not an original ADT".into());
        };
        if variant >= 2
            || *actual != variant
            || name != &self.name
            || *is_option != self.is_option
            || *discriminant != self.tags[variant]
        {
            return Err("niche codec original enum variant/tag differs".into());
        }
        if variant == self.payload_variant {
            if fields.len() != 1 || fields[0].0 != self.payload_field {
                return Err("niche codec payload field inventory differs".into());
            }
            Ok(Some(&fields[0].1))
        } else if fields.is_empty() {
            Ok(None)
        } else {
            Err("niche codec empty variant has payload fields".into())
        }
    }

    fn raw(&self, engine: &Engine<'_>, value: &Value) -> Result<Term, String> {
        let Value::Adt {
            name,
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields,
        } = value
        else {
            return Err("niche codec original NonZero wrapper differs".into());
        };
        if name != &self.outer_name || fields.len() != 1 || fields[0].0 != self.outer_field {
            return Err("niche codec NonZero original field differs".into());
        }
        let Value::Adt {
            name,
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields,
        } = &fields[0].1
        else {
            return Err("niche codec original inner wrapper differs".into());
        };
        if name != &self.inner_name || fields.len() != 1 || fields[0].0 != self.inner_field {
            return Err("niche codec original inner field differs".into());
        }
        let Value::Int {
            expression,
            bits,
            signed,
        } = &fields[0].1
        else {
            return Err("niche codec payload is not an integer".into());
        };
        if *bits != self.facts.payload_bits
            || *signed != self.facts.payload_signed()
            || expression.sort() != &Sort::BitVec(*bits)
            || !expression.belongs_to(&engine.terms)
        {
            return Err("niche codec payload width/sign/Context differs".into());
        }
        Ok(expression.clone())
    }

    fn nonzero(
        &self,
        engine: &Engine<'_>,
        raw: &Term,
        conditions: &[Term],
        guard: Option<Term>,
    ) -> Result<(), String> {
        let mut invalid = conditions.to_vec();
        if let Some(guard) = guard {
            invalid.push(guard)
        }
        invalid.push(engine.terms.apply(
            Op::Equal,
            &[
                raw.clone(),
                engine.terms.bit_vector(0, self.facts.payload_bits)?,
            ],
        )?);
        if engine.feasible(&invalid)? {
            return Err("niche codec active payload nonzero validity is unproved".into());
        }
        Ok(())
    }

    fn encode(
        &self,
        engine: &Engine<'_>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Term, String> {
        match value {
            Value::Adt { variant, .. } => match self.variant(value, *variant)? {
                None => engine.terms.bit_vector(0, self.facts.payload_bits),
                Some(payload) => {
                    let raw = self.raw(engine, payload)?;
                    self.nonzero(engine, &raw, conditions, None)?;
                    Ok(raw)
                }
            },
            Value::Enum {
                discriminant,
                variants,
                is_option,
            } => {
                if variants.len() != 2 || *is_option != self.is_option {
                    return Err("niche codec symbolic variant inventory differs".into());
                }
                let raw = self.raw(
                    engine,
                    self.variant(&variants[self.payload_variant], self.payload_variant)?
                        .ok_or("niche codec symbolic payload absent")?,
                )?;
                self.variant(
                    &variants[1 - self.payload_variant],
                    1 - self.payload_variant,
                )?;
                let Value::Int {
                    expression: tag,
                    bits,
                    signed,
                } = discriminant.as_ref()
                else {
                    return Err("niche codec symbolic tag is not an integer".into());
                };
                if *bits != self.bits
                    || *signed != self.signed
                    || tag.sort() != &Sort::BitVec(self.bits)
                    || !tag.belongs_to(&engine.terms)
                {
                    return Err("niche codec symbolic tag width/sign/Context differs".into());
                }
                let empty = engine.terms.apply(
                    Op::Equal,
                    &[
                        tag.clone(),
                        engine
                            .terms
                            .bit_vector(self.tags[1 - self.payload_variant], self.bits)?,
                    ],
                )?;
                let active = engine.terms.apply(
                    Op::Equal,
                    &[
                        tag.clone(),
                        engine
                            .terms
                            .bit_vector(self.tags[self.payload_variant], self.bits)?,
                    ],
                )?;
                let valid = engine
                    .terms
                    .apply(Op::Or, &[empty.clone(), active.clone()])?;
                let mut invalid = conditions.to_vec();
                invalid.push(symbolic::not(&valid));
                if engine.feasible(&invalid)? {
                    return Err("niche codec symbolic tag validity is unproved".into());
                }
                self.nonzero(engine, &raw, conditions, Some(active))?;
                engine.terms.apply(
                    Op::Ite,
                    &[
                        empty,
                        engine.terms.bit_vector(0, self.facts.payload_bits)?,
                        raw,
                    ],
                )
            }
            _ => Err("niche codec whole enum value has unsupported domain".into()),
        }
    }
}

#[cfg(test)]
#[path = "mutable_codec/probe.rs"]
mod probe;
