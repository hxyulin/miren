//! Finite selected pointer values; every leaf keeps its complete selection predicates.
use super::super::aggregates::RepeatWork;
use super::*;
#[path = "signature.rs"]
mod signature;

pub(super) fn pay(engine: &mut Engine<'_>, count: usize) -> Result<(), String> {
    engine.steps = engine.steps.saturating_add(count);
    if engine.steps > engine.limits.max_steps {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "nested function choice shared step budget exhausted".into(),
        ));
    }
    Ok(())
}

// Signature metadata only: Body authentication and primitive-domain admission remain separate.
struct AdmittedSignature<'tcx> {
    instance: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    pointer: Ty<'tcx>,
    comparison_work: usize,
}

pub(super) struct Admission<'tcx> {
    context: Term,
    signatures: Vec<AdmittedSignature<'tcx>>,
    failed: bool,
}

impl<'tcx> Admission<'tcx> {
    fn new(engine: &Engine<'tcx>, work: &mut RepeatWork) -> Result<Self, String> {
        engine.repeat_charge(work, 4)?;
        Ok(Self {
            context: engine.terms.boolean(true),
            signatures: Vec::new(),
            failed: false,
        })
    }

    fn check_record(
        &self,
        engine: &Engine<'tcx>,
        record: &AdmittedSignature<'tcx>,
        expected: Option<Ty<'tcx>>,
    ) -> Result<(), String> {
        if self.failed || !self.context.belongs_to(&engine.terms) {
            return Err("nested choice signature admission failed or Context differs".into());
        }
        if engine
            .call_signatures
            .borrow()
            .get(&record.instance)
            .is_some_and(|signature| *signature != record.signature)
            || expected.is_some_and(|expected| expected != record.pointer)
        {
            return Err("nested choice admitted original/full cached signature changed".into());
        }
        Ok(())
    }

    fn authenticate(
        &mut self,
        engine: &Engine<'tcx>,
        instance: ty::Instance<'tcx>,
        expected: Ty<'tcx>,
        work: &mut RepeatWork,
    ) -> Result<(), String> {
        let result = self.authenticate_inner(engine, instance, expected, work);
        if result.is_err() {
            self.failed = true;
        }
        result
    }

    fn authenticate_inner(
        &mut self,
        engine: &Engine<'tcx>,
        instance: ty::Instance<'tcx>,
        expected: Ty<'tcx>,
        work: &mut RepeatWork,
    ) -> Result<(), String> {
        if self.failed {
            return Err("nested choice signature admission already failed".into());
        }
        engine.repeat_charge(work, 6 + instance.args.len() + self.signatures.len())?;
        if !self.context.belongs_to(&engine.terms) {
            return Err("nested choice signature admission Context differs".into());
        }
        if let Some(record) = self
            .signatures
            .iter()
            .find(|record| record.instance == instance)
        {
            engine.repeat_charge(
                work,
                record.comparison_work + engine.call_signatures.borrow().len(),
            )?;
            return self.check_record(engine, record, Some(expected));
        }
        if self.signatures.len() >= MAX_ARRAY_ELEMENTS {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested choice admitted signatures exceed existing16 source records".into(),
            ));
        }
        let signature = signature::check(engine, instance, Some(expected), work)?;
        let comparison_work = 8
            + instance.args.len()
            + signature.bound_vars().len()
            + signature.skip_binder().inputs_and_output.len();
        engine.repeat_charge(work, 8 + comparison_work)?;
        self.signatures
            .try_reserve_exact(1)
            .map_err(|_| "nested choice admitted signature allocation failed")?;
        self.signatures.push(AdmittedSignature {
            instance,
            signature,
            pointer: expected,
            comparison_work,
        });
        Ok(())
    }

    pub(super) fn graph_signature(
        &mut self,
        engine: &mut Engine<'tcx>,
        instance: ty::Instance<'tcx>,
    ) -> Result<Option<ty::PolyFnSig<'tcx>>, String> {
        let result = self.graph_signature_inner(engine, instance);
        if result.is_err() {
            self.failed = true;
        }
        result
    }

    fn graph_signature_inner(
        &self,
        engine: &mut Engine<'tcx>,
        instance: ty::Instance<'tcx>,
    ) -> Result<Option<ty::PolyFnSig<'tcx>>, String> {
        if self.failed {
            return Err("nested choice signature admission already failed".into());
        }
        if instance.args.len() > MAX_INPUT_VALUES
            || self.signatures.len() > MAX_ARRAY_ELEMENTS
            || engine.call_signatures.borrow().len() > MAX_INPUT_VALUES
        {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested choice signature reuse exceeds existing record/type/cache bounds".into(),
            ));
        }
        pay(engine, 6 + instance.args.len() + self.signatures.len())?;
        if !self.context.belongs_to(&engine.terms) {
            return Err("nested choice signature admission Context differs".into());
        }
        let Some(record) = self
            .signatures
            .iter()
            .find(|record| record.instance == instance)
        else {
            return Ok(None);
        };
        let comparison_work = record.comparison_work + engine.call_signatures.borrow().len();
        pay(engine, comparison_work)?;
        self.check_record(engine, record, None)?;
        Ok(Some(record.signature))
    }
}

struct Leaf<'tcx> {
    instance: ty::Instance<'tcx>,
    conditions: Vec<Term>,
    body: std::rc::Rc<Body<'tcx>>,
}

struct Recipe<'tcx> {
    leaves: Vec<Leaf<'tcx>>,
    sources: Vec<Source<'tcx>>,
    tree_nodes: usize,
    source_nodes: usize,
    admission: Admission<'tcx>,
}

struct Source<'tcx> {
    instance: ty::Instance<'tcx>,
    body: std::rc::Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
}

fn current_sources<'tcx>(
    engine: &mut Engine<'tcx>,
    sources: &[Source<'tcx>],
) -> Result<(), String> {
    pay(engine, 4 + sources.len() * 4)?;
    for source in sources {
        if !engine
            .bodies
            .borrow()
            .get(&source.instance)
            .is_some_and(|body| std::rc::Rc::ptr_eq(body, &source.body))
            || engine
                .call_signatures
                .borrow()
                .get(&source.instance)
                .is_some_and(|signature| *signature != source.signature)
        {
            return Err(
                "nested choice held original/current Body or full signature changed".into(),
            );
        }
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn signature_check_count() -> usize {
    signature::check_count()
}

impl<'tcx> Engine<'tcx> {
    #[cfg(test)]
    pub(super) fn admitted_source_probe(
        &mut self,
        instance: ty::Instance<'tcx>,
        mut admission: Admission<'tcx>,
    ) -> Result<std::rc::Rc<Body<'tcx>>, String> {
        self.nested_source_graph(instance, 0, &mut Vec::new(), &mut 0, &mut admission)
    }

    pub(super) fn admit_nested_target(
        &self,
        id: usize,
        expected: Ty<'tcx>,
        work: &mut RepeatWork,
    ) -> Result<(), String> {
        self.admit_nested_node(id, expected, 0, work, &mut None)
    }

    pub(super) fn admit_dispatch_signatures(
        &self,
        id: usize,
        expected: Ty<'tcx>,
        mut work: RepeatWork,
    ) -> Result<Admission<'tcx>, String> {
        let mut admission = Some(Admission::new(self, &mut work)?);
        // A failed partial admission is consumed here, never returned to the caller.
        self.admit_nested_node(id, expected, 0, &mut work, &mut admission)?;
        Ok(admission.unwrap())
    }

    fn admit_nested_node(
        &self,
        id: usize,
        expected: Ty<'tcx>,
        depth: usize,
        work: &mut RepeatWork,
        admission: &mut Option<Admission<'tcx>>,
    ) -> Result<(), String> {
        self.repeat_charge(work, 6)?;
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested function choice exceeds existing depth16".into(),
            ));
        }
        let pointers = self.function_pointers.borrow();
        let target = pointers
            .get(id)
            .ok_or("nested function choice registry entry absent")?;
        match target {
            Target::Opaque { .. } => Err(self.categorized_error(
                UnknownCategory::Semantics,
                "function table cannot contain opaque or nested choices".into(),
            )),
            Target::Known {
                instance,
                signature: actual,
            } => {
                if *actual != expected {
                    return Err("nested function choice leaf signature differs".into());
                }
                if let Some(admission) = admission {
                    admission.authenticate(self, *instance, expected, work)?;
                } else {
                    signature::check(self, *instance, Some(expected), work)?;
                }
                self.validate_table_target(id, expected)?;
                Ok(())
            }
            Target::Choice(choice) => {
                let ty::Array(element, count) = choice.original.kind() else {
                    return Err("nested function choice original array differs".into());
                };
                self.repeat_charge(work, 6 + choice.targets.len())?;
                if choice.signature != expected
                    || self.tcx.erase_and_anonymize_regions(*element) != expected
                    || choice.targets.is_empty()
                    || choice.targets.len() > MAX_ARRAY_ELEMENTS
                    || count.try_to_target_usize(self.tcx) != Some(choice.targets.len() as u64)
                    || !choice.index.belongs_to(&self.terms)
                    || choice.index.sort()
                        != &Sort::BitVec(u32::from(self.tcx.sess.target.pointer_width))
                {
                    return Err("nested function choice original type/index/Context differs".into());
                }
                // Production registry entries are append-only. Backward edges also prohibit cycles.
                for child in &choice.targets {
                    if *child >= id {
                        return Err("nested function choice forward or cyclic registry edge".into());
                    }
                    self.admit_nested_node(*child, expected, depth + 1, work, admission)?;
                }
                Ok(())
            }
        }
    }

    pub(super) fn nested_table_candidate(&mut self, id: usize) -> Result<bool, String> {
        pay(self, 3)?;
        let length = {
            let pointers = self.function_pointers.borrow();
            let Some(Target::Choice(choice)) = pointers.get(id) else {
                return Ok(false);
            };
            choice.targets.len()
        };
        if length > MAX_ARRAY_ELEMENTS {
            return Err("nested function choice candidate exceeds original table bounds".into());
        }
        pay(self, 2 * length)?;
        let pointers = self.function_pointers.borrow();
        let Some(Target::Choice(choice)) = pointers.get(id) else {
            return Err("nested choice candidate registry changed".into());
        };
        Ok(choice
            .targets
            .iter()
            .any(|id| matches!(pointers.get(*id), Some(Target::Choice(_)))))
    }

    fn nested_caller_source(&mut self, call: &TableCall<'_, 'tcx>) -> Result<Source<'tcx>, String> {
        let registered = self.bodies.borrow().len();
        pay(self, 8 + registered * 3)?;
        if registered > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested choice caller Body registry exceeds existing512 bounds".into(),
            ));
        }
        let instance = {
            let bodies = self.bodies.borrow();
            let mut matches = bodies
                .iter()
                .filter(|(_, body)| std::ptr::eq(body.as_ref(), call.body));
            let (instance, _) = matches
                .next()
                .ok_or("nested choice caller cached source absent")?;
            if matches.next().is_some() || instance.def_id() != call.site.0 {
                return Err("nested choice caller full Instance association differs".into());
            }
            *instance
        };
        pay(self, MAX_INPUT_VALUES)?;
        let signature = signature::check(self, instance, None, &mut RepeatWork::new())?;
        let body = match super::source::borrowed(self, instance)? {
            Some(body) => body,
            None => array_iterator_constructors::steps::authenticated_helper_body(self, instance)?,
        };
        if !std::ptr::eq(body.as_ref(), call.body) {
            return Err("nested choice original/current caller identity differs".into());
        }
        pay(self, 8 + body.arg_count)?;
        let concrete = self.tcx.instantiate_bound_regions_with_erased(signature);
        if body.arg_count != concrete.inputs().len()
            || body.return_ty() != concrete.output()
            || body
                .args_iter()
                .zip(concrete.inputs())
                .any(|(local, ty)| body.local_decls[local].ty != *ty)
        {
            return Err("nested choice caller locals/full signature differ".into());
        }
        Ok(Source {
            instance,
            body,
            signature,
        })
    }

    fn nested_source_graph(
        &mut self,
        instance: ty::Instance<'tcx>,
        depth: usize,
        sources: &mut Vec<Source<'tcx>>,
        nodes: &mut usize,
        admission: &mut Admission<'tcx>,
    ) -> Result<std::rc::Rc<Body<'tcx>>, String> {
        pay(self, 8 + instance.args.len() + sources.len())?;
        *nodes = nodes.saturating_add(1);
        if depth >= MAX_INPUT_DEPTH || *nodes > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested function choice helper source exceeds depth16".into(),
            ));
        }
        if let Some(source) = sources.iter().find(|source| source.instance == instance) {
            // A repeated edge reuses this operation's immutable evidence, after checking both
            // mutable registries. No new normalization or Body traversal is performed.
            pay(self, 8)?;
            if !self
                .bodies
                .borrow()
                .get(&instance)
                .is_some_and(|body| std::rc::Rc::ptr_eq(body, &source.body))
                || self
                    .call_signatures
                    .borrow()
                    .get(&instance)
                    .is_some_and(|signature| *signature != source.signature)
            {
                return Err("nested choice repeated source Body or full signature changed".into());
            }
            return Ok(source.body.clone());
        }
        let poly = match admission.graph_signature(self, instance)? {
            Some(signature) => signature,
            None => {
                pay(self, MAX_INPUT_VALUES)?;
                signature::check(self, instance, None, &mut RepeatWork::new())?
            }
        };
        if sources.len() >= MAX_ARRAY_ELEMENTS {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested function choice helper source exceeds existing16 records".into(),
            ));
        }
        let body = match super::source::borrowed(self, instance)? {
            Some(body) => body,
            None => array_iterator_constructors::steps::authenticated_helper_body(self, instance)?,
        };
        pay(self, 8 + body.arg_count)?;
        let concrete = self.tcx.instantiate_bound_regions_with_erased(poly);
        if body.arg_count != concrete.inputs().len()
            || body.return_ty() != concrete.output()
            || body
                .args_iter()
                .zip(concrete.inputs())
                .any(|(local, ty)| body.local_decls[local].ty != *ty)
        {
            return Err("nested function choice source locals/full signature differ".into());
        }
        pay(self, 4 + sources.len())?;
        sources
            .try_reserve_exact(1)
            .map_err(|_| "nested choice source record allocation failed")?;
        sources.push(Source {
            instance,
            body: body.clone(),
            signature: poly,
        });
        for data in body.basic_blocks.iter() {
            pay(self, 2)?;
            match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    pay(self, 4)?;
                    let Operand::Constant(function) = func else {
                        return Err(
                            "nested function choice static helper graph has an indirect frontier"
                                .into(),
                        );
                    };
                    let ty::FnDef(id, arguments) = function.const_.ty().kind() else {
                        return Err("nested function choice helper source lacks exact FnDef".into());
                    };
                    pay(self, 4 + arguments.skip_binder().len())?;
                    let selected = self.resolve_function_item(*id, arguments.skip_binder())?;
                    if matches!(selected.def, ty::InstanceKind::Intrinsic(_)) {
                        pay(self, MAX_INPUT_VALUES)?;
                        signature::check(self, selected, None, &mut RepeatWork::new())?;
                        continue; // Metadata only; ordinary builtin execution is still required.
                    }
                    if !matches!(selected.def, ty::InstanceKind::Item(id)
                        if matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
                    {
                        return Err(
                            "nested function choice helper adapter remains unsupported".into()
                        );
                    }
                    if self.foreign_rust_target(selected)?.is_some()
                        || self.specification(selected)?.is_some_and(|spec| {
                            spec.trusted
                                || spec.storage_effect.is_some()
                                || spec.returns_alias.is_some()
                        })
                    {
                        return Err(
                            "nested function choice helper summary remains unsupported".into()
                        );
                    }
                    if super::super::super::identity::is_panic_call(self.tcx, selected.def_id())
                        || self.is_core_panic_helper(selected.def_id())
                    {
                        pay(self, MAX_INPUT_VALUES)?;
                        signature::check(self, selected, None, &mut RepeatWork::new())?;
                        continue; // Actual panic execution must create its ordinary obligation.
                    }
                    self.nested_source_graph(selected, depth + 1, sources, nodes, admission)?;
                }
                TerminatorKind::Drop { place, .. }
                    if place
                        .ty(&body.local_decls, self.tcx)
                        .ty
                        .needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) =>
                {
                    return Err(
                        "nested function choice helper owning Drop frontier unsupported".into(),
                    );
                }
                TerminatorKind::TailCall { .. } => {
                    return Err(
                        "nested function choice helper TailCall frontier unsupported".into(),
                    );
                }
                _ => {}
            }
        }
        Ok(body)
    }

    fn nested_leaves(
        &mut self,
        id: usize,
        expected: Ty<'tcx>,
        conditions: &[Term],
        depth: usize,
        recipe: &mut Recipe<'tcx>,
    ) -> Result<(), String> {
        pay(self, 8)?;
        recipe.tree_nodes = recipe.tree_nodes.saturating_add(1);
        if recipe.tree_nodes > MAX_INPUT_VALUES || depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested function choice complete tree exceeds existing bounds".into(),
            ));
        }
        let size = {
            let pointers = self.function_pointers.borrow();
            match pointers.get(id) {
                Some(Target::Choice(choice)) => choice.targets.len(),
                Some(Target::Known { .. } | Target::Opaque { .. }) => 0,
                None => return Err("nested function choice registry entry absent".into()),
            }
        };
        if size > MAX_ARRAY_ELEMENTS {
            return Err("nested function choice target vector exceeds16".into());
        }
        pay(self, size + 8)?; // Complete owned registry snapshot before cloning.
        let target = self.function_pointers.borrow().get(id).cloned().unwrap();
        match target {
            Target::Known { instance, .. } => {
                if recipe.leaves.len() >= MAX_ARRAY_ELEMENTS {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "nested function choice leaves exceed existing16 branch bound".into(),
                    ));
                }
                // Real original/current body authentication remains a separately paid service.
                let body = self.nested_source_graph(
                    instance,
                    0,
                    &mut recipe.sources,
                    &mut recipe.source_nodes,
                    &mut recipe.admission,
                )?;
                pay(self, 4 + recipe.leaves.len())?;
                let validated = recipe.leaves.iter().any(|leaf| leaf.instance == instance);
                if let Some(primitive) = self
                    .primitive_table_signature(expected)
                    .filter(|_| !validated)
                {
                    pay(self, MAX_INPUT_VALUES)?;
                    let mut work = PrimitiveBodyWork {
                        engine: self,
                        domain: primitive.body_domain(),
                        used: 0,
                        error: None,
                        locals: 0,
                    };
                    self.primitive_table_body_work(instance, &body, &mut work)?;
                }
                pay(self, conditions.len() + 4 + recipe.leaves.len())?;
                recipe
                    .leaves
                    .try_reserve_exact(1)
                    .map_err(|_| "nested choice leaf allocation failed")?;
                recipe.leaves.push(Leaf {
                    instance,
                    conditions: conditions.to_vec(),
                    body,
                });
                Ok(())
            }
            Target::Opaque { .. } => {
                Err("function table cannot contain opaque or nested choices".into())
            }
            Target::Choice(choice) => {
                let bits = u32::from(self.tcx.sess.target.pointer_width);
                pay(self, 16 + conditions.len())?;
                let outside = self.terms.apply(
                    Op::Not,
                    &[self.terms.apply(
                        Op::BvUnsignedLt,
                        &[
                            choice.index.clone(),
                            self.terms.bit_vector(choice.targets.len() as u128, bits)?,
                        ],
                    )?],
                )?;
                let mut uncovered = conditions.to_vec();
                uncovered.push(outside);
                if self.feasible(&uncovered)? {
                    return Err("nested function choice lost its covered index domain".into());
                }
                for (position, child) in choice.targets.iter().enumerate() {
                    pay(self, 12 + conditions.len())?;
                    let mut branch = conditions.to_vec();
                    branch.push(self.terms.apply(
                        Op::Equal,
                        &[
                            choice.index.clone(),
                            self.terms.bit_vector(position as u128, bits)?,
                        ],
                    )?);
                    self.nested_leaves(*child, expected, &branch, depth + 1, recipe)?;
                }
                Ok(())
            }
        }
    }

    pub(super) fn prepared_nested_table_call(
        &mut self,
        state: &State,
        call: TableCall<'_, 'tcx>,
        id: usize,
    ) -> Result<Option<Vec<(State, Return)>>, String> {
        pay(self, 4)?;
        if state.conditions.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested choice conditions exceed existing512 bounds".into(),
            ));
        }
        pay(self, 2 + state.conditions.len())?;
        if state
            .conditions
            .iter()
            .any(|condition| condition.sort() != &Sort::Bool || !condition.belongs_to(&self.terms))
        {
            return Err("nested choice current path condition Context or sort differs".into());
        }
        let caller_source = self.nested_caller_source(&call)?;
        pay(self, 24)?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &call.body.basic_blocks[call.block].terminator().kind
        else {
            return Err("nested function choice requires actual Call".into());
        };
        if !std::ptr::eq(func, call.func)
            || !std::ptr::eq(args.as_ref(), call.args)
            || *destination != call.destination
            || *target != call.target
            || target.is_none()
            || *unwind != rustc_middle::mir::UnwindAction::Unreachable
            || call.body.source.def_id() != call.site.0
            || call.body.basic_blocks[call.block]
                .terminator()
                .source_info
                .span
                != call.site.1
            || call.body.coroutine.is_some()
            || call.body.tainted_by_errors.is_some()
            || call.body.spread_arg.is_some()
            || call.body.basic_blocks[call.block].is_cleanup
            || !state.memory.mutable_u16.is_empty()
            || !state.memory.owned_regions.is_empty()
        {
            return Err("nested function choice actual Call/Memory differs".into());
        }
        operand_type_work(self, call.func)?;
        let expected = self
            .tcx
            .erase_and_anonymize_regions(call.func.ty(&call.body.local_decls, self.tcx));
        if !self.table_signature(expected) {
            return Err("nested function choice signature unsupported".into());
        }
        // One cumulative local admission budget for the complete tree, prepaid in shared steps.
        pay(self, MAX_INPUT_VALUES)?;
        let admission = self.admit_dispatch_signatures(id, expected, RepeatWork::new())?;
        let signature = expected.fn_sig(self.tcx).skip_binder();
        if call.args.len() != signature.inputs().len() {
            return Err("nested function choice original argument arity differs".into());
        }
        for (argument, expected) in call.args.iter().zip(signature.inputs()) {
            operand_type_work(self, &argument.node)?;
            if argument.node.ty(&call.body.local_decls, self.tcx) != *expected {
                return Err("nested function choice original argument types differ".into());
            }
            if let Operand::Copy(place) | Operand::Move(place) = &argument.node {
                pay(self, 8 + place.projection.len() * 4)?;
                self.owned_field_footprint(call.body, *place)?;
            }
        }
        pay(self, 8 + call.destination.projection.len() * 4)?;
        if call.destination.ty(&call.body.local_decls, self.tcx).ty != signature.output() {
            return Err("nested function choice original result type differs".into());
        }
        pay(self, 8 + call.destination.projection.len() * 4)?;
        self.owned_field_footprint(call.body, call.destination)?;
        let mut recipe = Recipe {
            leaves: Vec::new(),
            sources: Vec::new(),
            tree_nodes: 0,
            source_nodes: 0,
            admission,
        };
        self.nested_leaves(id, expected, &state.conditions, 0, &mut recipe)?;
        pay(self, 8 + state.conditions.len() + state.locals.len())?;
        let mut consumed = clone_state(self, state)?;
        let actual = self.evaluate_operand(call.site.0, call.body, &mut consumed, call.func)?;
        if !matches!(actual, Value::FunctionPointer { id: actual } if actual == id) {
            return Err("nested function choice callable differs from initialized token".into());
        }
        let mut values = Vec::new();
        pay(self, call.args.len() * 6 + 2)?;
        for (operand, original) in call.args.iter().zip(signature.inputs()) {
            let value =
                self.evaluate_operand(call.site.0, call.body, &mut consumed, &operand.node)?;
            if let Some(integer) = self.original_integer_signature(*original) {
                self.validate_table_result(&value, integer)?;
            } else {
                self.validate_primitive_table_value(
                    &value,
                    self.primitive_table_signature(expected)
                        .ok_or("nested primitive signature absent")?,
                    &consumed.conditions,
                )?;
            }
            values.push(value);
        }
        self.validate_owned_call_arguments(&values, &consumed.memory)?;
        let mut returns = Vec::new();
        for leaf in recipe.leaves {
            pay(self, 4)?;
            if !self
                .bodies
                .borrow()
                .get(&caller_source.instance)
                .is_some_and(|body| std::rc::Rc::ptr_eq(body, &caller_source.body))
            {
                return Err("nested choice suspended caller source identity changed".into());
            }
            if !self.feasible(&leaf.conditions)? {
                continue;
            }
            if self.specification(leaf.instance)?.is_some() {
                return Err(
                    "function table configured target is outside the initial domain".into(),
                );
            }
            pay(self, 8 + consumed.conditions.len() + consumed.locals.len())?;
            if !self
                .bodies
                .borrow()
                .get(&leaf.instance)
                .is_some_and(|current| std::rc::Rc::ptr_eq(current, &leaf.body))
            {
                return Err("nested function choice current source identity changed".into());
            }
            current_sources(self, std::slice::from_ref(&caller_source))?;
            current_sources(self, &recipe.sources)?;
            let mut branch = clone_state(self, &consumed)?;
            self.byte_copy_call_eligibility(leaf.instance, true, &mut branch);
            pay(self, 4 + values.len() * 4)?;
            let memory = clone_memory(self, &branch.memory)?;
            for result in self.call_instance(
                leaf.instance,
                values.clone(),
                leaf.conditions,
                memory,
                call.stack,
                call.site,
            )? {
                if let Some(integer) = self.original_integer_signature(signature.output()) {
                    self.validate_table_result(&result.value, integer)?;
                } else {
                    let primitive = self.primitive_table_signature(expected).unwrap();
                    // The existing test observer changes a clone at the actual Return boundary.
                    #[cfg(test)]
                    let observed = match primitive {
                        PrimitiveSignature::Float32(_) | PrimitiveSignature::Float64(_) => {
                            observed_float_table_return(self, &result.value)
                        }
                        PrimitiveSignature::Bool(_) | PrimitiveSignature::Char(_) => {
                            result.value.clone()
                        }
                    };
                    #[cfg(test)]
                    let value = &observed;
                    #[cfg(not(test))]
                    let value = &result.value;
                    self.validate_primitive_table_value(value, primitive, &result.conditions)?;
                }
                pay(
                    self,
                    4 + returns.len() + branch.locals.len() + branch.conditions.len(),
                )?;
                returns
                    .try_reserve_exact(1)
                    .map_err(|_| "nested function choice Return allocation failed")?;
                if !self
                    .bodies
                    .borrow()
                    .get(&leaf.instance)
                    .is_some_and(|current| std::rc::Rc::ptr_eq(current, &leaf.body))
                {
                    return Err("nested function choice returned source identity changed".into());
                }
                current_sources(self, std::slice::from_ref(&caller_source))?;
                current_sources(self, &recipe.sources)?;
                returns.push((clone_state(self, &branch)?, result));
            }
        }
        Ok(Some(returns))
    }
}

fn operand_type_work(engine: &mut Engine<'_>, operand: &Operand<'_>) -> Result<(), String> {
    let length = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.projection.len(),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => 0,
    };
    pay(engine, 4 + length * 2)?;
    if length > MAX_INPUT_DEPTH {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "nested choice actual operand type projection exceeds depth16".into(),
        ));
    }
    Ok(())
}

fn value_clone_work(
    engine: &mut Engine<'_>,
    value: &Value,
    nodes: &mut usize,
    depth: usize,
) -> Result<usize, String> {
    if depth >= MAX_INPUT_DEPTH {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "nested function choice clone depth16 exhausted".into(),
        ));
    }
    match value {
        Value::Tuple(fields) => {
            pay(engine, 2 + fields.len())?;
            *nodes += 1;
            if *nodes > MAX_INPUT_VALUES {
                return Err(engine.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "nested choice tuple clone nodes exhausted".into(),
                ));
            }
            let mut cost = 2 + fields.len();
            for field in fields {
                cost += value_clone_work(engine, field, nodes, depth + 1)?;
            }
            Ok(cost)
        }
        Value::FunctionPointer { .. } | Value::Uninitialized => {
            pay(engine, 1)?;
            *nodes += 1;
            if *nodes > MAX_INPUT_VALUES {
                return Err(engine.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "nested function choice clone exceeds existing512 nodes".into(),
                ));
            }
            Ok(3)
        }
        Value::Reference { projection, .. } => {
            pay(engine, 2 + projection.len())?;
            *nodes += 1;
            if *nodes > MAX_INPUT_VALUES || projection.len() > MAX_INPUT_DEPTH {
                return Err(engine.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "nested function choice reference clone exceeds bounds".into(),
                ));
            }
            let mut cost = 6 + projection.len() * 3;
            for part in projection {
                if let symbolic::MemoryProjection::TypedIndex { index, .. } = part {
                    cost += value_clone_work(engine, index, nodes, depth + 1)?;
                }
            }
            Ok(cost)
        }
        Value::Input(_)
        | Value::Bool(_)
        | Value::Int { .. }
        | Value::Float { .. }
        | Value::Unit
        | Value::Elements(_)
        | Value::Adt { .. } => {
            array_iterator_constructors::clone_value_work(engine, value, depth, nodes)
        }
        Value::OwnedArrayIterator { .. }
        | Value::MutableU16 { .. }
        | Value::OwnedRegion { .. }
        | Value::OwnedSnapshot(_)
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
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::StaticText
        | Value::FormatArguments
        | Value::Function => Err("nested choice State clone payload domain unsupported".into()),
    }
}

fn clone_memory(engine: &mut Engine<'_>, memory: &Memory) -> Result<Memory, String> {
    pay(engine, 10)?;
    if !memory.incoming_byte_roots.is_empty()
        || !memory.startup_values.is_empty()
        || !memory.isolated_static_types.is_empty()
        || !memory.startup_overwritten.is_empty()
        || !memory.static_uninitialized.is_empty()
    {
        return Err("nested function choice auxiliary Memory clone domain unsupported".into());
    }
    let masks = array_iterator_constructors::clone_masks(engine, &memory.missing_places)?;
    pay(engine, 24)?;
    Ok(memory.clone_with_iterator_drop_masks(masks))
}

fn clone_state(engine: &mut Engine<'_>, state: &State) -> Result<State, String> {
    state.flow.require_unarmed()?;
    pay(engine, 10)?;
    if state.locals.len() > MAX_INPUT_VALUES
        || state.addresses.len() > MAX_INPUT_VALUES
        || state.constant_receipts.len() > MAX_INPUT_VALUES
        || state.conditions.len() > MAX_INPUT_VALUES
    {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "nested function choice State clone exceeds existing512 bound".into(),
        ));
    }
    pay(engine, state.locals.len())?;
    let mut nodes = 0;
    let mut cost = state.locals.len()
        + state.addresses.len()
        + state.conditions.len()
        + state.constant_receipts.len() * 8
        + 8;
    for value in state.locals.iter().flatten() {
        cost += value_clone_work(engine, value, &mut nodes, 0)?;
    }
    let masks = array_iterator_constructors::clone_masks(engine, &state.missing_places)?;
    let memory = clone_memory(engine, &state.memory)?;
    pay(engine, cost)?;
    Ok(State {
        flow: state.flow.clone(),
        locals: state.locals.clone(),
        constant_receipts: state.constant_receipts.clone(),
        missing_places: masks,
        conditions: state.conditions.clone(),
        addresses: state.addresses.clone(),
        memory,
    })
}

#[cfg(test)]
#[path = "probe.rs"]
mod tests;
