//! Actual compiler graphs, recorded separately from a comparison-law certificate.
use super::*;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Location, Statement, Terminator};
use std::path::PathBuf;

#[derive(Default)]
struct Inventory {
    work: usize,
}

impl<'tcx> Visitor<'tcx> for Inventory {
    fn visit_local_decl(&mut self, local: Local, decl: &rustc_middle::mir::LocalDecl<'tcx>) {
        self.work += 1;
        self.super_local_decl(local, decl);
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.work += 1;
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.work += 1;
        self.super_terminator(terminator, location);
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.work += 1;
        self.super_operand(operand, location);
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: Location,
    ) {
        self.work += place.projection.len();
        self.super_place(place, context, location);
    }
}

fn engine<'tcx>(tcx: TyCtxt<'tcx>) -> Engine<'tcx> {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    Engine {
        activation: Default::default(),
        tcx,
        terms: Context::default(),
        next_symbol: std::cell::Cell::new(0),
        float_encodings: BTreeMap::new(),
        float_pairs: super::super::super::float_pairs::Registry::default(),
        abstraction_symbols: std::cell::RefCell::new(BTreeMap::new()),
        static_views: std::cell::RefCell::new(Vec::new()),
        static_origins: Default::default(),
        static_epoch: None,
        static_roots: None,
        function_pointers: std::cell::RefCell::new(Vec::new()),
        static_addresses: std::collections::HashMap::new(),
        tracked_addresses: Vec::new(),
        maybe_uninit_types: Vec::new(),
        scalar_slice_types: Vec::new(),
        composite_slice_types: Vec::new(),
        steps: 0,
        call_chain: Vec::new(),
        failed_call_chain: None,
        trait_objects: std::cell::RefCell::new(Vec::new()),
        trait_object_choice_work: std::cell::Cell::new(0),
        trait_object_choices_issued: std::cell::Cell::new(false),
        input_depth: 0,
        input_values: 0,
        input_reservations: Vec::new(),
        owned_projection_certificates: Vec::new(),
        input_shapes: std::collections::HashMap::new(),
        zero_sized_inputs: std::collections::HashMap::new(),
        zero_sized_input_nodes: 0,
        prefer_lazy_inputs: false,
        building_mutable_input: false,
        unknown_causes: std::cell::RefCell::new(BTreeMap::new()),
        started: std::time::Instant::now(),
        config: config.clone(),
        all_failures,
        induction,
        startup,
        isolated_startup,
        limits,
        resolved_contracts: BTreeMap::new(),
        solver: std::cell::RefCell::new(Solver::with_limits(limits)),
        mutable_u16_frames: Default::default(),
        mutable_integer_types: Vec::new(),
        mutable_u16_staging: Default::default(),
        coroutine_places: Default::default(),
        owned_box_types: Vec::new(),
        next_owned_region: 0,
        owned_box_constructors: Vec::new(),
        bodies: std::cell::RefCell::new(std::collections::HashMap::new()),
        call_signatures: std::cell::RefCell::new(std::collections::HashMap::new()),
        proof: Proof {
            status: ProofStatus::Proved,
            async_entry,
            assumptions: Vec::new(),
            entry_assumptions: Vec::new(),
            inputs: BTreeMap::new(),
            models: Vec::new(),
            invariants: Vec::new(),
            analyzed_bodies: Vec::new(),
            body_entries: Vec::new(),
            body_entries_truncated: false,
            obligations: Vec::new(),
            trusted_calls: Vec::new(),
            matched_contracts: Vec::new(),
            stopped_after_counterexample: false,
            replay_inputs: None,
        },
    }
}

fn research_trace<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    payload: Ty<'tcx>,
    bodies: &'a [(ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>)],
    graph: &'a mut GraphBudget<'tcx>,
    limit: usize,
) -> LawTrace<'a, 'tcx> {
    LawTrace {
        tcx,
        engine: None,
        graph: Some(graph),
        original,
        payload,
        tags: None,
        equality: 0xaa,
        completed: Vec::new(),
        bodies,
        work: 0,
        limit,
        observed: LawWork::default(),
        active: [None; 16],
    }
}

fn engine_controls<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    outer: ty::Instance<'tcx>,
    primitive: ty::Instance<'tcx>,
    payload_eq: ty::Instance<'tcx>,
    available: &std::collections::HashMap<ty::Instance<'tcx>, std::rc::Rc<Body<'tcx>>>,
) -> Vec<String> {
    let mut records = Vec::new();
    public_application_controls(tcx, original, outer);
    let mut graph = GraphBudget::new(0).unwrap();
    graph.charge(NICHE_BODIES + 1).unwrap();
    let mut bounded = Vec::new();
    bounded.try_reserve_exact(NICHE_BODIES).unwrap();
    let body = available.get(&primitive).unwrap();
    graph
        .insert_body(&mut bounded, primitive, body.clone())
        .unwrap();
    let before = graph.work;
    graph
        .insert_body(&mut bounded, primitive, body.clone())
        .unwrap();
    assert_eq!(graph.work - before, 2 + primitive.args.len());
    assert_eq!(bounded.len(), 1);
    let replacement = std::rc::Rc::new((**body).clone());
    assert!(
        graph
            .insert_body(&mut bounded, primitive, replacement)
            .unwrap_err()
            .contains("body record changed")
    );
    for instance in available
        .keys()
        .filter(|instance| **instance != primitive)
        .take(NICHE_BODIES - 1)
    {
        // These direct record controls grant no Body/type/certificate authority.
        graph
            .insert_body(&mut bounded, *instance, body.clone())
            .unwrap();
    }
    assert_eq!(bounded.len(), NICHE_BODIES);
    let tenth = available
        .keys()
        .find(|instance| !bounded.iter().any(|(key, _)| key == *instance))
        .unwrap();
    assert!(
        graph
            .insert_body(&mut bounded, *tenth, body.clone())
            .is_err()
    );
    assert_eq!(bounded.len(), NICHE_BODIES);
    let mut exhausted = GraphBudget::new(0).unwrap();
    exhausted.work = NICHE_GRAPH_WORK;
    assert!(exhausted.lookup_body(&bounded, primitive).is_err());
    let mut bits = 0;
    mark_niche_block(&mut bits, 128, 0).unwrap();
    mark_niche_block(&mut bits, 128, 127).unwrap();
    assert!(
        mark_niche_block(&mut bits, 128, 0)
            .unwrap_err()
            .contains("cyclic")
    );
    let before = bits;
    for (blocks, index) in [(0, 0), (129, 0), (128, 128), (1, 1)] {
        assert!(mark_niche_block(&mut bits, blocks, index).is_err());
        assert_eq!(bits, before);
    }
    records.push(
        "bounded Vec9 duplicate/replacement/tenth/graph refusal and fixed128 block controls".into(),
    );
    let target = engine(tcx);
    match target.check_niche_comparison_law(original, outer) {
        Ok(mut law) => {
            law.validate(&target).unwrap();
            assert_eq!(law.law_limit, NICHE_ADMISSION_LAW_WORK);
            for wrong in [NICHE_LEGACY_LAW_WORK, NICHE_ADMISSION_LAW_WORK + 1] {
                law.law_limit = wrong;
                assert!(
                    law.validate(&target)
                        .unwrap_err()
                        .contains("policy metadata")
                );
            }
            law.law_limit = NICHE_ADMISSION_LAW_WORK;
            let measured = law.law_work;
            law.law_work = NICHE_ADMISSION_LAW_WORK + 1;
            assert!(
                law.validate(&target)
                    .unwrap_err()
                    .contains("policy metadata")
            );
            law.law_work = measured;
            let measured_graph = law.graph_work;
            law.graph_work = NICHE_GRAPH_WORK + 1;
            assert!(
                law.validate(&target)
                    .unwrap_err()
                    .contains("policy metadata")
            );
            law.graph_work = measured_graph;
            let observed = law.observed;
            law.observed.semantic = usize::MAX;
            law.observed.materialization = 1;
            assert!(
                law.validate(&target)
                    .unwrap_err()
                    .contains("policy metadata")
            );
            law.observed = observed;
            law.validate(&target).unwrap();
            records.push(
                "issued LAW1024 metadata limit/work/graph/observation mutations refused".into(),
            );
            let foreign = engine(tcx);
            foreign.bodies.borrow_mut().extend(
                target
                    .bodies
                    .borrow()
                    .iter()
                    .map(|(instance, body)| (*instance, body.clone())),
            );
            assert!(
                law.validate(&foreign)
                    .unwrap_err()
                    .contains("different live Engine")
            );
            records.push("foreign live Engine with identical cached Rc bodies refused".into());
            let selected = law.bodies[0].0;
            let old = target.bodies.borrow().get(&selected).unwrap().clone();
            target
                .bodies
                .borrow_mut()
                .insert(selected, std::rc::Rc::new((*old).clone()));
            assert!(
                law.validate(&target)
                    .unwrap_err()
                    .contains("replaced or evicted")
            );
            records.push("actual Engine same-key Rc replacement refused".into());
            foreign.bodies.borrow_mut().clear();
            target.bodies.borrow_mut().clear();
            drop(old);
            assert!(law.validate(&target).is_err());
            records.push("actual Engine eviction/expiry refused".into());
        }
        Err(error) => {
            assert!(
                error.contains(&format!("limit={NICHE_GRAPH_WORK}"))
                    || error.contains("512")
                    || error.contains("limit=1024"),
                "unexpected accounted refusal: {error}"
            );
            records.push(format!(
                "no issued law; Engine provenance controls not rerun: {error}"
            ));
        }
    }

    let target = engine(tcx);
    let error = GraphBudget::new(NICHE_GRAPH_WORK - 16).unwrap_err();
    assert!(
        error.contains(&format!("limit={NICHE_GRAPH_WORK}")) || error.contains("expansion bound")
    );
    assert!(target.bodies.borrow().is_empty());
    assert!(target.call_signatures.borrow().is_empty());
    records.push(
        "cumulative near-limit inventory refused before body/signature cache publication".into(),
    );

    let target = engine(tcx);
    let invalid = ty::Instance::new_raw(primitive.def_id(), tcx.mk_args(&[original.into()]));
    let error = target
        .capture_niche_comparison_body(invalid, &mut GraphBudget::new(0).unwrap(), false)
        .unwrap_err();
    assert!(error.contains("argument count mismatch"));
    assert!(target.bodies.borrow().is_empty());
    records.push("wrong full Instance arguments refused before cache publication".into());

    let target = engine(tcx);
    let signature = target.call_poly_signature(payload_eq).unwrap();
    target
        .call_signatures
        .borrow_mut()
        .insert(primitive, signature);
    let error = target
        .capture_niche_comparison_body(primitive, &mut GraphBudget::new(0).unwrap(), false)
        .unwrap_err();
    assert!(error.contains("cached full signature differs"));
    assert!(target.bodies.borrow().is_empty());
    records.push(
        "same-result but wrong original receiver cached signature refused before body clone".into(),
    );

    let target = engine(tcx);
    let valid = target.instantiated_body(primitive).unwrap();
    let mut oversized = (*valid).clone();
    let statement = rustc_middle::mir::Statement::new(
        *oversized.source_info(START_BLOCK.start_location()),
        StatementKind::Nop,
    );
    oversized.basic_blocks.as_mut()[START_BLOCK].statements = vec![statement; 8193];
    target
        .bodies
        .borrow_mut()
        .insert(primitive, std::rc::Rc::new(oversized));
    let error = target
        .capture_niche_comparison_body(primitive, &mut GraphBudget::new(0).unwrap(), false)
        .unwrap_err();
    assert!(error.contains("8192") || error.contains("512 operations"));
    records.push("oversized actual cached body inventory refused before mirror clone".into());

    let target = engine(tcx);
    let valid = target.instantiated_body(primitive).unwrap();
    let mut deep = (*valid).clone();
    let mut original_ref = tcx.types.u16;
    for _ in 0..17 {
        original_ref = Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            original_ref,
            rustc_hir::Mutability::Not,
        );
    }
    deep.local_decls[Local::from_usize(1)].ty = original_ref;
    target
        .bodies
        .borrow_mut()
        .insert(primitive, std::rc::Rc::new(deep));
    let error = target
        .capture_niche_comparison_body(primitive, &mut GraphBudget::new(0).unwrap(), false)
        .unwrap_err();
    assert!(error.contains("expansion bound"));
    records.push("depth17 cached original type refused before mirror clone".into());

    let target = engine(tcx);
    let valid = target.instantiated_body(primitive).unwrap();
    let mut promoted = (*valid).clone();
    promoted.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
    target
        .bodies
        .borrow_mut()
        .insert(primitive, std::rc::Rc::new(promoted));
    assert!(
        target
            .capture_niche_comparison_body(primitive, &mut GraphBudget::new(0).unwrap(), false)
            .unwrap_err()
            .contains("cached body metadata mismatch")
    );
    records.push("cached promoted source refused".into());

    let target = engine(tcx);
    let valid = target.instantiated_body(primitive).unwrap();
    let mut rekeyed = (*valid).clone();
    rekeyed.source.instance = payload_eq.def;
    target
        .bodies
        .borrow_mut()
        .insert(primitive, std::rc::Rc::new(rekeyed));
    assert!(
        target
            .capture_niche_comparison_body(primitive, &mut GraphBudget::new(0).unwrap(), false)
            .unwrap_err()
            .contains("cached body metadata mismatch")
    );
    records.push("cached source full Instance rekey refused".into());

    let target = engine(tcx);
    let schema = certify(tcx, original).unwrap();
    let ty::Adt(option, _) = original.kind() else {
        unreachable!()
    };
    let naked = Ty::new_adt(tcx, *option, tcx.mk_args(&[tcx.types.u16.into()]));
    assert!(
        target
            .check_niche_comparison_law(naked, outer)
            .err()
            .unwrap()
            .contains("payload is not original NonZero")
    );
    assert!(target.bodies.borrow().is_empty());
    records.push("same-width naked original u16 payload refused before cache publication".into());
    let lookalike = tcx
        .hir_crate_items(())
        .free_items()
        .map(|item| item.owner_id.def_id)
        .filter(|id| tcx.def_kind(id.to_def_id()) == DefKind::Enum)
        .find(|id| tcx.item_name(id.to_def_id()).as_str() == "Lookalike")
        .unwrap()
        .to_def_id();
    let local = tcx
        .type_of(lookalike)
        .instantiate_identity()
        .skip_norm_wip();
    assert!(
        target
            .check_niche_comparison_law(local, outer)
            .err()
            .unwrap()
            .contains("only original core Option")
    );
    records.push("genuine local zero-niche lookalike refused".into());

    let target = engine(tcx);
    let wrong = ty::Instance::new_raw(outer.def_id(), tcx.mk_args(&[tcx.types.u16.into()]));
    assert!(
        target
            .check_niche_comparison_law(original, wrong)
            .err()
            .unwrap()
            .contains("outer original element mismatch")
    );
    records.push("wrong original outer contains element refused".into());

    let target = engine(tcx);
    let valid = target.instantiated_body(payload_eq).unwrap();
    let mut swapped = (*valid).clone();
    let mut changed = false;
    for block in swapped.basic_blocks.as_mut() {
        if let TerminatorKind::Call { args, .. } = &mut block.terminator_mut().kind {
            args.swap(0, 1);
            changed = true;
            break;
        }
    }
    assert!(changed);
    target
        .bodies
        .borrow_mut()
        .insert(payload_eq, std::rc::Rc::new(swapped));
    assert!(
        target
            .capture_niche_comparison_body(payload_eq, &mut GraphBudget::new(0).unwrap(), false)
            .unwrap_err()
            .contains("differs from actual compiler body")
    );
    records.push("actual cached delegate argument order mutation refused".into());

    let target = engine(tcx);
    let valid = target.instantiated_body(payload_eq).unwrap();
    let mut cyclic = (*valid).clone();
    for block in cyclic.basic_blocks.as_mut() {
        let span = block.terminator().source_info.span;
        if let TerminatorKind::Call { func, .. } = &mut block.terminator_mut().kind {
            *func = Operand::Constant(Box::new(rustc_middle::mir::ConstOperand {
                span,
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    rustc_middle::mir::ConstValue::ZeroSized,
                    Ty::new_fn_def(tcx, payload_eq.def_id(), ty::Binder::dummy(payload_eq.args)),
                ),
            }));
            break;
        }
    }
    target
        .bodies
        .borrow_mut()
        .insert(payload_eq, std::rc::Rc::new(cyclic));
    assert!(
        target
            .capture_niche_comparison_body(payload_eq, &mut GraphBudget::new(0).unwrap(), false)
            .unwrap_err()
            .contains("differs from actual compiler body")
    );
    records.push("actual cached cyclic delegate mutation refused".into());
    let mut genuine = available
        .keys()
        .copied()
        .filter(|instance| matches!(instance.def, ty::InstanceKind::Item(_)))
        .collect::<Vec<_>>();
    genuine.sort_by_key(|instance| format!("{instance:?}"));
    assert!(genuine.len() >= 10);
    let mut budget = GraphBudget::new(0).unwrap();
    for instance in genuine.iter().take(9) {
        budget.body(*instance).unwrap();
    }
    let target = engine(tcx);
    assert!(
        target
            .capture_niche_comparison_body(genuine[9], &mut budget, false)
            .unwrap_err()
            .contains("exceed nine")
    );
    assert!(target.bodies.borrow().is_empty());
    assert!(target.call_signatures.borrow().is_empty());
    records
        .push("direct preallocation boundary: nine genuine keys; tenth before construction".into());

    let mut budget = GraphBudget::new(0).unwrap();
    for _ in 0..32 {
        budget.encoding(1).unwrap();
    }
    let before = budget.text_reservations;
    assert!(budget.encoding(1).unwrap_err().contains("32 operations"));
    assert_eq!(budget.text_reservations, before);
    records.push("direct encoder boundary32/33: refusal before encoder invocation".into());
    let mut budget = GraphBudget::new(0).unwrap();
    let mut pending = Vec::new();
    pending.try_reserve_exact(32).unwrap();
    for _ in 0..32 {
        budget.pending(&mut pending, primitive, None).unwrap();
    }
    let before = pending.clone();
    assert!(
        budget
            .pending(&mut pending, primitive, None)
            .unwrap_err()
            .contains("exceed32")
    );
    assert_eq!(pending, before);
    records.push("actual pending helper32/33: no append on refusal".into());

    let mut budget = GraphBudget::new(0).unwrap();
    let rest = NICHE_GRAPH_WORK - budget.work;
    budget.charge(rest - 1).unwrap();
    assert_eq!(budget.work, NICHE_GRAPH_WORK - 1);
    budget.charge(1).unwrap();
    assert_eq!(budget.work, NICHE_GRAPH_WORK);
    assert!(
        budget
            .charge(1)
            .unwrap_err()
            .contains(&format!("limit={NICHE_GRAPH_WORK}"))
    );
    records.push(format!(
        "cumulative{}/{}/{} hard bound",
        NICHE_GRAPH_WORK - 1,
        NICHE_GRAPH_WORK,
        NICHE_GRAPH_WORK + 1
    ));

    let target = engine(tcx);
    let existing = engine(tcx).instantiated_body(primitive).unwrap();
    for index in 0..256 {
        let array = Ty::new_array(tcx, tcx.types.u16, index);
        let key = ty::Instance::new_raw(primitive.def_id(), tcx.mk_args(&[array.into()]));
        target.call_signatures.borrow_mut().insert(
            key,
            tcx.fn_sig(primitive.def_id())
                .instantiate_identity()
                .skip_norm_wip(),
        );
        if index < 128 {
            target.bodies.borrow_mut().insert(key, existing.clone());
        }
    }
    let mut budget = GraphBudget::new(0).unwrap();
    assert!(
        target
            .capture_niche_comparison_body(primitive, &mut budget, false)
            .unwrap_err()
            .contains("clear unrelated")
    );
    assert_eq!(target.bodies.borrow().len(), 128);
    assert!(!target.bodies.borrow().contains_key(&primitive));
    assert!(!target.call_signatures.borrow().contains_key(&primitive));
    records.push("full128 body cache refuses miss without clearing unrelated Rc entries".into());
    target.bodies.borrow_mut().clear();
    let mut budget = GraphBudget::new(0).unwrap();
    let captured = target
        .capture_niche_comparison_body(primitive, &mut budget, false)
        .unwrap();
    assert!(!target.call_signatures.borrow().contains_key(&primitive));
    budget
        .phase(GraphPhase::SignatureInstantiate, captured.inventory)
        .unwrap();
    budget
        .phase(GraphPhase::SignatureNormalize, captured.inventory)
        .unwrap();
    target.call_signature(primitive).unwrap();
    assert!(!target.call_signatures.borrow().contains_key(&primitive));
    assert!(budget.phases[GraphPhase::SignatureInstantiate as usize] >= captured.inventory * 2);
    records.push("full256 signature cache: actual getter recomputes; both passes charged".into());
    assert_eq!(schema.facts.size, 2);
    records
}

struct Graph {
    directory: PathBuf,
    checked: bool,
}

impl rustc_driver::Callbacks for Graph {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let root = tcx
            .mir_keys(())
            .iter()
            .copied()
            .find(|id| tcx.item_name(id.to_def_id()).as_str() == "membership")
            .unwrap();
        let body = tcx.optimized_mir(root.to_def_id());
        let original = match body.local_decls[Local::from_usize(1)].ty.kind() {
            ty::Ref(_, slice, _) => match slice.kind() {
                ty::Slice(element) => *element,
                _ => panic!("actual slice"),
            },
            _ => panic!("actual reference"),
        };
        let certificate = certify(tcx, original).unwrap();
        assert_eq!(certificate.bits, u32::from(tcx.sess.target.pointer_width));
        let env = ty::TypingEnv::fully_monomorphized();
        let eq = tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
            .unwrap();
        let args = tcx.mk_args(&[original.into(), original.into()]);
        let ne = tcx
            .associated_items(tcx.parent(eq))
            .in_definition_order()
            .find(|item| item.opt_name() == Some(rustc_span::Symbol::intern("ne")))
            .unwrap()
            .def_id;
        let mut pending = vec![
            ty::Instance::try_resolve(tcx, env, eq, args)
                .unwrap()
                .unwrap(),
            ty::Instance::try_resolve(tcx, env, ne, args)
                .unwrap()
                .unwrap(),
        ];
        for block in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                && let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind()
            {
                pending.push(
                    ty::Instance::try_resolve(tcx, env, *id, args.skip_binder())
                        .unwrap()
                        .unwrap(),
                );
            }
        }
        let mut seen = std::collections::HashSet::new();
        let mut available = std::collections::HashMap::new();
        let mut records = Vec::new();
        while let Some(instance) = pending.pop() {
            if !seen.insert(instance) {
                continue;
            }
            assert!(seen.len() <= 512);
            if !tcx.is_mir_available(instance.def_id()) {
                records.push(format!("{instance:?}: MIR unavailable"));
                continue;
            }
            if tcx.intrinsic(instance.def_id()).is_some() {
                records.push(format!("{instance:?}: actual intrinsic, no instance MIR"));
                continue;
            }
            let raw = tcx.instance_mir(instance.def);
            // This is actual safe-fixture graph research, not a production preclone certificate.
            let encoded =
                super::super::super::pure_comparison_templates::encode_template(tcx, raw, eq.krate);
            std::fs::write(
                self.directory.join(format!("{}-raw.mir", records.len())),
                format!("{raw:#?}"),
            )
            .unwrap();
            let full = full_inventory(tcx, instance, raw);
            let body = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    env,
                    ty::EarlyBinder::bind(tcx, raw.clone()),
                )
                .unwrap();
            std::fs::write(
                self.directory
                    .join(format!("{}-instantiated.mir", records.len())),
                format!("{body:#?}"),
            )
            .unwrap();
            let normalized_inventory = full_inventory(tcx, instance, &body);
            available.insert(instance, std::rc::Rc::new(body.clone()));
            let mut inventory = Inventory::default();
            inventory.visit_body(raw);
            let headers = body.local_decls.len()
                + body.basic_blocks.len()
                + body
                    .basic_blocks
                    .iter()
                    .map(|b| b.statements.len())
                    .sum::<usize>();
            records.push(format!(
                "{instance:?}: headers={headers}; borrowed_lower_bound={}; \
                 full_inventory={full:?}; normalized_inventory={normalized_inventory:?}; \
                 existing_template_encoder={}",
                inventory.work,
                encoded
                    .as_ref()
                    .map(|s| s.len())
                    .map_err(String::as_str)
                    .map_or_else(|error| error.to_owned(), |n| n.to_string()),
            ));
            for block in body.basic_blocks.iter() {
                if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                    && let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind()
                {
                    match ty::Instance::try_resolve(tcx, env, *id, args.skip_binder()) {
                        Ok(Some(child)) => pending.push(child),
                        other => records.push(format!("unresolved {id:?}: {other:?}")),
                    }
                }
            }
        }
        std::fs::write(self.directory.join("graph.txt"), records.join("\n")).unwrap();
        let ty::Adt(_, args) = original.kind() else {
            panic!("actual Option");
        };
        let payload = args.type_at(0);
        let arguments = tcx.mk_args(&[original.into(), original.into()]);
        let eq_instance = ty::Instance::try_resolve(tcx, env, eq, arguments)
            .unwrap()
            .unwrap();
        let ne_instance = ty::Instance::try_resolve(tcx, env, ne, arguments)
            .unwrap()
            .unwrap();
        // Observational pool includes unsupported transport bodies. The interpreter uses
        // separately reserved bounded records and a research graph, without Engine authority.
        let mut research_graph = GraphBudget::new(0).unwrap();
        research_graph.charge(NICHE_BODIES + 1).unwrap();
        let mut bodies = Vec::new();
        bodies.try_reserve_exact(NICHE_BODIES).unwrap();
        for (instance, body) in &available {
            if body.arg_count == 2 && body.return_ty().is_bool() {
                research_graph
                    .insert_body(&mut bodies, *instance, body.clone())
                    .unwrap();
            }
        }
        let mut total = 0;
        let mut traces = Vec::new();
        for left in 0..2 {
            for right in 0..2 {
                for equality in [false, true] {
                    for (selected, negated) in [(eq_instance, false), (ne_instance, true)] {
                        let mut graph = GraphBudget::new(0).unwrap();
                        let mut trace = LawTrace {
                            tcx,
                            engine: None,
                            graph: Some(&mut graph),
                            original,
                            payload,
                            tags: Some([left, right]),
                            equality: if equality { u8::MAX } else { 0 },
                            completed: Vec::new(),
                            bodies: &bodies,
                            work: 0,
                            limit: 16384,
                            observed: LawWork::default(),
                            active: [None; 16],
                        };
                        let values = [0, 1].map(|side| TraceValue::Origin {
                            original,
                            side,
                            refs: 1,
                            variant: None,
                        });
                        let result = trace.call(selected, values, 0).unwrap();
                        let expected = left == right && (left == 0 || equality);
                        assert_eq!(result, if expected ^ negated { u8::MAX } else { 0 });
                        total += trace.work;
                        traces.push(format!(
                            "left={left} right={right} equality={equality} \
                            negated={negated}: result={result}, work={}",
                            trace.work
                        ));
                    }
                }
            }
        }
        traces.push(format!("total independently executed case work={total}"));
        std::fs::write(self.directory.join("law-trace.txt"), traces.join("\n")).unwrap();
        let primitive_args = tcx.mk_args(&[tcx.types.u16.into(), tcx.types.u16.into()]);
        let primitive = ty::Instance::try_resolve(tcx, env, eq, primitive_args)
            .unwrap()
            .unwrap();
        let payload_args = tcx.mk_args(&[payload.into(), payload.into()]);
        let payload_eq = ty::Instance::try_resolve(tcx, env, eq, payload_args)
            .unwrap()
            .unwrap();
        let roots = |original| {
            [0, 1].map(|side| TraceValue::Origin {
                original,
                side,
                refs: 1,
                variant: None,
            })
        };
        // Holding the Engine map mutably proves precharge refusal precedes its lookup.
        let live = engine(tcx);
        for work in [NICHE_GRAPH_WORK - 2, NICHE_GRAPH_WORK - 1, NICHE_GRAPH_WORK] {
            let mut graph = GraphBudget::new(0).unwrap();
            graph.work = work;
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &bodies,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative.engine = Some(&live);
            let held = live.bodies.borrow_mut();
            let error = negative.call(eq_instance, roots(original), 0).unwrap_err();
            assert!(error.contains("phase=LawLiveEngine"), "{error}");
            assert_eq!(negative.work, 1);
            assert_eq!(negative.observed.live_engine, 3);
            drop(negative);
            assert_eq!(graph.work, work + 3);
            assert_eq!(graph.phases[GraphPhase::LawLiveEngine as usize], 3);
            drop(held);
        }
        let mut graph = GraphBudget::new(0).unwrap();
        let mut negative = research_trace(
            tcx,
            original,
            payload,
            &bodies,
            &mut graph,
            NICHE_LEGACY_LAW_WORK,
        );
        negative.engine = Some(&live);
        negative.graph = None;
        let held = live.bodies.borrow_mut();
        assert!(
            negative
                .call(eq_instance, roots(original), 0)
                .unwrap_err()
                .contains("requires the same admission graph")
        );
        drop(held);
        let mut graph = GraphBudget::new(0).unwrap();
        let mut negative = research_trace(
            tcx,
            original,
            payload,
            &bodies,
            &mut graph,
            NICHE_LEGACY_LAW_WORK,
        );
        negative.charge(NICHE_LEGACY_LAW_WORK).unwrap();
        assert!(
            negative
                .charge_materialization(1)
                .unwrap_err()
                .contains("attempted=513")
        );
        drop(negative);
        assert_eq!(graph.phases[GraphPhase::LawLiveEngine as usize], 0);
        std::fs::write(
            self.directory.join("live-engine-budget-controls.txt"),
            "three graph-bound actual entries refused before Engine lookup; \
             missing graph refused before lookup; \
             independent semantic/materialization513 refused\n",
        )
        .unwrap();
        for initial in [1023, 1024, 1025] {
            let mut graph = GraphBudget::new(0).unwrap();
            let mut diagnostic = research_trace(
                tcx,
                original,
                payload,
                &bodies,
                &mut graph,
                NICHE_ADMISSION_LAW_WORK,
            );
            let charged = diagnostic.charge(initial);
            if initial <= NICHE_ADMISSION_LAW_WORK {
                charged.unwrap();
            } else {
                assert!(charged.unwrap_err().contains("attempted=1025"));
            }
        }
        let mut graph = GraphBudget::new(0).unwrap();
        let mut diagnostic = research_trace(
            tcx,
            original,
            payload,
            &bodies,
            &mut graph,
            NICHE_ADMISSION_LAW_WORK,
        );
        diagnostic.charge(1023).unwrap();
        diagnostic.charge_materialization(1).unwrap();
        assert_eq!(diagnostic.work, NICHE_ADMISSION_LAW_WORK);
        assert!(
            diagnostic
                .charge_materialization(1)
                .unwrap_err()
                .contains("attempted=1025")
        );
        drop(diagnostic);
        let mut diagnostic = research_trace(
            tcx,
            original,
            payload,
            &bodies,
            &mut graph,
            NICHE_ADMISSION_LAW_WORK,
        );
        assert!(diagnostic.charge(usize::MAX).is_err());
        assert!(
            diagnostic
                .charge_materialization(1)
                .unwrap_err()
                .contains("overflow")
        );
        drop(diagnostic);
        assert_eq!(graph.phases[GraphPhase::LawLiveEngine as usize], 0);
        std::fs::write(
            self.directory.join("law1024-boundary-controls.txt"),
            "new policy LAW1023/1024 acceptance,1025 refusal and checked overflow; \
             legacy LAW512/513 control remains separate; spare graph unchanged\n",
        )
        .unwrap();
        // Mutation fixtures do not issue Body authority. Both paths enter the interpreter;
        // the repeated block is refused before any repeated statements are evaluated.
        let primitive_body = research_graph
            .lookup_body(&bodies, primitive)
            .unwrap()
            .unwrap();
        let mut self_cycle = (**primitive_body).clone();
        self_cycle.basic_blocks.as_mut()[START_BLOCK]
            .terminator_mut()
            .kind = TerminatorKind::Goto {
            target: START_BLOCK,
        };
        let mut multi_cycle = self_cycle.clone();
        let mut second = multi_cycle.basic_blocks[START_BLOCK].clone();
        second.statements.clear();
        let second_index = multi_cycle.basic_blocks.as_mut().push(second);
        multi_cycle.basic_blocks.as_mut()[START_BLOCK]
            .terminator_mut()
            .kind = TerminatorKind::Goto {
            target: second_index,
        };
        let mut cycle_work = Vec::new();
        for changed in [self_cycle, multi_cycle] {
            let mut graph = GraphBudget::new(0).unwrap();
            graph.charge(NICHE_BODIES + 1).unwrap();
            let mut selected = Vec::new();
            selected.try_reserve_exact(NICHE_BODIES).unwrap();
            graph
                .insert_body(&mut selected, primitive, std::rc::Rc::new(changed))
                .unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &selected,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            assert!(
                negative
                    .call(primitive, roots(tcx.types.u16), 0)
                    .unwrap_err()
                    .contains("cyclic selected path")
            );
            cycle_work.push(negative.work);
        }
        // Empty second block pays loop1 + bitset4 + terminator1, without repeated statements.
        assert_eq!(cycle_work[1] - cycle_work[0], 6);
        std::fs::write(
            self.directory.join("interpreter-cycle-controls.txt"),
            format!(
                "actual interpreter self/multiblock cycles refused before repeated execution; \
             work={cycle_work:?}\n"
            ),
        )
        .unwrap();
        let composed_observation = (|| -> Result<(), String> {
            let mut graph = GraphBudget::new(0).unwrap();
            let mut composed = LawTrace {
                tcx,
                engine: None,
                graph: Some(&mut graph),
                original,
                payload,
                tags: None,
                equality: 0xaa,
                completed: Vec::new(),
                bodies: &bodies,
                work: 0,
                limit: NICHE_LEGACY_LAW_WORK,
                observed: LawWork::default(),
                active: [None; 16],
            };
            let roots = |original| {
                [0, 1].map(|side| TraceValue::Origin {
                    original,
                    side,
                    refs: 1,
                    variant: None,
                })
            };
            let primitive_relation = composed
                .call(primitive, roots(tcx.types.u16), 0)
                .map_err(|error| composed.failure(error))?;
            assert_eq!(primitive_relation, 0xaa);
            composed
                .charge(1)
                .map_err(|error| composed.failure(error))?;
            composed
                .charge_materialization(4)
                .map_err(|error| composed.failure(error))?;
            composed
                .completed
                .try_reserve_exact(1)
                .map_err(|_| "research completed record allocation failed")?;
            composed.completed.push(CompletedTrace {
                instance: primitive,
                original: tcx.types.u16,
                relation: primitive_relation,
                body: std::rc::Rc::downgrade(
                    composed
                        .graph
                        .as_deref_mut()
                        .unwrap()
                        .lookup_body(&bodies, primitive)?
                        .ok_or("research completed body unavailable")?,
                ),
            });
            let primitive_work = composed.work;
            let payload_relation = composed
                .call(payload_eq, roots(payload), 0)
                .map_err(|error| composed.failure(error))?;
            assert_eq!(payload_relation, 0xaa);
            composed
                .charge(1)
                .map_err(|error| composed.failure(error))?;
            composed
                .charge_materialization(4)
                .map_err(|error| composed.failure(error))?;
            composed
                .completed
                .try_reserve_exact(1)
                .map_err(|_| "research completed record allocation failed")?;
            composed.completed.push(CompletedTrace {
                instance: payload_eq,
                original: payload,
                relation: payload_relation,
                body: std::rc::Rc::downgrade(
                    composed
                        .graph
                        .as_deref_mut()
                        .unwrap()
                        .lookup_body(&bodies, payload_eq)?
                        .ok_or("research completed body unavailable")?,
                ),
            });
            let payload_work = composed.work - primitive_work;
            let before_option = composed.work;
            let mut option_relation = 0;
            for left in 0..2 {
                for right in 0..2 {
                    composed.tags = Some([left, right]);
                    let relation = composed
                        .call(eq_instance, roots(original), 0)
                        .map_err(|error| composed.failure(error))?;
                    let expected = if left != right {
                        0
                    } else if left == 0 {
                        0xff
                    } else {
                        0xaa
                    };
                    assert_eq!(relation, expected);
                    option_relation |= relation & (3 << (2 * (2 * left + right)));
                }
            }
            assert_eq!(option_relation, 0x83);
            let option_work = composed.work - before_option;
            composed
                .charge(1)
                .map_err(|error| composed.failure(error))?;
            composed
                .charge_materialization(4)
                .map_err(|error| composed.failure(error))?;
            composed
                .completed
                .try_reserve_exact(1)
                .map_err(|_| "research completed record allocation failed")?;
            composed.completed.push(CompletedTrace {
                instance: eq_instance,
                original,
                relation: option_relation,
                body: std::rc::Rc::downgrade(
                    composed
                        .graph
                        .as_deref_mut()
                        .unwrap()
                        .lookup_body(&bodies, eq_instance)?
                        .ok_or("research completed body unavailable")?,
                ),
            });
            composed.tags = None;
            let before_ne = composed.work;
            let ne_relation = composed
                .call(ne_instance, roots(original), 0)
                .map_err(|error| composed.failure(error))?;
            assert_eq!(ne_relation, !option_relation);
            let ne_work = composed.work - before_ne;
            std::fs::write(
                self.directory.join("composed-law-trace.txt"),
                format!(
                    "research only; no issued certificate\nprimitive={primitive_work}\n\
                 payload={payload_work}\noption={option_work}\nne={}\ntotal={}\nlaw512_fits={}\n",
                    ne_work,
                    composed.work,
                    composed.work <= 512,
                ),
            )
            .unwrap();
            let option_body = composed
                .graph
                .as_deref_mut()
                .unwrap()
                .lookup_body(&bodies, eq_instance)?
                .ok_or("research Option body unavailable")?;
            let make_proof = |body| CompletedTrace {
                instance: eq_instance,
                original,
                relation: option_relation,
                body,
            };
            let mut graph = GraphBudget::new(0).unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &bodies,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative
                .completed
                .push(make_proof(std::rc::Rc::downgrade(option_body)));
            let mut wrong_sides = roots(original);
            wrong_sides[1] = wrong_sides[0];
            assert!(
                negative
                    .call(eq_instance, wrong_sides, 0)
                    .unwrap_err()
                    .contains("receiver mapping mismatch")
            );
            let mut replaced = bodies.clone();
            replaced
                .iter_mut()
                .find(|(instance, _)| *instance == eq_instance)
                .unwrap()
                .1 = std::rc::Rc::new((**option_body).clone());
            let mut graph = GraphBudget::new(0).unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &replaced,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative
                .completed
                .push(make_proof(std::rc::Rc::downgrade(option_body)));
            assert!(
                negative
                    .call(eq_instance, roots(original), 0)
                    .unwrap_err()
                    .contains("body was replaced")
            );
            let expired = {
                let body = std::rc::Rc::new((**option_body).clone());
                std::rc::Rc::downgrade(&body)
            };
            let mut graph = GraphBudget::new(0).unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &bodies,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative.completed.push(make_proof(expired));
            assert!(
                negative
                    .call(eq_instance, roots(original), 0)
                    .unwrap_err()
                    .contains("witness expired")
            );
            let mut missing = bodies.clone();
            missing.retain(|(instance, _)| *instance != eq_instance);
            let mut graph = GraphBudget::new(0).unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &missing,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative
                .completed
                .push(make_proof(std::rc::Rc::downgrade(option_body)));
            assert!(
                negative
                    .call(eq_instance, roots(original), 0)
                    .unwrap_err()
                    .contains("body unavailable")
            );
            let mut graph = GraphBudget::new(0).unwrap();
            let mut negative = research_trace(
                tcx,
                original,
                payload,
                &bodies,
                &mut graph,
                NICHE_LEGACY_LAW_WORK,
            );
            negative
                .completed
                .push(make_proof(std::rc::Rc::downgrade(option_body)));
            negative.work = 511;
            assert!(
                negative
                    .call(eq_instance, roots(original), 0)
                    .unwrap_err()
                    .contains("cumulative work limit exceeded")
            );
            std::fs::write(
                self.directory.join("witness-negative-controls.txt"),
                "five actual-body controls rejected: side mapping, replaced Rc, expired weak, \
                 missing body, cumulative work513\n",
            )
            .unwrap();
            Ok(())
        })();
        if let Err(error) = composed_observation {
            assert!(
                error.contains("512") || error.contains(&format!("limit={NICHE_GRAPH_WORK}")),
                "{error}"
            );
            std::fs::write(
                self.directory.join("composed-law-resource.txt"),
                format!(
                    "research composed schedule refused: {error}; \
                 its subsequent research witness controls were not rerun\n"
                ),
            )
            .unwrap();
        }
        let actual_engine = engine(tcx);
        let key = |instance: &&ty::Instance<'tcx>| {
            super::super::super::pure_comparison_templates::definition_key(instance.def_id())
        };
        let outer = available
            .keys()
            .find(|instance| key(instance) == "DefId(core::slice::{impl#0}::contains)")
            .or_else(|| {
                available.keys().find(|instance| {
                    key(instance) == "DefId(core::slice::cmp::{impl#18}::slice_contains)"
                })
            })
            .copied()
            .expect("actual root selected contains transport");
        let actual = actual_engine.check_niche_comparison_law(original, outer);
        std::fs::write(
            self.directory.join("engine-certificate.txt"),
            match actual {
                Ok(law) => {
                    assert_eq!(law.original, original);
                    assert_eq!(law.relation, 0x83);
                    law.validate(&actual_engine).unwrap();
                    format!(
                        "actual Engine certificate: graph={} law={} bodies={} \
                         policy_limit={} observed={:?}\n",
                        law.graph_work,
                        law.law_work,
                        law.bodies.len(),
                        law.law_limit,
                        law.observed
                    )
                }
                Err(error) => {
                    let graph_limit = error.contains(&format!("limit={NICHE_GRAPH_WORK}"));
                    assert!(
                        graph_limit || error.contains("512") || error.contains("limit=1024"),
                        "unexpected private certificate refusal: {error}"
                    );
                    format!("actual private Engine attempt refused: {error}\n")
                }
            },
        )
        .unwrap();
        let warmed = engine(tcx);
        warmed.instantiated_body(outer).unwrap();
        let warmed_result = match warmed.check_niche_comparison_law(original, outer) {
            Ok(law) => {
                law.validate(&warmed).unwrap();
                format!(
                    "pre-existing actual outer cache: graph={} law={} bodies={} \
                     policy_limit={} observed={:?}\n",
                    law.graph_work,
                    law.law_work,
                    law.bodies.len(),
                    law.law_limit,
                    law.observed
                )
            }
            Err(error) => {
                assert!(
                    error.contains(&format!("limit={NICHE_GRAPH_WORK}"))
                        || error.contains("512")
                        || error.contains("limit=1024"),
                    "unexpected warmed-cache refusal: {error}"
                );
                format!("pre-existing actual outer cache refused: {error}\n")
            }
        };
        std::fs::write(
            self.directory.join("engine-warmed-certificate.txt"),
            warmed_result,
        )
        .unwrap();
        let controls = engine_controls(tcx, original, outer, primitive, payload_eq, &available);
        std::fs::write(
            self.directory.join("engine-negative-controls.txt"),
            controls.join("\n"),
        )
        .unwrap();
        self.checked = true;
        rustc_driver::Compilation::Stop
    }
}

#[test]
fn actual_niche_membership_graph() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = PathBuf::from(format!(
        "/tmp/miren-nonzero-niche-membership/compiler-{}-{nonce}",
        std::process::id(),
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("guest.rs");
    std::fs::write(
        &source,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
         pub fn membership(values: &[Option<core::num::NonZeroU16>],\n\
         needle: Option<core::num::NonZeroU16>) -> bool { values.contains(&needle) }\n\
         #[derive(Clone, Copy)] pub enum Lookalike { None, Some(core::num::NonZeroU16) }\n",
    )
    .unwrap();
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in [0, 2] {
            let profile = directory.join(format!("{}-{opt}", target.unwrap_or("host")));
            std::fs::create_dir(&profile).unwrap();
            let mut args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={opt}"),
                "--sysroot".into(),
                sysroot.trim().into(),
                "--out-dir".into(),
                profile.to_str().unwrap().into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            let mut graph = Graph {
                directory: profile,
                checked: false,
            };
            rustc_driver::run_compiler(&args, &mut graph);
            assert!(graph.checked);
        }
    }
    eprintln!("actual niche membership graph: {}", directory.display());
}

fn public_application_controls<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    outer: ty::Instance<'tcx>,
) {
    let mut target = engine(tcx);
    let mut conditions = Vec::new();
    let slice = target
        .composite_slice_input(outer.def_id(), original, &mut conditions)
        .unwrap();
    let law = target.check_niche_comparison_law(original, outer).unwrap();
    let schema = law.membership_schema.clone();
    drop(law);
    let none = Value::Adt {
        name: schema.name.clone(),
        variant: 0,
        is_option: true,
        discriminant: 0,
        fields: Vec::new().into(),
    };
    let some = |raw: Value| Value::Adt {
        name: schema.name.clone(),
        variant: 1,
        is_option: true,
        discriminant: 1,
        fields: vec![(
            schema.payload_field.clone(),
            Value::Adt {
                name: schema.outer_name.clone(),
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields: vec![(
                    schema.outer_field.clone(),
                    Value::Adt {
                        name: schema.inner_name.clone(),
                        variant: 0,
                        is_option: false,
                        discriminant: 0,
                        fields: vec![(schema.inner_field.clone(), raw)].into(),
                    },
                )]
                .into(),
            },
        )]
        .into(),
    };
    let some_one = some(symbolic::integer(&target.terms, 1, 16, false));
    let some_zero = some(symbolic::integer(&target.terms, 0, 16, false));
    let symbolic = |tag: u128, payload: Value| Value::Enum {
        discriminant: Box::new(symbolic::integer(
            &target.terms,
            tag,
            schema.bits,
            schema.signed,
        )),
        variants: vec![none.clone(), payload],
        is_option: true,
    };
    let inactive_zero = symbolic(0, some_zero.clone());
    let active_zero = symbolic(1, some_zero);
    let symbolic_one = symbolic(1, some_one.clone());
    let Value::CompositeSlice { length, leaves, .. } = &slice else {
        unreachable!()
    };
    let bits = u32::from(tcx.sess.target.pointer_width);
    let first = target
        .terms
        .apply(
            Op::Select,
            &[leaves[0].clone(), target.terms.bit_vector(0, bits).unwrap()],
        )
        .unwrap();
    conditions.push(
        target
            .terms
            .apply(
                Op::Equal,
                &[
                    length.integer().unwrap().0,
                    target.terms.bit_vector(1, bits).unwrap(),
                ],
            )
            .unwrap(),
    );
    let state = State {
        flow: super::super::super::activation_flow::Flow::Unarmed,
        locals: Vec::new(),
        missing_places: Default::default(),
        conditions,
        addresses: Vec::new(),
        memory: Default::default(),
    };
    // All three positive domains are synthetic compiler controls, not guest Proof assumptions.
    for (label, needle, expected_raw) in [
        ("None", &none, 0),
        ("Some", &some_one, 1),
        ("symbolic Some", &symbolic_one, 1),
        ("inactive Some zero", &inactive_zero, 0),
    ] {
        let mut current = state.clone();
        current.conditions.push(
            target
                .terms
                .apply(
                    Op::Equal,
                    &[
                        first.clone(),
                        target.terms.bit_vector(expected_raw, 16).unwrap(),
                    ],
                )
                .unwrap(),
        );
        let before = current.conditions.clone();
        let mut actual = target.check_niche_comparison_law(original, outer).unwrap();
        let start = actual.graph_work;
        eprintln!(
            "public niche start {label}: graph={start} law={} application_limit={}",
            actual.law_work, NICHE_APPLICATION_WORK
        );
        let result = target.apply_niche_membership(&mut actual, &slice, needle, &current);
        match result {
            Ok(member) => {
                assert!(
                    !target
                        .feasible(
                            &[
                                current.conditions.as_slice(),
                                &[target.terms.apply(Op::Not, &[member]).unwrap()]
                            ]
                            .concat()
                        )
                        .unwrap()
                );
                eprintln!(
                    "public niche {label}: complete positive after graph={start}; no premise added"
                );
            }
            Err(error) => {
                // Source outcomes remain unmeasured. A real accounting refusal is reported
                // honestly, never relabeled validity or successful membership.
                assert!(
                    error.starts_with("niche application exceeds NICHE_APPLICATION_WORK policy:"),
                    "{error}"
                );
                eprintln!(
                    "public niche {label}: honest Resource before successful application: {error}"
                );
            }
        }
        assert_eq!(current.conditions, before);
        assert!(actual.application.is_none());
        assert!(
            target
                .apply_niche_membership(&mut actual, &slice, needle, &current)
                .unwrap_err()
                .contains("already consumed")
        );
    }
    let mut actual = target.check_niche_comparison_law(original, outer).unwrap();
    actual.application.as_mut().unwrap().work = NICHE_GRAPH_WORK;
    actual.graph_work = NICHE_GRAPH_WORK;
    assert!(
        target
            .apply_niche_membership(&mut actual, &slice, &none, &state)
            .is_err()
    );
    assert!(actual.application.is_none());
    let mut application = MembershipApplication {
        graph: GraphBudget::new(0).unwrap(),
        work: 0,
    };
    application.charge(NICHE_APPLICATION_WORK - 1).unwrap();
    assert_eq!(application.work, NICHE_APPLICATION_WORK - 1);
    application.charge(1).unwrap();
    assert_eq!(application.work, NICHE_APPLICATION_WORK);
    let paid_graph = application.graph.work;
    assert!(
        application
            .charge(1)
            .unwrap_err()
            .contains(&format!("attempted={}", NICHE_APPLICATION_WORK + 1))
    );
    assert_eq!(application.graph.work, paid_graph);
    // Real public mask and condition services, not just a standalone counter boundary.
    let mut application = MembershipApplication {
        graph: GraphBudget::new(0).unwrap(),
        work: 0,
    };
    let mut many = state.clone();
    many.conditions = vec![target.terms.boolean(true); NICHE_APPLICATION_WORK];
    assert!(
        target
            .niche_memory_clone_service(&mut application, &many)
            .is_err()
    );
    assert!(
        target
            .checked_niche_membership(original, outer, &slice, &none, &many)
            .unwrap_err()
            .starts_with("niche application exceeds NICHE_APPLICATION_WORK policy:")
    );
    let mut application = MembershipApplication {
        graph: GraphBudget::new(0).unwrap(),
        work: 0,
    };
    let mut masks = state.clone();
    for owner in 0..super::super::super::MAX_INPUT_VALUES {
        masks
            .memory
            .missing_places
            .consume(owner, Vec::new())
            .unwrap();
    }
    assert!(
        target
            .niche_memory_clone_service(&mut application, &masks)
            .is_err()
    );
    assert!(
        target
            .checked_niche_membership(original, outer, &slice, &none, &masks)
            .unwrap_err()
            .starts_with("niche application exceeds NICHE_APPLICATION_WORK policy:")
    );
    for fault in 0..3 {
        let changed = target.test_niche_descriptor_fault(&slice, fault);
        assert!(
            target
                .checked_niche_membership(original, outer, &changed, &none, &state)
                .is_err()
        );
    }
    let mut foreign = slice.clone();
    let Value::CompositeSlice { leaves, .. } = &mut foreign else {
        unreachable!()
    };
    let other = Context::default();
    leaves[0] = other.symbol(0, leaves[0].sort().clone()).unwrap();
    assert!(
        target
            .checked_niche_membership(original, outer, &foreign, &none, &state)
            .is_err()
    );
    let schema = &schema;
    let mut application = MembershipApplication {
        graph: GraphBudget::new(0).unwrap(),
        work: 0,
    };
    let parsed = target
        .parse_niche_needle(&mut application, schema, &active_zero)
        .unwrap();
    assert!(
        target
            .encode_niche_needle(&mut application, schema, parsed, &state.conditions)
            .unwrap_err()
            .contains("active Some lacks proved nonzero validity")
    );
    let mut invalid_tag = inactive_zero.clone();
    let Value::Enum { discriminant, .. } = &mut invalid_tag else {
        unreachable!()
    };
    **discriminant = symbolic::integer(&target.terms, 2, schema.bits, schema.signed);
    let mut application = MembershipApplication {
        graph: GraphBudget::new(0).unwrap(),
        work: 0,
    };
    let parsed = target
        .parse_niche_needle(&mut application, schema, &invalid_tag)
        .unwrap();
    assert!(
        target
            .encode_niche_needle(&mut application, schema, parsed, &state.conditions)
            .unwrap_err()
            .contains("symbolic tag lacks proved validity")
    );
    assert_eq!(state.conditions.len(), 2);
    eprintln!(
        "public niche actual application handoff/reuse/exhaustion/masks/conditions/\
         descriptor/context/tag controls"
    );
}
