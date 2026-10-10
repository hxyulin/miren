use super::*;
use initialized_places::Step;
use rustc_span::Symbol;
use symbolic::MemoryProjection;

struct Observation<'a> {
    memory: &'a Memory,
    conditions: &'a [Term],
    nodes: std::cell::Cell<usize>,
    detached: bool,
    incoming: Option<usize>,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn typed_coroutine_snapshots(
        &self,
        types: &[Ty<'tcx>],
        values: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Vec<Value>, String> {
        if types.len() != values.len() {
            return self.snapshots(values, memory, conditions);
        }
        let observation = Observation {
            memory,
            conditions,
            nodes: Default::default(),
            detached: true,
            incoming: None,
        };
        types
            .iter()
            .zip(values)
            .map(|(ty, value)| self.coroutine_snapshot(*ty, value, &observation, None, 0))
            .collect()
    }

    pub(super) fn validate_coroutine_transport_return(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        state: &State,
        incoming: usize,
    ) -> Result<bool, String> {
        self.validate_coroutine_reference_transport(original, value, state, Some(incoming))
    }

    pub(super) fn validate_coroutine_reference_transport(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        state: &State,
        incoming: Option<usize>,
    ) -> Result<bool, String> {
        if !self.coroutine_reference_carrier_type(original, 0) {
            return Ok(false);
        }
        let observation = Observation {
            memory: &state.memory,
            conditions: &state.conditions,
            nodes: Default::default(),
            detached: false,
            incoming,
        };
        let checked = self.coroutine_snapshot(original, value, &observation, None, 0)?;
        Self::validate_reference_graph(&checked, state, incoming, &mut Vec::new())?;
        self.validate_static_initialization_graph(&checked, state, &mut Vec::new())?;
        Ok(true)
    }

    fn pin_macro_coroutine_helper(&self, original: Ty<'tcx>) -> bool {
        let ty::Adt(def, args) = original.kind() else {
            return false;
        };
        let Some(pin) = self.tcx.lang_items().get(LangItem::Pin) else {
            return false;
        };
        if def.did().krate != pin.krate
            || !self
                .tcx
                .is_diagnostic_item(Symbol::intern("PinMacroHelper"), def.did())
            || !def.is_struct()
            || def.has_dtor(self.tcx)
            || def.non_enum_variant().fields.len() != 1
        {
            return false;
        }
        let field = &def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)];
        field.name.as_str() == "value" && field.ty(self.tcx, args).skip_norm_wip().is_coroutine()
    }

    fn coroutine_reference_carrier_type(&self, original: Ty<'tcx>, depth: usize) -> bool {
        if depth >= MAX_INPUT_DEPTH {
            return false;
        }
        match original.kind() {
            ty::Ref(_, target, _) => {
                matches!(target.kind(), ty::Coroutine(..))
                    || self.pin_macro_coroutine_helper(*target)
                    || self.coroutine_reference_carrier_type(*target, depth + 1)
            }
            ty::Adt(def, args) if self.tcx.lang_items().get(LangItem::Pin) == Some(def.did()) => {
                self.coroutine_reference_carrier_type(args.type_at(0), depth + 1)
            }
            _ => false,
        }
    }

    pub(super) fn borrow_coroutine_carrier(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        mutable: bool,
    ) -> Result<Option<Value>, String> {
        let original = place.ty(&body.local_decls, self.tcx).ty;
        if !original.is_coroutine() && !self.pin_macro_coroutine_helper(original) {
            return Ok(None);
        }
        let (allocation, path, writable) = self
            .memory_path(state, place)
            .map_err(|reason| format!("coroutine carrier storage resolution: {reason}"))?;
        let Some(allocation) = allocation else {
            return Ok(None);
        };
        if mutable && !writable {
            return Err("coroutine receiver reborrow lacks original writable storage".into());
        }
        let reference = Value::Reference {
            allocation,
            projection: path.clone(),
            mutable,
        };
        let value = self.reference_storage(&reference, &state.memory, &state.conditions)?;
        let observation = Observation {
            memory: &state.memory,
            conditions: &state.conditions,
            nodes: Default::default(),
            detached: false,
            incoming: None,
        };
        let active = self
            .coroutine_snapshot(original, &value, &observation, Some((allocation, path)), 0)
            .map_err(|reason| format!("coroutine active carrier observation: {reason}"))?;
        Self::validate_reference_graph(&active, state, None, &mut Vec::new())?;
        self.validate_static_initialization_graph(&active, state, &mut Vec::new())?;
        Ok(Some(reference))
    }

    fn coroutine_snapshot(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        observation: &Observation<'_>,
        source: Option<(usize, Vec<MemoryProjection>)>,
        depth: usize,
    ) -> Result<Value, String> {
        let memory = observation.memory;
        let conditions = observation.conditions;
        let nodes = observation
            .nodes
            .get()
            .checked_add(1)
            .ok_or("coroutine observation node count overflow")?;
        if nodes > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "coroutine observation exceeds its 512-node budget".into(),
            ));
        }
        observation.nodes.set(nodes);
        if depth >= MAX_INPUT_DEPTH {
            return Err("typed coroutine snapshot exceeds depth16".into());
        }
        if !original
            .walk()
            .any(|arg| arg.as_type().is_some_and(|ty| ty.is_coroutine()))
        {
            if let Some((allocation, path)) = &source {
                memory.check_projection_initialization(*allocation, path)?;
            }
            return if observation.detached {
                self.snapshot(value, memory, conditions, depth)
            } else {
                Ok(value.clone())
            };
        }
        if !original.is_coroutine()
            && !self.coroutine_reference_carrier_type(original, 0)
            && !self.pin_macro_coroutine_helper(original)
        {
            if let Some((allocation, path)) = &source {
                memory.check_projection_initialization(*allocation, path)?;
            }
            return if observation.detached {
                self.snapshot(value, memory, conditions, depth)
            } else {
                Err("coroutine transport uses an unsupported compiler wrapper".into())
            };
        }
        match (original.kind(), value) {
            (
                ty::Ref(_, pointee, permission),
                Value::Reference {
                    allocation,
                    projection,
                    mutable,
                },
            ) => {
                if let Some((owner, path)) = &source {
                    memory.check_projection_initialization(*owner, path)?;
                }
                if permission.is_mut() && !*mutable {
                    return Err("coroutine snapshot receiver lacks original mutable rights".into());
                }
                if observation
                    .incoming
                    .is_some_and(|incoming| *allocation >= incoming)
                {
                    return Err(self.categorized_error(
                        UnknownCategory::Semantics,
                        "reference to frame-owned storage cannot escape its frame".into(),
                    ));
                }
                let fields = initialized_places::field_footprint(projection)
                    .ok_or("coroutine snapshot requires exact retained field path")?;
                memory.missing_places.descendants(*allocation, &fields)?;
                let stored = self.reference_storage(value, memory, conditions)?;
                self.coroutine_snapshot(
                    *pointee,
                    &stored,
                    observation,
                    Some((*allocation, projection.clone())),
                    depth + 1,
                )
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
            ) if self.tcx.lang_items().get(LangItem::Pin) == Some(def.did())
                || self.pin_macro_coroutine_helper(original) =>
            {
                let declared = &def.non_enum_variant().fields;
                if *name != self.tcx.def_path_str(def.did())
                    || *variant != 0
                    || *is_option
                    || *discriminant != 0
                    || fields.len() != declared.len()
                {
                    return Err("coroutine Pin snapshot differs from compiler wrapper".into());
                }
                let mut detached = Vec::new();
                for (index, (field, (name, value))) in declared.iter().zip(fields).enumerate() {
                    if *name != field.name.to_string() {
                        return Err(
                            "coroutine Pin snapshot field differs from compiler declaration".into(),
                        );
                    }
                    let field_source = source.as_ref().map(|(allocation, path)| {
                        let mut path = path.clone();
                        path.push(MemoryProjection::Field(index));
                        (*allocation, path)
                    });
                    detached.push((
                        name.clone(),
                        self.coroutine_snapshot(
                            field.ty(self.tcx, args).skip_norm_wip(),
                            value,
                            observation,
                            field_source,
                            depth + 1,
                        )?,
                    ));
                }
                Ok(Value::Adt {
                    name: name.clone(),
                    variant: *variant,
                    is_option: *is_option,
                    discriminant: *discriminant,
                    fields: detached.into(),
                })
            }
            (
                ty::Coroutine(id, args),
                Value::Adt {
                    name,
                    variant,
                    is_option,
                    discriminant,
                    fields,
                },
            ) => {
                let layout = self
                    .tcx
                    .coroutine_layout(*id, args)
                    .map_err(|error| format!("coroutine snapshot layout unavailable: {error:?}"))?;
                let captures = args.as_coroutine().upvar_tys();
                if fields.len() > MAX_INPUT_VALUES
                    || *name != coroutines::coroutine_name(*id, args)
                    || *is_option
                    || *variant >= layout.variant_fields.len()
                    || *discriminant != *variant as u128
                    || fields.len() != captures.len() + layout.field_tys.len()
                {
                    return Err(
                        "coroutine snapshot differs from exact compiler state schema".into(),
                    );
                }
                let holes = if let Some((allocation, path)) = &source {
                    let path = initialized_places::field_footprint(path)
                        .ok_or("coroutine snapshot has unsupported original storage path")?;
                    memory.missing_places.descendants(*allocation, &path)?
                } else {
                    Vec::new()
                };
                let required = &layout.variant_fields[rustc_abi::VariantIdx::from_usize(*variant)];
                let mut detached = Vec::new();
                for (index, (field_name, child)) in fields.iter().enumerate() {
                    let expected_name = if index < captures.len() {
                        index.to_string()
                    } else {
                        format!("saved_{}", index - captures.len())
                    };
                    if *field_name != expected_name {
                        return Err(
                            "coroutine snapshot field order differs from original layout".into(),
                        );
                    }
                    let active = if index < captures.len() {
                        *variant == 0
                    } else {
                        required
                            .iter()
                            .any(|saved| captures.len() + saved.as_usize() == index)
                    };
                    let consumed = holes
                        .iter()
                        .any(|hole| hole.first() == Some(&Step::Field(index)));
                    if !active && consumed {
                        detached.push((field_name.clone(), Value::Uninitialized));
                        continue;
                    }
                    if active && matches!(child, Value::Uninitialized) {
                        return Err("coroutine snapshot active field is uninitialized".into());
                    }
                    let child_ty = if index < captures.len() {
                        captures[index]
                    } else {
                        layout.field_tys[rustc_middle::mir::CoroutineSavedLocal::from_usize(
                            index - captures.len(),
                        )]
                        .ty
                    };
                    let child_source = source.as_ref().map(|(allocation, path)| {
                        let mut path = path.clone();
                        path.push(MemoryProjection::Field(index));
                        (*allocation, path)
                    });
                    let detached_child = if matches!(child, Value::Uninitialized) {
                        Value::Uninitialized
                    } else {
                        self.coroutine_snapshot(
                            child_ty,
                            child,
                            observation,
                            child_source,
                            depth + 1,
                        )?
                    };
                    detached.push((field_name.clone(), detached_child));
                }
                Ok(Value::Adt {
                    name: name.clone(),
                    variant: *variant,
                    is_option: *is_option,
                    discriminant: *discriminant,
                    fields: detached.into(),
                })
            }
            _ => Err("coroutine observation differs from its original reference carrier".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_observer_checks_consumed_handles_active_fields_and_wrapper_identity() {
        struct Check(bool);
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                let limits = miren::AnalysisLimits::default();
                let all_failures = false;
                let induction = false;
                let startup = false;
                let isolated_startup = false;
                let async_entry = false;
                let engine = Engine {
                    tcx,
                    terms: Context::default(),
                    next_symbol: std::cell::Cell::new(0),
                    float_encodings: BTreeMap::new(),
                    float_pairs: super::float_pairs::Registry::default(),
                    abstraction_symbols: std::cell::RefCell::new(BTreeMap::new()),
                    static_views: std::cell::RefCell::new(Vec::new()),
                    static_origins: Default::default(),
                    static_epoch: None,
                    static_roots: None,
                    function_pointers: std::cell::RefCell::new(Vec::new()),
                    static_addresses: std::collections::HashMap::new(),
                    tracked_addresses: Vec::new(),
                    maybe_uninit_types: Vec::new(),
                    owned_box_types: Vec::new(),
                    next_owned_region: 0,
                    owned_box_constructors: Vec::new(),
                    scalar_slice_types: Vec::new(),
                    composite_slice_types: Vec::new(),
                    steps: 0,
                    call_chain: Vec::new(),
                    failed_call_chain: None,
                    trait_objects: Vec::new(),
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
                };

                let factory = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == "factory"
                    })
                    .unwrap();
                let cached = std::rc::Rc::new(tcx.optimized_mir(factory).clone());
                let key = std::rc::Rc::downgrade(&cached);
                assert!(coroutines::matches_body(&key, &cached));
                let distinct = std::rc::Rc::new((*cached).clone());
                assert!(!coroutines::matches_body(&key, &distinct));
                let active = cached.clone();
                drop(cached);
                assert!(coroutines::matches_body(&key, &active));
                drop(active);
                assert!(!coroutines::matches_body(&key, &distinct));
                let original = tcx.optimized_mir(factory).return_ty();
                let ty::Coroutine(id, args) = original.kind() else {
                    panic!("coroutine");
                };
                let layout = tcx.coroutine_layout(*id, args).unwrap();
                let captures = args.as_coroutine().upvar_tys();
                assert_eq!(captures.len(), 1);
                assert_eq!(captures[0], tcx.types.u16);
                let field = Value::Int {
                    expression: engine.terms.bit_vector(19, 16).unwrap(),
                    bits: 16,
                    signed: false,
                };
                let mut fields = vec![("0".to_owned(), field)];
                fields.extend(layout.field_tys.iter_enumerated().map(|(saved, _)| {
                    (format!("saved_{}", saved.as_usize()), Value::Uninitialized)
                }));
                let future = Value::Adt {
                    name: coroutines::coroutine_name(*id, args),
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: fields.into(),
                };
                let reference = Value::Reference {
                    allocation: 1,
                    projection: Vec::new(),
                    mutable: true,
                };
                let ref_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, original);
                let pin_id = tcx.lang_items().get(LangItem::Pin).unwrap();
                let pin_def = tcx.adt_def(pin_id);
                let pin_ty = Ty::new_adt(tcx, pin_def, tcx.mk_args(&[ref_ty.into()]));
                let pointer_name = pin_def.non_enum_variant().fields
                    [rustc_abi::FieldIdx::from_usize(0)]
                .name
                .to_string();
                let pin = Value::Adt {
                    name: tcx.def_path_str(pin_id),
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: vec![(pointer_name, reference.clone())].into(),
                };
                let mut memory = Memory::from(vec![Some(pin), Some(future.clone())]);
                let pin_reference = Value::Reference {
                    allocation: 0,
                    projection: Vec::new(),
                    mutable: true,
                };
                let pin_ref_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, pin_ty);
                let observe = |memory: &Memory, detached| {
                    let observation = Observation {
                        memory,
                        conditions: &[],
                        nodes: Default::default(),
                        detached,
                        incoming: None,
                    };
                    engine.coroutine_snapshot(pin_ref_ty, &pin_reference, &observation, None, 0)
                };
                let ghost = observe(&memory, true).unwrap();
                let Value::Adt { fields, .. } = &mut memory[1].as_mut().unwrap() else {
                    unreachable!()
                };
                fields[0].1 = Value::Int {
                    expression: engine.terms.bit_vector(41, 16).unwrap(),
                    bits: 16,
                    signed: false,
                };
                let Value::Adt { fields, .. } = ghost else {
                    panic!("detached Pin");
                };
                let Value::Adt { fields, .. } = &fields[0].1 else {
                    panic!("detached future");
                };
                assert_eq!(
                    fields[0].1.integer().unwrap().0,
                    engine.terms.bit_vector(19, 16).unwrap()
                );
                assert!(observe(&memory, false).is_ok());
                memory
                    .missing_places
                    .consume(0, vec![Step::Field(0)])
                    .unwrap();
                assert!(
                    observe(&memory, false)
                        .unwrap_err()
                        .contains("place initialization is unavailable")
                );
                memory.missing_places.initialize(0, &[]);
                memory
                    .missing_places
                    .consume(1, vec![Step::Field(0)])
                    .unwrap();
                assert!(observe(&memory, false).is_err());
                memory.missing_places.initialize(1, &[]);
                memory.missing_places.consume(1, Vec::new()).unwrap();
                assert!(observe(&memory, false).is_err());
                memory.missing_places.initialize(1, &[]);
                let helper_id = tcx
                    .get_diagnostic_item(Symbol::intern("PinMacroHelper"))
                    .unwrap();
                let helper_def = tcx.adt_def(helper_id);
                let helper_ty = Ty::new_adt(tcx, helper_def, tcx.mk_args(&[original.into()]));
                assert!(engine.pin_macro_coroutine_helper(helper_ty));
                assert!(!engine.coroutine_reference_carrier_type(helper_ty, 0));
                let helper = Value::Adt {
                    name: tcx.def_path_str(helper_id),
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: vec![("value".into(), future)].into(),
                };
                let observation = Observation {
                    memory: &memory,
                    conditions: &[],
                    nodes: Default::default(),
                    detached: false,
                    incoming: None,
                };
                assert!(
                    engine
                        .coroutine_snapshot(helper_ty, &helper, &observation, None, 0)
                        .is_ok()
                );
                let mut wrong = helper.clone();
                let Value::Adt { name, .. } = &mut wrong else {
                    unreachable!()
                };
                *name = "same_shape_user_wrapper".into();
                assert!(
                    engine
                        .coroutine_snapshot(helper_ty, &wrong, &observation, None, 0)
                        .is_err()
                );
                let mut malformed = helper.clone();
                let Value::Adt { fields, .. } = &mut malformed else {
                    unreachable!()
                };
                let Value::Adt { variant, .. } = &mut fields[0].1 else {
                    unreachable!()
                };
                *variant = layout.variant_fields.len();
                assert!(
                    engine
                        .coroutine_snapshot(helper_ty, &malformed, &observation, None, 0)
                        .is_err()
                );
                let mut dead = memory.clone();
                dead[1] = None;
                assert!(observe(&dead, false).is_err());
                let escaped = Observation {
                    memory: &memory,
                    conditions: &[],
                    nodes: Default::default(),
                    detached: false,
                    incoming: Some(1),
                };
                assert!(
                    engine
                        .coroutine_snapshot(ref_ty, &reference, &escaped, None, 0)
                        .unwrap_err()
                        .contains("frame-owned storage")
                );
                let reference_factory = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == "reference_factory"
                    })
                    .unwrap();
                let reference_original = tcx.optimized_mir(reference_factory).return_ty();
                let ty::Coroutine(reference_id, reference_args) = reference_original.kind() else {
                    panic!("reference coroutine");
                };
                let reference_layout = tcx.coroutine_layout(*reference_id, reference_args).unwrap();
                let mut fields = vec![(
                    "0".into(),
                    Value::Reference {
                        allocation: 2,
                        projection: Vec::new(),
                        mutable: false,
                    },
                )];
                fields.extend(
                    reference_layout
                        .field_tys
                        .iter_enumerated()
                        .map(|(saved, _)| {
                            (format!("saved_{}", saved.as_usize()), Value::Uninitialized)
                        }),
                );
                let nested = Value::Adt {
                    name: coroutines::coroutine_name(*reference_id, reference_args),
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: fields.into(),
                };
                let mut state = State {
                    locals: Vec::new(),
                    addresses: Vec::new(),
                    missing_places: Default::default(),
                    conditions: Vec::new(),
                    memory: Memory::from(vec![Some(Value::Unit), Some(nested), None]),
                };
                let nested_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, reference_original);
                assert!(
                    engine
                        .validate_coroutine_reference_transport(nested_ty, &reference, &state, None)
                        .is_err()
                );
                state.memory[2] = Some(Value::Int {
                    expression: engine.terms.bit_vector(7, 16).unwrap(),
                    bits: 16,
                    signed: false,
                });
                assert!(
                    engine
                        .validate_coroutine_reference_transport(nested_ty, &reference, &state, None)
                        .unwrap()
                );
                assert!(
                    engine
                        .validate_coroutine_reference_transport(
                            nested_ty,
                            &reference,
                            &state,
                            Some(2)
                        )
                        .unwrap_err()
                        .contains("frame-owned")
                );
                state
                    .memory
                    .missing_places
                    .consume(1, vec![Step::Field(0)])
                    .unwrap();
                assert!(
                    engine
                        .validate_coroutine_reference_transport(nested_ty, &reference, &state, None)
                        .is_err()
                );
                self.0 = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory =
            std::env::temp_dir().join(format!("miren-coroutine-observer-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(&source, "#![no_std]\npub async fn factory(word:u16)->u16{word}\npub async fn reference_factory(word:&u16)->u16{*word}\n").unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        let mut check = Check(false);
        rustc_driver::run_compiler(
            &[
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            ],
            &mut check,
        );
        assert!(check.0);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
