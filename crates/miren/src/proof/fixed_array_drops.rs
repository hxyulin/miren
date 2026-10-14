//! Compiler-issued fixed Subslice Drop only; never a general partial-array borrow.
use super::*;
use rustc_middle::mir::BasicBlock;
use std::rc::Rc;

fn fixed_range(count: u64, from: u64, to: u64, from_end: bool) -> Result<(u64, u64), String> {
    let end = if from_end {
        count.checked_sub(to)
    } else {
        Some(to)
    }
    .ok_or("fixed array Drop range exceeds original compiler count")?;
    if from > end || end > count {
        return Err("fixed array Drop range exceeds original compiler count".into());
    }
    Ok((from, end))
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn drop_fixed_subslice(
        &mut self,
        instance: ty::Instance<'tcx>,
        body: &Rc<Body<'tcx>>,
        block: BasicBlock,
        state: &State,
        stack: &[DefId],
    ) -> Result<Option<Vec<State>>, String> {
        let terminator = body.basic_blocks[block].terminator();
        let TerminatorKind::Drop { place, .. } = &terminator.kind else {
            return Err("fixed array Drop requires its actual current Drop terminator".into());
        };
        if !place
            .projection
            .iter()
            .any(|part| matches!(part, ProjectionElem::Subslice { .. }))
        {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        if !Rc::ptr_eq(body, &self.instantiated_body(instance)?) {
            return Err("fixed array Drop differs from current instantiated Body".into());
        }
        let Some((ProjectionElem::Subslice { from, to, from_end }, prefix)) =
            place.projection.split_last()
        else {
            return Err("fixed array Drop requires one terminal compiler Subslice".into());
        };
        let parent = Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(prefix),
        };
        self.owned_field_footprint(body, parent)?;
        let original = parent.ty(&body.local_decls, self.tcx).ty;
        let ty::Array(element, count) = original.kind() else {
            return Err("fixed array Drop requires original compiler array parent".into());
        };
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("fixed array Drop requires concrete original compiler count")?;
        if count > symbolic::MAX_REPEAT_VALUES as u64 || prefix.len() >= 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "fixed array Drop exceeds fixed-array or depth16 limits".into(),
            ));
        }
        let (start, end) = fixed_range(count, *from, *to, *from_end)?;
        // Preflight all selected initialized children and the complete cumulative mask update.
        // No whole-array read, new borrow or destructor effects occur during this pass.
        let owner = state.addresses[place.local.as_usize()];
        if let Some(allocation) = owner {
            if state
                .memory
                .get(allocation)
                .and_then(Option::as_ref)
                .is_none()
            {
                return Err("fixed array Drop requires current live allocation".into());
            }
            self.check_initialized_owner_type(
                &state.memory,
                allocation,
                body.local_decls[place.local].ty,
            )?;
        } else {
            self.raw_local(state, place.local.as_usize())?;
        }
        let mut mask = if owner.is_some() {
            state.memory.missing_places.clone()
        } else {
            state.missing_places.clone()
        };
        for index in start..end {
            let mut projection = prefix.to_vec();
            projection.push(ProjectionElem::ConstantIndex {
                offset: index,
                min_length: count,
                from_end: false,
            });
            let child = Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(&projection),
            };
            self.preflight_initialized_owner(body, state, child)?;
            self.check_typed_place_initialization(body, state, child)?;
            self.validate_fixed_array_storage(body, state, child)?;
            mask.consume(
                owner.unwrap_or(place.local.as_usize()),
                self.owned_field_footprint(body, child)?,
            )?;
        }
        let mut pending = vec![state.clone()];
        for index in start..end {
            let mut projection = prefix.to_vec();
            projection.push(ProjectionElem::ConstantIndex {
                offset: index,
                min_length: count,
                from_end: false,
            });
            let child = Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(&projection),
            };
            let mut next = Vec::new();
            for mut branch in pending {
                self.steps.legacy_increment();
                if self.steps.used() > self.limits.max_steps {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "fixed array Drop execution step limit reached".into(),
                    ));
                }
                if !Rc::ptr_eq(body, &self.instantiated_body(instance)?) {
                    return Err("fixed array Drop differs from current instantiated Body".into());
                }
                let fields = self.owned_field_footprint(body, child)?;
                self.check_typed_place_initialization(body, &branch, child)?;
                if !element.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) {
                    if let Some(allocation) = branch.addresses[place.local.as_usize()] {
                        branch.memory.missing_places.consume(allocation, fields)?;
                    } else {
                        branch
                            .missing_places
                            .consume(place.local.as_usize(), fields)?;
                    }
                    next.push(branch);
                    continue;
                }
                let argument = self.borrow_typed(body, &mut branch, child, true)?;
                let Value::Reference { allocation, .. } = &argument else {
                    return Err("fixed array Drop requires actual tracked element storage".into());
                };
                let allocation = *allocation;
                let glue = ty::Instance::resolve_drop_glue(self.tcx, *element);
                for result in self.call_instance(
                    glue,
                    vec![argument],
                    branch.conditions.clone(),
                    branch.memory.clone(),
                    stack,
                    (instance.def_id(), terminator.source_info.span),
                )? {
                    if next.len() >= MAX_INPUT_VALUES {
                        return Err(self.categorized_error(
                            UnknownCategory::ResourceLimit,
                            "fixed array Drop exceeds 512 returned branches".into(),
                        ));
                    }
                    let mut continuation = self.adopt_flow_return(
                        &branch,
                        result.conditions,
                        result.memory,
                        result.flow,
                    )?;
                    self.preflight_initialized_owner(body, &continuation, child)?;
                    continuation
                        .memory
                        .missing_places
                        .descendants(allocation, &fields)?;
                    continuation
                        .memory
                        .missing_places
                        .consume(allocation, fields.clone())?;
                    next.push(continuation);
                }
            }
            pending = next;
        }
        Ok(Some(pending))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_compiler_ranges_refuse_wrong_counts_and_preserve_order() {
        assert_eq!(fixed_range(3, 1, 0, true).unwrap(), (1, 3));
        assert_eq!(fixed_range(3, 1, 3, false).unwrap(), (1, 3));
        assert_eq!(fixed_range(0, 0, 0, true).unwrap(), (0, 0));
        for args in [(2, 1, 3, false), (2, 0, 3, true), (2, 2, 1, false)] {
            assert_eq!(
                fixed_range(args.0, args.1, args.2, args.3).unwrap_err(),
                "fixed array Drop range exceeds original compiler count"
            );
        }
    }

    #[test]
    fn compiler_drop_blocks_reject_foreign_body_and_non_drop_roles() {
        struct Check(bool);
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                            && tcx.item_name(id.to_def_id()).as_str() == "partial"
                    })
                    .unwrap()
                    .to_def_id();
                let config = miren::ContractConfig::default();
                let options = VerificationOptions {
                    all_failures: false,
                    induction: false,
                    startup: false,
                    isolated_startup: false,
                    async_entry: false,
                    limits: miren::AnalysisLimits::default(),
                };
                let mut engine = Engine::new(tcx, &config, options);
                let instance = engine
                    .resolve_function_item(id, ty::GenericArgs::empty())
                    .unwrap();
                let body = engine.instantiated_body(instance).unwrap();
                let block = body
                    .basic_blocks
                    .iter_enumerated()
                    .find(|(_, data)| {
                        matches!(&data.terminator().kind, TerminatorKind::Drop { place, .. }
                        if place.projection.iter().any(|p|
                            matches!(p, ProjectionElem::Subslice { .. })))
                    })
                    .unwrap()
                    .0;
                let state = State {
                    flow: activation_flow::Flow::Unarmed,
                    constant_receipts: constant_reference_receipts::Slots::default(),
                    locals: vec![None; body.local_decls.len()],
                    addresses: vec![None; body.local_decls.len()],
                    conditions: Vec::new(),
                    memory: Memory::default(),
                    missing_places: initialized_places::MissingPlaces::default(),
                };
                let foreign = Rc::new(body.as_ref().clone());
                assert_eq!(
                    engine
                        .drop_fixed_subslice(instance, &foreign, block, &state, &[])
                        .err()
                        .unwrap(),
                    "fixed array Drop differs from current instantiated Body"
                );
                let mut changed = body.as_ref().clone();
                changed.local_decls[rustc_middle::mir::Local::from_usize(2)].ty = tcx.types.u32;
                assert_eq!(
                    engine
                        .drop_fixed_subslice(instance, &Rc::new(changed), block, &state, &[])
                        .err()
                        .unwrap(),
                    "fixed array Drop differs from current instantiated Body"
                );
                assert_eq!(
                    engine
                        .drop_fixed_subslice(instance, &body, START_BLOCK, &state, &[])
                        .err()
                        .unwrap(),
                    "fixed array Drop requires its actual current Drop terminator"
                );
                self.0 = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-fixed-drop-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("drop.rs");
        std::fs::write(
            &source,
            include_str!("../../../../tests/fixtures/partial_array_drops.rs"),
        )
        .unwrap();
        let args = vec![
            "rustc".into(),
            source.to_str().unwrap().into(),
            "--crate-type=lib".into(),
            "--edition=2024".into(),
            "-Cpanic=abort".into(),
            "-Copt-level=0".into(),
            "--out-dir".into(),
            directory.to_str().unwrap().into(),
            "--sysroot".into(),
            env!("MIREN_SYSROOT").into(),
        ];
        let mut callback = Check(false);
        rustc_driver::run_compiler(&args, &mut callback);
        assert!(callback.0);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
