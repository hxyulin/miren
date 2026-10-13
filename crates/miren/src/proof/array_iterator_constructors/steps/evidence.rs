//! Immutable original/current MIR evidence; no execution or ownership facts are cached.
use super::*;

pub(in crate::proof) struct Evidence<'tcx> {
    pub(super) instance: ty::Instance<'tcx>,
    pub(super) raw: &'tcx Body<'tcx>,
    pub(super) current: Rc<Body<'tcx>>,
    pub(super) context: Term,
}
pub(super) fn schema<'tcx>(
    engine: &mut Engine<'tcx>,
    evidence: &BodyEvidence<'tcx>,
    kind: FrameKind,
    direction: Direction,
    element: Ty<'tcx>,
) -> Result<(), String> {
    let body = &evidence.current;
    pay(engine, body.local_decls.len() + body.basic_blocks.len() + 1)?;
    let counts: &[usize] = match kind {
        FrameKind::Public => &[5, 1],
        FrameKind::Inner => &[11, 4, 7, 0, 17, 2, 2, 1, 8, 10],
        FrameKind::BoundsHelper => return Err("bounds helper has no iterator schema".into()),
    };
    if body.arg_count != 1
        || body.basic_blocks.len() != counts.len()
        || body.local_decls.len() != if kind == FrameKind::Public { 4 } else { 25 }
        || body
            .basic_blocks
            .iter()
            .zip(counts)
            .any(|(block, count)| block.is_cleanup || block.statements.len() != *count)
        || engine.tcx.lang_items().get(LangItem::Option)
            != body.return_ty().ty_adt_def().map(|def| def.did())
    {
        return Err("IntoIter step exact original local/block/output schema differs".into());
    }
    let ty::Adt(_, args) = body.return_ty().kind() else {
        unreachable!()
    };
    if args.type_at(0) != element {
        return Err("IntoIter step Option original element type differs".into());
    }
    if kind == FrameKind::Public {
        if !matches!(assignment(body,0,2,3)?,Rvalue::Ref(_,BorrowKind::Mut{..},place)
            if field_path(*place,1,&[0,0]))
            || !matches!(assignment(body,0,3,2)?,Rvalue::Cast(
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize,_),operand,_)
                if copied(operand,3))
        {
            return Err("IntoIter step exact public forwarding projection/Unsize differs".into());
        }
    } else {
        for (index, field) in [(4, 1), (6, 0)] {
            if !matches!(assignment(body,0,index,if field==1{9}else{10})?,
                Rvalue::Use(Operand::Copy(place),_) if field_path(*place,1,&[0,field]))
            {
                return Err("IntoIter step exact range read differs".into());
            }
        }
        let cursor = if direction == Direction::Front { 1 } else { 2 };
        let StatementKind::Assign(pair) =
            &body.basic_blocks[BasicBlock::from_usize(4)].statements[cursor].kind
        else {
            return Err("IntoIter step cursor store absent".into());
        };
        if !field_path(
            pair.0,
            1,
            &[0, if direction == Direction::Front { 0 } else { 1 }],
        ) || !matches!(&pair.1,Rvalue::Use(operand,_) if
                matches!(
                    operand,
                    Operand::Move(place) if direction == Direction::Front && local(*place, 11)
                )
                || copied(operand,8)&&direction==Direction::Back)
            || !matches!(assignment(body,9,2,14)?,Rvalue::Use(Operand::Copy(place),_)
                if place.local.as_usize()==22&&place.projection.as_ref()==[ProjectionElem::Deref])
        {
            return Err("IntoIter step exact cursor store/owning read differs".into());
        }
    }
    Ok(())
}
pub(super) fn load_evidence<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<BodyEvidence<'tcx>, String> {
    pay(engine, 2)?;
    if !engine.tcx.is_mir_available(instance.def_id()) {
        return Err(engine.categorized_error(
            UnknownCategory::MissingCompilerEvidence,
            engine.missing_body_reason(instance.def_id()),
        ));
    }
    let raw = engine.tcx.instance_mir(instance.def);
    source_identity(raw, instance)?;
    pay(engine, engine.array_iterator_step_evidence.len() + 3)?;
    if let Some(evidence) = engine
        .array_iterator_step_evidence
        .iter()
        .find(|evidence| evidence.instance == instance)
    {
        let cached = engine.bodies.borrow();
        if !std::ptr::eq(raw, evidence.raw)
            || !evidence.context.belongs_to(&engine.terms)
            || cached
                .get(&instance)
                .is_none_or(|current| !Rc::ptr_eq(current, &evidence.current))
        {
            return Err(
                "IntoIter step authenticated compiler/current Body cache was replaced".into(),
            );
        }
        source_identity(&evidence.current, instance)?;
        return Ok(BodyEvidence {
            instance,
            current: evidence.current.clone(),
        });
    }

    #[cfg(test)]
    let trace = std::env::var_os("MIREN_INTOITER_STEP_TRACE").map(|path| {
        static OCCURRENCE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let ordinal = OCCURRENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let directory = std::path::PathBuf::from(path);
        std::fs::create_dir_all(&directory).unwrap();
        let prefix = directory.join(format!("occurrence-{ordinal:04}"));
        std::fs::write(
            prefix.with_extension("raw"),
            format!(
                "Target {}\nOpt {:?}\nInstance {instance:?}\nRaw {raw:#?}\n",
                engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.cg.opt_level
            ),
        )
        .unwrap();
        prefix
    });
    let owned = clone_work::step_body(engine, raw)?;
    #[cfg(test)]
    if trace.is_some() {
        println!(
            "Step evidence {} planning steps={} owned={owned} cached={}",
            engine.tcx.item_name(instance.def_id()),
            engine.steps,
            engine.bodies.borrow().contains_key(&instance)
        );
    }
    if !engine.bodies.borrow().contains_key(&instance) {
        pay(engine, owned)?;
        pay(engine, owned)?; // Actual current clone and distinct fold allowance.
    }
    let current = engine.instantiated_body(instance)?;
    #[cfg(test)]
    if trace.is_some() {
        println!(
            "Step evidence {} current clone/fold steps={}",
            engine.tcx.item_name(instance.def_id()),
            engine.steps
        );
    }
    source_identity(&current, instance)?;
    if raw.phase != current.phase
        || raw.pass_count != current.pass_count
        || raw.is_polymorphic != current.is_polymorphic
        || raw.injection_phase != current.injection_phase
        || current.coverage_early_info.is_some()
        || current.coverage_mir_info.is_some()
        || raw.arg_count != current.arg_count
        || raw.span != current.span
        || raw.local_decls.len() != current.local_decls.len()
        || raw.basic_blocks.len() != current.basic_blocks.len()
        || raw.source_scopes.len() != current.source_scopes.len()
        || raw.var_debug_info.len() != current.var_debug_info.len()
        || current.coroutine.is_some()
        || current.tainted_by_errors.is_some()
        || current.spread_arg.is_some()
        || !current.user_type_annotations.is_empty()
    {
        return Err("IntoIter step borrowed original/current header differs".into());
    }
    for (original, actual) in raw.local_decls.iter().zip(&current.local_decls) {
        pay(engine, 3)?;
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.ty),
            )
            .map_err(|error| {
                format!("IntoIter step original local normalization failed: {error:?}")
            })?;
        if normalized != actual.ty
            || original.mutability != actual.mutability
            || original.source_info != actual.source_info
            || actual.user_ty.is_some()
            || !matches!(actual.local_info, rustc_middle::mir::ClearCrossCrate::Clear)
        {
            return Err("IntoIter step normalized original/current local differs".into());
        }
    }
    for (original, actual) in raw.source_scopes.iter().zip(&current.source_scopes) {
        pay(engine, 5)?;
        pay(engine, 5)?;
        pay(engine, 5)?; // clone, fold, comparison are separate.
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("IntoIter step original scope normalization failed: {error:?}")
            })?;
        if normalized.span != actual.span
            || normalized.parent_scope != actual.parent_scope
            || normalized.inlined != actual.inlined
            || normalized.inlined_parent_scope != actual.inlined_parent_scope
            || !match (&normalized.local_data, &actual.local_data) {
                (
                    rustc_middle::mir::ClearCrossCrate::Clear,
                    rustc_middle::mir::ClearCrossCrate::Clear,
                ) => true,
                (
                    rustc_middle::mir::ClearCrossCrate::Set(a),
                    rustc_middle::mir::ClearCrossCrate::Set(b),
                ) => a.lint_root == b.lint_root,
                _ => false,
            }
        {
            return Err("IntoIter step original/current source scope differs".into());
        }
    }
    for (original, actual) in raw.var_debug_info.iter().zip(&current.var_debug_info) {
        let owned = clone_work::step_variable(engine, original)?;
        pay(engine, owned)?;
        pay(engine, owned)?;
        pay(engine, 5)?;
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("IntoIter step original debug normalization failed: {error:?}")
            })?;
        let composite = match (&normalized.composite, &actual.composite) {
            (None, None) => true,
            (Some(a), Some(b)) => a.ty == b.ty && a.projection == b.projection,
            _ => false,
        };
        let value = match (&normalized.value, &actual.value) {
            (VarDebugInfoContents::Place(a), VarDebugInfoContents::Place(b)) => a == b,
            (VarDebugInfoContents::Const(a), VarDebugInfoContents::Const(b)) => a == b,
            _ => false,
        };
        if normalized.name != actual.name
            || normalized.source_info != actual.source_info
            || normalized.argument_index != actual.argument_index
            || !composite
            || !value
        {
            return Err("IntoIter step original/current debug variable differs".into());
        }
    }
    if raw.required_consts.as_ref().map(Vec::len) != current.required_consts.as_ref().map(Vec::len)
        || raw.mentioned_items.as_ref().map(Vec::len)
            != current.mentioned_items.as_ref().map(Vec::len)
    {
        return Err("IntoIter step original/current auxiliary vectors differ".into());
    }
    if let (Some(original), Some(actual)) = (&raw.required_consts, &current.required_consts) {
        for (original, actual) in original.iter().zip(actual) {
            pay(engine, 3)?;
            pay(engine, 3)?;
            pay(engine, 3)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, *original),
                )
                .map_err(|error| {
                    format!("IntoIter step required constant normalization failed: {error:?}")
                })?;
            if normalized != *actual {
                return Err("IntoIter step original/current required constant differs".into());
            }
        }
    }
    if let (Some(original), Some(actual)) = (&raw.mentioned_items, &current.mentioned_items) {
        for (original, actual) in original.iter().zip(actual) {
            pay(engine, 5)?;
            pay(engine, 5)?;
            pay(engine, 3)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, *original),
                )
                .map_err(|error| {
                    format!("IntoIter step mentioned item normalization failed: {error:?}")
                })?;
            if normalized != *actual {
                return Err("IntoIter step original/current mentioned item differs".into());
            }
        }
    }
    for (original, actual) in raw.basic_blocks.iter().zip(current.basic_blocks.iter()) {
        pay(engine, 4)?;
        if original.is_cleanup != actual.is_cleanup
            || original.statements.len() != actual.statements.len()
            || !step_debug_equal(
                engine,
                &original.after_last_stmt_debuginfos,
                &actual.after_last_stmt_debuginfos,
            )?
        {
            return Err("IntoIter step original/current block differs".into());
        }
        for (original, actual) in original.statements.iter().zip(&actual.statements) {
            let owned = clone_work::step_statement(engine, original)?;
            pay(engine, owned)?;
            pay(engine, owned)?;
            pay(engine, 4)?;
            let normalized = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    engine.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(engine.tcx, original.clone()),
                )
                .map_err(|error| {
                    format!("IntoIter step original statement normalization failed: {error:?}")
                })?;
            if normalized.kind != actual.kind
                || normalized.source_info != actual.source_info
                || !step_debug_equal(engine, &normalized.debuginfos, &actual.debuginfos)?
            {
                return Err("IntoIter step original/current statement differs".into());
            }
        }
        let original = original.terminator();
        let actual = actual.terminator();
        let owned = clone_work::step_terminator(engine, original)?;
        pay(engine, owned)?;
        pay(engine, owned)?;
        pay(engine, 4)?;
        let normalized = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                engine.tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(engine.tcx, original.clone()),
            )
            .map_err(|error| {
                format!("IntoIter step original terminator normalization failed: {error:?}")
            })?;
        if normalized.kind != actual.kind
            || normalized.source_info != actual.source_info
            || !normalized.attributes.is_empty()
            || !actual.attributes.is_empty()
        {
            return Err("IntoIter step original/current terminator differs".into());
        }
    }
    #[cfg(test)]
    if let Some(prefix) = &trace {
        std::fs::write(
            prefix.with_extension("current"),
            format!(
                "Target {}\nOpt {:?}\nInstance {instance:?}\nCurrent {current:#?}\n",
                engine.tcx.sess.target.llvm_target, engine.tcx.sess.opts.cg.opt_level
            ),
        )
        .unwrap();
    }
    #[cfg(test)]
    if trace.is_some() {
        println!(
            "Step evidence {} streamed comparisons steps={}",
            engine.tcx.item_name(instance.def_id()),
            engine.steps
        );
    }
    if engine.array_iterator_step_evidence.len() >= MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter step compiler evidence exceeds existing 512-node limit".into(),
        ));
    }
    pay(engine, engine.array_iterator_step_evidence.len() + 6)?;
    engine.array_iterator_step_evidence.push(Evidence {
        instance,
        raw,
        current: current.clone(),
        context: engine.terms.boolean(true),
    });
    Ok(BodyEvidence { instance, current })
}
