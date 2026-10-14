//! Consumed incomplete source metadata. There is no completed source or search constructor.
use super::*;

struct MissingEdge<'tcx> {
    caller: ty::Instance<'tcx>,
    current: Rc<Body<'tcx>>,
    caller_signature: ty::PolyFnSig<'tcx>,
    block: rustc_middle::mir::BasicBlock,
    target: ty::Instance<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
}

pub(in crate::proof) struct PendingSources<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    selected: Vec<(ty::Instance<'tcx>, usize)>,
    remaining: Vec<(ty::Instance<'tcx>, usize)>,
    edge: Option<MissingEdge<'tcx>>,
    work: Work,
}

fn missing_edge<'tcx>(
    engine: &Engine<'tcx>,
    caller: ty::Instance<'tcx>,
    source: &SourceObservation<'_, 'tcx>,
    helper: &Helper<'tcx>,
    work: &mut Work,
) -> Result<MissingEdge<'tcx>, Failure> {
    work.charge(8)?;
    let body = source
        .bodies
        .get(&caller)
        .ok_or("pending source lost its current caller")?;
    work.charge(2)?;
    let caller_signature = *source
        .signatures
        .get(&caller)
        .ok_or("pending source lost its original caller signature")?;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        work.charge(4)?;
        let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
            continue;
        };
        work.charge(4)?;
        let ty::FnDef(id, args) = func.ty(&body.local_decls, engine.tcx).kind() else {
            return Err("pending source has a non-original direct Call".into());
        };
        work.charge(8 + 2 * args.skip_binder().len())?;
        let target = engine.resolve_function_item(*id, args.skip_binder())?;
        if target == helper.selected {
            work.charge(8)?; // Actual Rc clone and exact occurrence/signature record construction.
            return Ok(MissingEdge {
                caller,
                current: body.clone(),
                caller_signature,
                block,
                target,
                signature: helper.signature,
            });
        }
    }
    Err("pending missing helper has no actual current Call occurrence".into())
}

pub(in crate::proof) fn pending<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<PendingSources<'a, 'tcx>, String> {
    pending_inner(engine, root, prior)
        .map_err(|error| engine.categorized_error(error.category, error.reason))
}

fn pending_inner<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<PendingSources<'a, 'tcx>, Failure> {
    let mut work = Work::new(prior)?;
    work.charge(10)?; // Actual initial vector/metadata state allocation.
    let mut remaining = vec![(root, 0usize)];
    let mut selected = Vec::new();
    while let Some((instance, depth)) = remaining.pop() {
        work.depth(depth)?;
        work.charge(2 + 2 * selected.len())?;
        if selected.iter().any(|(prior, _)| *prior == instance) {
            continue;
        }
        if selected.len() >= SOURCE_HELPERS {
            return Err(Failure {
                category: UnknownCategory::ResourceLimit,
                reason: "byte pending source exceeds distinct source512 policy".into(),
            });
        }
        // Only successful available-source work is transferred; no failed service is retried.
        let source = observe_inner(engine, instance, depth, work.used)?;
        work.used = source.work.used;
        work.charge(3 + 5 * source.helpers.len())?;
        for helper in &source.helpers {
            match helper.kind {
                HelperKind::PopulationCount => {}
                HelperKind::RustBody(false) => {
                    let edge = missing_edge(engine, instance, &source, helper, &mut work)?;
                    work.charge(8)?; // Actual consumed incomplete metadata publication.
                    return Ok(PendingSources {
                        engine,
                        root,
                        selected,
                        remaining,
                        edge: Some(edge),
                        work,
                    });
                }
                HelperKind::RustBody(true) => {
                    work.charge(4 + 2 * remaining.len())?;
                    remaining
                        .try_reserve(1)
                        .map_err(|_| "byte pending source queue allocation failed")?;
                    remaining.push((helper.selected, depth + 1));
                }
            }
        }
        drop(source);
        work.charge(4 + 2 * selected.len())?;
        selected
            .try_reserve(1)
            .map_err(|_| "byte pending source record allocation failed")?;
        selected.push((instance, depth));
    }
    work.charge(8)?;
    Ok(PendingSources {
        engine,
        root,
        selected,
        remaining,
        edge: None,
        work,
    })
}

impl PendingSources<'_, '_> {
    pub(in crate::proof) fn reject(mut self) -> Result<(), String> {
        // Consumption is the only exposed transition. No retry or completed certificate exists.
        self.work.used = range::reject_pending_range(self.engine, self.root, self.work.used)
            .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
        self.work
            .charge(8 + 2 * self.selected.len() + 2 * self.remaining.len())
            .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
        let error = if let Some(edge) = self.edge {
            if edge.current.source.instance != edge.caller.def
                || edge.block.as_usize() >= edge.current.basic_blocks.len()
                || edge.signature.skip_binder().output().has_param()
                || edge.caller_signature.skip_binder().output().has_param()
            {
                Failure::from("byte pending missing-edge metadata lost original identity")
            } else {
                self.work
                    .charge(64)
                    .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
                Failure {
                    category: UnknownCategory::MissingCompilerEvidence,
                    reason: self.engine.missing_body_reason(edge.target.def_id()),
                }
            }
        } else {
            let _root = self.root;
            Failure::from("byte available source closure still lacks a verified search relation")
        };
        self.work
            .charge(2 + error.reason.len())
            .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
        self.work.failed = Some(error.clone());
        Err(self.engine.categorized_error(error.category, error.reason))
    }
}

#[cfg(test)]
pub(in crate::proof) fn compiler_controls<'tcx>(
    engine: &Engine<'tcx>,
    search: ty::Instance<'tcx>,
    prior: usize,
) {
    let candidate = pending_inner(engine, search, prior).unwrap();
    assert!(candidate.work.used > prior);
    assert_eq!(candidate.root, search);
    assert!(!candidate.selected.is_empty());
    assert!(!candidate.remaining.is_empty());
    let edge = candidate
        .edge
        .as_ref()
        .expect("actual pending missing edge");
    assert!(!engine.tcx.is_mir_available(edge.target.def_id()));
    assert!(
        engine
            .tcx
            .lang_items()
            .from_def_id(edge.target.def_id())
            .is_none()
    );
    assert!(matches!(
        edge.current.basic_blocks[edge.block].terminator().kind,
        TerminatorKind::Call { .. }
    ));
    let expected = engine.categorized_error(
        UnknownCategory::MissingCompilerEvidence,
        engine.missing_body_reason(edge.target.def_id()),
    );
    let stopped = candidate.work.used;
    assert_eq!(candidate.reject().unwrap_err(), expected);
    let error = match pending_inner(engine, search, usize::MAX) {
        Ok(_) => panic!("overflowing source work produced a pending record"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::ResourceLimit);
    let current = engine.bodies.borrow().get(&search).unwrap().clone();
    let mut paid = Work::new(prior).unwrap();
    let inventory =
        inventory(engine, search, &current, SourcePhase::Normalized, &mut paid).unwrap();
    paid.charge(inventory + 16).unwrap();
    let mut changed = current.as_ref().clone();
    changed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK].statements[0].kind =
        StatementKind::Nop;
    engine.bodies.borrow_mut().insert(search, Rc::new(changed));
    let error = match pending_inner(engine, search, prior) {
        Ok(_) => panic!("changed caller source produced pending evidence"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::Semantics);
    assert_eq!(
        error.reason,
        "byte source current statement differs from original compiler statement"
    );
    engine.bodies.borrow_mut().insert(search, current);
    let held = engine.bodies.borrow_mut();
    let error = match pending_inner(engine, search, prior) {
        Ok(_) => panic!("conflicting source registry produced pending evidence"),
        Err(error) => error,
    };
    assert_eq!(error.category, UnknownCategory::Semantics);
    drop(held);
    eprintln!(
        "BYTE PENDING actual missing Call metadata consumed as MCE used={stopped}; no source rights"
    );
}
