//! Bounded cold preparation; records never carry live source or Memory authority.
use super::*;

pub(in crate::proof) struct PreparedSources<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    selected: Vec<(ty::Instance<'tcx>, usize)>,
    used: usize,
}

pub(in crate::proof) fn prepare<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<PreparedSources<'a, 'tcx>, String> {
    prepare_inner(engine, root, prior)
        .map_err(|error| engine.categorized_error(error.category, error.reason))
}

fn prepare_inner<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    root: ty::Instance<'tcx>,
    prior: usize,
) -> Result<PreparedSources<'a, 'tcx>, Failure> {
    let mut work = Work::new(prior)?;
    work.charge(8)?;
    let mut pending = vec![(root, 0usize)];
    let mut selected = Vec::new();
    while let Some((instance, depth)) = pending.pop() {
        work.depth(depth)?; // Every occurrence, including a deduplicated helper.
        work.charge(2 + 2 * selected.len())?;
        if selected.iter().any(|(prior, _)| *prior == instance) {
            continue;
        }
        if selected.len() >= SOURCE_HELPERS {
            return Err(Failure {
                category: UnknownCategory::ResourceLimit,
                reason: "byte preparation exceeds distinct source512 policy".into(),
            });
        }
        let source = observe_inner(engine, instance, depth, work.used)?;
        // Transfer actual successful service work exactly once, before the next cold service.
        work.used = source.work.used;
        work.charge(3 + 5 * source.helpers.len())?;
        for helper in &source.helpers {
            match helper.kind {
                HelperKind::PopulationCount => {}
                HelperKind::RustBody(_) => {
                    work.charge(4 + 2 * pending.len())?;
                    pending
                        .try_reserve(1)
                        .map_err(|_| "byte preparation pending allocation failed")?;
                    pending.push((helper.selected, depth + 1));
                }
            }
        }
        drop(source); // Actual guards drop before any following cold cache publication.
        work.charge(4 + 2 * selected.len())?;
        selected
            .try_reserve(1)
            .map_err(|_| "byte preparation record allocation failed")?;
        selected.push((instance, depth));
    }
    work.charge(4)?;
    Ok(PreparedSources {
        engine,
        root,
        selected,
        used: work.used,
    })
}

impl<'a, 'tcx> PreparedSources<'a, 'tcx> {
    pub(in crate::proof) fn used(&self) -> usize {
        self.used
    }

    pub(in crate::proof) fn revalidate(
        self,
        engine: &'a Engine<'tcx>,
        root: ty::Instance<'tcx>,
        prior: usize,
    ) -> Result<BorrowedSources<'a, 'tcx>, String> {
        self.revalidate_inner(engine, root, prior)
            .map_err(|error| engine.categorized_error(error.category, error.reason))
    }

    fn revalidate_inner(
        self,
        engine: &'a Engine<'tcx>,
        root: ty::Instance<'tcx>,
        prior: usize,
    ) -> Result<BorrowedSources<'a, 'tcx>, Failure> {
        let mut work = Work::new(prior)?;
        work.charge(4)?;
        if !std::ptr::eq(engine, self.engine) || root != self.root || prior < self.used {
            return Err("byte preparation has a different root or lost prior work".into());
        }
        // Keep every actual source guard alive until the complete revalidation ends.
        work.charge(3 + self.selected.len())?;
        let mut observations = Vec::new();
        observations
            .try_reserve_exact(self.selected.len())
            .map_err(|_| "byte preparation guard allocation failed")?;
        for (instance, depth) in self.selected {
            work.charge(2)?;
            let source = observe_inner(engine, instance, depth, work.used)?;
            work.used = source.work.used;
            observations.push(source);
        }
        work.charge(3)?;
        work.charge(2)?; // Actual new failed-state field and construction services.
        Ok(BorrowedSources {
            observations,
            work,
            failed: None,
        })
    }
}

// Operation-local read guards, not a cached permit. Their lifetime covers the consuming service.
pub(in crate::proof) struct BorrowedSources<'a, 'tcx> {
    observations: Vec<SourceObservation<'a, 'tcx>>,
    work: Work,
    failed: Option<Failure>,
}

impl<'tcx> BorrowedSources<'_, 'tcx> {
    pub(in crate::proof) fn used(&self) -> usize {
        // Reading a spent-work total grants no source, address or Memory authority.
        self.work.used
    }

    fn require_live(&self) -> Result<(), Failure> {
        match &self.failed {
            Some(error) => Err(error.clone()),
            None => Ok(()),
        }
    }

    fn finish_service(&mut self, result: Result<usize, Failure>) -> Result<usize, String> {
        match result {
            Ok(used) => Ok(used),
            Err(error) => {
                if self.failed.is_none() {
                    self.failed = Some(error.clone());
                }
                let Some(first) = self.observations.first() else {
                    return Err(error.reason);
                };
                Err(first.engine.categorized_error(error.category, error.reason))
            }
        }
    }

    pub(in crate::proof) fn size_one_helper_fact(&mut self, prior: usize) -> Result<usize, String> {
        let result = self.size_one_inner(prior);
        self.finish_service(result)
    }

    fn size_one_inner(&mut self, prior: usize) -> Result<usize, Failure> {
        self.require_live()?; // Before any later service or cumulative handoff.
        if prior < self.work.used {
            return Err("byte size-one fact lost cumulative source/storage work".into());
        }
        let transfer = prior - self.work.used;
        self.work.charge(4)?; // New sticky-state dispatch and exact cumulative handoff planning.
        self.work.charge(transfer)?; // Preserve the actual failed total, including saturation.
        self.work.charge(3)?; // Retain the old Work.new allowance; never replace a failed Work.
        let first = self
            .observations
            .first()
            .ok_or("byte preparation lacks its actual guarded root")?;
        let engine = first.engine;
        self.work.charge(3 + 8 * self.observations.len())?;
        for source in &self.observations {
            let id = source.instance.def_id();
            if engine.tcx.item_name(id).as_str() == "is_valid_allocation_size"
                && engine
                    .tcx
                    .opt_parent(id)
                    .is_some_and(|parent| engine.tcx.item_name(parent).as_str() == "ub_checks")
            {
                allocation_size::size_one_fact(source, &mut self.work)?;
            }
        }
        // This total is not evidence that raw-parts selected this helper or size argument.
        // Exact caller/size/align/null mapping and complete search remain independent obligations.
        Ok(self.work.used)
    }

    pub(in crate::proof) fn check_held(&mut self) -> Result<(), String> {
        let result = self.check_held_inner();
        self.finish_service(result).map(|_| ())
    }

    fn check_held_inner(&mut self) -> Result<usize, Failure> {
        self.require_live()?;
        self.work.charge(2)?; // New sticky-state service dispatch; old scan fee remains literal.
        self.work.charge(3 + 5 * self.observations.len())?;
        let first = self
            .observations
            .first()
            .ok_or("byte preparation lacks its actual guarded root")?;
        for source in &self.observations {
            if !std::ptr::eq(source.engine, first.engine)
                || !source.bodies.contains_key(&source.instance)
                || !source.signatures.contains_key(&source.instance)
            {
                return Err("byte preparation lost its guarded current source".into());
            }
        }
        Ok(self.work.used)
    }

    pub(in crate::proof) fn route_handoff(&mut self) -> Result<(), String> {
        let result = self
            .require_live()
            .and_then(|()| self.work.charge(12))
            .map(|()| self.work.used);
        self.finish_service(result).map(|_| ())
    }

    pub(in crate::proof) fn check_route_records(
        &mut self,
        records: &[super::super::byte_route::RouteRecord<'tcx>],
    ) -> Result<(), String> {
        let result = self.route_records_inner(records);
        self.finish_service(result).map(|_| ())
    }

    fn route_records_inner(
        &mut self,
        records: &[super::super::byte_route::RouteRecord<'tcx>],
    ) -> Result<usize, Failure> {
        self.require_live()?;
        self.work.charge(3 + 10 * records.len())?;
        let source = self
            .observations
            .first()
            .ok_or("byte preparation lacks its actual guarded root")?;
        for record in records {
            if !source
                .bodies
                .get(&record.instance)
                .is_some_and(|current| Rc::ptr_eq(current, &record.body))
                || source.signatures.get(&record.instance) != Some(&record.signature)
            {
                return Err("byte route source Body/signature was replaced or unavailable".into());
            }
        }
        Ok(self.work.used)
    }

    pub(in crate::proof) fn check_transport_signatures(
        &mut self,
        mapping: &super::super::byte_transport::TypedRoute<'tcx>,
    ) -> Result<(), String> {
        let result = (|| {
            self.require_live()?;
            self.work.charge(43 + 10 * mapping.helpers.len())?;
            let source = self
                .observations
                .first()
                .ok_or("typed byte transport lacks its held source registry")?;
            mapping.check_held_modes(&source.bodies)?;
            for helper in &mapping.helpers {
                if source.signatures.get(&helper.instance) != Some(&helper.signature) {
                    return Err("typed byte transport full helper signature changed".into());
                }
            }
            Ok(self.work.used)
        })();
        self.finish_service(result).map(|_| ())
    }

    #[cfg(test)]
    pub(super) fn failed_probe(
        &mut self,
        control: allocation_size::FailureProbe,
    ) -> Result<(), String> {
        let result = self.failed_probe_inner(control);
        self.finish_service(result).map(|_| ())
    }

    #[cfg(test)]
    fn failed_probe_inner(
        &mut self,
        control: allocation_size::FailureProbe,
    ) -> Result<usize, Failure> {
        self.require_live()?;
        self.work.charge(2)?;
        let source = self
            .observations
            .first()
            .ok_or("byte preparation lacks its actual guarded root")?;
        allocation_size::failure_probe(source, &mut self.work, control)?;
        Ok(self.work.used)
    }
}
