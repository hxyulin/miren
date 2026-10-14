//! Authenticated outer-to-byte route metadata; argument/storage/search semantics remain separate.
use super::*;
use std::rc::Rc;

pub(super) struct RouteRecord<'tcx> {
    pub(super) instance: ty::Instance<'tcx>,
    pub(super) body: Rc<Body<'tcx>>,
    pub(super) signature: ty::PolyFnSig<'tcx>,
}

pub(super) struct ByteBoundary<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    original: Ty<'tcx>,
    outer: ty::Instance<'tcx>,
    dispatcher: ty::Instance<'tcx>,
    search: ty::Instance<'tcx>,
    records: Vec<RouteRecord<'tcx>>,
    mapping: Option<Box<super::byte_transport::TypedRoute<'tcx>>>,
    work: usize,
}

pub(super) fn boundary<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    original: Ty<'tcx>,
    outer: ty::Instance<'tcx>,
    dispatcher: ty::Instance<'tcx>,
    bodies: Vec<(ty::Instance<'tcx>, Rc<Body<'tcx>>)>,
    mut budget: GraphBudget<'tcx>,
) -> Result<ByteBoundary<'a, 'tcx>, String> {
    let mapping = super::byte_transport::bind_current(
        engine,
        original,
        outer,
        dispatcher,
        &bodies,
        &mut budget,
    )?;
    budget.charge(8 + 2 * bodies.len())?;
    let body = bodies
        .iter()
        .find(|(instance, _)| *instance == dispatcher)
        .map(|(_, body)| body)
        .ok_or("byte route lacks its matched dispatcher Body")?;
    // The complete dispatcher is already original/current/template/type/layout authenticated.
    // Locate only the actual selected memchr FnDef Call; this is not argument transport proof.
    budget.phase(GraphPhase::Edges, body.basic_blocks.len())?;
    let mut search = None;
    for block in body.basic_blocks.iter() {
        budget.charge(1)?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &block.terminator().kind
        else {
            continue;
        };
        budget.charge(6 + args.len())?;
        let ty::FnDef(id, parameters) = func.ty(&body.local_decls, engine.tcx).kind() else {
            return Err("byte route dispatcher has a non-function Call".into());
        };
        budget.arguments(engine.tcx, parameters.skip_binder())?;
        let instance = engine.resolve_function_item(*id, parameters.skip_binder())?;
        let key = budget.key(instance.def_id())?;
        if key == "DefId(core::slice::memchr::memchr)" {
            if search.is_some() || target.is_none() || args.len() != 2 {
                return Err("byte route memchr occurrence inventory differs".into());
            }
            budget.charge(16)?;
            let first = args[0].node.ty(&body.local_decls, engine.tcx);
            let second = args[1].node.ty(&body.local_decls, engine.tcx);
            if first != engine.tcx.types.u8
                || !matches!(second.kind(), ty::Ref(_, slice, rustc_hir::Mutability::Not)
                    if matches!(slice.kind(), ty::Slice(item) if *item == engine.tcx.types.u8))
                || !matches!(destination.ty(&body.local_decls, engine.tcx).ty.kind(),
                    ty::Adt(def, parameters)
                        if engine.tcx.lang_items().get(LangItem::Option) == Some(def.did())
                            && parameters.len() == 1
                            && parameters.type_at(0) == engine.tcx.types.usize)
            {
                return Err("byte route memchr actual operand/result types differ".into());
            }
            search = Some(instance);
        }
    }
    let search = search.ok_or("byte route matched dispatcher has no actual memchr Call")?;
    budget.charge(3 + bodies.len())?;
    let mut records = Vec::new();
    records
        .try_reserve_exact(bodies.len())
        .map_err(|_| "byte route source receipt allocation failed")?;
    for (instance, body) in bodies {
        budget.record(instance)?;
        budget.charge(10 + instance.args.len())?;
        if !engine
            .bodies
            .try_borrow()
            .map_err(|_| "byte route Body registry is borrowed")?
            .get(&instance)
            .is_some_and(|current| Rc::ptr_eq(current, &body))
        {
            return Err("byte route source Body was replaced before publication".into());
        }
        // capture_niche_comparison_body independently normalized and checked this full signature.
        let signature = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "byte route signature registry is borrowed")?
            .get(&instance)
            .copied()
            .ok_or("byte route lacks its complete actual signature")?;
        records.push(RouteRecord {
            instance,
            body,
            signature,
        });
    }
    budget.charge(13)?; // Old12 plus the actual new optional mapping field.
    Ok(ByteBoundary {
        engine,
        original,
        outer,
        dispatcher,
        search,
        records,
        mapping,
        work: budget.work,
    })
}

pub(in crate::proof) struct PreparedByteRoute<'a, 'tcx> {
    boundary: ByteBoundary<'a, 'tcx>,
    sources: byte_search_source::PreparedSources<'a, 'tcx>,
    scope: super::super::super::readonly_byte_origins::RouteScope<'a, 'tcx>,
    used: usize,
}

impl<'a, 'tcx> ByteBoundary<'a, 'tcx> {
    pub(super) fn prepare(
        self,
        scope: super::super::super::readonly_byte_origins::RouteScope<'a, 'tcx>,
    ) -> Result<PreparedByteRoute<'a, 'tcx>, String> {
        let sources = byte_search_source::prepare(self.engine, self.search, self.work)?;
        let mut work = byte_search_source::Work::new(sources.used())
            .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
        work.charge(24)
            .map_err(|error| self.engine.categorized_error(error.category, error.reason))?;
        Ok(PreparedByteRoute {
            boundary: self,
            sources,
            scope,
            used: work.used(),
        })
    }
}

pub(in crate::proof) struct BorrowedByteRoute<'a, 'tcx> {
    boundary: ByteBoundary<'a, 'tcx>,
    sources: byte_search_source::BorrowedSources<'a, 'tcx>,
}

impl<'a, 'tcx> PreparedByteRoute<'a, 'tcx> {
    pub(in crate::proof) fn used(&self) -> usize {
        self.used
    }

    pub(in crate::proof) fn bind_relation(
        &self,
        relation: &mut super::super::super::readonly_byte_origins::Relation<'_, 'tcx>,
    ) -> Result<usize, String> {
        relation.bind_route(&self.scope)
    }

    pub(in crate::proof) fn revalidate(
        self,
        engine: &'a Engine<'tcx>,
        outer: ty::Instance<'tcx>,
        original: Ty<'tcx>,
        prior: usize,
    ) -> Result<BorrowedByteRoute<'a, 'tcx>, String> {
        let mut work = revalidation_work(prior, self.used)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        work.charge(8 + 3 * self.boundary.records.len())
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        if !std::ptr::eq(self.boundary.engine, engine)
            || outer != self.boundary.outer
            || original != self.boundary.original
            || !self
                .boundary
                .records
                .iter()
                .any(|record| record.instance == self.boundary.dispatcher)
        {
            return Err("byte route belongs to another actual outer Instance/Engine".into());
        }
        let mut sources = self
            .sources
            .revalidate(engine, self.boundary.search, work.used())?;
        sources.check_route_records(&self.boundary.records)?;
        if let Some(mapping) = &self.boundary.mapping {
            sources.check_transport_signatures(mapping)?;
        }
        sources.route_handoff()?;
        Ok(BorrowedByteRoute {
            boundary: self.boundary,
            sources,
        })
    }
}

impl BorrowedByteRoute<'_, '_> {
    pub(in crate::proof) fn used(&self) -> usize {
        self.sources.used()
    }
    pub(in crate::proof) fn check_held(&mut self) -> Result<(), String> {
        self.sources.check_held()?;
        self.sources.check_route_records(&self.boundary.records)?;
        if let Some(mapping) = &self.boundary.mapping {
            self.sources.check_transport_signatures(mapping)?;
        }
        Ok(())
    }
    pub(in crate::proof) fn size_one_helper_fact(&mut self, prior: usize) -> Result<usize, String> {
        self.sources.size_one_helper_fact(prior)
    }
}

// Revalidation consumes its ready route. Establish the complete paid floor before any source
// service; even a rejected lower incoming total cannot create a cheaper continuation.
fn revalidation_work(
    prior: usize,
    ready: usize,
) -> Result<byte_search_source::Work, byte_search_source::Failure> {
    let mut work = byte_search_source::Work::new(ready)?;
    work.charge(4)?; // Actual floor comparison, difference and paid handoff dispatch.
    if prior < ready {
        return Err("byte route revalidation lost its complete paid preparation work".into());
    }
    work.charge(prior - ready)?;
    Ok(work)
}

// Retained core emits Copy for these original shared references. This complete additional
// transport schema is limited to the byte-route goal; ordinary canonical laws remain literal.
#[cfg(test)]
pub(super) fn copy_contains_reference(
    key: &str,
    encoded: &str,
    budget: &mut GraphBudget<'_>,
) -> Result<Option<super::super::super::pure_comparison_templates::PureTemplateFamily>, String> {
    const KEY: &str = "DefId(core::slice::{impl#0}::contains)";
    const BODY: &str = include_str!("byte-route-contains-copy.mir");
    budget.charge(6)?; // Actual additional matcher dispatch and equality services.
    budget.byte_route_reference_text(KEY.len() + BODY.len() + key.len() + encoded.len())?;
    Ok((key == KEY && BODY.strip_suffix('\n') == Some(encoded))
        .then_some(super::super::super::pure_comparison_templates::PureTemplateFamily::Contains))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_copy_transport_matcher_accepts_source_and_rejects_changed_arguments() {
        const KEY: &str = "DefId(core::slice::{impl#0}::contains)";
        let body = include_str!("byte-route-contains-copy.mir")
            .strip_suffix('\n')
            .unwrap();
        let mut budget = GraphBudget::new(0).unwrap();
        assert_eq!(
            copy_contains_reference(KEY, body, &mut budget).unwrap(),
            Some(
                super::super::super::super::pure_comparison_templates::PureTemplateFamily::Contains
            )
        );
        let changed = body.replace("copy _2/[]", "copy _1/[]");
        assert!(
            copy_contains_reference(KEY, &changed, &mut budget)
                .unwrap()
                .is_none()
        );
        assert!(
            copy_contains_reference("foreign Contains", body, &mut budget)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn route_revalidation_preserves_ready_work_before_source_services() {
        // Standalone actual floor gate, not issuance of a route/source/storage certificate.
        let mut issued_work = byte_search_source::Work::new(0).unwrap();
        issued_work.charge(24).unwrap();
        let ready = issued_work.used();
        let error = match revalidation_work(ready - 1, ready) {
            Ok(_) => panic!("a lowered ready work total was accepted"),
            Err(error) => error,
        };
        assert_eq!(error.category, UnknownCategory::Semantics);
        assert_eq!(
            error.reason,
            "byte route revalidation lost its complete paid preparation work"
        );
        assert_eq!(revalidation_work(ready, ready).unwrap().used(), ready + 7);
        assert_eq!(
            revalidation_work(ready + 19, ready).unwrap().used(),
            ready + 26
        );
        let error = match revalidation_work(usize::MAX, ready) {
            Ok(_) => panic!("overflowing incoming work was accepted"),
            Err(error) => error,
        };
        assert_eq!(error.category, UnknownCategory::ResourceLimit);
    }
}
