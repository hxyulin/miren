//! Bounded isolated pointer weak-CAS retry frontiers preserve checked returning paths.
use super::*;
use rustc_middle::mir::BasicBlock;

const MAX_RETRY_VISITS: u8 = 3;

#[derive(Clone, Default)]
pub(super) struct Path {
    visits: BTreeMap<BasicBlock, u8>,
}

impl Path {
    pub(super) fn note(&mut self, block: BasicBlock) {
        let visits = self.visits.entry(block).or_default();
        *visits = visits.saturating_add(1);
    }

    pub(super) fn exhausted(&self, block: BasicBlock) -> bool {
        self.visits
            .get(&block)
            .is_some_and(|visits| *visits >= MAX_RETRY_VISITS)
    }
}

pub(super) fn cyclic_block(body: &Body<'_>, block: BasicBlock) -> bool {
    let mut pending: Vec<_> = body.basic_blocks[block].terminator().successors().collect();
    let mut seen = std::collections::BTreeSet::new();
    while let Some(next) = pending.pop() {
        if next == block {
            return true;
        }
        if seen.insert(next) {
            pending.extend(body.basic_blocks[next].terminator().successors());
        }
    }
    false
}

impl Engine<'_> {
    pub(super) fn record_retry_frontier(&mut self, id: DefId, span: Span) {
        self.proof.obligations.push(Obligation {
            unknown_category: Some(UnknownCategory::ResourceLimit),
            function: self.tcx.def_path_str(id),
            source: super::super::source(self.tcx, span.source_callsite()),
            kind: ObligationKind::Unsupported,
            detail: "isolated pointer weak-CAS retry frontier remains unfinished; checked \
                     returning paths continue without assuming eventual success"
                .into(),
            status: ProofStatus::Unknown,
            query: None,
            model: None,
            call_chain: self
                .call_chain
                .iter()
                .map(|id| self.tcx.def_path_str(*id))
                .collect(),
            abstraction_reasons: Vec::new(),
            replay: None,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retry_visits_are_branch_local_and_other_blocks_are_not_exhausted() {
        let block = BasicBlock::from_usize(2);
        let other = BasicBlock::from_usize(3);
        let mut original = Path::default();
        original.note(block);
        let mut branch = original.clone();
        branch.note(block);
        branch.note(block);
        assert!(branch.exhausted(block));
        assert!(!original.exhausted(block));
        assert!(!branch.exhausted(other));
    }
}
