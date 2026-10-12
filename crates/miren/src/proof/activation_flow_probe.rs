//! Hostile envelopes accompany actual compiler-produced sibling Returns.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReturnFault {
    Erased,
    OtherEngine,
    LostFloor,
    ClearedEnvelope,
    StaleEnvelope,
    OtherWork,
    DeletedHierarchy,
    AdvancedGeneration,
    ExpiredBody,
    OtherCall,
}

pub(super) const RETURN_FAULTS: [ReturnFault; 10] = [
    ReturnFault::Erased,
    ReturnFault::OtherEngine,
    ReturnFault::LostFloor,
    ReturnFault::ClearedEnvelope,
    ReturnFault::StaleEnvelope,
    ReturnFault::OtherWork,
    ReturnFault::DeletedHierarchy,
    ReturnFault::AdvancedGeneration,
    ReturnFault::ExpiredBody,
    ReturnFault::OtherCall,
];

pub(super) fn return_controls(
    engine: &Engine<'_>,
    caller: &State,
    returned: &Return,
    control: ReturnFault,
) {
    engine.activation_test_return_controls(caller, returned, control);
}

#[test]
fn cumulative_work_refuses_overflow_and_exhaustion() {
    super::activation_flow::test_work_controls();
}
