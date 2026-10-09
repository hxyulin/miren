//! Diagnostic UNKNOWN causes; categories never change proof outcomes.
use serde::{Deserialize, Serialize};

/// The producer's cause for an unfinished obligation, not a claim of infeasibility or a fix.
/// Untagged engine errors remain unclassified while producer coverage is extended.
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum UnknownCategory {
    /// Rust operations or validity rules outside the implemented model.
    Semantics,
    /// Required compiler bodies or certificates were not available.
    MissingCompilerEvidence,
    /// A solver could not decide or complete a query.
    Solver,
    /// A bounded analysis stopped before completing all paths.
    ResourceLimit,
    /// Required device or other external behavior is not modeled.
    ExternalEnvironment,
    /// No explicit producer cause was recorded.
    Unclassified,
}
