#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-retained-owned-array-projections-{}-{id}",
            std::process::id()
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/retained_owned_array_projections.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if matches!(
            *name,
            "callee"
                | "equality"
                | "aliases"
                | "returned"
                | "refreshed"
                | "record"
                | "tuple"
                | "floats"
                | "zero"
                | "mutation_claim"
                | "different_roots"
                | "wrong_field"
                | "bounds"
                | "analyzer_only::copied_handle"
        ) {
            assert_eq!(
                proof
                    .inputs
                    .values()
                    .filter(|v| v.starts_with("lazy input;"))
                    .count(),
                3,
                "{name}: {:?}",
                proof.inputs,
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "reference_zero" | "refined_zero" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "over_cap" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::shared_reborrow" => (
                    UnknownCategory::Semantics,
                    "mutable borrow needs writable allocation storage",
                ),
                "analyzer_only::raw" => (
                    UnknownCategory::Unclassified,
                    "unsupported place projection Deref",
                ),
                "analyzer_only::owner_dead" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
                ),
                "analyzer_only::frame_escape" | "analyzer_only::typed_frame_escape" => (
                    UnknownCategory::Semantics,
                    "reference to frame-owned storage cannot escape",
                ),
                "analyzer_only::closure_escape" | "analyzer_only::shared_to_mut" => {
                    (UnknownCategory::Unclassified, "unsupported transmute")
                }
                "analyzer_only::closure_escape_identity" => (
                    UnknownCategory::Unclassified,
                    "reference to frame-owned storage cannot escape",
                ),
                other => panic!("missing expected frontier for {other}"),
            };
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(reason)),
                "{name}: {:?}",
                proof.obligations
            );
        }
        let body = match *name {
            "callee" | "aliases" | "refreshed" | "mutation_claim" => Some("first"),
            "returned" => Some("identity"),
            "record" | "wrong_field" => Some("record_left"),
            "analyzer_only::copied_handle" => Some("analyzer_only::forget_handle"),
            "analyzer_only::shared_reborrow" => Some("analyzer_only::reborrow_write"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof.body_entries.iter().any(|b| b.function == body),
                "{name}: {:?}",
                proof.body_entries
            );
        }
        if (*expected == ProofStatus::Proved && *name != "analyzer_only::static_source")
            || matches!(
                *name,
                "different_roots"
                    | "wrong_field"
                    | "custom_equality"
                    | "analyzer_only::shared_reborrow"
            )
        {
            assert!(
                proof.models.iter().any(|model| {
                    model == "compiler-certified retained owned array shared projection"
                }),
                "{name}: {:?}",
                proof.models
            );
        }
        if matches!(*name, "record" | "custom_equality") {
            let owner = if *name == "record" {
                "Record"
            } else {
                "FalseEquality"
            };
            assert!(
                proof.body_entries.iter().any(|entry| {
                    entry.function == format!("<{owner} as core::cmp::PartialEq>::eq")
                }),
                "{name}: {:?}",
                proof.body_entries
            );
        }
        if matches!(*name, "equality" | "bytes" | "zero") {
            assert!(
                proof.models.iter().any(|model| {
                    model.contains(
                        "fixed primitive array equality; exact numeric element comparisons",
                    )
                }),
                "{name}: {:?}",
                proof.models
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.model.is_some()
                    && obligation.query.is_some()
            }));
        }
    }
}

fn native_tests(path: &Path, directory: &Directory, optimized: bool, filter: Option<&str>) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let mut command = Command::new(compiler);
    command
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(executable);
    if let Some(filter) = filter {
        command.arg(filter);
    }
    command.output().unwrap().status.success()
}

#[test]
fn shared_typed_projections_preserve_owner_identity_and_liveness() {
    let entries = [
        ("callee", ProofStatus::Proved),
        ("equality", ProofStatus::Proved),
        ("aliases", ProofStatus::Proved),
        ("returned", ProofStatus::Proved),
        ("refreshed", ProofStatus::Proved),
        ("record", ProofStatus::Proved),
        ("tuple", ProofStatus::Proved),
        ("bytes", ProofStatus::Proved),
        ("floats", ProofStatus::Proved),
        ("zero", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("analyzer_only::copied_handle", ProofStatus::Proved),
        ("different_roots", ProofStatus::Refuted),
        ("wrong_field", ProofStatus::Refuted),
        ("custom_equality", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("over_cap", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::raw", ProofStatus::Unknown),
        ("analyzer_only::static_source", ProofStatus::Proved),
        ("analyzer_only::owner_dead", ProofStatus::Unknown),
        ("analyzer_only::frame_escape", ProofStatus::Unknown),
        ("analyzer_only::typed_frame_escape", ProofStatus::Unknown),
        ("analyzer_only::closure_escape", ProofStatus::Unknown),
        (
            "analyzer_only::closure_escape_identity",
            ProofStatus::Unknown,
        ),
        ("analyzer_only::shared_to_mut", ProofStatus::Unknown),
        ("analyzer_only::shared_reborrow", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_projected_getter_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn first(value: &[u16; 2]) -> u16 {\n    value[0]\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, &original.replace("value[0]", "value[1]")),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("mutation_claim", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_tests(&fixture(), &Directory::new(), optimized, None));
        assert!(!native_tests(
            &mutated,
            &Directory::new(),
            optimized,
            Some("mutation_guard"),
        ));
    }
}
