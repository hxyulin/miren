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
            "miren-finite-slice-projections-{}-{id}",
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

struct Case {
    entry: &'static str,
    expected: ProofStatus,
    diagnostic: Option<&'static str>,
}

fn cases() -> Vec<Case> {
    [
        ("indexed_update", ProofStatus::Proved, None),
        ("nested_tuple_update", ProofStatus::Proved, None),
        ("shared_reborrow", ProofStatus::Proved, None),
        ("returned_view", ProofStatus::Proved, None),
        ("escaped_frame", ProofStatus::Unknown, Some("escape")),
        ("empty_at_end", ProofStatus::Proved, None),
        ("constrained_symbolic_length", ProofStatus::Proved, None),
        ("symbolic_scalar_offset", ProofStatus::Proved, None),
        ("callback_order", ProofStatus::Proved, None),
        ("bounded_large_backing", ProofStatus::Proved, None),
        ("wrong_callback_order", ProofStatus::Refuted, None),
        ("invalid_range", ProofStatus::Refuted, None),
        ("invalid_index", ProofStatus::Refuted, None),
        (
            "variable_length",
            ProofStatus::Unknown,
            Some("not uniquely determined"),
        ),
        (
            "ambiguous_tuple_offset",
            ProofStatus::Unknown,
            Some("not uniquely determined"),
        ),
        (
            "ambiguous_write",
            ProofStatus::Unknown,
            Some("array write index is not uniquely determined"),
        ),
        (
            "oversized",
            ProofStatus::Unknown,
            Some("128-element budget"),
        ),
        ("floating_shape", ProofStatus::Unknown, None),
        (
            "dead_empty",
            ProofStatus::Unknown,
            Some("dead or uninitialized storage"),
        ),
        ("shared_write", ProofStatus::Unknown, Some("shared")),
        (
            "opaque_effect",
            ProofStatus::Unknown,
            Some("arbitrary function-pointer"),
        ),
    ]
    .into_iter()
    .map(|(entry, expected, diagnostic)| Case {
        entry,
        expected,
        diagnostic,
    })
    .collect()
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/finite_slice_projections.rs")
}

fn analyze(path: &Path, cases: &[Case], target: Option<&str>, optimized: bool) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for case in cases {
        command.args(["--entry", case.entry]);
    }
    command
        .args([
            "--",
            "--crate-name=finite_slice_projections",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(!output.status.success(), "the matrix contains R/U controls");
    serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)))
}

fn check_report(report: &Report, cases: &[Case], target: Option<&str>, optimized: bool) {
    for case in cases {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == case.entry)
            .unwrap_or_else(|| panic!("missing capability {}", case.entry))
            .proof
            .as_ref()
            .unwrap();
        let expected = case.expected;
        assert_eq!(
            proof.status, expected,
            "{} target={target:?} optimized={optimized}: {:?}",
            case.entry, proof.obligations
        );
        assert!(proof.assumptions.is_empty(), "{}", case.entry);
        assert!(proof.entry_assumptions.is_empty(), "{}", case.entry);
        assert!(proof.trusted_calls.is_empty(), "{}", case.entry);
        if expected == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.model.is_some())
            );
        }
        if case.entry == "oversized" {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.unknown_category == Some(UnknownCategory::ResourceLimit)
            }));
        }
        if expected == ProofStatus::Unknown {
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && case
                            .diagnostic
                            .is_none_or(|detail| obligation.detail.contains(detail))
                        && obligation.unknown_category.is_some()
                }),
                "{}: {:?}",
                case.entry,
                proof.obligations
            );
        }
    }
}

fn native(path: &Path) -> bool {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Command::new(executable)
        .arg("native::")
        .output()
        .unwrap()
        .status
        .success()
}

#[test]
fn retained_finite_slice_projections_keep_backing_and_permissions() {
    let cases = cases();
    assert!(native(&fixture()));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = analyze(&fixture(), &cases, target, optimized);
            check_report(&report, &cases, target, optimized);
        }
    }
}

#[test]
fn actual_update_mutation_refutes_and_fails_native() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("*value += 1;").count(), 1);
    std::fs::write(&mutated, source.replace("*value += 1;", "*value += 2;")).unwrap();
    assert!(!native(&mutated));
    let cases = [Case {
        entry: "indexed_update",
        expected: ProofStatus::Refuted,
        diagnostic: None,
    }];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = analyze(&mutated, &cases, target, optimized);
            check_report(&report, &cases, target, optimized);
        }
    }
}
