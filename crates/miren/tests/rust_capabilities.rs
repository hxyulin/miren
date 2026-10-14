#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use serde::Deserialize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-rust-capabilities-{}-{id}",
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

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema_version: u32,
    fixture: String,
    cases: Vec<Case>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    entry: String,
    family: String,
    expected: String,
    unknown_reason: Option<String>,
    unknown_category: Option<UnknownCategory>,
}

fn manifest() -> Manifest {
    let manifest: Manifest =
        serde_json::from_str(include_str!("../../../tests/capabilities/rust.json")).unwrap();
    assert_eq!(manifest.schema_version, 1);
    assert!(!manifest.cases.is_empty());
    for case in &manifest.cases {
        assert!(!case.family.is_empty());
        assert_eq!(case.expected == "unknown", case.unknown_reason.is_some());
        assert!(case.unknown_category.is_none() || case.expected == "unknown");
    }
    manifest
}

fn expected_status(case: &Case) -> ProofStatus {
    match case.expected.as_str() {
        "proved" => ProofStatus::Proved,
        "refuted" => ProofStatus::Refuted,
        "unknown" => ProofStatus::Unknown,
        other => panic!("unsupported capability expectation {other}"),
    }
}

fn fixture(manifest: &Manifest) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&manifest.fixture)
}

fn analyze(path: &Path, cases: &[Case], target: Option<&str>, optimized: bool) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for case in cases {
        command.args(["--entry", &case.entry]);
    }
    command
        .args([
            "--",
            "--crate-name=rust_capabilities",
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
        let expected = expected_status(case);
        assert_eq!(
            proof.status, expected,
            "{} / {} target={target:?} optimized={optimized}: {:?}",
            case.family, case.entry, proof.obligations
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
        if expected == ProofStatus::Unknown {
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation
                            .detail
                            .contains(case.unknown_reason.as_deref().unwrap())
                        && obligation.unknown_category
                            == Some(case.unknown_category.unwrap_or(UnknownCategory::Semantics))
                }),
                "{} target={target:?} optimized={optimized}: {:?}",
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
fn strict_rust_capability_matrix() {
    let manifest = manifest();
    let fixture = fixture(&manifest);
    assert!(native(&fixture));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = analyze(&fixture, &manifest.cases, target, optimized);
            check_report(&report, &manifest.cases, target, optimized);
        }
    }
}

#[test]
fn actual_reference_mutation_refutes_and_fails_native() {
    let manifest = manifest();
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let original_fixture = fixture(&manifest);
    let source = std::fs::read_to_string(&original_fixture).unwrap();
    let companion = original_fixture
        .parent()
        .unwrap()
        .join("nested_function_choice_cases.rs");
    let copied_companion = directory.0.join("nested_function_choice_cases.rs");
    std::fs::copy(&companion, &copied_companion).unwrap();
    assert_eq!(
        std::fs::read(companion).unwrap(),
        std::fs::read(copied_companion).unwrap()
    );
    let original = "*value += 1;";
    assert_eq!(source.matches(original).count(), 1);
    // Alter the shared helper body, not an assertion or analyzer expectation.
    std::fs::write(&mutated, source.replacen(original, "*value += 2;", 1)).unwrap();
    assert!(!native(&mutated));
    let cases = [Case {
        entry: "reference_effects".into(),
        family: "reference_slice".into(),
        expected: "refuted".into(),
        unknown_reason: None,
        unknown_category: None,
    }];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = analyze(&mutated, &cases, target, optimized);
            check_report(&report, &cases, target, optimized);
        }
    }
}
