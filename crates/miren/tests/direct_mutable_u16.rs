#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-direct-u16-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/direct_mutable_u16.rs")
}
fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    contract: Option<&str>,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet", "--induction"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    if let Some(predicate) = contract {
        let config = directory.0.join("contracts.json");
        std::fs::write(
            &config,
            serde_json::to_vec(&serde_json::json!({
                "schema_version":1,"functions":[{"function":"direct_mutable_u16::ghost_length",
                "arguments":["values"],"ensures":[predicate]}]
            }))
            .unwrap(),
        )
        .unwrap();
        command.arg("--contracts").arg(config);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=direct_mutable_u16",
            "--edition=2024",
        ])
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
    let result = command.output().unwrap();
    let report: Report = serde_json::from_slice(&result.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&result.stderr)));
    assert_eq!(
        result.status.success(),
        entries.iter().all(|(_, s)| *s == ProofStatus::Proved)
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
            "{name} {target:?}/{optimized}: {:?}",
            proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.entry_assumptions.is_empty()
                && proof.trusted_calls.is_empty()
        );
        if *expected == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted
                        && o.query.is_some()
                        && o.model.is_some())
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "child_unknown" | "closure_unknown" | "raw_unknown" | "return_unknown" => (
                    UnknownCategory::Semantics,
                    "child reborrow requires child lease",
                ),
                "retained_shared" => (
                    UnknownCategory::Semantics,
                    "metadata needs original direct root",
                ),
                "metadata_helper_unknown" | "duplicate_metadata" => (
                    UnknownCategory::Semantics,
                    "metadata needs original direct root",
                ),
                "duplicate_root" => (UnknownCategory::Semantics, "one original borrow"),
                "analyzer_only::copied_root" | "analyzer_only::moved_root" => (
                    UnknownCategory::Semantics,
                    "Copy/Move transport is unsupported",
                ),
                "analyzer_only::dead_root" => (
                    UnknownCategory::Unclassified,
                    "uninitialized or unavailable local",
                ),
                "analyzer_only::aggregate_metadata" => {
                    (UnknownCategory::Semantics, "cannot enter aggregate storage")
                }
                "analyzer_only::raw_root" | "analyzer_only::raw_metadata" => {
                    (UnknownCategory::Semantics, "cannot issue a raw address")
                }
                "induction_unknown" => (
                    UnknownCategory::Semantics,
                    "separate inductive backing transport",
                ),
                _ => panic!("unmatched UNKNOWN {name}"),
            };
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(reason))
            );
        }
        if matches!(*name, "selected" | "wrong") {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|e| e.function == "replacement")
            );
        }
        if *expected == ProofStatus::Proved {
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("metadata-only length"))
            );
        }
        if contract.is_some() {
            assert!(
                proof
                    .matched_contracts
                    .iter()
                    .any(|c| c == "direct_mutable_u16::ghost_length")
            );
        }
    }
}

#[test]
fn direct_root_storage_and_restricted_metadata_cover_four_compiler_profiles() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("wrong", R),
        ("untouched", P),
        ("sequential", P),
        ("branches", P),
        ("empty", P),
        ("ghost_length", P),
        ("bounds", R),
        ("child_unknown", U),
        ("retained_shared", U),
        ("raw_unknown", U),
        ("duplicate_root", U),
        ("return_unknown", U),
        ("closure_unknown", U),
        ("analyzer_only::copied_root", U),
        ("analyzer_only::moved_root", U),
        ("analyzer_only::dead_root", U),
        ("analyzer_only::aggregate_metadata", U),
        ("analyzer_only::raw_root", U),
        ("analyzer_only::raw_metadata", U),
        ("induction_unknown", U),
        ("metadata_helper_unknown", U),
        ("duplicate_metadata", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
            verify(
                &fixture(),
                &[("ghost_length", P)],
                target,
                optimized,
                Some("final_values.len() == values.len()"),
            );
            verify(
                &fixture(),
                &[("ghost_length", R)],
                target,
                optimized,
                Some("final_values.len() != values.len()"),
            );
        }
    }
}

fn native(path: &Path, optimized: bool, mutant: bool) {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    assert!(compiler.output().unwrap().status.success());
    let mut run = Command::new(executable);
    if mutant {
        run.arg("mutation_guard");
    }
    assert_eq!(
        run.output().unwrap().status.code(),
        Some(if mutant { 101 } else { 0 })
    );
}
#[test]
fn actual_scalar_helper_mutation_refutes_and_valid_native_extent_is_129() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let pattern = "pub fn replacement(word: u16) -> u16 { word }";
    assert_eq!(source.matches(pattern).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(pattern, "pub fn replacement(word: u16) -> u16 { word ^ 1 }"),
    )
    .unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
        for target in [None, Some("thumbv7em-none-eabihf")] {
            verify(
                &mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
                None,
            );
        }
    }
}

#[test]
fn scalar_dependency_requires_its_actual_selected_body() {
    let dependency = fixture().with_file_name("direct_mutable_u16_dependency.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage184_dependency.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-name=stage184_dependency",
                        "--crate-type=rlib",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&library);
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                let output = compiler.output().unwrap();
                assert!(output.status.success(), "{output:?}");
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command
                    .args([
                        "--verify",
                        "--json",
                        "--quiet",
                        "--entry",
                        "external_scalar",
                        "--",
                        "--crate-type=lib",
                        "--crate-name=direct_mutable_u16",
                        "--edition=2024",
                        "--cfg=missing_dependency",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .arg(fixture())
                    .arg("--extern")
                    .arg(format!("stage184_dependency={}", library.display()))
                    .arg("--out-dir")
                    .arg(&directory.0);
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                let report: Report = serde_json::from_slice(&output.stdout)
                    .unwrap_or_else(|e| panic!("{e}: {output:?}"));
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == "external_scalar")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(
                    proof.status,
                    if retained {
                        ProofStatus::Proved
                    } else {
                        ProofStatus::Unknown
                    },
                    "{target:?}/{optimized}/{retained}: {:?}",
                    proof.obligations
                );
                assert!(
                    proof.assumptions.is_empty()
                        && proof.entry_assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                );
                if retained {
                    assert!(
                        proof.body_entries.iter().any(|entry| entry
                            .function
                            .contains("stage184_dependency::replacement"))
                    );
                } else {
                    assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|obligation| obligation.status == ProofStatus::Unknown
                                && obligation.unknown_category
                                    == Some(UnknownCategory::MissingCompilerEvidence))
                    );
                }
            }
        }
    }
}
