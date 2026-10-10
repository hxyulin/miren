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
        let path =
            std::env::temp_dir().join(format!("miren-trait-upcasts-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trait_upcasts.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
) -> Report {
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
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.assumptions.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| {
                o.status == ProofStatus::Refuted && o.model.is_some() && o.query.is_some()
            }));
        }
    }
    report
}

#[test]
fn certified_supertraits_execute_concrete_bodies_and_preserve_rights() {
    let entries = [
        ("selected", ProofStatus::Proved),
        ("second_supertrait", ProofStatus::Proved),
        ("chained", ProofStatus::Proved),
        ("auto_trait_drop", ProofStatus::Proved),
        ("caller_backed", ProofStatus::Proved),
        ("mutable_effect", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("wrong_effect", ProofStatus::Refuted),
        ("actual_panic", ProofStatus::Refuted),
        ("incoming_object", ProofStatus::Unknown),
        ("analyzer_only::dead_owner", ProofStatus::Unknown),
        ("analyzer_only::escape", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized);
            for (name, _) in entries {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if matches!(
                    name,
                    "selected" | "second_supertrait" | "chained" | "caller_backed"
                ) {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function.contains("parent_reader")
                                || b.function.contains("Parent>::parent"))
                    );
                    assert!(
                        proof
                            .models
                            .iter()
                            .any(|m| m.ends_with("concrete compiler vtable dispatch"))
                    );
                }
                if name == "selected" {
                    assert!(proof.body_entries.iter().any(|b| b.function == "as_parent"));
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function == "<Number as Parent>::parent")
                    );
                }
                let expected = match name {
                    "incoming_object" => {
                        Some((UnknownCategory::Semantics, "unsupported argument type dyn"))
                    }
                    "analyzer_only::dead_owner" => Some((
                        UnknownCategory::Unclassified,
                        "reference points to dead or uninitialized storage",
                    )),
                    "analyzer_only::escape" => Some((
                        UnknownCategory::Unclassified,
                        "reference to frame-owned storage cannot escape its frame",
                    )),
                    _ => None,
                };
                if let Some((category, reason)) = expected {
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
            }
        }
    }
    missing_dependency_body();
}

fn missing_dependency_body() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#[derive(Clone, Copy)]
pub struct Number(pub u16);
pub trait Parent { fn parent(&self) -> u16; }
pub trait Child: Parent {}
impl Parent for Number {
    #[inline(never)]
    fn parent(&self) -> u16 { self.0 & 15 }
}
impl Child for Number {}
"#,
    )
    .unwrap();
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &caller,
        r#"#![no_std]
extern crate upcast_dependency;
use upcast_dependency::{Number, Child, Parent};
pub fn missing_body(value: u16) {
    let number = Number(value);
    let child: &dyn Child = &number;
    let parent: &dyn Parent = child;
    assert!(parent.parent() <= 15);
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let library = directory.0.join("libupcast_dependency.rlib");
            let mut compiler = Command::new("rustc");
            compiler
                .args([
                    "--crate-name=upcast_dependency",
                    "--crate-type=rlib",
                    "--edition=2024",
                ])
                .arg(&dependency)
                .arg("-o")
                .arg(&library)
                .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
            if optimized {
                compiler.arg("-Copt-level=2");
            }
            if let Some(target) = target {
                compiler.args(["--target", target]);
            }
            let output = compiler.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "missing_body",
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                ])
                .arg(&caller)
                .arg("--out-dir")
                .arg(&directory.0)
                .arg("--extern")
                .arg(format!("upcast_dependency={}", library.display()))
                .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
            if optimized {
                command.arg("-Copt-level=2");
            }
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout)
                .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "missing_body")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(
                proof.status,
                ProofStatus::Unknown,
                "{:?}",
                proof.obligations
            );
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(UnknownCategory::MissingCompilerEvidence)
                        && o.detail.contains("body")),
                "{:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
            assert!(proof.entry_assumptions.is_empty());
        }
    }
}

#[test]
fn concrete_parent_mutation_refutes_unchanged_claim_and_native_guard() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "        self.0 & 15";
    assert_eq!(source.matches(original).count(), 1);
    let mutation = source.replacen(original, "        self.0", 1);
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|b| b.function == "<Number as Parent>::parent")
            );
        }
    }
    for optimized in [false, true] {
        for (path, success) in [(&fixture(), true), (&mutant, false)] {
            let binary = directory.0.join("native-tests");
            let mut command = Command::new("rustc");
            command
                .args(["--test", "--edition=2024"])
                .arg(path)
                .arg("-o")
                .arg(&binary);
            if optimized {
                command.arg("-Copt-level=2");
            }
            let output = command.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let output = Command::new(&binary)
                .args(["native_tests::original", "--exact"])
                .output()
                .unwrap();
            assert_eq!(
                output.status.success(),
                success,
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}
