#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-nested-integer-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nested_mutable_integers.rs")
}
fn verify(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    extra: &[String],
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=nested_mutable_integers",
            "--edition=2024",
            "-Coverflow-checks=yes",
        ])
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0);
    if !extra.iter().any(|arg| arg == "-Cpanic=unwind") {
        command.arg("-Cpanic=abort");
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    command.args(extra);
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    for (name, status) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *status,
            "{name}/{target:?}/{optimized}: {:?}",
            proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.entry_assumptions.is_empty()
                && proof.trusted_calls.is_empty()
        );
        match status {
            ProofStatus::Proved => {}
            ProofStatus::Refuted => {
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == ProofStatus::Refuted
                            && obligation.query.is_some()
                            && obligation.model.is_some())
                )
            }
            ProofStatus::Unknown => {
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == ProofStatus::Unknown
                            && obligation.query.is_none()
                            && obligation.model.is_none())
                )
            }
            ProofStatus::ProvedWithAssumptions => panic!("new assumptions are not permitted"),
        }
    }
    report
}

const MODULES: [&str; 11] = [
    "signed8",
    "signed16",
    "signed32",
    "signed64",
    "signed128",
    "signed_size",
    "unsigned16",
    "unsigned32",
    "unsigned64",
    "unsigned128",
    "unsigned_size",
];

#[test]
fn original_integer_hierarchy_compiler_frontiers() {
    use ProofStatus::{Proved as P, Refuted as R};
    let mut names = Vec::new();
    for module in MODULES {
        for (entry, active) in [
            ("selected", P),
            ("sibling", P),
            ("sequential", P),
            ("scalar_return", P),
            ("cast", P),
            ("wrong", R),
            ("bounds", R),
            ("deeper", P),
        ] {
            names.push((format!("{module}::{entry}"), active));
        }
    }
    let entries: Vec<_> = names
        .iter()
        .map(|(name, status)| (name.as_str(), *status))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, &[]);
        }
    }
}

#[test]
fn real_integer_scalar_mutation_refutes_the_same_claim() {
    let directory = Directory::new();
    let source = directory.0.join("mutant.rs");
    let original = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(original.matches("word ^ 0").count(), 1);
    std::fs::write(&source, original.replace("word ^ 0", "word ^ 1")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &source,
                &[("signed32::selected", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "signed32::selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "signed32::scalar")
            );
        }
    }
}
