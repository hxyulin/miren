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
            "miren-typed-constant-index-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/typed_constant_indices.rs")
}
fn verify(source: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, level: &str) {
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
            "--crate-name=typed_constant_indices",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Copt-level={level}"))
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0);
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
            "{name}/{target:?}/{level}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty() && proof.entry_assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if *status == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
}

#[test]
fn original_typed_index_paths_keep_their_current_compiler_outcomes() {
    let entries = [
        ("first", ProofStatus::Proved),
        ("last", ProofStatus::Proved),
        ("wrong", ProofStatus::Refuted),
        ("bool_first", ProofStatus::Proved),
        ("char_first", ProofStatus::Proved),
        ("i32_first", ProofStatus::Proved),
        ("float_first", ProofStatus::Proved),
        ("child", ProofStatus::Proved),
        ("parent", ProofStatus::Proved),
        ("proper", ProofStatus::Unknown),
        ("unguarded", ProofStatus::Refuted),
        ("extra_field", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), &entries, target, level);
        }
    }
}

#[test]
fn actual_word_mutation_refutes_the_unchanged_claim() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("value ^ 0").count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace("value ^ 0", "value ^ 1")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&mutant, &[("first", ProofStatus::Refuted)], target, level);
        }
    }
}
