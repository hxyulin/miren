#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "miren-local-byte-copy-boundaries-{}-{nonce}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/local_byte_copy_boundaries.rs")
}

fn inspect(path: &Path, entries: &[(&str, ProofStatus)]) {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let scratch = Scratch::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
            for (name, _) in entries {
                command.args(["--entry", name]);
            }
            command
                .args(["--", "--crate-type=lib", "--edition=2024"])
                .arg(path)
                .arg("--out-dir")
                .arg(&scratch.0)
                .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            if optimized {
                command.arg("-Copt-level=2");
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
            });
            assert_eq!(
                output.status.success(),
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
                    "{target:?}/{optimized}: {name}: {proof:?}"
                );
                assert!(proof.assumptions.is_empty());
                assert!(proof.entry_assumptions.is_empty());
                assert!(proof.trusted_calls.is_empty());
                if *expected == ProofStatus::Refuted {
                    assert!(proof.obligations.iter().any(|o| {
                        o.status == ProofStatus::Refuted && o.query.is_some() && o.model.is_some()
                    }));
                }
                if name.starts_with("boundary_") {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function == "boundary_source")
                    );
                }
            }
        }
    }
}

fn mutant(source: &str) -> String {
    let implementation = "pub fn boundary_source() -> [u8; 128] {\n    [17; 128]\n}";
    assert_eq!(source.matches(implementation).count(), 1);
    source.replace(
        implementation,
        &implementation.replace("[17; 128]", "[19; 128]"),
    )
}

#[test]
fn empty_retention_and_exact_local_byte_array_boundaries() {
    inspect(
        &fixture(),
        &[
            ("empty_retains_first", ProofStatus::Proved),
            ("empty_wrong", ProofStatus::Refuted),
            ("boundary_positive", ProofStatus::Proved),
            ("boundary_wrong", ProofStatus::Refuted),
            ("oversized", ProofStatus::Unknown),
        ],
    );
}

#[test]
fn actual_payload_mutation_preserves_claims_and_refutes_copy() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let mutant = mutant(&original);
    let path = scratch.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    inspect(&path, &[("boundary_positive", ProofStatus::Refuted)]);
}

#[test]
fn genuine_native_claims_fail_after_the_actual_implementation_mutation() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let mutant = mutant(&original);
    for (label, source, expected) in [("original", original, 0), ("mutant", mutant, 101)] {
        let path = scratch.0.join(format!("{label}.rs"));
        std::fs::write(&path, source).unwrap();
        for level in [0, 2] {
            let executable = scratch.0.join(format!("{label}-{level}"));
            let compiler = Command::new("rustc")
                .arg(&path)
                .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
                .arg(format!("-Copt-level={level}"))
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                compiler.status.success(),
                "{}",
                String::from_utf8_lossy(&compiler.stderr)
            );
            let result = Command::new(executable)
                .args(["--exact", "native::genuine_claims"])
                .output()
                .unwrap();
            assert_eq!(result.status.code(), Some(expected));
            let output = String::from_utf8(result.stdout).unwrap();
            assert!(output.contains(if expected == 0 {
                "test result: ok. 1 passed; 0 failed;"
            } else {
                "test result: FAILED. 0 passed; 1 failed;"
            }));
        }
    }
}
