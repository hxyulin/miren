#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("miren-trait-objects-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trait_objects.rs")
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
        assert!(proof.trusted_calls.is_empty());
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn concrete_dispatch_preserves_methods_and_effects() {
    let entries = [
        ("concrete_shared", ProofStatus::Proved),
        ("incoming_concrete", ProofStatus::Proved),
        ("selected_concrete", ProofStatus::Proved),
        ("concrete_mutable", ProofStatus::Proved),
        ("inherited_slot", ProofStatus::Proved),
        ("concrete_panic", ProofStatus::Refuted),
        ("wrong_effect", ProofStatus::Refuted),
        ("arbitrary_object", ProofStatus::Unknown),
        ("arbitrary_mutable", ProofStatus::Unknown),
        ("upcast_unknown", ProofStatus::Proved),
        ("escaping_object", ProofStatus::Unknown),
        ("dead_object", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn changing_the_concrete_implementation_breaks_the_proof() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("        self.0 & 15", "        self.0", 1);
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("concrete_shared", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    let binary = directory.0.join("native-tests");
    assert!(
        Command::new("rustc")
            .args(["--test", "--edition=2024"])
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .status()
            .unwrap()
            .success()
    );
    assert!(!Command::new(binary).status().unwrap().success());
}

#[test]
fn concrete_dispatch_replays_and_associated_type_mismatches_are_rejected() {
    let directory = Directory::new();
    let binary = directory.0.join("native-tests");
    let output = Command::new("rustc")
        .args(["--test", "--edition=2024"])
        .arg(fixture())
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(Command::new(binary).output().unwrap().status.success());

    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("type Output = u8;", "type Output = u16;", 1);
    assert_ne!(source, mutation);
    let path = directory.0.join("wrong-associated-output.rs");
    std::fs::write(&path, mutation).unwrap();
    let output = Command::new("rustc")
        .args(["--crate-type=lib", "--edition=2024", "--emit=metadata"])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("incompatible type for trait"));
}
