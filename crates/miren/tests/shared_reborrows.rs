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
        let path = std::env::temp_dir().join(format!(
            "miren-shared-reborrows-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/shared_reborrows.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    let directory = Directory::new();
    let library = directory.0.join("libshared_reborrow_dependency.rlib");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args([
            "--crate-name=shared_reborrow_dependency",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zalways-encode-mir=yes",
            "-Zmir-opt-level=0",
            "-Cpanic=abort",
        ])
        .arg(fixture().with_file_name("shared_reborrow_dependency.rs"))
        .arg("-o")
        .arg(&library);
    if let Some(target) = target {
        compiler.args(["--target", target]);
    }
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--extern")
        .arg(format!("shared_reborrow_dependency={}", library.display()))
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
        let required_unknown = match *name {
            "dead_local_reborrow" | "nested_dead_local_reborrow" => Some("dead or uninitialized"),
            "local_pointer_escape" => Some("frame-owned"),
            "snapshot_address" => Some("tracked allocation reference"),
            _ => None,
        };
        if let Some(detail) = required_unknown {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.detail.contains(detail)),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn shared_snapshots_reborrow_without_temporary_allocation_lifetimes() {
    let entries = [
        ("static_reborrow", ProofStatus::Proved),
        ("dependency_reborrow", ProofStatus::Proved),
        ("wrong_static_reborrow", ProofStatus::Refuted),
        ("input_reborrow", ProofStatus::Proved),
        ("owned_local_reborrow", ProofStatus::Proved),
        ("snapshot_address", ProofStatus::Unknown),
        ("dead_local_reborrow", ProofStatus::Unknown),
        ("nested_dead_local_reborrow", ProofStatus::Unknown),
        ("local_pointer_escape", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn initializer_and_projected_field_mutations_are_refuted() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let directory = Directory::new();
    let path = directory.0.join("shared_reborrows.rs");
    for (original, replacement, entry) in [
        (
            "static INFO: Info = Info {\n    word: 7",
            "static INFO: Info = Info {\n    word: 8",
            "static_reborrow",
        ),
        ("&value.pair.1", "&value.pair.0", "input_reborrow"),
    ] {
        assert_eq!(source.matches(original).count(), 1);
        std::fs::write(&path, source.replace(original, replacement)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            verify(&path, &[(entry, ProofStatus::Refuted)], target, false);
        }
    }
}
