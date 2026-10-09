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
            "miren-immutable-root-storage-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/immutable_root_storage.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
) -> Report {
    let summary = specification.is_some();
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if let Some(specification) = specification {
        let config = directory.0.join("contracts.json");
        std::fs::write(&config, serde_json::to_vec(&specification).unwrap()).unwrap();
        command.arg("--contracts").arg(config);
    }
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
        assert_eq!(proof.trusted_calls.len(), usize::from(summary));
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
    report
}

fn native_tests(path: &Path, directory: &Directory) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn incoming_immutable_storage_retains_actual_lifetime_and_rejects_alias_frontiers() {
    let entries = [
        ("shared_zip", ProofStatus::Proved),
        ("byte_zip", ProofStatus::Proved),
        ("projected_zip", ProofStatus::Proved),
        ("aggregate_feedback_views", ProofStatus::Proved),
        ("returned_and_reborrowed", ProofStatus::Proved),
        ("root_local_storage_dead", ProofStatus::Proved),
        ("incoming_address_identity", ProofStatus::Proved),
        ("shared_write_unknown", ProofStatus::Unknown),
        ("wrong_shared_claim", ProofStatus::Refuted),
        ("competing_shared_unknown", ProofStatus::Unknown),
        ("competing_mutable_unknown", ProofStatus::Unknown),
        ("competing_pointer_unknown", ProofStatus::Unknown),
        ("nested_reference_unknown", ProofStatus::Unknown),
        ("nested_pointer_unknown", ProofStatus::Unknown),
        ("owned_nested_reference_unknown", ProofStatus::Unknown),
        ("owned_nested_pointer_unknown", ProofStatus::Unknown),
        ("competing_interior_unknown", ProofStatus::Unknown),
        ("dead_local_source_unknown", ProofStatus::Unknown),
        ("dead_callee_source_unknown", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
            let summary = serde_json::json!({"schema_version":1,"functions":[{
                "function":"immutable_root_storage::fixture_opaque_boundary",
                "arguments":[],"trusted":true,"no_panic":true,
                "reason":"Explicit fixture claim: opaque boundary with unspecified memory effects"
            }]});
            let report = verify(
                &fixture(),
                &[(
                    "opaque_invalidates_incoming_byte_view",
                    ProofStatus::Unknown,
                )],
                target,
                optimized,
                Some(summary),
            );
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "opaque_invalidates_incoming_byte_view")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.obligations.iter().any(|obligation| {
                obligation
                    .detail
                    .contains("reference points to dead or uninitialized storage")
            }));
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
}

#[test]
fn changing_the_shared_iterator_payload_fails_symbolic_and_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let needle = "*destination = *source;";
    assert_eq!(source.matches(needle).count(), 3);
    let mutation = source.replacen(needle, "*destination = 0;", 1);
    let directory = Directory::new();
    let path = directory.0.join("mutation.rs");
    std::fs::write(&path, mutation).unwrap();
    let entries = [("shared_zip", ProofStatus::Refuted)];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&path, &entries, target, optimized, None);
        }
    }
    assert!(!native_tests(&path, &directory));
}
