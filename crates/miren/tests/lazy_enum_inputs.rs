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
            "miren-lazy-enum-inputs-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/lazy_enum_inputs.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
) {
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
        assert!(proof.trusted_calls.is_empty());
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
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
fn lazy_enum_descriptors_keep_all_variants_and_occurrence_identity() {
    let entries = [
        ("watching", ProofStatus::Proved),
        ("payload_variant_cap_stays_unknown", ProofStatus::Unknown),
        ("fieldless_variant_cap_stays_unknown", ProofStatus::Unknown),
        ("negative_driver_tag_is_reachable", ProofStatus::Refuted),
        (
            "positive_small_driver_tag_is_reachable",
            ProofStatus::Refuted,
        ),
        (
            "positive_wide_driver_tag_is_reachable",
            ProofStatus::Refuted,
        ),
        ("union_payloads_remain_unknown", ProofStatus::Unknown),
        (
            "direct_large_enum_payloads_keep_identity",
            ProofStatus::Proved,
        ),
        (
            "direct_sparse_negative_tag_is_reachable",
            ProofStatus::Refuted,
        ),
        ("direct_sparse_zero_tag_is_reachable", ProofStatus::Refuted),
        (
            "direct_sparse_positive_tag_is_reachable",
            ProofStatus::Refuted,
        ),
        ("reference_payloads_remain_unknown", ProofStatus::Unknown),
        (
            "observing_unvisited_enum_payloads_keeps_the_actual_field",
            ProofStatus::Proved,
        ),
        (
            "same_occurrence_keeps_exact_variant_and_payload",
            ProofStatus::Proved,
        ),
        (
            "sparse_signed_tags_keep_only_actual_variants",
            ProofStatus::Proved,
        ),
        (
            "owned_enum_copy_preserves_untouched_payloads",
            ProofStatus::Proved,
        ),
        ("separate_occurrences_can_differ", ProofStatus::Refuted),
        ("late_payload_claim_is_refuted", ProofStatus::Refuted),
        ("restricted_payloads_remain_unknown", ProofStatus::Unknown),
        ("pointer_payloads_remain_unknown", ProofStatus::Unknown),
        ("interior_payloads_remain_unknown", ProofStatus::Unknown),
        (
            "symbol_slot_exhaustion_remains_unknown",
            ProofStatus::Unknown,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
}

#[test]
fn mutating_actual_observed_field_fails_analysis_and_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("bench.watching", "!bench.watching", 1);
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[(
                    "observing_unvisited_enum_payloads_keeps_the_actual_field",
                    ProofStatus::Refuted,
                )],
                target,
                optimized,
                None,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
}
