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
        let path = std::env::temp_dir().join(format!("miren-unit-box-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/zst_box_ownership.rs")
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
            "{target:?} {optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "nonzero" => (
                    UnknownCategory::Semantics,
                    "exact local nominal zero-sized struct",
                ),
                "aligned_zero" => (UnknownCategory::Semantics, "Copy, Freeze and no drop glue"),
                "analyzer_only::copied_owner" => (
                    UnknownCategory::Semantics,
                    "executable owned Box Copy needs",
                ),
                "analyzer_only::double_drop" => {
                    (UnknownCategory::Semantics, "owned region is unavailable")
                }
                "analyzer_only::mutable_virtual_owner" => (
                    UnknownCategory::Semantics,
                    "readonly virtual Box cannot acquire mutable",
                ),
                "analyzer_only::raw_virtual_owner" => (
                    UnknownCategory::Semantics,
                    "transport cannot issue a raw address",
                ),
                "analyzer_only::escaping_shared" => (
                    UnknownCategory::Unclassified,
                    "store_dangling: owned region is unavailable",
                ),
                "forgotten" => (
                    UnknownCategory::Semantics,
                    "live owned Box must retire or transfer",
                ),
                "mutable_access" => (UnknownCategory::Semantics, "readonly Unit borrowing only"),
                "incoming" => (
                    UnknownCategory::Unclassified,
                    "unmodeled call adapter Intrinsic",
                ),
                "pointer_equality" | "exposed_address" | "leaked" => (
                    UnknownCategory::Semantics,
                    "private owned region transport cannot issue a raw address",
                ),
                _ => panic!("unmatched UNKNOWN control {name}"),
            };
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
        let body = match *name {
            "selected_claim" | "selected_wrong" | "independent" => Some("selected"),
            "borrowed_claim" | "borrowed_wrong" => Some("borrowed"),
            "readonly_owner_claim" => Some("borrowed_unit"),
            "return_transfer" => Some("transfer"),
            "reached_panic" => Some("rejected"),
            "analyzer_only::raw_virtual_owner" => Some("analyzer_only::virtual_raw"),
            "analyzer_only::escaping_shared" => Some("analyzer_only::store_dangling"),
            "analyzer_only::mutable_virtual_owner" => Some("analyzer_only::virtual_mutation"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == body),
                "{name}"
            );
        }
        if *expected != ProofStatus::Unknown
            || name.starts_with("analyzer_only::")
            || *name == "forgotten"
        {
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("complete selected Box/Global Unit"))
            );
        }
        if matches!(
            *name,
            "automatic_drop" | "analyzer_only::escaping_shared" | "analyzer_only::double_drop"
        ) {
            assert!(proof.models.iter().any(|m| m.contains("region retired")));
        }
    }
}

fn native(path: &Path, optimized: bool, filter: Option<&str>) -> bool {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    command
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(executable);
    if let Some(filter) = filter {
        command.arg(filter);
    }
    command.output().unwrap().status.success()
}

#[test]
fn unit_box_ownership_preserves_regions_without_pointer_permissions() {
    let entries = [
        ("construct_drop", ProofStatus::Proved),
        ("selected_claim", ProofStatus::Proved),
        ("selected_wrong", ProofStatus::Refuted),
        ("borrowed_claim", ProofStatus::Proved),
        ("readonly_owner_claim", ProofStatus::Proved),
        ("borrowed_wrong", ProofStatus::Refuted),
        ("reached_panic", ProofStatus::Refuted),
        ("return_transfer", ProofStatus::Proved),
        ("independent", ProofStatus::Proved),
        ("automatic_drop", ProofStatus::Proved),
        ("nonzero", ProofStatus::Unknown),
        ("aligned_zero", ProofStatus::Unknown),
        ("pointer_equality", ProofStatus::Unknown),
        ("exposed_address", ProofStatus::Unknown),
        ("mutable_access", ProofStatus::Unknown),
        ("leaked", ProofStatus::Unknown),
        ("forgotten", ProofStatus::Unknown),
        ("incoming", ProofStatus::Unknown),
        ("analyzer_only::copied_owner", ProofStatus::Unknown),
        ("analyzer_only::double_drop", ProofStatus::Unknown),
        ("analyzer_only::mutable_virtual_owner", ProofStatus::Unknown),
        ("analyzer_only::escaping_shared", ProofStatus::Unknown),
        ("analyzer_only::raw_virtual_owner", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_owned_helper_mutation_refutes_and_fails_native_guard() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "core::mem::drop(owner);\n    19";
    assert_eq!(source.matches(original).count(), 1);
    let changed = directory.0.join("mutated.rs");
    std::fs::write(
        &changed,
        source.replace(original, "core::mem::drop(owner);\n    20"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &changed,
                &[("selected_claim", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native(&fixture(), optimized, None));
        assert!(!native(&changed, optimized, Some("mutation_guard")));
    }
}
