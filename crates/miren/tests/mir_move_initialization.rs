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
            "miren-move-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mir_move_initialization.rs")
}
fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    verify_mode(path, entries, target, optimized, false);
}
fn verify_mode(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    induction: bool,
) {
    let dir = Directory::new();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_miren"));
    cmd.args(["--verify", "--json", "--quiet"]);
    if induction {
        cmd.arg("--induction");
    }

    for (name, _) in entries {
        cmd.args(["--entry", name]);
    }
    cmd.args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--out-dir")
        .arg(&dir.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if optimized {
        cmd.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        cmd.args(["--target", target]);
    }
    let output = cmd.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries.iter().all(|(_, s)| *s == ProofStatus::Proved)
    );
    for (name, status) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *status,
            "{target:?}/{optimized}/{name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *status == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted
                        && o.query.is_some()
                        && o.model.is_some())
            );
        }
        if *name == "analyzer_only::overlapping_call_claim" {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains("call Move input overlaps return storage"))
            );
        }
        for (entry, reason) in [
            (
                "analyzer_only::terminal_reference_argument",
                "inductive return retains an observable consumed source place",
            ),
            (
                "analyzer_only::terminal_addressed_argument",
                "inductive return retains unavailable allocation storage",
            ),
        ] {
            if *name == entry {
                assert!(proof.obligations.iter().any(|o| {
                    o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains(reason)
                }));
            }
        }
        if [
            "analyzer_only::stale_after_call_claim",
            "analyzer_only::duplicate_call_move_claim",
            "analyzer_only::stale_alias",
            "analyzer_only::stale_whole_claim",
            "analyzer_only::stale_field_claim",
            "analyzer_only::double_field_drop_claim",
            "analyzer_only::moved_static_handle_store",
            "analyzer_only::consumed_unit_return",
            "analyzer_only::whole_consumed_tag",
            "analyzer_only::ancestor_consumed_tag",
            "analyzer_only::payload_after_move_claim",
            "analyzer_only::no_drop_cannot_repair",
            "analyzer_only::terminal_current_argument",
        ]
        .contains(name)
        {
            assert!(proof.obligations.iter().any(|o| {
                o.status == ProofStatus::Unknown
                    && o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail
                        .contains("place initialization is unavailable after ownership consumption")
            }));
        }
    }
}
#[test]
fn ownership_consumption_preserves_destination_siblings_and_reinitialization() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("safe_whole", P),
        ("ordinary_reassignment", P),
        ("noncopy_result_payload", P),
        ("analyzer_only::retained_tag_claim", P),
        ("analyzer_only::whole_consumed_tag", U),
        ("analyzer_only::ancestor_consumed_tag", U),
        ("analyzer_only::payload_after_move_claim", U),
        ("analyzer_only::no_drop_payload_nop", P),
        ("analyzer_only::no_drop_cannot_repair", U),
        ("safe_partial", P),
        ("safe_drop", P),
        ("transferred", P),
        ("reinitialize", P),
        ("moved_handle", P),
        ("wrong_transfer", R),
        ("analyzer_only::moved_destination", P),
        ("analyzer_only::unaffected_sibling", P),
        ("analyzer_only::live_sibling_alias", P),
        ("analyzer_only::stale_after_call", U),
        ("analyzer_only::stale_after_call_claim", U),
        ("analyzer_only::duplicate_call_move", U),
        ("analyzer_only::duplicate_call_move_claim", U),
        ("analyzer_only::stale_whole", U),
        ("analyzer_only::stale_field", U),
        ("analyzer_only::stale_whole_claim", U),
        ("analyzer_only::stale_field_claim", U),
        ("analyzer_only::stale_alias", U),
        ("analyzer_only::double_field_drop", U),
        ("analyzer_only::double_field_drop_claim", U),
        ("analyzer_only::moved_static_handle_store", U),
        ("analyzer_only::indexed_move", U),
        ("analyzer_only::consumed_unit_return", U),
        ("analyzer_only::overlapping_call_claim", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}
#[test]
fn inductive_consumption_cannot_reappear_in_caller_ghosts() {
    let entries = [
        (
            "analyzer_only::terminal_owned_argument",
            ProofStatus::Proved,
        ),
        (
            "analyzer_only::terminal_reference_argument",
            ProofStatus::Unknown,
        ),
        (
            "analyzer_only::terminal_addressed_argument",
            ProofStatus::Unknown,
        ),
        (
            "analyzer_only::terminal_current_argument",
            ProofStatus::Unknown,
        ),
        ("analyzer_only::inductive_live_move", ProofStatus::Unknown),
        ("analyzer_only::consumed_unit_return", ProofStatus::Unknown),
        (
            "analyzer_only::overlapping_call_claim",
            ProofStatus::Unknown,
        ),
        ("ordinary_reassignment", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_mode(&fixture(), &entries, target, optimized, true);
        }
    }
}
fn native(path: &Path, optimized: bool) -> bool {
    let dir = Directory::new();
    let binary = dir.0.join("native");
    let mut cmd = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    cmd.args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&binary);
    if optimized {
        cmd.arg("-Copt-level=2");
    }
    let output = cmd.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Command::new(binary).output().unwrap().status.success()
}
#[test]
fn actual_callee_mutation_refutes_and_fails_valid_native_companion() {
    let dir = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutant = source.replacen(
        "fn chosen(value: Token) -> u16 {\n    value.word",
        "fn chosen(value: Token) -> u16 {\n    value.word ^ 1",
        1,
    );
    assert_ne!(source, mutant);
    let path = dir.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    for optimized in [false, true] {
        assert!(native(&fixture(), optimized));
        assert!(!native(&path, optimized));
        for target in [None, Some("thumbv7em-none-eabihf")] {
            verify(
                &path,
                &[("transferred", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
}
