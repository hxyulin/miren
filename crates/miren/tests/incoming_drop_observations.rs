#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/incoming_drop_observations.rs")
}

fn entered(report: &Report, entry: &str, callee: &str) {
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == entry)
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert!(
        proof
            .body_entries
            .iter()
            .any(|body| body.function.contains(callee))
    );
    assert!(proof.assumptions.is_empty());
    assert!(proof.trusted_calls.is_empty());
}

#[test]
fn lazy_drop_scalar_observations_execute_destructors_and_refuse_other_authority() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("borrowed", P),
                    ("direct", P),
                    ("nested", P),
                    ("wrong", R),
                    ("unguarded", R),
                    ("whole_unknown", P),
                    ("mutable_unknown", U),
                    ("raw_unknown", U),
                    ("reserved", P),
                    ("deferred", P),
                    ("reserved_constant", P),
                    ("reserved_wrong", R),
                    ("deferred_wrong", R),
                    ("deferred_unguarded", R),
                    ("scalar_codecs", P),
                    ("scalar_wrong", R),
                    ("char_eager_pressure", P),
                ],
                target,
                optimized,
                &[],
            );
            for entry in [
                "borrowed",
                "direct",
                "nested",
                "reserved",
                "deferred",
                "reserved_constant",
            ] {
                entered(&report, entry, "Record as core::ops::Drop");
                entered(&report, entry, "release_guard");
            }
            for (entry, reason) in [
                ("mutable_unknown", "grants no mutable reference authority"),
                ("raw_unknown", "grants no raw pointer authority"),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(proof.obligations.iter().any(|obligation| {
                    obligation.status == U
                        && obligation.unknown_category == Some(miren::UnknownCategory::Semantics)
                        && obligation.detail.contains(reason)
                }));
            }
            entered(&report, "scalar_codecs", "ScalarRecord as core::ops::Drop");
            entered(&report, "scalar_codecs", "signed_guard");
            for accessor in [
                "bool_accessor",
                "signed_accessor",
                "float_accessor",
                "wide_accessor",
            ] {
                entered(&report, "scalar_codecs", accessor);
            }
        }
    }
}

#[test]
fn genuine_lazy_drop_accessor_and_destructor_mutations_refute() {
    use ProofStatus::Refuted as R;
    let original = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (before, after) in [
        (
            "pub fn accessor(value: &u16) -> u16 {\n    *value\n}",
            "pub fn accessor(value: &u16) -> u16 {\n    *value ^ 1\n}",
        ),
        (
            "pub fn release_guard(value: u16) -> u16 {\n    value\n}",
            "pub fn release_guard(value: u16) -> u16 {\n    value ^ 1\n}",
        ),
    ] {
        assert_eq!(original.matches(before).count(), 1);
        let directory = Directory::new();
        let source = directory.0.join("mutated.rs");
        std::fs::write(&source, original.replacen(before, after, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let report = verify(
                    &source,
                    &[("reserved", R), ("deferred", R)],
                    target,
                    optimized,
                    &[],
                );
                for entry in ["reserved", "deferred"] {
                    entered(
                        &report,
                        entry,
                        if before.contains("release_guard") {
                            "release_guard"
                        } else {
                            "accessor"
                        },
                    );
                }
            }
        }
        for optimized in [false, true] {
            native(&source, optimized, true);
        }
    }
}
