#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/retained_mutable_views.rs")
}
#[test]
fn actual_typed_retained_views_preserve_current_owner_and_sibling_storage() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("product_offset", P),
                    ("scalar_offset", P),
                    ("wrong_write", R),
                    ("wrong_extent", R),
                    ("invalid_range", R),
                    ("scalar_helper_unknown", U),
                    ("nested_unknown", U),
                    ("nll_unknown", U),
                    ("unsupported_codec", U),
                ],
                target,
                optimized,
                &[],
            );
            for entry in ["product_offset", "scalar_offset"] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(proof.body_entries.iter().any(|b| b.function == entry));
                assert!(
                    proof
                        .models
                        .iter()
                        .any(|m| m.contains("exclusive same-frame retained lease"))
                );
                assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
            }
            for (entry, reason) in [
                (
                    "scalar_helper_unknown",
                    "scalar helper transport is unsupported",
                ),
                ("nested_unknown", "reborrow requires exact current carrier"),
                ("nll_unknown", "current carrier witness"),
                ("unsupported_codec", "direct abort-only Rust body"),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof.obligations.iter().any(|o| o.status == U
                        && o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains(reason)),
                    "{entry}: {:?}",
                    proof.obligations
                );
            }
        }
    }
}
#[test]
fn genuine_child_writes_and_original_extent_mutations_refute() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (before, after, entry) in [
        (
            "child[0][0] = 1.0;\n            assert!",
            "child[0][0] = 3.0;\n            assert!",
            "product_offset",
        ),
        ("child[0] = word;", "child[0] = word ^ 1;", "scalar_offset"),
    ] {
        assert_eq!(original.matches(before).count(), 1);
        let directory = Directory::new();
        let source = directory.0.join("mutant.rs");
        std::fs::write(&source, original.replacen(before, after, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(
                    &source,
                    &[(entry, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
            }
        }
        for optimized in [false, true] {
            native(&source, optimized, true);
        }
    }
    let parent = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_slices.rs");
    let original = std::fs::read_to_string(&parent).unwrap();
    let before = "assert!(child.len() == 1);";
    assert_eq!(original.matches(before).count(), 1);
    let directory = Directory::new();
    let source = directory.0.join("extent_mutant.rs");
    std::fs::write(
        &source,
        original.replace(before, "assert!(child.len() == 2);"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &source,
                &[("proper_reborrow", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
        }
    }
}

#[test]
fn earlier_whole_staging_parent_is_unknown_before_child_extent_can_be_observed() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/retained_staging_parent.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &source,
                &[("earlier_staging_parent", ProofStatus::Unknown)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "earlier_staging_parent")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
            assert!(proof.obligations.iter().any(|o| {
                o.status == ProofStatus::Unknown
                    && o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail
                        .contains("retained issuance has another executable carrier")
            }));
            assert!(
                !proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted)
            );
        }
    }
}
