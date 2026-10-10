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
        let path =
            std::env::temp_dir().join(format!("miren-nominal-box-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nominal_zst_boxes.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    verify_dependency(path, entries, target, optimized, None);
}

fn verify_dependency(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    library: Option<&Path>,
) {
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
    if let Some(library) = library {
        command
            .args(["--cfg=external_control", "--extern"])
            .arg(format!("stage188_dependency={}", library.display()));
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
                "nested" => (
                    UnknownCategory::Unclassified,
                    "unsupported memory projection",
                ),
                "core_zero" => (
                    UnknownCategory::Semantics,
                    "unsupported original child type",
                ),
                "ref_zero" | "raw_zero" | "pat_zero" | "aligned" => {
                    (UnknownCategory::Semantics, "size zero and alignment one")
                }
                "drop_payload" => (UnknownCategory::Semantics, "Copy, Freeze and no drop glue"),
                "enum_payload" | "external_payload" => (
                    UnknownCategory::Semantics,
                    "exact local nominal zero-sized struct",
                ),
                "weighted_raw_budget" => (
                    UnknownCategory::ResourceLimit,
                    "memory allocation budget reached",
                ),
                "foreign_helper" => (UnknownCategory::MissingCompilerEvidence, "missing_tag"),
                "arbitrary_input" => (
                    UnknownCategory::Unclassified,
                    "expected an issued owned Box region",
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
            "fieldless" | "wrong_tag" => Some("selected"),
            "transferred" => Some("transfer"),
            "custom_clone" => Some("<ClonePanic as core::clone::Clone>::clone"),
            "custom_eq" => Some("<FalseEq as core::cmp::PartialEq>::eq"),
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
        if *expected != ProofStatus::Unknown && *name != "small_raw" {
            assert!(proof.models.iter().any(|m| {
                m.contains("complete selected Box/Global nominal zero-branch certificate")
            }));
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
fn nominal_zero_boxes_preserve_original_payload_and_retirement() {
    let entries = [
        ("fieldless", ProofStatus::Proved),
        ("readonly", ProofStatus::Proved),
        ("automatic_drop", ProofStatus::Proved),
        ("transferred", ProofStatus::Proved),
        ("generic", ProofStatus::Proved),
        ("nested_copy", ProofStatus::Proved),
        ("wrong_tag", ProofStatus::Refuted),
        ("custom_clone", ProofStatus::Refuted),
        ("custom_eq", ProofStatus::Refuted),
        ("nested", ProofStatus::Unknown),
        ("ref_zero", ProofStatus::Unknown),
        ("raw_zero", ProofStatus::Unknown),
        ("pat_zero", ProofStatus::Unknown),
        ("core_zero", ProofStatus::Unknown),
        ("aligned", ProofStatus::Unknown),
        ("drop_payload", ProofStatus::Unknown),
        ("enum_payload", ProofStatus::Unknown),
        ("arbitrary_input", ProofStatus::Unknown),
        ("weighted_raw_budget", ProofStatus::Unknown),
        ("small_raw", ProofStatus::Proved),
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
    let original = "pub fn tag(&self) -> u16 {\n        17\n    }";
    assert_eq!(source.matches(original).count(), 1);
    let changed = directory.0.join("mutated.rs");
    std::fs::write(
        &changed,
        source.replace(original, "pub fn tag(&self) -> u16 {\n        18\n    }"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &changed,
                &[("fieldless", ProofStatus::Refuted)],
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

#[test]
fn foreign_helper_body_availability_is_distinct_from_external_payload_refusal() {
    let source = fixture();
    let dependency = source.with_file_name("nominal_zst_box_dependency.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage188_dependency.rlib");
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage188_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&library)
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    });
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                if optimized {
                    command.arg("-Copt-level=2");
                }
                let output = command.output().unwrap();
                assert!(output.status.success(), "{output:?}");
                verify_dependency(
                    &source,
                    &[
                        ("external_payload", ProofStatus::Unknown),
                        (
                            "foreign_helper",
                            if retained {
                                ProofStatus::Proved
                            } else {
                                ProofStatus::Unknown
                            },
                        ),
                    ],
                    target,
                    optimized,
                    Some(&library),
                );
            }
        }
    }
}
