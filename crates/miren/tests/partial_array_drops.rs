#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-partial-drops-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/partial_array_drops.rs")
}
fn verify(path: &Path, target: Option<&str>, level: &str, mutant: bool) {
    use ProofStatus::Unknown as U;
    use ProofStatus::{Proved as P, Refuted as R};
    let entries = [
        ("partial_claim", if mutant { R } else { P }),
        ("partial_wrong", R),
        ("nested_claim", if mutant { R } else { P }),
        ("covering_claim", if mutant { R } else { P }),
        ("iterator_claim", U),
    ];
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (entry, _) in entries {
        command.args(["--entry", entry]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Copt-level={level}"))
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    assert!(!output.status.success());
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, expected,
            "{target:?}/O{level}/{name}: {:?}",
            proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.trusted_calls.is_empty()
                && proof.entry_assumptions.is_empty()
        );
        if name == "iterator_claim" {
            assert!(proof.obligations.iter().any(|o| {
                o.status == U
                    && o.query.is_none()
                    && o.model.is_none()
                    && o.detail
                        .contains("owned array iterator element destructors")
            }));
        } else {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.contains(" as core::ops::Drop"))
            );
        }
        if expected == R {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.status == R
                        && obligation.query.is_some()
                        && obligation.model.is_some()
                        && obligation.abstraction_reasons.is_empty())
            );
        }
    }
}
fn native(path: &Path, name: &str, level: &str) -> bool {
    let directory = Directory::new();
    let binary = directory.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args(["--test", "--edition=2024"])
        .arg(format!("-Copt-level={level}"))
        .arg(path)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let output = Command::new(binary)
        .args(["--exact", name])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&output.stdout).contains("running 1 test"));
    output.status.success()
}
#[test]
fn compiler_subslice_drop_preserves_actual_order_and_covering_assignment() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), target, level, false);
        }
    }
    for level in ["0", "2"] {
        for name in [
            "native::partial",
            "native::nested",
            "native::covering",
            "native::iterator",
        ] {
            assert!(native(&fixture(), name, level));
        }
        assert!(!native(&fixture(), "native::wrong", level));
    }
}
#[test]
fn actual_destructor_effect_mutation_refutes_unchanged_claims() {
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("wrapping_add(self.digit)").count(), 1);
    let changed = source.replacen(
        "wrapping_add(self.digit)",
        "wrapping_add(self.digit ^ 1)",
        1,
    );
    assert_ne!(source, changed);
    std::fs::write(&path, changed).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&path, target, level, true);
        }
    }
    for level in ["0", "2"] {
        assert!(!native(&path, "native::partial", level));
    }
}

#[test]
fn missing_dependency_destructor_body_remains_unknown() {
    let directory = Directory::new();
    let dependency = directory.0.join("omitted.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\npub struct External;\nimpl Drop for External {\n\
         #[inline(never)] fn drop(&mut self) { panic!(\"real omitted Drop\"); }\n}\n",
    )
    .unwrap();
    let library = directory.0.join("libomitted.rlib");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(&compiler)
        .args([
            "--crate-name=omitted",
            "--crate-type=rlib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Copt-level=0",
        ])
        .arg(&dependency)
        .arg("-o")
        .arg(&library)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let guest = directory.0.join("missing.rs");
    std::fs::write(
        &guest,
        "#![no_std]\npub fn missing() {\n\
         let values = [omitted::External, omitted::External]; drop(values); }\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "missing",
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Copt-level=0",
        ])
        .arg(&guest)
        .arg("--extern")
        .arg(format!("omitted={}", library.display()))
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let report: Report = serde_json::from_slice(&output.stdout).unwrap();
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == "missing")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert_eq!(
        proof.status,
        ProofStatus::Unknown,
        "{:?}",
        proof.obligations
    );
    assert!(proof.obligations.iter().any(|o| o.unknown_category
        == Some(miren::UnknownCategory::MissingCompilerEvidence)
        && o.detail.contains("MIR body unavailable")
        && o.query.is_none()
        && o.model.is_none()));
    assert!(
        proof.assumptions.is_empty()
            && proof.trusted_calls.is_empty()
            && proof.entry_assumptions.is_empty()
    );
}

#[test]
fn zero_array_drop_keeps_normal_no_drop_glue() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            let directory = Directory::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "zero_claim",
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                ])
                .arg(format!("-Copt-level={level}"))
                .arg(fixture())
                .arg("--out-dir")
                .arg(&directory.0);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            assert!(output.status.success(), "{output:?}");
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "zero_claim")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(proof.status, ProofStatus::Proved);
            assert!(
                proof.assumptions.is_empty()
                    && proof.trusted_calls.is_empty()
                    && proof.entry_assumptions.is_empty()
            );
        }
    }
}

#[test]
fn symbolic_unsigned_drop_order_and_wrapping_effects_have_real_counterexamples() {
    use ProofStatus::{Proved as P, Refuted as R};
    let entries = [
        ("symbolic_partial", P),
        ("symbolic_partial_wrong", R),
        ("symbolic_nested", P),
        ("symbolic_nested_wrong", R),
        ("symbolic_covering", P),
        ("symbolic_covering_wrong", R),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            let directory = Directory::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
            for (name, _) in entries {
                command.args(["--entry", name]);
            }
            command
                .args([
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(format!("-Copt-level={level}"))
                .arg(fixture())
                .arg("--out-dir")
                .arg(&directory.0);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            assert!(!output.status.success());
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            for (name, expected) in entries {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(
                    proof.status, expected,
                    "{target:?}/O{level}/{name}: {:?}",
                    proof.obligations
                );
                assert_eq!(
                    proof.inputs.len(),
                    if name.contains("partial") { 3 } else { 4 }
                );
                assert!(
                    proof.assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                        && proof.entry_assumptions.is_empty()
                );
                assert!(
                    proof
                        .analyzed_bodies
                        .iter()
                        .any(|body| body.contains("symbolic_"))
                );
                if name.contains("nested") || name.contains("covering") {
                    assert!(proof.models.iter().any(|model| {
                        model.contains("complete compiler array/slice DropGlue protocol")
                    }));
                }
                if expected == R {
                    assert!(proof.obligations.iter().any(|o| {
                        o.status == R
                            && o.query.as_ref().zip(o.model.as_ref()).is_some_and(
                                |(query, model)| {
                                    proof
                                        .inputs
                                        .values()
                                        .filter(|symbol| {
                                            (query.contains(&format!("(declare-const {symbol} "))
                                                || query
                                                    .contains(&format!("(declare-fun {symbol} ")))
                                                && model.contains(&format!("(define-fun {symbol} "))
                                        })
                                        .count()
                                        >= 2
                                },
                            )
                            && o.abstraction_reasons.is_empty()
                    }));
                }
            }
        }
    }
    for level in ["0", "2"] {
        assert!(native(&fixture(), "symbolic_native::positive", level));
        for name in [
            "symbolic_native::partial_wrong",
            "symbolic_native::nested_wrong",
            "symbolic_native::covering_wrong",
        ] {
            assert!(!native(&fixture(), name, level));
        }
    }
}
