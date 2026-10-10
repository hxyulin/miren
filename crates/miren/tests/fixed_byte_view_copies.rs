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
            "miren-fixed-byte-copy-{}-{}",
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
fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}
fn verify(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    extra: &[String],
) -> Report {
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
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0);
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    command.args(extra);
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
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
        assert_eq!(proof.status, *expected, "{name}: {:#?}", proof.obligations);
        assert!(proof.assumptions.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
    }
    report
}
#[test]
fn finite_promoted_byte_copies_preserve_current_symbolic_backing_and_frontiers() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("direct", P),
        ("sibling", P),
        ("sequential", P),
        ("nested_prefix", P),
        ("branches", P),
        ("one", P),
        ("empty", P),
        ("exact_budget", P),
        ("wrong", R),
        ("wrong_sibling", R),
        ("bounds", R),
        ("mismatch", R),
        ("dynamic_source", U),
        ("two_inputs", U),
        ("shifted", U),
        ("raw_exposure", U),
        ("returned_opaque", U),
        ("opaque_returned", U),
        ("zero_copy", U),
        ("over_budget", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture("fixed_byte_view_copies.rs"),
                &entries,
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|e| e.function == "copy_selected")
            );
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("fixed immutable source"))
            );
            let over = report
                .functions
                .iter()
                .find(|f| f.name == "over_budget")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(over.obligations.iter().any(|o| o.unknown_category
                == Some(UnknownCategory::ResourceLimit)
                && o.detail.contains("fixed replacement budget")));
            for (name, detail) in [
                ("dynamic_source", "uncertified transport or effects"),
                ("opaque_returned", "unexposed incoming writable origin"),
                ("zero_copy", "unavailable or uninitialized bytes"),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|o| o.unknown_category == Some(UnknownCategory::Semantics)
                            && o.detail.contains(detail))
                );
            }
        }
    }
}
#[test]
fn actual_copy_replacement_mutation_refutes_and_fails_native_guard() {
    let source = std::fs::read_to_string(fixture("fixed_byte_view_copies.rs")).unwrap();
    assert!(source.contains("values[..2].copy_from_slice(&[17, 19]);"));
    let mutated = source.replacen(
        "values[..2].copy_from_slice(&[17, 19]);",
        "values[..2].copy_from_slice(&[17, 20]);",
        1,
    );
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, &mutated).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|e| e.function == "copy_selected")
            );
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("fixed immutable source"))
            );
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted
                        && o.query.is_some()
                        && o.model.is_some())
            );
        }
    }
    for optimized in [false, true] {
        for (path, mutant) in [
            (fixture("fixed_byte_view_copies.rs"), false),
            (mutant.clone(), true),
        ] {
            let executable = directory.0.join(format!("native-{optimized}-{mutant}"));
            let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            compiler
                .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
                .arg(path)
                .arg("-o")
                .arg(&executable);
            if optimized {
                compiler.arg("-Copt-level=2");
            }
            let output = compiler.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let mut command = Command::new(executable);
            if mutant {
                command.arg("mutation_guard");
            }
            assert_eq!(
                command.output().unwrap().status.code(),
                Some(if mutant { 101 } else { 0 })
            );
        }
    }
}
#[test]
fn external_copy_child_requires_actual_selected_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for (retained, library_optimized) in [(false, false), (true, false), (true, true)] {
                let directory = Directory::new();
                let library = directory.0.join("libfixed_byte_copy_dependency.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=fixed_byte_copy_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(fixture("fixed_byte_copy_dependency.rs"))
                    .arg("-o")
                    .arg(&library);
                if library_optimized {
                    compiler.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.output().unwrap().status.success());
                let report = verify(
                    &fixture("fixed_byte_copy_external.rs"),
                    &[(
                        "selected",
                        if retained && !library_optimized {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    )],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("fixed_byte_copy_dependency={}", library.display()),
                    ],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == "selected")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained && !library_optimized {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|e| e.function.contains("apply"))
                    );
                    assert!(
                        proof
                            .models
                            .iter()
                            .any(|m| m.contains("fixed immutable source"))
                    );
                } else if retained {
                    assert!(proof.obligations.iter().any(|o| {
                        o.detail
                            .contains("tracked raw addresses require a sized pointee")
                    }));
                } else {
                    assert!(
                        proof.obligations.iter().any(|o| o.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence))
                    );
                }
            }
        }
    }
}
