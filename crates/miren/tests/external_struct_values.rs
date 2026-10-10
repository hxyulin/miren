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
        let path = std::env::temp_dir().join(format!(
            "miren-external-struct-values-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/external_struct_values.rs")
}

fn dependency() -> PathBuf {
    fixture().with_file_name("external_struct_values_dependency.rs")
}

fn build_dependency(
    path: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    retained: bool,
    native: bool,
) -> PathBuf {
    let library = directory
        .0
        .join("libexternal_struct_values_dependency.rlib");
    let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    command
        .args([
            "--crate-name=external_struct_values_dependency",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zmir-opt-level=0",
            "-Coverflow-checks=yes",
        ])
        .arg(if retained {
            "-Zalways-encode-mir=yes"
        } else {
            "-Zalways-encode-mir=no"
        });
    if !native {
        command.arg("-Cpanic=abort");
    }
    command.arg(path).arg("-o").arg(&library);
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    library
}

fn verify(
    dependency_path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    retained: bool,
) {
    let directory = Directory::new();
    let library = build_dependency(
        dependency_path,
        &directory,
        target,
        optimized,
        retained,
        false,
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(fixture())
        .arg("--extern")
        .arg(format!(
            "external_struct_values_dependency={}",
            library.display()
        ))
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
        assert_eq!(
            proof.status, *expected,
            "{target:?} optimized={optimized} retained={retained} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected != ProofStatus::Unknown {
            assert!(
                proof.models.iter().any(|m| m.contains(concat!(
                    "readonly composite slice; exact compiler shape ",
                    "and independent primitive leaf arrays"
                ))) || *name == "owned"
            );
        }
        let body = match *name {
            "selected_method" if retained => Some("Pair::selected"),
            "borrowed_method" => Some("Pair::borrowed"),
            "overflow" => Some("Pair::checked_next"),
            "constructor_invariant" => Some("Private::get"),
            "zero" | "wrong_const" => Some("Zero::<N>::marker"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof.body_entries.iter().any(|b| b
                    .function
                    .starts_with("external_struct_values_dependency::")
                    && b.function.ends_with(body)),
                "{name}: {:?}",
                proof.body_entries
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
        if *expected == ProofStatus::Unknown {
            let (category, detail) = if !retained {
                (
                    UnknownCategory::MissingCompilerEvidence,
                    "MIR body unavailable for external_struct_values_dependency::Pair::selected",
                )
            } else if *name == "whole_contains" {
                (
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported",
                )
            } else if *name == "analyzer_only::dead_empty" {
                (UnknownCategory::Unclassified, "dead or uninitialized")
            } else if *name == "oversized" {
                (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                )
            } else {
                (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                )
            };
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(detail)),
                "{name}: {:?}",
                proof.obligations
            );
        }
    }
}

fn native_tests(dependency_path: &Path, optimized: bool, mutation: bool) -> bool {
    let directory = Directory::new();
    let library = build_dependency(dependency_path, &directory, None, optimized, true, true);
    let executable = directory.0.join("native");
    let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    command
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(fixture())
        .arg("--extern")
        .arg(format!(
            "external_struct_values_dependency={}",
            library.display()
        ))
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(executable);
    if mutation {
        command.arg("mutation_guard");
    }
    let output = command.output().unwrap();
    if output.status.success() == mutation {
        panic!("unexpected native output: {output:?}");
    }
    output.status.success()
}

#[test]
fn actual_dependency_struct_metadata_and_retained_bodies_preserve_rust_values() {
    let entries = [
        ("named", ProofStatus::Proved),
        ("tuple", ProofStatus::Proved),
        ("generic", ProofStatus::Proved),
        ("rich", ProofStatus::Proved),
        ("selected_method", ProofStatus::Proved),
        ("borrowed_method", ProofStatus::Proved),
        ("views", ProofStatus::Proved),
        ("layout", ProofStatus::Proved),
        ("owned", ProofStatus::Proved),
        ("zero", ProofStatus::Proved),
        ("independent_fields", ProofStatus::Refuted),
        ("constructor_invariant", ProofStatus::Refuted),
        ("overflow", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("wrong_const", ProofStatus::Refuted),
        ("reference_field", ProofStatus::Unknown),
        ("raw_field", ProofStatus::Unknown),
        ("refined_field", ProofStatus::Unknown),
        ("core_field", ProofStatus::Unknown),
        ("nonzero_field", ProofStatus::Unknown),
        ("packed", ProofStatus::Unknown),
        ("dropped", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("mutable", ProofStatus::Unknown),
        ("competing", ProofStatus::Unknown),
        ("whole_contains", ProofStatus::Unknown),
        ("analyzer_only::dead_empty", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&dependency(), &entries, target, optimized, true);
            verify(
                &dependency(),
                &[("selected_method", ProofStatus::Unknown)],
                target,
                optimized,
                false,
            );
        }
    }
}

#[test]
fn actual_dependency_field_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("changed_dependency.rs");
    let source = std::fs::read_to_string(dependency()).unwrap();
    let original = "    pub fn selected(&self) -> u16 {\n        self.left\n    }";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            "    pub fn selected(&self) -> u16 {\n        self.right\n    }",
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("selected_method", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_tests(&dependency(), optimized, false));
        assert!(!native_tests(&mutated, optimized, true));
    }
}
