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
        let path =
            std::env::temp_dir().join(format!("miren-static-metadata-{}-{id}", std::process::id()));
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

fn dependency(directory: &Directory, target: Option<&str>, optimized: bool) -> PathBuf {
    let library = directory.0.join("libdependency_statics.rlib");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args([
            "--crate-name=dependency_statics",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zalways-encode-mir=yes",
            "-Zmir-opt-level=0",
            "-Cpanic=abort",
        ])
        .arg(fixture("dependency_statics.rs"))
        .arg("-o")
        .arg(&library);
    if let Some(target) = target {
        compiler.args(["--target", target]);
    }
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    library
}

fn verify(
    path: &Path,
    target: Option<&str>,
    optimized: bool,
    startup: bool,
    entries: &[(&str, ProofStatus)],
) -> Report {
    let directory = Directory::new();
    let library = dependency(&directory, target, optimized);
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet", "--allow-assumptions"]);
    if startup {
        command.arg("--startup");
    }
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-name=static_metadata",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(path)
        .arg("--extern")
        .arg(format!("dependency_statics={}", library.display()))
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries.iter().all(|(_, status)| matches!(
            status,
            ProofStatus::Proved | ProofStatus::ProvedWithAssumptions
        ))
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(proof.status, *expected, "{name}: {:?}", proof.obligations);
        assert!(proof.trusted_calls.is_empty());
        if *expected == ProofStatus::Unknown {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation
                    .detail
                    .contains("dependency static initializer MIR unavailable")
            }));
        }
        if *expected == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.model.is_some())
            );
        }
    }
    report
}

#[test]
fn dependency_storage_origins_are_unknown_but_evaluated_frozen_initializers_are_available() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for startup in [false, true] {
                let frozen_status = if startup {
                    ProofStatus::ProvedWithAssumptions
                } else {
                    ProofStatus::Proved
                };
                verify(
                    &fixture("static_metadata.rs"),
                    target,
                    optimized,
                    startup,
                    &[
                        ("dependency_atomic", ProofStatus::Unknown),
                        ("dependency_frozen", frozen_status),
                        ("dependency_slice", frozen_status),
                    ],
                );
            }
        }
    }
}

#[test]
fn local_initializers_remain_available_and_initializer_mutations_fail() {
    let directory = Directory::new();
    let original = fixture("static_metadata.rs");
    let source = std::fs::read_to_string(&original).unwrap();
    assert!(source.contains("AtomicU32::new(7)"));
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source
            .replace("AtomicU32::new(7)", "AtomicU32::new(8)")
            .replace(
                "assert!(dependency_statics::frozen() == 7);",
                "assert!(dependency_statics::frozen() == 8);",
            ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &original,
                target,
                optimized,
                true,
                &[
                    ("local_initializer", ProofStatus::ProvedWithAssumptions),
                    (
                        "local_frozen_initializer",
                        ProofStatus::ProvedWithAssumptions,
                    ),
                ],
            );
            verify(
                &mutant,
                target,
                optimized,
                true,
                &[
                    ("local_initializer", ProofStatus::Refuted),
                    ("dependency_frozen", ProofStatus::Refuted),
                ],
            );
        }
    }
}
