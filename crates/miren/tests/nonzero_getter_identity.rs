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
            "miren-nonzero-getter-identity-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_getter_identity.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
    dependency: Option<&Path>,
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
    if let Some(dependency) = dependency {
        command
            .arg("--extern")
            .arg(format!("getter_dependency={}", dependency.display()));
    }
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
        for model in &proof.models {
            if model.ends_with(": nonzero integer value") {
                assert!(
                    model.starts_with("core::num::NonZero::<T>::get:"),
                    "{model}"
                );
            }
        }
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
fn only_the_actual_core_inherent_getter_receives_the_model() {
    let entries = [
        ("free_getter_body_returns_zero", ProofStatus::Proved),
        ("free_getter_is_not_the_core_getter", ProofStatus::Refuted),
        ("free_getter_panic_runs", ProofStatus::Refuted),
        ("trait_getter_body_returns_zero", ProofStatus::Proved),
        ("trait_getter_is_not_the_core_getter", ProofStatus::Refuted),
        ("trait_getter_panic_runs", ProofStatus::Refuted),
        ("genuine_unsigned_getter", ProofStatus::Proved),
        ("genuine_signed_getter", ProofStatus::Proved),
        ("genuine_pointer_width_getter", ProofStatus::Proved),
        ("wrong_genuine_getter_claim", ProofStatus::Refuted),
        ("unrelated_inherent_getter_runs", ProofStatus::Proved),
        ("unrelated_string_getter_is_unknown", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None, None);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
}

#[test]
fn mutating_actual_free_getter_body_refutes_and_fails_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen(
        "fn get(_: NonZeroU32) -> u32 {\n    0",
        "fn get(_: NonZeroU32) -> u32 {\n    1",
        1,
    );
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("free_getter_body_returns_zero", ProofStatus::Refuted)],
                target,
                optimized,
                None,
                None,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
}

#[test]
fn dependency_function_named_get_without_retained_body_stays_unknown() {
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let source = directory.0.join("getter_dependency.rs");
            std::fs::write(
                &source,
                "#![no_std]\n#[inline(never)] pub fn get(_: core::num::NonZeroU32) -> u32 { 0 }\n",
            )
            .unwrap();
            let library = directory.0.join("libgetter_dependency.rlib");
            let mut command = Command::new(&compiler);
            command
                .args([
                    "--crate-name=getter_dependency",
                    "--crate-type=rlib",
                    "--edition=2024",
                    "-Cpanic=abort",
                ])
                .arg(&source)
                .arg("-o")
                .arg(&library);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            if optimized {
                command.arg("-Copt-level=2");
            }
            let output = command.output().unwrap();
            assert!(output.status.success(), "{output:?}");
            let root = directory.0.join("root.rs");
            std::fs::write(
                &root,
                concat!(
                    "#![no_std]\n",
                    "pub fn unavailable_getter(value: core::num::NonZeroU32) { ",
                    "assert!(getter_dependency::get(value) == 0); }\n",
                ),
            )
            .unwrap();
            verify(
                &root,
                &[("unavailable_getter", ProofStatus::Unknown)],
                target,
                optimized,
                None,
                Some(&library),
            );
        }
    }
}
