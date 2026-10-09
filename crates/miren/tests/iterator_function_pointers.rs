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
            "miren-iterator-function-pointers-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/iterator_function_pointers.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
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
fn known_callback_values_execute_actual_bodies_in_order() {
    let entries = [
        (
            "owned_fold_and_reverse_fold_keep_order",
            ProofStatus::Proved,
        ),
        ("borrowed_fold_keeps_order", ProofStatus::Proved),
        (
            "for_each_preserves_last_element_effect",
            ProofStatus::Proved,
        ),
        (
            "selected_pointer_callbacks_preserve_each_branch",
            ProofStatus::Proved,
        ),
        ("owned_predicate_runs_actual_body", ProofStatus::Proved),
        (
            "predicate_short_circuit_preserves_cursor",
            ProofStatus::Proved,
        ),
        (
            "find_map_pointer_keeps_order_and_short_circuit",
            ProofStatus::Proved,
        ),
        ("wrong_fold_result_is_refuted", ProofStatus::Refuted),
        (
            "a_late_predicate_panic_is_not_skipped",
            ProofStatus::Refuted,
        ),
        ("arbitrary_pointer_input_is_unknown", ProofStatus::Unknown),
        (
            "reference_to_callback_remains_unknown",
            ProofStatus::Unknown,
        ),
        (
            "unsafe_callback_is_not_retyped_as_safe",
            ProofStatus::Unknown,
        ),
        (
            "non_rust_callback_is_not_retyped_as_rust",
            ProofStatus::Unknown,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
}

#[test]
fn callback_postconditions_are_checked_against_actual_return_values() {
    let specification = serde_json::json!({"schema_version": 1, "functions": [{
        "function": "iterator_function_pointers::decimal",
        "arguments": ["accumulator", "digit"],
        "ensures": ["result == accumulator"]
    }]});
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &[(
                    "owned_fold_and_reverse_fold_keep_order",
                    ProofStatus::Refuted,
                )],
                target,
                optimized,
                Some(specification.clone()),
            );
        }
    }
}

#[test]
fn mutated_callback_body_fails_analysis_and_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("accumulator * 10 + digit", "accumulator + digit", 1);
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[(
                    "owned_fold_and_reverse_fold_keep_order",
                    ProofStatus::Refuted,
                )],
                target,
                optimized,
                None,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
}

#[test]
fn known_iterator_callback_without_retained_dependency_body_stays_unknown() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#[inline(never)] pub fn narrow(value: u8) -> bool { value < 4 }\n",
    )
    .unwrap();
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args([
            "--crate-name=callback_dependency",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zalways-encode-mir=no",
        ])
        .arg(&dependency)
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let source = directory.0.join("caller.rs");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "pub fn entry(value: u8) {\n",
            "    let callback: fn(u8) -> bool = callback_dependency::narrow;\n",
            "    assert!([value].into_iter().all(callback));\n}\n",
        ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "entry",
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
        ])
        .arg(&source)
        .arg("--out-dir")
        .arg(&directory.0)
        .arg("--extern")
        .arg(format!(
            "callback_dependency={}",
            directory.0.join("libcallback_dependency.rlib").display()
        ))
        .output()
        .unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    let proof = report
        .functions
        .iter()
        .find(|function| function.name == "entry")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert!(!output.status.success());
    assert_eq!(proof.status, ProofStatus::Unknown);
    assert!(
        proof
            .obligations
            .iter()
            .any(|obligation| obligation.detail.contains("retained Rust body"))
    );
}
