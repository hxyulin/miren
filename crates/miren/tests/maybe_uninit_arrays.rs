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
            "miren-maybe-uninit-arrays-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/maybe_uninit_arrays.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
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
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if matches!(*name, "uninitialized" | "conditional") {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains("MaybeUninit payload is not initialized"))
            );
        }
        if *expected == ProofStatus::Proved {
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("compiler-certified MaybeUninit extraction"))
            );
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.starts_with("core::intrinsics::assert_inhabited:"))
            );
        }
        let refusal = match *name {
            "oversized" => Some("MaybeUninit array exceeds the 128-element budget"),
            "node_exhaustion" | "zero_byte_node_exhaustion" | "depth_exhaustion" => {
                Some("MaybeUninit payload exceeds the bounded Copy Freeze value domain")
            }
            "pattern_elements" | "nested_pattern_elements" => {
                Some("MaybeUninit payload contains a restricted scalar pattern")
            }
            "wrong_type" => Some("MaybeUninit extraction changes the exact compiler payload type"),
            _ => None,
        };
        if let Some(refusal) = refusal {
            assert!(proof.obligations.iter().any(|o| o.detail.contains(refusal)));
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

fn native_tests(path: &Path, directory: &Directory, optimized: bool) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let mut command = Command::new(compiler);
    command
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn whole_array_initialization_preserves_values_and_checks_exact_shape_limits() {
    let entries = [
        ("integers", ProofStatus::Proved),
        ("bytes", ProofStatus::Proved),
        ("bools", ProofStatus::Proved),
        ("tuples", ProofStatus::Proved),
        ("nested", ProofStatus::Proved),
        ("float_bits", ProofStatus::Proved),
        ("float64_bits", ProofStatus::Proved),
        ("boundary", ProofStatus::Proved),
        ("node_boundary", ProofStatus::Proved),
        ("empty_initialized", ProofStatus::Proved),
        ("empty_bytes", ProofStatus::Proved),
        ("empty_integers", ProofStatus::Proved),
        ("unique_units", ProofStatus::Proved),
        ("unique_nested", ProofStatus::Proved),
        ("replaced", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("bounds_failure", ProofStatus::Refuted),
        ("uninitialized", ProofStatus::Unknown),
        ("conditional", ProofStatus::Unknown),
        ("wrong_type", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("node_exhaustion", ProofStatus::Unknown),
        ("zero_byte_node_exhaustion", ProofStatus::Unknown),
        ("depth_exhaustion", ProofStatus::Unknown),
        ("raw_elements", ProofStatus::Unknown),
        ("reference_elements", ProofStatus::Unknown),
        ("never_elements", ProofStatus::Unknown),
        ("nonzero_elements", ProofStatus::Unknown),
        ("drop_elements", ProofStatus::Unknown),
        ("arbitrary_wrapper", ProofStatus::Unknown),
        ("array_assume_init", ProofStatus::Unknown),
        ("wrapper_repeat", ProofStatus::Unknown),
        ("reference_result", ProofStatus::Unknown),
        ("zeroed", ProofStatus::Unknown),
        ("pattern_elements", ProofStatus::Unknown),
        ("nested_pattern_elements", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}
#[test]
fn initialized_array_helper_mutation_refutes_and_fails_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "MaybeUninit::new([3, 5, 7]).assume_init()";
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(original, "MaybeUninit::new([3, 6, 7]).assume_init()"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("mutation_claim", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_tests(&fixture(), &Directory::new(), optimized));
        assert!(!native_tests(&mutated, &Directory::new(), optimized));
    }
}
