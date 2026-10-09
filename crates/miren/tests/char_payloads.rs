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
            std::env::temp_dir().join(format!("miren-char-payloads-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/char_payloads.rs")
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
        if matches!(
            *name,
            "uninitialized" | "uninitialized_array" | "conditional"
        ) {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains("MaybeUninit payload is not initialized"))
            );
        }
        if name.starts_with("invalid_") {
            assert!(proof.obligations.iter().any(|o| {
                o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail
                        .contains("char formation requires a proven Unicode scalar value")
            }));
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
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|m| m.starts_with("core::mem::MaybeUninit::<T>::assume_init "))
            );
        }
        let refusal = match *name {
            "oversized" => Some("MaybeUninit array exceeds the 128-element budget"),
            "node_exhaustion" => {
                Some("MaybeUninit payload exceeds the bounded Copy Freeze value domain")
            }
            "pattern" | "empty_pattern" => {
                Some("MaybeUninit payload contains a restricted scalar pattern")
            }
            "wrong_type" => Some("MaybeUninit extraction changes the exact compiler payload type"),
            "initialized_ref" | "partial_write" => Some("unsupported place projection Deref"),
            "pointer_payload" => Some("MaybeUninit payload requires primitive or pure tuple types"),
            _ => None,
        };
        if let Some(refusal) = refusal {
            assert!(
                proof.obligations.iter().any(|o| o.detail.contains(refusal)),
                "{name}: expected {refusal}: {:?}",
                proof.obligations
            );
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
fn owned_char_payloads_preserve_exact_values_and_current_conditions() {
    let mut entries = vec![
        ("symbolic", ProofStatus::Proved),
        ("scalar_edges", ProofStatus::Proved),
        ("checked", ProofStatus::Proved),
        ("copied", ProofStatus::Proved),
        ("nested_tuple", ProofStatus::Proved),
        ("wrapper_carrier", ProofStatus::Proved),
        ("array", ProofStatus::Proved),
        ("selected_tuple", ProofStatus::Proved),
        ("boundary", ProofStatus::Proved),
        ("empty_initialized", ProofStatus::Proved),
        ("empty_uninitialized", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("wrong_element", ProofStatus::Refuted),
        ("uninitialized", ProofStatus::Unknown),
        ("uninitialized_array", ProofStatus::Unknown),
        ("conditional", ProofStatus::Unknown),
        ("invalid_surrogate", ProofStatus::Unknown),
        ("invalid_float", ProofStatus::Unknown),
        ("incoming", ProofStatus::Unknown),
        ("wrong_type", ProofStatus::Unknown),
        ("initialized_ref", ProofStatus::Unknown),
        ("partial_write", ProofStatus::Unknown),
        ("pointer_payload", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("node_exhaustion", ProofStatus::Unknown),
        ("pattern", ProofStatus::Unknown),
        ("empty_pattern", ProofStatus::Unknown),
    ];
    for optimized in [false, true] {
        verify(&fixture(), &entries, None, optimized);
    }
    entries.push(("invalid_pointer", ProofStatus::Unknown));
    for optimized in [false, true] {
        verify(
            &fixture(),
            &entries,
            Some("thumbv7em-none-eabihf"),
            optimized,
        );
    }
}

#[test]
fn native_complete_payloads_pass_and_real_initializer_mutation_fails() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn mutation_initializer() -> MaybeUninit<char> {\n",
        "    MaybeUninit::new('\\u{e000}')"
    );
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(original, &original.replace("e000", "e001")),
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
