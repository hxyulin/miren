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
            "miren-maybe-uninit-values-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/maybe_uninit_values.rs")
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
        if matches!(*name, "uninitialized" | "conditional_uninitialized") {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.detail.contains("MaybeUninit payload is not initialized"))
            );
        }
        if matches!(*name, "uninitialized" | "conditional_uninitialized") {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.unknown_category == Some(UnknownCategory::Semantics))
            );
        }
        let refusal = match *name {
            "root_pattern" | "direct_pattern" | "nested_pattern" => {
                Some("MaybeUninit payload contains a restricted scalar pattern")
            }
            "wrong_primitive" => {
                Some("MaybeUninit extraction changes the exact compiler payload type")
            }
            "foreign_union" => Some("unsupported aggregate kind"),
            "reference_payload" | "pointer_payload" => {
                Some("MaybeUninit payload requires primitive or pure tuple types")
            }
            "safe_write" | "initialized_ref" => Some("unsupported place projection Deref"),
            "zeroed" => Some("intrinsics::write_bytes"),
            _ => None,
        };
        if let Some(refusal) = refusal {
            assert!(proof.obligations.iter().any(|o| o.detail.contains(refusal)));
        }
        if *name == "lookalike_guard" {
            assert!(
                !proof
                    .models
                    .iter()
                    .any(|m| m.starts_with("core::intrinsics::assert_inhabited:"))
            );
        }
        if *name == "uninhabited_guard" {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted
                        && o.detail.starts_with("compiler inhabitance guard"))
            );
        }
        if name.starts_with("exact_")
            || matches!(
                *name,
                "unique_unit"
                    | "unique_tuple"
                    | "whole_assignment"
                    | "nested_container"
                    | "copied_wrapper"
            )
        {
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
                    .obligations
                    .iter()
                    .any(|o| o.detail.starts_with("compiler inhabitance guard"))
            );
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|m| m.starts_with("core::mem::MaybeUninit::<T>::assume_init "))
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
fn compiler_certified_initialization_preserves_values_and_refuses_missing_payloads() {
    let entries = [
        ("exact_u8", ProofStatus::Proved),
        ("exact_u16", ProofStatus::Proved),
        ("exact_u32", ProofStatus::Proved),
        ("exact_u64", ProofStatus::Proved),
        ("exact_u128", ProofStatus::Proved),
        ("exact_usize", ProofStatus::Proved),
        ("exact_i8", ProofStatus::Proved),
        ("exact_i16", ProofStatus::Proved),
        ("exact_i32", ProofStatus::Proved),
        ("exact_i64", ProofStatus::Proved),
        ("exact_i128", ProofStatus::Proved),
        ("exact_isize", ProofStatus::Proved),
        ("exact_bool", ProofStatus::Proved),
        ("exact_tuple", ProofStatus::Proved),
        ("exact_f32", ProofStatus::Proved),
        ("exact_f64", ProofStatus::Proved),
        ("uninit_container", ProofStatus::Proved),
        ("unique_unit", ProofStatus::Proved),
        ("unique_tuple", ProofStatus::Proved),
        ("whole_assignment", ProofStatus::Proved),
        ("nested_container", ProofStatus::Proved),
        ("copied_wrapper", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("uninhabited_guard", ProofStatus::Refuted),
        ("lookalike_guard", ProofStatus::Proved),
        ("root_pattern", ProofStatus::Unknown),
        ("direct_pattern", ProofStatus::Unknown),
        ("nested_pattern", ProofStatus::Unknown),
        ("uninitialized", ProofStatus::Unknown),
        ("conditional_uninitialized", ProofStatus::Unknown),
        ("wrong_primitive", ProofStatus::Unknown),
        ("foreign_union", ProofStatus::Unknown),
        ("zst_adt", ProofStatus::Unknown),
        ("pointer_payload", ProofStatus::Unknown),
        ("reference_payload", ProofStatus::Unknown),
        ("safe_write", ProofStatus::Unknown),
        ("initialized_ref", ProofStatus::Unknown),
        ("zeroed", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}
#[test]
fn initialized_native_controls_pass_and_actual_constructor_mutation_fails() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "pub fn mutation_claim(value: u32) {\n",
        "    assert!(unsafe { MaybeUninit::new(value).assume_init() } == value);\n",
        "}",
    );
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(
            original,
            &original.replace("new(value)", "new(value.wrapping_add(1))"),
        ),
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
