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
            std::env::temp_dir().join(format!("miren-char-validity-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/char_validity.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if entries.iter().all(|(name, _)| name.starts_with("startup_")) {
        command.args(["--startup", "--allow-assumptions"]);
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
        entries.iter().all(|(_, status)| matches!(
            *status,
            ProofStatus::Proved | ProofStatus::ProvedWithAssumptions
        ))
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
            "surrogate"
                | "out_of_range"
                | "unconstrained"
                | "invalid_float_bits"
                | "expose_invalid"
                | "integer_cast_invalid"
                | "pointer_invalid"
                | "static_address"
        ) {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("char formation requires a proven Unicode scalar value")
                    && o.unknown_category == Some(UnknownCategory::Semantics)
            }));
        }
        if matches!(
            *name,
            "float_pattern_integer" | "float_pattern_char_zero" | "pointer_pattern"
        ) {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("scalar formation requires a proven compiler scalar pattern")
                    && o.unknown_category == Some(UnknownCategory::Semantics)
            }));
        }
        if *name == "float_pattern_char" {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("char formation requires a proven Unicode scalar value")
            }));
        }
        if *name == "no_initializer" {
            assert!(
                proof
                    .obligations
                    .iter()
                    .flat_map(|o| &o.abstraction_reasons)
                    .any(|r| r.contains("Unicode scalar domain encoding"))
            );
        }
        if *name == "checked" {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|b| b.contains("core::char::convert::from_u32"))
            );
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m.contains("Unicode validity proved"))
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
fn char_formation_proves_unicode_validity_and_executes_actual_checked_conversions() {
    let mut entries = vec![
        ("incoming", ProofStatus::Proved),
        ("checked", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("checked_unchecked", ProofStatus::Proved),
        ("exact_bits", ProofStatus::Proved),
        ("exact_signed", ProofStatus::Proved),
        ("output_bits", ProofStatus::Proved),
        ("byte_character", ProofStatus::Proved),
        ("valid_float_bits", ProofStatus::Proved),
        ("float_roundtrip", ProofStatus::Proved),
        ("zeroed", ProofStatus::Proved),
        ("surrogate", ProofStatus::Unknown),
        ("out_of_range", ProofStatus::Unknown),
        ("unconstrained", ProofStatus::Unknown),
        ("invalid_float_bits", ProofStatus::Unknown),
        ("expose_invalid", ProofStatus::Unknown),
        ("expose_valid", ProofStatus::Proved),
        ("integer_cast_invalid", ProofStatus::Unknown),
        ("integer_cast_valid", ProofStatus::Proved),
        ("static_domain", ProofStatus::Proved),
        ("cell_domain", ProofStatus::Proved),
        ("no_initializer", ProofStatus::Refuted),
        ("uninitialized", ProofStatus::Unknown),
        ("static_address", ProofStatus::Unknown),
        ("owned_wrapper", ProofStatus::Proved),
        ("float_pattern_integer", ProofStatus::Unknown),
        ("float_pattern_char", ProofStatus::Unknown),
        ("float_pattern_integer_valid", ProofStatus::Proved),
        ("float_pattern_char_valid", ProofStatus::Proved),
        ("float_pattern_char_zero", ProofStatus::Unknown),
    ];
    for optimized in [false, true] {
        verify(&fixture(), &entries, None, optimized);
    }
    entries.extend([
        ("pointer_invalid", ProofStatus::Unknown),
        ("pointer_valid", ProofStatus::Proved),
        ("pointer_pattern", ProofStatus::Unknown),
        ("pointer_pattern_valid", ProofStatus::Proved),
    ]);
    for optimized in [false, true] {
        verify(
            &fixture(),
            &entries,
            Some("thumbv7em-none-eabihf"),
            optimized,
        );
    }
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &[
                    ("startup_initializer", ProofStatus::ProvedWithAssumptions),
                    ("startup_store", ProofStatus::ProvedWithAssumptions),
                ],
                target,
                optimized,
            );
        }
    }
}

#[test]
fn valid_native_conversions_pass_and_actual_argument_mutation_is_refuted() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "pub fn mutation_claim(value: u32) {\n",
        "    if let Some(character) = char::from_u32(value) {"
    );
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(
            original,
            &original.replace("from_u32(value)", "from_u32(value ^ 1)"),
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
