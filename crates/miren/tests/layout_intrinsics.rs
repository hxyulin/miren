#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-layout-intrinsics-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/layout_intrinsics.rs")
}

fn verify(path: &Path, names: &[&str], target: Option<&str>, optimized: bool) -> (Output, Report) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json"]);
    for name in names {
        command.args(["--entry", name]);
    }
    command.args(["--", "--crate-type=lib", "--edition=2024"]);
    command.arg(path).arg("--out-dir").arg(&directory.0);
    command.args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=3");
    }
    let output = command.output().unwrap();
    let report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    (output, report)
}

#[test]
fn compiler_layout_guards_and_byte_float_encodings() {
    let entries = [
        ("slice_size", ProofStatus::Proved),
        ("array_size", ProofStatus::Proved),
        ("wide_slice_size", ProofStatus::Proved),
        ("bad_array_size", ProofStatus::Refuted),
        ("zero_guard", ProofStatus::Proved),
        ("bad_zero_guard", ProofStatus::Refuted),
        ("valid_zero_guard_then_panic", ProofStatus::Refuted),
        ("byte_float", ProofStatus::Proved),
        ("byte_word", ProofStatus::Proved),
        ("byte_wide_float", ProofStatus::Proved),
        ("special_byte_floats", ProofStatus::Proved),
        ("unsupported_byte_reference", ProofStatus::Unknown),
        ("unsupported_byte_char", ProofStatus::Unknown),
        ("unsupported_byte_range", ProofStatus::Unknown),
        ("unsupported_byte_bool", ProofStatus::Unknown),
        ("same_name_guard", ProofStatus::Refuted),
    ];
    let names: Vec<_> = entries.iter().map(|(name, _)| *name).collect();
    for (target, optimized) in [
        (None, false),
        (None, true),
        (Some("thumbv7em-none-eabihf"), false),
        (Some("thumbv7em-none-eabihf"), true),
    ] {
        let (_, report) = verify(&fixture(), &names, target, optimized);
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
                "{target:?} {name}: {:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty());
        }
    }
}

#[test]
fn byte_order_and_validity_mutations_fail() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutated = source
        .replace("u32::from_ne_bytes(bytes)", "u32::from_ne_bytes(bytes) ^ 1")
        .replace(
            "assert_zero_valid::<(u32, bool)>",
            "assert_zero_valid::<core::num::NonZeroU32>",
        );
    assert_ne!(source, mutated);
    let path = directory.0.join("layout_mutation.rs");
    std::fs::write(&path, mutated).unwrap();
    for (target, optimized) in [
        (None, false),
        (None, true),
        (Some("thumbv7em-none-eabihf"), false),
        (Some("thumbv7em-none-eabihf"), true),
    ] {
        let (_, report) = verify(&path, &["byte_float", "zero_guard"], target, optimized);
        for name in ["byte_float", "zero_guard"] {
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == name)
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(
                proof.status,
                ProofStatus::Refuted,
                "{target:?} {name}: {:?}",
                proof.obligations
            );
        }
    }
}

#[test]
fn native_rust_confirms_sizes_and_special_float_encodings() {
    let directory = Directory::new();
    let executable = directory.0.join("layout-native");
    let output = Command::new("rustc")
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(fixture())
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(executable).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn restricting_byte_cast_target_validity_returns_unknown() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn byte_word(bytes: [u8; 4]) -> u32";
    assert!(source.contains(original));
    for target_type in ["char", "Positive"] {
        let path = directory.0.join("restricted_layout.rs");
        std::fs::write(
            &path,
            source.replace(
                original,
                &format!("pub fn byte_word(bytes: [u8; 4]) -> {target_type}"),
            ),
        )
        .unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let (_, report) = verify(&path, &["byte_word"], target, false);
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "byte_word")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(
                proof.status,
                ProofStatus::Unknown,
                "{target:?} {target_type}: {:?}",
                proof.obligations
            );
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.detail.contains("unsupported transmute"))
            );
        }
    }
}
