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
            std::env::temp_dir().join(format!("miren-raw-subobjects-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/raw_subobjects.rs")
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
        assert!(proof.trusted_calls.is_empty());
        let boundary = match *name {
            "frame_element_escape" => Some("frame-owned storage cannot escape"),
            "multiple_shared_inputs_have_no_subobject_origin" => {
                Some("tracked allocation reference")
            }
            "symbolic_mutation" => Some("non-scalar array index is not uniquely determined"),
            "duplicate_mutable_subobjects" => Some("overlapping or unproved-disjoint"),
            "numeric_addresses_cannot_become_references" => Some("fabricate allocation provenance"),
            "shared_subobjects_cannot_gain_write_permission" => Some("upgrade shared storage"),
            "dead_subobject_origin" => Some("dead or uninitialized storage"),
            "raw_subobject_reads_remain_unknown" => Some("unsupported place projection Deref"),
            _ => None,
        };
        if let Some(boundary) = boundary {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| { o.status == ProofStatus::Unknown && o.detail.contains(boundary) }),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn typed_subobject_addresses_and_each_mut_on_host_and_arm() {
    let entries = [
        ("array_mutations", ProofStatus::Proved),
        ("guarded_element_address", ProofStatus::Proved),
        ("unguarded_element_address", ProofStatus::Refuted),
        ("field_address", ProofStatus::Proved),
        ("frame_element_escape", ProofStatus::Unknown),
        (
            "incoming_reference_subobject_provenance",
            ProofStatus::Proved,
        ),
        (
            "multiple_shared_inputs_have_no_subobject_origin",
            ProofStatus::Unknown,
        ),
        ("symbolic_mutation", ProofStatus::Unknown),
        ("nested_array_mutations", ProofStatus::Proved),
        ("zero_sized_subobjects", ProofStatus::Proved),
        ("subobject_one_past", ProofStatus::Proved),
        ("subobject_extent_is_not_the_parent", ProofStatus::Refuted),
        ("raw_subobject_reads_remain_unknown", ProofStatus::Unknown),
        ("dead_subobject_origin", ProofStatus::Unknown),
        ("duplicate_mutable_subobjects", ProofStatus::Unknown),
        (
            "numeric_addresses_cannot_become_references",
            ProofStatus::Unknown,
        ),
        (
            "shared_subobjects_cannot_gain_write_permission",
            ProofStatus::Unknown,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
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
fn changing_a_subobject_claim_fails_static_and_native_checks() {
    assert!(native_tests(&fixture(), &Directory::new()));
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "assert!(values == [7, 11, 19]);";
    assert!(source.contains(original));
    std::fs::write(
        &mutant,
        source.replacen(original, "assert!(values == [7, 11, 20]);", 1),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &[("array_mutations", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    assert!(!native_tests(&mutant, &directory));
}

#[test]
fn the_compiler_rejects_a_spoofed_tuple_field_type() {
    let directory = Directory::new();
    let source = directory.0.join("spoofed.rs");
    std::fs::write(
        &source,
        r#"
#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn spoofed(mut value: (u32, u32)) -> *mut f32 {
    mir! { { RET = &raw mut Field::<f32>(value, 0); Return() } }
}
"#,
    )
    .unwrap();
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--crate-type=lib", "--edition=2024", "--emit=metadata"])
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("mismatched types"));
}
