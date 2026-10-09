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
            std::env::temp_dir().join(format!("miren-large-enums-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/large_enum_inputs.rs")
}

fn verify(path: &Path, entries: &[&str], target: Option<&str>, optimized: bool) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for entry in entries {
        command.args(["--entry", entry]);
    }
    command.args([
        "--",
        "--crate-name=large_enum_inputs",
        "--crate-type=lib",
        "--edition=2024",
    ]);
    command.arg(path).arg("--out-dir").arg(&directory.0);
    command.args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert_eq!(output.status.code(), Some(1));
    serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)))
}

fn status(report: &Report, entry: &str) -> ProofStatus {
    report
        .functions
        .iter()
        .find(|function| function.name == entry)
        .unwrap()
        .proof
        .as_ref()
        .unwrap()
        .status
}

#[test]
fn sparse_signed_fieldless_enums_have_exact_valid_domains() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &["valid", "wrong", "concrete"],
                target,
                optimized,
            );
            assert_eq!(status(&report, "valid"), ProofStatus::Proved);
            assert_eq!(status(&report, "concrete"), ProofStatus::Proved);
            assert_eq!(status(&report, "wrong"), ProofStatus::Refuted);
        }
    }
}

#[test]
fn oversized_and_large_payload_enums_remain_unknown() {
    let directory = Directory::new();
    let path = directory.0.join("bounds.rs");
    let mut source = "#![no_std]\n#![forbid(unsafe_code)]\npub enum TooMany {\n".to_owned();
    for index in 0..257 {
        source.push_str(&format!("V{index},\n"));
    }
    source.push_str("}\npub enum Payload {\n");
    for index in 0..64 {
        source.push_str(&format!("V{index},\n"));
    }
    source.push_str("Data(u8),\n}\npub enum Maximum {\n");
    for index in 0..256 {
        source.push_str(&format!("V{index},\n"));
    }
    source.push_str("}\npub fn over(_: TooMany) {}\npub fn payload(_: Payload) {}\n");
    source.push_str("pub fn maximum(value: Maximum) { assert!((value as usize) < 256); }\n");
    source.push_str("pub fn exhausted(_: Maximum, _: Maximum) {}\n");
    std::fs::write(&path, source).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let report = verify(
            &path,
            &["over", "payload", "maximum", "exhausted"],
            target,
            false,
        );
        assert_eq!(status(&report, "over"), ProofStatus::Unknown);
        assert_eq!(status(&report, "payload"), ProofStatus::Unknown);
        assert_eq!(status(&report, "maximum"), ProofStatus::Proved);
        assert_eq!(status(&report, "exhausted"), ProofStatus::Unknown);
    }
}

#[test]
fn guard_mutation_refutes_and_matches_native_boundary() {
    let directory = Directory::new();
    let path = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture())
        .unwrap()
        .replace("tag <= 145", "tag <= 142");
    std::fs::write(&path, &source).unwrap();
    let report = verify(&path, &["valid", "wrong"], None, false);
    assert_eq!(status(&report, "valid"), ProofStatus::Refuted);
    let native = directory.0.join("native.rs");
    let source = source.replace("#![no_std]", "") + "\nfn main() { concrete(); }\n";
    std::fs::write(&native, source).unwrap();
    let executable = directory.0.join("native");
    assert!(
        Command::new("rustc")
            .arg(&native)
            .args(["--edition=2024", "-Cpanic=abort"])
            .arg("-o")
            .arg(&executable)
            .status()
            .unwrap()
            .success()
    );
    assert!(!Command::new(executable).output().unwrap().status.success());
}
