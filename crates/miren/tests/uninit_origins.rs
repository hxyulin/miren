#![forbid(unsafe_code)]

use miren::static_origins::{Evidence, sidecar};
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("miren-origins-{}-{id}", std::process::id()));
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

fn verify_entry(
    artifact: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    entry: &str,
    startup: bool,
) -> Report {
    verify_source(
        artifact,
        directory,
        target,
        optimized,
        entry,
        startup,
        &fixture("uninit_origin_consumer.rs"),
    )
}

fn verify_source(
    artifact: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    entry: &str,
    startup: bool,
    source: &Path,
) -> Report {
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    if startup {
        command.args(["--startup", "--allow-assumptions"]);
    }
    command
        .args(["--verify", "--json", "--quiet", "--entry", entry, "--"])
        .args([
            "--crate-name=origin_consumer",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
        ])
        .arg(source)
        .arg("--extern")
        .arg(format!("dependency_uninit={}", artifact.display()))
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)))
}
fn status_entry(report: &Report, entry: &str) -> ProofStatus {
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

fn compile_dependency(artifact: &Path, source: &Path, target: Option<&str>, optimized: bool) {
    let mut compiler = Command::new(env!("CARGO_BIN_EXE_miren-rustc"));
    compiler
        .arg(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args([
            "--crate-name",
            "dependency_uninit",
            "--crate-type=rlib",
            "--edition=2024",
            "--emit=metadata",
            "-Cpanic=abort",
        ])
        .arg(source)
        .arg("-o")
        .arg(artifact);
    if let Some(target) = target {
        compiler.args(["--target", target]);
    }
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert!(output.status.success(), "{output:?}");
}

#[test]
fn compiler_certifies_uninitialized_container_construction_without_payload_reads() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let artifact = directory.0.join("libdependency_uninit.rmeta");
            compile_dependency(
                &artifact,
                &fixture("dependency_uninit.rs"),
                target,
                optimized,
            );
            let evidence: Evidence =
                serde_json::from_slice(&std::fs::read(sidecar(&artifact)).unwrap()).unwrap();
            assert_eq!(evidence.origins.len(), 3);
            for (entry, expected) in [
                ("dependency_uninit_store", ProofStatus::Proved),
                ("dependency_boolean_storage", ProofStatus::Proved),
                ("dependency_uninit_read", ProofStatus::Unknown),
                ("dependency_initialized_union", ProofStatus::Unknown),
                ("dependency_spoof_union", ProofStatus::Unknown),
                ("dependency_wrong_payload_type", ProofStatus::Unknown),
                ("dependency_uninit_store_real_guard", ProofStatus::Proved),
                ("dependency_uninit_store_wrong_guard", ProofStatus::Refuted),
                ("dependency_uninit_read_after_store", ProofStatus::Unknown),
            ] {
                let report = verify_entry(&artifact, &directory, target, optimized, entry, false);
                assert_eq!(status_entry(&report, entry), expected, "{report:?}");
            }
        }
    }
}

#[test]
fn stale_schema_or_artifact_evidence_cannot_authorize_uninitialized_container_stores() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let artifact = directory.0.join("libdependency_uninit.rmeta");
            compile_dependency(
                &artifact,
                &fixture("dependency_uninit.rs"),
                target,
                optimized,
            );
            let original = std::fs::read(sidecar(&artifact)).unwrap();
            for schema in [true, false] {
                let mut bad: Evidence = serde_json::from_slice(&original).unwrap();
                if schema {
                    bad.schema += 1;
                } else {
                    bad.artifact_sha256 = miren::static_origins::digest(b"stale");
                }
                bad.seal().unwrap();
                std::fs::write(sidecar(&artifact), serde_json::to_vec(&bad).unwrap()).unwrap();
                let entry = "dependency_uninit_store";
                let report = verify_entry(&artifact, &directory, target, optimized, entry, false);
                assert_eq!(status_entry(&report, entry), ProofStatus::Unknown);
            }
        }
    }
}

fn native_guard(source: &Path, directory: &Directory) -> bool {
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let dependency = directory.0.join("libdependency_uninit.rlib");
    let output = Command::new(&compiler)
        .args([
            "--crate-name=dependency_uninit",
            "--crate-type=rlib",
            "--edition=2024",
        ])
        .arg(fixture("dependency_uninit.rs"))
        .arg("-o")
        .arg(&dependency)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let executable = directory.0.join("native");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(source)
        .arg("--extern")
        .arg(format!("dependency_uninit={}", dependency.display()))
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn changing_a_post_store_guard_refutes_and_fails_native_execution() {
    let original = std::fs::read_to_string(fixture("uninit_origin_consumer.rs")).unwrap();
    let mutation = original.replace("if byte < 8 {", "if byte < 9 {");
    assert_ne!(original, mutation);
    let directory = Directory::new();
    let source = directory.0.join("mutant.rs");
    std::fs::write(&source, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let artifact = directory.0.join("libdependency_uninit.rmeta");
            compile_dependency(
                &artifact,
                &fixture("dependency_uninit.rs"),
                target,
                optimized,
            );
            let entry = "dependency_uninit_store_real_guard";
            let report = verify_source(
                &artifact, &directory, target, optimized, entry, false, &source,
            );
            assert_eq!(status_entry(&report, entry), ProofStatus::Refuted);
        }
    }
    assert!(native_guard(
        &fixture("uninit_origin_consumer.rs"),
        &directory
    ));
    assert!(!native_guard(&source, &directory));
}

#[test]
fn changing_uninit_to_initialized_union_construction_does_not_receive_a_certificate() {
    let original = std::fs::read_to_string(fixture("dependency_uninit.rs")).unwrap();
    let mutation = original.replacen(
        "SyncUnsafeCell::new(MaybeUninit::uninit());",
        "SyncUnsafeCell::new(MaybeUninit::new([7; 256]));",
        1,
    );
    assert_ne!(original, mutation);
    let directory = Directory::new();
    let source = directory.0.join("dependency_mutant.rs");
    std::fs::write(&source, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let artifact = directory.0.join("libdependency_uninit.rmeta");
            compile_dependency(&artifact, &source, target, optimized);
            let entry = "dependency_uninit_store";
            let report = verify_entry(&artifact, &directory, target, optimized, entry, false);
            assert_eq!(status_entry(&report, entry), ProofStatus::Unknown);
        }
    }
}
