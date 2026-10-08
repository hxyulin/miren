#![forbid(unsafe_code)]

use miren::static_origins::{Construction, Evidence, Origin, OriginKind, SCHEMA, digest, sidecar};
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

#[test]
fn evidence_requires_exact_artifact_and_complete_unique_construction() {
    let directory = Directory::new();
    let artifact = directory.0.join("libdep.rmeta");
    std::fs::write(&artifact, b"metadata").unwrap();
    let mut evidence = Evidence {
        schema: SCHEMA,
        payload_sha256: String::new(),
        compiler: "compiler".into(),
        target: "target".into(),
        crate_id: "crate".into(),
        artifact_sha256: digest(b"metadata"),
        origins: vec![Origin {
            static_id: "static".into(),
            kind: OriginKind::Declared,
            construction: vec![Construction {
                definition: "static".into(),
                kind: OriginKind::Declared,
                mir_sha256: digest(b"mir"),
                calls: vec![],
            }],
        }],
    };
    evidence.seal().unwrap();
    assert!(!sidecar(&artifact).exists());
    assert!(Evidence::read(&artifact, "compiler", "target", "crate").is_err());
    std::fs::write(sidecar(&artifact), serde_json::to_vec(&evidence).unwrap()).unwrap();
    let read = Evidence::read(&artifact, "compiler", "target", "crate").unwrap();
    assert!(read.certifies("static"));
    assert!(!read.certifies("absent"));
    for (compiler, target, crate_id) in [
        ("other", "target", "crate"),
        ("compiler", "other", "crate"),
        ("compiler", "target", "other"),
    ] {
        assert!(Evidence::read(&artifact, compiler, target, crate_id).is_err());
    }
    evidence.origins[0].construction[0]
        .calls
        .push("missing".into());
    assert!(!evidence.certifies("static"));
    std::fs::write(&artifact, b"mutated metadata").unwrap();
    assert!(Evidence::read(&artifact, "compiler", "target", "crate").is_err());
    std::fs::write(sidecar(&artifact), b"{").unwrap();
    assert!(Evidence::read(&artifact, "compiler", "target", "crate").is_err());
}

fn verify(artifact: &Path, directory: &Directory, target: Option<&str>, optimized: bool) -> Report {
    verify_entry(
        artifact,
        directory,
        target,
        optimized,
        "dependency_atomic",
        false,
    )
}

fn verify_entry(
    artifact: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    entry: &str,
    startup: bool,
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
        .arg(fixture("static_origin_consumer.rs"))
        .arg("--extern")
        .arg(format!("dependency_statics={}", artifact.display()))
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
fn status(report: &Report) -> ProofStatus {
    status_entry(report, "dependency_atomic")
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
            "dependency_statics",
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
fn compiler_origins_unlock_atomic_dependencies_and_fail_closed_on_bad_evidence() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let artifact = directory.0.join("libdependency_statics.rmeta");
            compile_dependency(
                &artifact,
                &fixture("dependency_statics.rs"),
                target,
                optimized,
            );
            assert!(sidecar(&artifact).is_file());
            let report = verify(&artifact, &directory, target, optimized);
            assert_eq!(status(&report), ProofStatus::Proved, "{report:?}");
            let site = "dependency_site";
            let site_report = verify_entry(&artifact, &directory, target, optimized, site, false);
            assert_eq!(
                status_entry(&site_report, site),
                ProofStatus::Proved,
                "{site_report:?}"
            );
            let site_expected = "dependency_site_expected";
            let site_startup = verify_entry(
                &artifact,
                &directory,
                target,
                optimized,
                site_expected,
                true,
            );
            assert_eq!(
                status_entry(&site_startup, site_expected),
                ProofStatus::ProvedWithAssumptions
            );
            let expected = "dependency_atomic_expected";
            let ordinary = verify_entry(&artifact, &directory, target, optimized, expected, false);
            assert_eq!(status_entry(&ordinary, expected), ProofStatus::Refuted);
            let startup = verify_entry(&artifact, &directory, target, optimized, expected, true);
            assert_eq!(
                status_entry(&startup, expected),
                ProofStatus::ProvedWithAssumptions
            );
            assert!(
                !startup
                    .functions
                    .iter()
                    .find(|function| function.name == expected)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap()
                    .entry_assumptions
                    .is_empty()
            );
            let evidence = std::fs::read(sidecar(&artifact)).unwrap();
            std::fs::remove_file(sidecar(&artifact)).unwrap();
            assert_eq!(
                status(&verify(&artifact, &directory, target, optimized)),
                ProofStatus::Unknown
            );
            std::fs::write(sidecar(&artifact), b"{").unwrap();
            assert_eq!(
                status(&verify(&artifact, &directory, target, optimized)),
                ProofStatus::Unknown
            );
            let mut stale: Evidence = serde_json::from_slice(&evidence).unwrap();
            stale.artifact_sha256 = digest(b"wrong artifact");
            std::fs::write(sidecar(&artifact), serde_json::to_vec(&stale).unwrap()).unwrap();
            assert_eq!(
                status(&verify(&artifact, &directory, target, optimized)),
                ProofStatus::Unknown
            );
            let original_source =
                std::fs::read_to_string(fixture("dependency_statics.rs")).unwrap();
            let mutation = directory.0.join("dependency_mutant.rs");
            std::fs::write(
                &mutation,
                original_source.replace("AtomicU32::new(7)", "AtomicU32::new(8)"),
            )
            .unwrap();
            compile_dependency(&artifact, &mutation, target, optimized);
            let bad_claim = verify_entry(&artifact, &directory, target, optimized, expected, true);
            assert_eq!(status_entry(&bad_claim, expected), ProofStatus::Refuted);
            std::fs::write(sidecar(&artifact), &evidence).unwrap();
            assert_eq!(
                status(&verify(&artifact, &directory, target, optimized)),
                ProofStatus::Unknown
            );
            std::fs::write(
                &mutation,
                format!(
                    "{}\nconst fn cast(value: u16) -> u32 {{ value as u32 }}\n",
                    original_source.replace("AtomicU32::new(7)", "AtomicU32::new(cast(7))")
                ),
            )
            .unwrap();
            compile_dependency(&artifact, &mutation, target, optimized);
            assert_eq!(
                status(&verify(&artifact, &directory, target, optimized)),
                ProofStatus::Unknown
            );
        }
    }
}

#[test]
fn producer_emits_and_binds_its_own_metadata_when_source_changed_after_first_compile() {
    let directory = Directory::new();
    let artifact = directory.0.join("libdependency_statics.rmeta");
    let source = directory.0.join("dependency.rs");
    let original = std::fs::read_to_string(fixture("dependency_statics.rs")).unwrap();
    std::fs::write(&source, &original).unwrap();
    let rustc = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let args = [
        "--crate-name",
        "dependency_statics",
        "--crate-type=rlib",
        "--edition=2024",
        "--emit=metadata",
        "-Cpanic=abort",
        "-Zalways-encode-mir=yes",
        "-Zmir-opt-level=0",
    ];
    let first = Command::new(&rustc)
        .args(args)
        .arg(&source)
        .arg("-o")
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(first.status.success(), "{first:?}");
    let before = digest(&std::fs::read(&artifact).unwrap());
    std::fs::write(
        &source,
        original.replace("AtomicU32::new(7)", "AtomicU32::new(8)"),
    )
    .unwrap();
    let producer = Command::new(env!("CARGO_BIN_EXE_miren"))
        .arg("--produce-static-origins")
        .arg(&rustc)
        .args(args)
        .arg(&source)
        .arg("-o")
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(producer.status.success(), "{producer:?}");
    let evidence: Evidence =
        serde_json::from_slice(&std::fs::read(sidecar(&artifact)).unwrap()).unwrap();
    assert_ne!(before, evidence.artifact_sha256);
    assert_eq!(
        evidence.artifact_sha256,
        digest(&std::fs::read(&artifact).unwrap())
    );
    let entry = "dependency_atomic_expected";
    assert_eq!(
        status_entry(
            &verify_entry(&artifact, &directory, None, false, entry, true),
            entry
        ),
        ProofStatus::Refuted
    );
}

fn wrapper_artifacts(artifact: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_miren-rustc"))
        .arg(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args([
            "--crate-name",
            "dependency_statics",
            "--crate-type=rlib",
            "--edition=2024",
            "--emit=metadata",
            "--error-format=json",
            "--json=artifacts",
            "-Cpanic=abort",
        ])
        .arg(fixture("dependency_statics.rs"))
        .arg("-o")
        .arg(artifact)
        .output()
        .unwrap()
}

fn artifact_events(output: &std::process::Output) -> Vec<serde_json::Value> {
    output
        .stdout
        .split(|byte| *byte == b'\n')
        .chain(output.stderr.split(|byte| *byte == b'\n'))
        .filter_map(|line| serde_json::from_slice::<serde_json::Value>(line).ok())
        .filter(|message| {
            message
                .get("$message_type")
                .and_then(serde_json::Value::as_str)
                == Some("artifact")
        })
        .collect()
}

#[test]
fn wrapper_emits_one_artifact_notification_and_keeps_valid_origin_evidence() {
    let directory = Directory::new();
    let artifact = directory.0.join("libdependency_statics.rmeta");
    let output = wrapper_artifacts(&artifact);
    assert!(output.status.success(), "{output:?}");
    let events = artifact_events(&output);
    assert_eq!(events.len(), 1, "{events:?}");
    assert_eq!(
        events[0]["artifact"].as_str().unwrap(),
        artifact.to_str().unwrap()
    );
    let evidence: Evidence =
        serde_json::from_slice(&std::fs::read(sidecar(&artifact)).unwrap()).unwrap();
    let loaded = Evidence::read(
        &artifact,
        &evidence.compiler,
        &evidence.target,
        &evidence.crate_id,
    )
    .unwrap();
    assert!(!loaded.origins.is_empty());
}

#[test]
fn wrapper_filters_repeated_artifact_notification_when_evidence_write_fails_after_emission() {
    let directory = Directory::new();
    // The 255-byte sidecar name fits; its longer temporary filename cannot be written.
    let filename = format!("{}.rmeta", "a".repeat(230));
    let artifact = directory.0.join(filename);
    assert_eq!(sidecar(&artifact).file_name().unwrap().len(), 255);
    let output = wrapper_artifacts(&artifact);
    assert!(!output.status.success(), "{output:?}");
    assert!(artifact.is_file());
    assert!(!sidecar(&artifact).exists());
    let events = artifact_events(&output);
    assert!(events.is_empty(), "{events:?}");
    assert!(String::from_utf8_lossy(&output.stderr).contains("miren static origin producer:"));
}
