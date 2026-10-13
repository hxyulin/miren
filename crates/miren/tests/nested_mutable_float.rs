#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-stage211-float-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../tests/fixtures/{name}.rs"))
}
fn clean(command: &mut Command) {
    for (name, _) in std::env::vars_os() {
        if name.to_string_lossy().starts_with("MIREN_") {
            command.env_remove(name);
        }
    }
}
fn verify(
    source: &Path,
    entries: &[(String, ProofStatus)],
    target: Option<&str>,
    opt: u32,
    extra: &[String],
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    clean(&mut command);
    command.args(["--verify", "--json", "--quiet"]);
    for (entry, _) in entries {
        command.args(["--entry", entry]);
    }
    command.args(["--", "--crate-type=lib", "--edition=2024", "-Cpanic=abort"]);
    command.arg(source).arg("--out-dir").arg(&directory.0);
    command.arg(format!("-Copt-level={opt}"));
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    command.args(extra);
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    assert!(!entries.is_empty());
    for (entry, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == *entry)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(proof.status, *expected, "{entry}: {:?}", proof.obligations);
        assert!(proof.assumptions.is_empty() && proof.entry_assumptions.is_empty());
    }
}
#[test]
fn float_hierarchy_checks_actual_bodies_raw_returns_and_bounded_depth() {
    let entries: Vec<_> = ["single", "double"]
        .into_iter()
        .flat_map(|module| {
            [
                "selected",
                "sibling",
                "scalar_return",
                "sequential",
                "wrong",
                "deeper",
            ]
            .into_iter()
            .map(move |entry| {
                let expected = match entry {
                    "wrong" => ProofStatus::Refuted,
                    "selected" | "sibling" | "scalar_return" | "sequential" | "deeper" => {
                        ProofStatus::Proved
                    }
                    _ => unreachable!(),
                };
                (format!("{module}::{entry}"), expected)
            })
        })
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in [0, 2] {
            verify(&fixture("nested_mutable_float"), &entries, target, opt, &[]);
        }
    }
}
#[test]
fn foreign_float_body_availability_precedes_empty_shortcuts() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in [0, 2] {
            for retained in [false, true] {
                let expected = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let entries = vec![
                    ("retained_or_omitted".into(), expected),
                    ("empty_selected".into(), expected),
                ];
                let directory = Directory::new();
                let archive = directory.0.join("libnested_float_dependency.rlib");
                let mut compiler = Command::new("rustc");
                clean(&mut compiler);
                compiler.args([
                    "--crate-type=rlib",
                    "--crate-name=nested_float_dependency",
                    "--edition=2024",
                    "-Cpanic=abort",
                ]);
                compiler.arg(fixture("nested_mutable_float_dependency"));
                compiler
                    .arg("-o")
                    .arg(&archive)
                    .arg(format!("-Copt-level={opt}"));
                compiler.arg(format!(
                    "-Zalways-encode-mir={}",
                    if retained { "yes" } else { "no" }
                ));
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                let output = compiler.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                verify(
                    &fixture("nested_mutable_float_foreign"),
                    &entries,
                    target,
                    opt,
                    &[
                        "--extern".into(),
                        format!("nested_float_dependency={}", archive.display()),
                    ],
                );
            }
        }
    }
}
