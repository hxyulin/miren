#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("miren-coroutine-scope-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/coroutine_scope.rs")
}

#[test]
fn compiler_return_scope_distinguishes_factory_proofs_from_reached_async_panics() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for poll in [false, true] {
                let directory = Directory::new();
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command.args(["--verify", "--json", "--quiet"]);
                if poll {
                    command.args(["--async-entry", "delayed_panic"]);
                } else {
                    for entry in ["delayed_panic", "immediate_panic", "callback_boundary"] {
                        command.args(["--entry", entry]);
                    }
                }
                command
                    .args(["--", "--crate-type=lib", "--edition=2024"])
                    .arg(fixture())
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
                let report: Report =
                    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                        panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
                    });
                assert!(!output.status.success());
                let label = if poll {
                    " (async construction + polls)"
                } else {
                    " (future construction)"
                };
                assert!(miren::render(&report).contains(label));
                assert!(miren::cli::render_report(&report, false, false).contains(label));
                for (name, coroutine, status) in [
                    (
                        "delayed_panic",
                        true,
                        if poll {
                            ProofStatus::Refuted
                        } else {
                            ProofStatus::Proved
                        },
                    ),
                    ("immediate_panic", false, ProofStatus::Refuted),
                    ("callback_boundary", false, ProofStatus::Unknown),
                ] {
                    let function = report.functions.iter().find(|f| f.name == name).unwrap();
                    assert_eq!(function.returns_coroutine, Some(coroutine));
                    if poll && name != "delayed_panic" {
                        continue;
                    }
                    let proof = function.proof.as_ref().unwrap();
                    assert_eq!(
                        proof.status, status,
                        "{target:?} optimized={optimized} {name}"
                    );
                    assert_eq!(proof.async_entry, poll);
                    assert!(proof.trusted_calls.is_empty());
                }
            }
        }
    }
}

#[test]
fn native_construction_and_polling_confirm_the_scope_distinction() {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let output = Command::new("rustc")
        .args(["--test", "--edition=2024"])
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
    assert!(Command::new(executable).output().unwrap().status.success());
}
