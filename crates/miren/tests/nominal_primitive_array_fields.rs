#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-primitive-array-fields-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/nominal_primitive_array_fields.rs")
}

fn dependency() -> PathBuf {
    fixture().with_file_name("nominal_primitive_array_dependency.rs")
}

fn compiler() -> PathBuf {
    Path::new(env!("MIREN_SYSROOT")).join("bin/rustc")
}

fn build_dependency(
    source: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    retained: bool,
    native: bool,
) -> PathBuf {
    let library = directory.0.join("libprimitive_array_dependency.rlib");
    let mut command = Command::new(compiler());
    command
        .args([
            "--crate-name=primitive_array_dependency",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zmir-opt-level=0",
            "-Coverflow-checks=yes",
        ])
        .arg(if retained {
            "-Zalways-encode-mir=yes"
        } else {
            "-Zalways-encode-mir=no"
        })
        .arg(source)
        .arg("-o")
        .arg(&library)
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        });
    if !native {
        command.arg("-Cpanic=abort");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    library
}

fn verify(
    source: &Path,
    dependency_source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    retained: bool,
) {
    let directory = Directory::new();
    let library = build_dependency(
        dependency_source,
        &directory,
        target,
        optimized,
        retained,
        false,
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(source)
        .arg("--extern")
        .arg(format!("primitive_array_dependency={}", library.display()))
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"])
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        });
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
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?}/{optimized}/{retained}/{name}: {proof:?}"
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = if !retained {
                (
                    UnknownCategory::MissingCompilerEvidence,
                    "MIR body unavailable for",
                )
            } else {
                match *name {
                    "reference_child" | "core_child" | "pattern_child" => (
                        UnknownCategory::Semantics,
                        "only read-only byte slices and byte arrays are modeled",
                    ),
                    "oversized" | "expanded" => (UnknownCategory::ResourceLimit, "composite slice"),
                    "bad_comparer" | "boolean_member" => (
                        UnknownCategory::Semantics,
                        "nominal comparison compares different or repeated receiver fields",
                    ),
                    other => panic!("missing actual frontier {other}"),
                }
            };
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation.unknown_category == Some(category)
                        && obligation.detail.contains(reason)
                        && (retained || obligation.detail.contains("core::cmp::PartialEq>::eq"))
                }),
                "{name}: {:?}",
                proof.obligations
            );
        } else {
            let equality = matches!(
                *name,
                "boolean_self"
                    | "float32_self"
                    | "float64_self"
                    | "views"
                    | "different_views"
                    | "wrong_views"
                    | "vacant_maximum"
                    | "external_empty"
                    | "external_mismatch"
            );
            let model = if equality {
                "full-domain pure composite slice equality"
            } else {
                "full-domain pure composite slice membership"
            };
            assert!(
                proof.models.iter().any(|observed| observed.contains(model))
                    || *name == "external_mismatch"
            );
            assert!(
                proof.models.iter().any(|model| {
                    model.contains("readonly composite slice; exact compiler shape")
                })
            );
        }
        if matches!(*name, "boolean_member" | "boolean_absent") {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected")
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
}

fn native(source: &Path, optimized: bool, mutant: bool) {
    let directory = Directory::new();
    let library = build_dependency(&dependency(), &directory, None, optimized, true, true);
    let executable = directory.0.join("native");
    let output = Command::new(compiler())
        .args(["--test", "--edition=2024"])
        .arg(source)
        .arg("--extern")
        .arg(format!("primitive_array_dependency={}", library.display()))
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        })
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(executable);
    if mutant {
        command.args(["--exact", "tests::mutation_guard"]);
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() >= Duration::from_secs(10) {
            child.kill().unwrap();
            panic!("native timeout: {:?}", child.wait_with_output().unwrap());
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(if mutant { 101 } else { 0 }),
        "{output:?}"
    );
}

#[test]
fn primitive_array_comparers_and_missing_selected_bodies_are_certified() {
    let entries = [
        ("boolean_member", ProofStatus::Proved),
        ("boolean_absent", ProofStatus::Refuted),
        ("boolean_self", ProofStatus::Proved),
        ("character_member", ProofStatus::Proved),
        ("mixed_member", ProofStatus::Proved),
        ("character_boundaries", ProofStatus::Proved),
        ("float32_member", ProofStatus::Proved),
        ("float32_zero", ProofStatus::Proved),
        ("float32_self", ProofStatus::Refuted),
        ("float64_member", ProofStatus::Proved),
        ("float64_zero", ProofStatus::Proved),
        ("float64_self", ProofStatus::Refuted),
        ("nan_singleton", ProofStatus::Proved),
        ("views", ProofStatus::Proved),
        ("different_views", ProofStatus::Proved),
        ("wrong_views", ProofStatus::Refuted),
        ("vacant_member", ProofStatus::Proved),
        ("vacant_maximum", ProofStatus::Proved),
        ("bad_comparer", ProofStatus::Unknown),
        ("reference_child", ProofStatus::Unknown),
        ("pattern_child", ProofStatus::Unknown),
        ("core_child", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("expanded", ProofStatus::Unknown),
        ("external_member", ProofStatus::Proved),
        ("external_empty", ProofStatus::Proved),
        ("external_mismatch", ProofStatus::Proved),
    ];
    let omitted: Vec<_> = entries
        .iter()
        .filter(|(name, _)| name.starts_with("external_"))
        .map(|(name, _)| (*name, ProofStatus::Unknown))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &dependency(), &entries, target, optimized, true);
            verify(
                &fixture(),
                &dependency(),
                &omitted,
                target,
                optimized,
                false,
            );
        }
    }
}

#[test]
fn primitive_array_data_mutation_refutes_but_comparer_mutation_is_unknown() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "pub fn selected(values: &[Booleans], index: usize) -> Booleans {\n",
        "    values[index]\n}"
    );
    let replacement = concat!(
        "pub fn selected(values: &[Booleans], index: usize) -> Booleans {\n",
        "    let mut selected = values[index];\n",
        "    selected.values[0] = !selected.values[0];\n",
        "    selected\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    let mutant = directory.0.join("data-mutant.rs");
    std::fs::write(&mutant, source.replace(original, replacement)).unwrap();
    let record = "#[derive(Clone, Copy, PartialEq)]\npub struct Booleans {";
    assert_eq!(source.matches(record).count(), 1);
    let wrong = directory.0.join("comparator-mutant.rs");
    let changed = source.replace(record, "#[derive(Clone, Copy)]\npub struct Booleans {");
    let implementation = concat!(
        "\nimpl PartialEq for Booleans {\n",
        "    fn eq(&self, other: &Self) -> bool {\n",
        "        self.values == self.values && self.marker == other.marker\n",
        "    }\n}\n"
    );
    std::fs::write(&wrong, format!("{changed}{implementation}")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &dependency(),
                &[("boolean_member", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
            verify(
                &wrong,
                &dependency(),
                &[("boolean_member", ProofStatus::Unknown)],
                target,
                optimized,
                true,
            );
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
    }
}
