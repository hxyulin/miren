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
            "miren-composite-slice-iterators-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/composite_slice_iterators.rs")
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
        assert!(proof.entry_assumptions.is_empty());
        if matches!(*expected, ProofStatus::Proved | ProofStatus::Refuted) {
            assert!(proof.models.iter().any(|model| model.contains(concat!(
                "readonly composite slice; exact compiler shape ",
                "and independent primitive leaf arrays"
            ))));
        }
        if matches!(*expected, ProofStatus::Proved | ProofStatus::Refuted)
            && *name != "open_aggregate_slice"
        {
            assert!(proof.models.iter().any(|model| {
                model.contains("slice iterator; ordered elements and tracked cursor")
            }));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "mutable_root" | "competing_roots" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "analyzer_only::missing_invoked_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::raw_source" => (
                    UnknownCategory::Unclassified,
                    if optimized {
                        "raw slice construction requires a shared compiler-typed byte slice"
                    } else {
                        "tracked raw addresses require a sized pointee"
                    },
                ),
                "analyzer_only::dead_empty_metadata" | "analyzer_only::dead_exhausted_next" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
                ),
                other => panic!("missing expected frontier for {other}"),
            };
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation.unknown_category == Some(category)
                        && obligation.detail.contains(reason)
                }),
                "wrong frontier for {name}: {:?}",
                proof.obligations
            );
        }
        let helper = match *name {
            "mutation_claim" => Some("selected_field"),
            "returned_iterator" | "analyzer_only::copied_handle_live" => Some("composite_iterator"),
            _ => None,
        };
        if let Some(helper) = helper {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|body| body.function == helper)
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.model.is_some()
                    && obligation.query.is_some()
            }));
        }
    }
}

fn native_tests(path: &Path, directory: &Directory, optimized: bool, filter: Option<&str>) -> bool {
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
    let mut command = Command::new(executable);
    if let Some(filter) = filter {
        command.arg(filter);
    }
    command.output().unwrap().status.success()
}

#[test]
fn readonly_composite_cursors_preserve_positions_metadata_and_sources() {
    let entries = [
        ("metadata", ProofStatus::Proved),
        ("symbolic_nth", ProofStatus::Proved),
        ("reverse_and_mixed", ProofStatus::Proved),
        ("cloned_cursors", ProofStatus::Proved),
        ("returned_iterator", ProofStatus::Proved),
        ("array_bool_char", ProofStatus::Proved),
        ("float_field_bits", ProofStatus::Proved),
        ("large_view", ProofStatus::Proved),
        ("oversized_skip", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("analyzer_only::copied_handle_live", ProofStatus::Proved),
        ("deferred_iteration", ProofStatus::Proved),
        ("aggregate_input", ProofStatus::Proved),
        ("wrong_first_field", ProofStatus::Refuted),
        ("open_aggregate_slice", ProofStatus::Refuted),
        ("wrong_clone", ProofStatus::Refuted),
        ("unguarded_nth", ProofStatus::Refuted),
        ("float_numeric_reflexivity", ProofStatus::Refuted),
        ("mutable_root", ProofStatus::Unknown),
        ("competing_roots", ProofStatus::Unknown),
        ("analyzer_only::missing_invoked_body", ProofStatus::Unknown),
        ("analyzer_only::raw_source", ProofStatus::Unknown),
        ("analyzer_only::dead_empty_metadata", ProofStatus::Unknown),
        ("analyzer_only::dead_exhausted_next", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_cursor_field_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn selected_field(iterator: &mut core::slice::Iter<'_, (u16, u16)>, index: usize)",
        " -> u16 {\n",
        "    iterator.nth(index).unwrap().0\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "fn selected_field(iterator: &mut core::slice::Iter<'_, (u16, u16)>, index: usize)",
                " -> u16 {\n    iterator.nth(index).unwrap().1\n}"
            ),
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
        assert!(native_tests(&fixture(), &Directory::new(), optimized, None));
        assert!(!native_tests(
            &mutated,
            &Directory::new(),
            optimized,
            Some("mutation_guard")
        ));
    }
}
