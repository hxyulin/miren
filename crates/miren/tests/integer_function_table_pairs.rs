#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

const INTEGERS: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];
fn modules() -> Vec<String> {
    INTEGERS
        .iter()
        .flat_map(|argument| INTEGERS.map(|result| format!("{argument}_to_{result}")))
        .collect()
}
fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}
#[test]
fn independently_typed_integer_tables_execute_all_original_bodies() {
    let modules = modules();
    let mut names = Vec::new();
    for module in &modules {
        for (entry, status) in [
            ("selected", ProofStatus::Proved),
            ("wrong", ProofStatus::Refuted),
            ("opaque", ProofStatus::Unknown),
        ] {
            names.push((format!("{module}::{entry}"), status));
        }
    }
    let entries: Vec<_> = names.iter().map(|(n, s)| (n.as_str(), *s)).collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture("integer_function_table_pairs.rs"),
                &entries,
                target,
                optimized,
                &[],
            );
            for module in &modules {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == format!("{module}::selected"))
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                for helper in ["first", "second"] {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|e| e.function == format!("{module}::{helper}"))
                    );
                }
            }
        }
    }
}
#[test]
fn actual_cast_helper_and_order_mutations_refute_all_original_pairs() {
    let directory = Directory::new();
    let original = fixture("integer_function_table_pairs.rs");
    let source = std::fs::read_to_string(&original).unwrap();
    let names: Vec<_> = modules().iter().map(|m| format!("{m}::selected")).collect();
    let entries: Vec<_> = names
        .iter()
        .map(|n| (n.as_str(), ProofStatus::Refuted))
        .collect();
    for optimized in [false, true] {
        native(&original, optimized, false);
    }
    for (name, old, new) in [
        ("helper", "word ^ 1", "word ^ 3"),
        ("order", "[first, second]", "[second, first]"),
    ] {
        let position = source.find(old).unwrap();
        let mut mutated = source.clone();
        mutated.replace_range(position..position + old.len(), new);
        let path = directory.0.join(format!("{name}.rs"));
        std::fs::write(&path, mutated).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(&path, &entries, target, optimized, &[]);
            }
        }
        for optimized in [false, true] {
            native(&path, optimized, true);
        }
    }
}
#[test]
fn foreign_cast_pairs_require_actual_dependency_mir_and_prune_infeasible_targets() {
    let directory = Directory::new();
    let dependency = fixture("integer_function_table_pairs_dependency.rs");
    let source = fixture("integer_function_table_pairs_external.rs");
    let modules = modules();
    for retained in [false, true] {
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let archive = directory.0.join("libinteger_pair_external.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=integer_pair_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                let output = compiler.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let mut names = Vec::new();
                for module in &modules {
                    names.push((
                        format!("{module}::external"),
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    ));
                    names.push((format!("{module}::infeasible"), ProofStatus::Proved));
                }
                let entries: Vec<_> = names.iter().map(|(n, s)| (n.as_str(), *s)).collect();
                let extra = [
                    "--extern".into(),
                    format!("integer_pair_external={}", archive.display()),
                ];
                let report = verify(&source, &entries, target, optimized, &extra);
                for module in &modules {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == format!("{module}::external"))
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    if retained {
                        for helper in ["first", "second"] {
                            assert!(proof.body_entries.iter().any(|e| e.function
                                == format!("integer_pair_external::{module}::{helper}")));
                        }
                    } else {
                        assert!(proof.obligations.iter().any(|o| o.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)));
                    }
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == format!("{module}::infeasible"))
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|e| e.function == format!("{module}::local"))
                    );
                    assert!(
                        !proof
                            .body_entries
                            .iter()
                            .any(|e| e.function.starts_with("integer_pair_external::"))
                    );
                }
            }
        }
    }
}
