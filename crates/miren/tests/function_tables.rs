#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/function_tables.rs")
}

#[test]
fn correlated_tables_execute_actual_bodies_and_keep_unsupported_targets_unknown() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("duplicates", P),
        ("field", P),
        ("second_call", P),
        ("wrong", R),
        ("opaque", U),
        ("wide", P),
        ("shared", U),
        ("excessive", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            for helper in ["first", "second"] {
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == helper)
                );
            }
        }
    }
}

#[test]
fn actual_helper_and_table_order_mutations_refute_the_unchanged_assertion() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new) in [
        ("helper", "value ^ 1 }", "value ^ 3 }"),
        ("order", "[first,second]", "[second,first]"),
    ] {
        assert!(source.contains(old));
        let mutant = directory.0.join(format!("{name}.rs"));
        std::fs::write(&mutant, source.replacen(old, new, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(
                    &mutant,
                    &[("selected", ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
            }
        }
        for optimized in [false, true] {
            native(&mutant, optimized, true);
        }
    }
}

#[test]
fn feasible_external_targets_require_mir_and_infeasible_targets_are_pruned() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let source = directory.0.join("external.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        #[inline(never)] pub fn first(value: u16) -> u16 {value}\n\
        #[inline(never)] pub fn second(value: u16) -> u16 {value ^ 1}\n",
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn external(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [fn_table_external::first, fn_table_external::second];
    if index < 2 {assert!(table[index](value) == if index == 0 {value} else {value ^ 1});}
}
#[inline(never)] pub fn local(value: u16) -> u16 {value}
pub fn infeasible_external(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [local, fn_table_external::second];
    if index == 0 {assert!(table[index](value) == value);}
}
"#,
    )
    .unwrap();
    for retained in [false, true] {
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let archive = directory.0.join("libfn_table_external.rlib");
            let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            compiler
                .args([
                    "--crate-type=rlib",
                    "--crate-name=fn_table_external",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Copt-level=0",
                ])
                .arg(if retained {
                    "-Zalways-encode-mir=yes"
                } else {
                    "-Zalways-encode-mir=no"
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
            let extra = [
                "--extern".into(),
                format!("fn_table_external={}", archive.display()),
            ];
            for optimized in [false, true] {
                let report = verify(
                    &source,
                    &[
                        (
                            "external",
                            if retained {
                                ProofStatus::Proved
                            } else {
                                ProofStatus::Unknown
                            },
                        ),
                        ("infeasible_external", ProofStatus::Proved),
                    ],
                    target,
                    optimized,
                    &extra,
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == "external")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|e| e.function == "fn_table_external::second")
                    );
                } else {
                    assert!(
                        proof.obligations.iter().any(|o| o.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence))
                    );
                }
            }
        }
    }
}
