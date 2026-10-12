#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/primitive_function_pointer_repeat.rs")
}

#[test]
fn bool_char_repeat_executes_original_bodies_and_preserves_refusals() {
    let entries = [
        ("selected_bool", ProofStatus::Proved),
        ("wrong_bool", ProofStatus::Refuted),
        ("selected_char", ProofStatus::Proved),
        ("wrong_char", ProofStatus::Refuted),
        ("opaque_bool", ProofStatus::Unknown),
        ("opaque_char", ProofStatus::Unknown),
        ("generic_bool", ProofStatus::Unknown),
        ("foreign_bool", ProofStatus::Unknown),
        ("last_char", ProofStatus::Proved),
        ("count_budget", ProofStatus::Unknown),
        ("dispatch_budget", ProofStatus::Unknown),
        ("body_dispatch_budget", ProofStatus::Unknown),
        ("zero", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for (name, helper) in [("selected_bool", "boolean"), ("selected_char", "character")] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
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
fn real_bool_char_helper_mutations_fail_unchanged_claims() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new, selected) in [
        (
            "bool_helper",
            "value ^ false",
            "value ^ true",
            "selected_bool",
        ),
        (
            "char_helper",
            "pub fn character(value: char) -> char {\n    value\n}",
            "pub fn character(value: char) -> char {\n    'B'\n}",
            "selected_char",
        ),
    ] {
        assert_eq!(source.matches(old).count(), 1);
        let path = directory.0.join(format!("{name}.rs"));
        std::fs::write(&path, source.replacen(old, new, 1)).unwrap();
        for optimized in [false, true] {
            native(&path, optimized, true);
            for target in [None, Some("thumbv7em-none-eabihf")] {
                verify(
                    &path,
                    &[(selected, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
            }
        }
    }
}

#[test]
fn genuine_foreign_repeat_bodies_are_required() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn boolean(value: bool) -> bool { !value }
#[inline(never)] pub fn character(value: char) -> char {
    if value == 'A' { 'B' } else { 'A' }
}
"#,
    )
    .unwrap();
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn selected_bool(index: usize, value: bool) {
    let table: [fn(bool)->bool;2] = [primitive_external::boolean;2];
    if index < 2 {
        let actual = table[index](value);
        assert!(actual == !value);
    }
}
pub fn selected_char(index: usize, value: char) {
    let table: [fn(char)->char;2] = [primitive_external::character;2];
    if index < 2 {
        let actual = table[index](value);
        assert!(actual == if value == 'A' { 'B' } else { 'A' });
    }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "libprimitive_{}_{optimized}_{retained}.rlib",
                    target.unwrap_or("host")
                ));
                let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
                let mut command = Command::new(compiler);
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=primitive_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(format!("-Copt-level={}", if optimized { 2 } else { 0 }))
                    .arg(format!(
                        "-Zalways-encode-mir={}",
                        if retained { "yes" } else { "no" }
                    ))
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let status = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[("selected_bool", status), ("selected_char", status)],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("primitive_external={}", archive.display()),
                    ],
                );
                for function in &report.functions {
                    let Some(proof) = &function.proof else {
                        continue;
                    };
                    if retained {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function.starts_with("primitive_external::"))
                        );
                    } else {
                        assert!(
                            proof
                                .obligations
                                .iter()
                                .any(|obligation| obligation.unknown_category
                                    == Some(UnknownCategory::MissingCompilerEvidence))
                        );
                    }
                }
            }
        }
    }
}
