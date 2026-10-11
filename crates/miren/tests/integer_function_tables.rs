#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

const MODULES: [&str; 12] = [
    "u8_table",
    "u16_table",
    "u32_table",
    "u64_table",
    "u128_table",
    "usize_table",
    "i8_table",
    "i16_table",
    "i32_table",
    "i64_table",
    "i128_table",
    "isize_table",
];

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/integer_function_tables.rs")
}

#[test]
fn original_integer_signatures_execute_bodies_and_preserve_overflow_obligations() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let mut names = Vec::new();
    for module in MODULES {
        for (entry, status) in [
            ("selected", P),
            ("wrapping", P),
            ("wrong", R),
            ("overflow", R),
            ("opaque", U),
        ] {
            names.push((format!("{module}::{entry}"), status));
        }
    }
    for name in [
        "bool_unknown",
        "char_unknown",
        "float_unknown",
        "nz_unknown",
        "abi_unknown",
    ] {
        names.push((name.into(), U));
    }
    names.push(("result_unknown".into(), R));
    names.push(("arity_unknown".into(), R));
    names.extend([("associated".into(), P), ("wrong_associated".into(), R)]);
    let entries: Vec<_> = names
        .iter()
        .map(|(name, status)| (name.as_str(), *status))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            let arity = report
                .functions
                .iter()
                .find(|f| f.name == "arity_unknown")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                arity
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "pair_second")
            );
            assert!(arity.obligations.iter().any(|obligation| {
                obligation.status == R
                    && obligation.query.is_some()
                    && obligation.model.as_ref().is_some_and(|model| {
                        let compact = model.split_whitespace().collect::<Vec<_>>().join(" ");
                        compact.contains("(define-fun v0 () (_ BitVec 32) (_ bv1 32))")
                            || compact.contains("(define-fun v0 () (_ BitVec 64) (_ bv1 64))")
                    })
            }));
            for module in MODULES {
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
fn actual_integer_helper_and_order_mutations_fail_all_original_claims() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let names: Vec<_> = MODULES
        .iter()
        .map(|name| format!("{name}::selected"))
        .collect();
    let entries: Vec<_> = names
        .iter()
        .map(|name| (name.as_str(), ProofStatus::Refuted))
        .collect();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    // Keep the original mixed-return assertion: its second body changes the low bit.
    let witness = directory.0.join("original_result_counterexample.rs");
    let mut witness_source = source.clone();
    witness_source.push_str(
        "\n#[cfg(test)] mod original_result_counterexample {\n\
         #[test] fn unchanged_assertion_fails() { super::result_unknown(1, 0); }\n}\n",
    );
    std::fs::write(&witness, witness_source).unwrap();
    for optimized in [false, true] {
        native(&witness, optimized, true);
    }
    for (name, old, new) in [
        ("helper", "word ^ 1", "word ^ 3"),
        ("order", "[first, second]", "[second, first]"),
    ] {
        let mutant = directory.0.join(format!("{name}.rs"));
        let mutated = if name == "helper" {
            let first = source.find(old).unwrap();
            let mut mutated = source.clone();
            mutated.replace_range(first..first + old.len(), new);
            mutated
        } else {
            assert!(source.contains(old));
            source.replace(old, new)
        };
        std::fs::write(&mutant, mutated).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(&mutant, &entries, target, optimized, &[]);
            }
        }
        for optimized in [false, true] {
            native(&mutant, optimized, true);
        }
    }
}

#[test]
fn external_integer_choices_execute_available_bodies_and_prune_infeasible_ones() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let source = directory.0.join("external.rs");
    let mut dependency_text = String::from("#![no_std]\n#![forbid(unsafe_code)]\n");
    let mut source_text = dependency_text.clone();
    let mut names = Vec::new();
    for module in MODULES {
        let integer = module.strip_suffix("_table").unwrap();
        dependency_text.push_str(&format!(
            "#[inline(never)] pub fn first_{integer}(word: {integer}) -> {integer} {{word}}\n\
             #[inline(never)] pub fn second_{integer}(word: {integer}) -> {integer} {{word ^ 1}}\n"
        ));
        source_text.push_str(&format!(
            "#[inline(never)] pub fn local_{integer}(word: {integer}) -> {integer} {{word}}\n\
             pub fn external_{integer}(index: usize, word: {integer}) {{\n\
               let table: [fn({integer}) -> {integer}; 2] =\n\
                 [integer_external::first_{integer}, integer_external::second_{integer}];\n\
               if index < 2 {{assert!(table[index](word) ==\n\
                 if index == 0 {{word}} else {{word ^ 1}});}}\n\
             }}\n\
             pub fn infeasible_{integer}(index: usize, word: {integer}) {{\n\
               let table: [fn({integer}) -> {integer}; 2] =\n\
                 [local_{integer}, integer_external::second_{integer}];\n\
               if index == 0 {{assert!(table[index](word) == word);}}\n\
             }}\n"
        ));
        names.push((
            format!("external_{integer}"),
            format!("infeasible_{integer}"),
        ));
    }
    std::fs::write(&dependency, dependency_text).unwrap();
    std::fs::write(&source, source_text).unwrap();
    for retained in [false, true] {
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let archive = directory.0.join("libinteger_external.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=integer_external",
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
                let mut entries = Vec::new();
                for (external, infeasible) in &names {
                    entries.push((
                        external.as_str(),
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    ));
                    entries.push((infeasible.as_str(), ProofStatus::Proved));
                }
                let extra = [
                    "--extern".into(),
                    format!("integer_external={}", archive.display()),
                ];
                let report = verify(&source, &entries, target, optimized, &extra);
                for (external, _) in &names {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == *external)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    if retained {
                        let integer = external.strip_prefix("external_").unwrap();
                        for helper in ["first", "second"] {
                            assert!(
                                proof.body_entries.iter().any(|e| e.function
                                    == format!("integer_external::{helper}_{integer}"))
                            );
                        }
                    } else {
                        assert!(proof.obligations.iter().any(|o| o.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)));
                    }
                }
            }
        }
    }
}
