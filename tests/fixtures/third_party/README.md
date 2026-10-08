# Original Cortex-M compiler-test archives

These are unmodified crates.io release archives used only as compiler-integration test data by
`crates/miren/tests/arm_interrupts.rs`. They are not dependencies of the miren workspace. The tests
extract fresh copies into temporary Cargo projects and compile safe test roots against their
original Cortex-M implementations. Instruction mutations affect only these temporary copies;
no third-party implementation is copied into miren's Rust source. Cortex-M firmware instructions
are not executed on the test host; normal dependency build scripts and procedural macros are.

`manifest.json` records each exact release, original registry archive SHA256 checksum, byte size,
license expression and official download URL. The checksums were checked against the registry
checksums in Cargo.lock before the test-only Cortex-M dependency was removed. The archive bytes
remain identical to the original crates.io packages. Each archive preserves its original license
and copyright files. Most releases use MIT OR Apache-2.0 (older manifest spelling
`MIT/Apache-2.0`); `void` uses MIT. Consult the individual archived license texts for their terms.

The fixture contains Cortex-M 0.7.9 and its non-workspace dependencies. Two embedded-hal and two
nb releases are required by the original dependency graph. Existing workspace dependencies such
as critical-section, proc-macro2, quote and syn continue to use the normal Cargo registry cache.
The fixtures make the Cortex-M graph available even when those Cortex-M registry packages have
never been cached; tests use Cargo's offline mode. The test helper checks checksums, sizes and
bounded archive paths before extraction and patches each release through a local Cargo path.

The legacy `bare-metal` 0.2.5 archive has advisory RUSTSEC-2026-0110. It remains original test data
so the analyzer can exercise the pinned target library's actual compiler MIR. It is excluded from
the analyzer dependency graph; no advisory is ignored or suppressed in cargo deny. This fixture
is not a recommendation to use the affected library in production code, nor a verification of
its unsafe implementation or interrupt-exclusion guarantees.
