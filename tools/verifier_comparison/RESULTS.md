# First verifier comparison

Measured on 2026-10-15 on aarch64 macOS. This is a compatibility pilot, not a whole-fleet or std
coverage measurement. [Reproduction instructions](README.md) and
[machine-readable observations](measurement.json) accompany the results.

## Recommendation

Kani is the strongest candidate to try as an external verification backend before extending miren's
Rust semantics further. It matched every expected outcome in this small sample and proved the two
wrappers around the unchanged DR16 parser. Crux-MIR also fits the symbolic verification use case,
including allocation and explicit async polling, but the measured build has a reproducible false
alarm involving symbolic selection between two shared trait objects. Resolve that disagreement
before treating it as the primary backend.

MIRAI fits diagnostic triage and source analysis. Its measured warnings and silent runs do not meet
miren's requirement that every selected root receive a conservative supported or incomplete outcome.
Do not translate a silent MIRAI run into PROVED. This assessment is specific to the measured
version,
configuration and cases; it is not a claim about every use of MIRAI.

Keep the broad Rust parity goal paused. The next useful experiment is a small backend interface
around authentic source, selected roots, explicit input domains and recorded results. Compare Kani
and Crux on a few actual fleet functions before committing to a standalone interpreter extraction.
Neither successful parser verification nor these polling controls establish STM32 initialization,
executor behavior, MMIO validity or interrupt interference.

## Shared function outcomes

P = tool reported proved, R = tool reported refuted, U = incomplete. MIRAI has separate
warning/silent
labels, not proof outcomes. All four tools consumed byte-identical `cases.rs` bodies. Safe means the
intended property holds; panic means a known native panic witness exists.

| Case | Expected | miren | Kani | Crux | MIRAI |
| --- | --- | --- | --- | --- | --- |
| guarded_index | safe | P | P | P | silent |
| unguarded_index | panic | R | R | R | warning |
| checked_add | safe | P | P | P | silent |
| overflow_add | panic | R | R | R | warning |
| nonzero_match | safe | P | P | P | warning |
| nonzero_unwrap | panic | R | R | R | warning |
| mutable_preserve | safe | P | P | P | silent |
| mutable_wrong_claim | panic | U | R | R | silent |
| bounded_iterator | safe | P | P | P | warning |
| trait_dispatch | safe | P | P | R: false alarm | missing-body warning |
| vec_roundtrip | safe | U | P | P | warning |
| vec_wrong_length | panic | U | R | R | warning |
| async_two_polls | safe | P | P | P | warning |
| async_late_panic | panic | R | R | R | warning |

Miren reported 7 P / 4 R / 3 U. Kani reported 8 P / 6 R. Crux reported 7 P / 7 R, including the
false alarm; it matched 13 of 14 expected classifications. MIRAI emitted diagnostics for 10 roots
and none for 4. Five of its diagnostic roots are safe controls, including one missing-body refusal;
five are known panicking controls. The native tests pass all safe controls and confirm all six
negative witnesses. Trait dispatch is exhaustively checked for both choices and all 256 u8 values.

Miren's two Vec roots stop at an unsupported `Alignment` to `usize` transmute in allocation source.
The mutable false assertion reaches missing `core::panicking::assert_failed_inner` MIR from prebuilt
core, so it stays UNKNOWN rather than confirming a panic. No benchmark case was rewritten to avoid
these gaps.

For Crux's trait result, the counterexample chooses increment=true and value=253. Native execution
and Kani accept that input. Separate Crux controls accept concrete true/false choices and a symbolic
value with a fixed true choice, but reject a symbolic choice with fixed value 253. This isolates the
disagreement to symbolic selection in this example; it does not identify the underlying defect.

For MIRAI's silent mutable negative, an info-log rerun confirms that `mutable_wrong_claim` was
selected
and analyzed with paranoid diagnostics. A separate wrapper calling the same unchanged function with
`[0; 4], 0, 1` does produce the expected assertion warning. Its arbitrary-input root remains silent.
This difference is material for our desired root verification workflow.

## Existing parser

Both DR16 wrappers are reported proved by miren, Kani and Crux. MIRAI compiles the unchanged parser
and dependencies but emits a union-initialization warning in core's array iterator implementation.
The native wrapper boundary test passes. These are the bounded domains described in the README.

The older MIRAI compiler was a compatibility concern, but it did compile these edition-2024
dependencies successfully. There was no demonstrated edition blocker in this experiment.

## Versions and execution limits

- Miren: production engine corresponding to `8472192`, nightly 2026-09-22, default analysis limits.
- Kani: 0.68.0, CBMC 6.11.0, compiler nightly 2026-08-21, unwind 12 for shared cases and 24 for
DR16.
- Crux-MIR: CI build 0.13.0.0.99, commit `7f49dac06c656f7b92c8b6cc054f47c63b60abe4`,
  schema 13 mir-json with nightly 2026-03-21, Z3 and path feasibility checks.
- MIRAI: package 1.1.12, commit `aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`,
  nightly 2025-01-10, paranoid diagnostics and local Z3. Its CLI still prints version 1.1.7.

Shared-case process time is roughly 0.05-0.32s for miren, 0.19-1.74s for Kani, 0.19-0.57s for Crux,
and 0.08-0.14s for MIRAI in the final run. These include frontend work, use different toolchains and
are single samples with warm tool caches. They are not evidence of comparative scalability.
MIRAI's cheaper diagnostic results are not equivalent to the other tools' verification results.

Crux requires its matching translator and adapted standard libraries; its interpreter is written in
Haskell. MIRAI is written in Rust and exposes a library within its compiler plugin, but sharing its
implementation would retain compiler coupling and its analysis policies. Neither is a drop-in Rust
crate replacing miren's current symbolic engine. Initial integration through subprocess adapters
would let us evaluate usefulness without committing to that extraction.

## Evidence

Repository validation passed: formatting, cargo lint, the full workspace Rust suite, 91 Python
tests, release builds, cargo deny and manual hooks. Both standalone benchmark crates also pass
Clippy, native tests and release builds; the DR16 dependency check passes. No interpreter behavior
or application source was changed by this stage.

Raw final runs, earlier failed setup attempts, versions, hashes, the trait controls, MIRAI mutation
traces and native/project validation logs are under:

`/tmp/miren-verifier-comparison-20261015`

`measurement.json` fingerprints final shared runs and DR16 receipts. The runner hashes each selected
binary before and after execution and checks copied sources. This records local execution evidence;
it does not freeze every upstream compiler, solver, translated library or Cargo dependency. The raw
directory is local temporary storage, not a permanent public artifact or a soundness audit.

Primary tool documentation: [Kani](https://model-checking.github.io/kani/),
[Crux-MIR](https://github.com/GaloisInc/crucible/blob/master/crux-mir/README.md),
[MIRAI analysis policies](https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md).
