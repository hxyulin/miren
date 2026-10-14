# Rust verifier comparison

This is a small compatibility benchmark, independent of miren's capability manifest. It compares
identical synthetic Rust function bodies across miren, Kani, Crux-MIR and MIRAI, then checks
wrappers
around the unchanged DR16 parser. It measures selected outcomes, not Rust or std coverage.

See [the first measurement](RESULTS.md) for results, tool versions and the resulting recommendation.
The broader Rust coverage goal remains paused.

## Shared cases

`cases.rs` contains eight safe controls and six controls with known native panics. Inputs are
arbitrary primitive values and four-element arrays. There are no external device models, trusted
callees or harness assumptions. Async cases poll a fresh future twice using a noop waker; they do
not model an executor, interrupts or scheduling. The native tests exhaust both trait-dispatch
branches over all u8 inputs and exercise the other controls and known panic witnesses.

The runner creates per-case copies of the same source and separate symbolic harnesses. It preserves
commands, selected environment settings, versions, stdout, stderr, timings and binary/source hashes.
It rejects an existing output directory and writes a partial summary before executing commands.
Timeouts terminate the owned process group. Unsupported operations, errors and absent tools remain
visible in the raw records. `complete` means collection finished; it never means verification
passed.
The runner does not convert diagnostic silence or process exit zero into a proof.

Run each tool with its required compiler and libraries available:

```sh
python3 tools/verifier_comparison/run.py --tools miren kani \
  --miren "$PWD/target/release/miren" --output /tmp/verifier-host-001
python3 tools/verifier_comparison/run.py --tools crux \
  --crux /path/to/crux-mir --output /tmp/verifier-crux-001
RUSTUP_TOOLCHAIN=nightly-2025-01-10 \
  python3 tools/verifier_comparison/run.py --tools mirai \
  --mirai /path/to/mirai --output /tmp/verifier-mirai-001
```

For Crux, put matching `mir-json` tools and Z3 on PATH, and set `CRUX_RUST_LIBRARY_PATH` to the
translated libraries. A Crux binary alone is insufficient; the first measurement needed current CI
artifacts because stable Crux 0.12 expects schema 8 and current mir-json emits schema 13.
For MIRAI on macOS, `--mirai-library-path` can supply colon-separated rustc-driver and Z3 library
directories. Passing it through the runner avoids macOS stripping DYLD variables from system Python.
The first measurement built MIRAI with `--no-default-features --features z3,z3-sys` against the
local
Z3 headers/library. This changed only the dependency lock resolution, not upstream Rust source.

`--case` selects individual controls; `--timeout` bounds each command. Kani uses unwind 12 and
retains
unwinding checks. Its counterexample playback tests are printed into the logs, not injected into
source. Crux uses Z3, path feasibility checks and model output. MIRAI uses `--diag=paranoid`;
`--statistics` is deliberately absent because it suppresses diagnostic text in the measured version.
Miren uses its default analysis limits. The tools use different compiler and standard-library
versions; timings include frontend work and are single samples, not a throughput ranking.

## Existing parser

The separate `dr16` Cargo project depends directly on `examples/dr16`. Its two wrappers check
channel
and switch bounds for arbitrary 18-byte frames, and acceptance for lengths 0 through 20 over an
arbitrary 20-byte backing array. Lengths greater than 20 return immediately. These are bounded
wrapper domains, not verification of arbitrary-length slices or all DR16 functionality.
The application and contract sources are unchanged. Tool harnesses are cfg-selected in the wrapper.

```sh
cargo test --manifest-path tools/verifier_comparison/Cargo.toml
cargo test --manifest-path tools/verifier_comparison/dr16/Cargo.toml
cargo kani --manifest-path tools/verifier_comparison/dr16/Cargo.toml --lib --default-unwind 24
cargo +nightly-2026-03-21 crux-test \
  --manifest-path tools/verifier_comparison/dr16/Cargo.toml --lib -- --solver z3 --path-sat -m
MIRAI_FLAGS=--diag=paranoid cargo +nightly-2025-01-10 mirai \
  --manifest-path tools/verifier_comparison/dr16/Cargo.toml --lib
target/release/miren --manifest-path tools/verifier_comparison/dr16/Cargo.toml \
  --lib --no-config --entry parser_fixed --entry parser_lengths
```

The external tools must be installed/configured first; the runner does not install them. Current
MIRAI's older compiler did compile the edition-2024 parser and contract dependencies in this run.
MIRAI results are warnings, not PROVED/REFUTED equivalents. A missing-body warning is an incomplete
analysis, and a silent run is not an accepted proof.

## Reproducing the Crux disagreement

Generate a Crux harness for `trait_dispatch` with the runner. Compare the original symbolic inputs
with `cases::trait_dispatch(true, 253)`, `cases::trait_dispatch(false, 253)`,
`cases::trait_dispatch(true, u8::symbolic("value"))`, and
`cases::trait_dispatch(bool::symbolic("increment"), 253)`. Only the harness changes; retain the
original `cases.rs`. The measured build passes the first three controls and reports a counterexample
for the fourth. Native exhaustive testing and Kani pass the original function. The exact underlying
Crux defect has not been identified or fixed.
