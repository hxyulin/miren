<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="docs/public/mark-dark.svg">
    <source media="(prefers-color-scheme: light)" srcset="docs/public/mark.svg">
    <img src="docs/public/mark.svg" alt="miren logo" width="128" height="128">
  </picture>
</p>
<h1 align="center">miren</h1>
<p align="center">Panic freedom and contracts, verified from Rust MIR.</p>
<p align="center">
  <a href="https://github.com/hxyulin/miren/actions/workflows/ci.yml">
    <img alt="CI status"
      src="https://github.com/hxyulin/miren/actions/workflows/ci.yml/badge.svg?branch=main">
  </a>
  <a href="https://github.com/hxyulin/miren/actions/workflows/docs.yml">
    <img alt="Documentation status"
      src="https://github.com/hxyulin/miren/actions/workflows/docs.yml/badge.svg?branch=main">
  </a>
  <a href="rust-toolchain.toml">
    <img alt="Rust nightly 2026-09-22"
      src="https://img.shields.io/badge/Rust-nightly--2026--09--22-dea584?logo=rust">
  </a>
  <a href="docs/proofs.md">
    <img alt="Status: experimental"
      src="https://img.shields.io/badge/status-experimental-d4a24a">
  </a>
  <a href="#license">
    <img alt="MIT or Apache-2.0"
      src="https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue">
  </a>
</p>
<p align="center">
  <a href="https://hxyulin.github.io/miren/">Documentation</a> ·
  <a href="https://hxyulin.github.io/miren/usage.html">Getting started</a> ·
  <a href="https://hxyulin.github.io/miren/examples.html">Examples</a> ·
  <a href="https://hxyulin.github.io/miren/fleet-survey.html">Fleet survey</a>
</p>

A Rust MIR analyzer for panic freedom and function contracts. It follows actual function calls
with symbolic inputs and asks Z3 to check the resulting obligations. Contracts add metadata
without runtime assertions. Analysis runs on the host against your Cargo target and profile,
including embedded no_std builds.

This is an experimental side project. It requires a pinned nightly compiler, supports part of
Rust, and has not completed a soundness audit. Unsupported operations and unfinished proofs return
UNKNOWN. A solver counterexample is not automatically a confirmed runtime panic.

Readonly `Option<NonZero<T>>` slices support every Rust integer primitive on 32-bit and 64-bit
targets, including target-sized `usize`/`isize`. These and exact
local empty/NonZero integer enums retain the compiler's zero-only niche with correlated tags and
guarded payload observations. Signed payloads preserve negative and minimum values.
Original type, body, lifetime and resource checks remain required; pointer niches, mutable niches
and whole-slice comparison are separate unsupported domains. See the
[capability evidence](docs/rust-capabilities.md).

Mutable scalar slices support bounded whole-child helpers, scalar returns, local static associated
calls and original constant-index reads and stores. Exact f32/f64 backing preserves NaN payloads and
signed-zero bits. Typed mutable tuple, array and plain local struct slices support direct metadata
and guarded whole-element, constant-suffix and symbolic fixed-array suffix reads and stores. Whole
product helpers execute actual bodies and preserve returned storage. Primitive helpers with a
retained Range view execute actual bodies, preserving live owner storage and checked primitive
signatures. Nested primitive helpers and bounded recursion execute
actual bodies with checked live ancestry. Nested owner calls remain UNKNOWN. Guarded local u16 and
`[f32; 2]` Range views retain the parent owner through lexical
release and preserve offset writes and sibling storage. Deeper whole scalar calls preserve checked
owner lineage and returned storage. Bounded owned u16 products support writes through multiple
symbolic suffix indices, preserving compiler types and current Memory. The capability manifest
covers 591 cases across 107 families, including concrete and symbolic local byte-copy controls.
Available byte-search source and isolated word predicates have separate authentication checks.
Full aligned search remains UNKNOWN pending source metadata, storage, precondition and loop proofs.

Fixed-array partial moves preserve initialization and execute remaining destructors in compiler
order. Nested destruction and covering assignments retain actual destructor effects. The exact
compiler array/slice DropGlue protocol is authenticated separately; general slice destruction and
remaining iterator destruction with elements needing Drop remains UNKNOWN.
Authenticated non-inlined array iterator constructors preserve owning payloads through actual Rust
bodies and ordinary returns. Direct owners also pass through local helpers with unused observations.
Element transfer executes at an explicitly larger analysis budget; default next and remaining
iterator destruction remain UNKNOWN.

Shared fixed-array views of local Drop structs support guarded scalar field observations and
ordinary scalar accessor calls, including authenticated lazy input arrays. Original types, current
initialized storage and readonly witnesses remain required; actual destructors still execute.
Ordinary helpers with one shared whole Drop receiver and a primitive result execute actual Rust
bodies. Named whole contract observations, product-return helpers and mutable/raw projection
authority remain UNKNOWN.

Finite known shared trait objects can be selected from local fixed arrays and retained slices.
Selected alternatives execute actual method bodies, preserving their backing references and
returned Memory. Opaque inputs and unavailable bodies remain UNKNOWN. See the
[capability evidence](docs/rust-capabilities.md).

Known local integer function tables support one or two integer arguments, preserving exact
compiler signatures and executing selected helper bodies. Authenticated MIR Repeat assignments
can construct bounded arrays of known integer, unary Bool, unary Char and unary Float pointers.
Selected calls still require
actual bodies; opaque targets and pointer-bearing product repeats remain unsupported.
See the [capability evidence](docs/rust-capabilities.md) for scope and limits.
Known nongeneric Bool-to-Bool and Char-to-Char tables also execute actual available bodies.
Char values retain Unicode scalar validity; opaque targets and missing bodies remain UNKNOWN.
Known unary f32/f64 tables and Repeat arrays execute actual bodies with checked raw representation.
Mixed signatures and opaque targets remain unsupported.

## Install

The toolchain file installs the matching nightly, compiler development components and ARM target.

```sh
git clone https://github.com/hxyulin/miren.git
cd miren
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-solver.txt
cargo install --path crates/miren --locked
```

Z3 must remain available in the checkout's `.venv`, on PATH, or through `MIREN_Z3`.
The installed binaries also require their pinned rustc sysroot.

## Check a project

Run from the Cargo project you want to analyze:

```sh
miren --entry module::function --lib
miren --async-entry task --bin firmware
miren report
```

Verification is the default. Cargo supplies dependency metadata, environment variables, target,
features and profile; there is no compiler invocation or saved report to prepare. `cargo miren`
uses the same workflow. Without an entry, every inventoried local body is selected, including
generated bodies that may require unsupported inputs. Use `miren inventory --verbose` to find
exact names before selecting a smaller root.

An optional `miren.json` stores settings you want to repeat:

```json
{
  "schema_version": 1,
  "entries": ["module::function"],
  "cargo_args": ["--lib"],
  "limits": {"max_call_depth": 32}
}
```

Then run `miren`. Explicit entry options replace configured roots; CLI limit options override
configured limits. There are no built-in presets or named profiles. See the
[configuration guide](docs/usage.md#project-configuration) for precedence and supported fields.

Analysis reuses dependency builds but refreshes workspace artifacts and proof results on every
run. It keeps its own build cache and run reports beneath the Cargo workspace's
`target/miren`. `miren report` reads the latest attempted run without rebuilding or
rerunning Z3; interrupted and failed runs cannot fall back to an older successful scan.

## Try the parser example

From this checkout:

```sh
cargo build --workspace --locked
target/debug/miren --manifest-path examples/dr16/Cargo.toml
```

The example's project configuration selects `Raw::parse`. Its arbitrary byte-slice inputs prove
without entry preconditions. Add `--target thumbv7em-none-eabihf` to check the ARM build.

## Read the result

| Result | Meaning |
| --- | --- |
| **PROVED** | Every reached path completed and every obligation passed for the recorded root domain |
| **PROVED_WITH_ASSUMPTIONS** | Completed under listed assumptions; acceptance requires `--allow-assumptions` |
| **REFUTED** | A translated obligation has a solver counterexample; runtime evidence is reported separately |
| **UNKNOWN** | A missing model, unavailable body or resource limit prevented a complete proof |

The CLI names failing conditions, locations and call chains, and explains the next step for UNKNOWN.
Slow checks report their active root and elapsed time. Colors supplement labels; `--quiet`,
`--verbose` and `--color auto|always|never` control display. Counts describe selected MIR roots,
not line coverage or the safety of unselected code.

```sh
miren --entry decode --lib --jsonl results.jsonl
miren report results.jsonl --verbose
```

`--jsonl -` emits machine-readable reports on stdout and keeps human messages on stderr.
Native counterexample execution remains opt-in through `--replay`. Startup assumptions,
experimental loop induction and trusted boundaries require explicit settings. Raw rustc and
`--from-report` workflows remain available for compiler debugging.

## Documentation and development

- [Usage and configuration](docs/usage.md): installation, project checks and advanced commands.
- [Coverage](docs/coverage.md): supported language features, limitations and mutation evidence.
- [Contracts](docs/contracts.md): metadata and explicit trusted boundaries.
- [Proofs](docs/proofs.md): symbolic execution, induction and counterexample interpretation.
- [Examples](docs/examples.md): independently testable parser, frame and contract cases.
- [Fleet survey runner](tools/README.md): repeatable inventories, independent proofs and comparisons.
- [Development](docs/development.md): formatting, linting, tests, builds and documentation checks.
- [Analyzer design](docs/analyzer-redesign.md): remaining storage, call and proof work.

## License

Available under either the [MIT license](LICENSE-MIT) or [Apache License 2.0](LICENSE-APACHE).
