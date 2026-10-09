# Rust capability baseline and extension boundaries

The next development priority is general Rust execution. Fleet remains a regression workload;
its hardware and executor assumptions do not define the language semantics. The capability suite
runs without a firmware checkout, hardware policy or trusted function contract.

## First milestone

The first Rust-first milestone requires a shared machine-readable case manifest, host and ARM
execution at O0 and O2, positive/refuted/unknown controls, a source mutation that breaks a proof,
structured UNKNOWN reporting, and passing repository checks. Completion establishes a repeatable
baseline. It does not establish full Rust support or a completed memory-model refactor.

The manifest contains 23 cases across 12 families. After the finite typed-slice stage, each
build configuration expects 11 PROVED, 9 REFUTED and 3 UNKNOWN results. The initial stage-133
baseline was 10 PROVED, 9 REFUTED and 4 UNKNOWN. Covered examples exercise arithmetic, enum payloads,
array indexing, reference effects, concrete generics, closures, iterator callbacks, finite loops,
destructors and fresh future polling. Open dispatch and incoming non-byte slices retain explicit
unsupported frontiers. Indexed retained mutable integer/tuple prefixes now execute through checked
projection snapshots with a uniquely determined length of at most 128 elements. An expected UNKNOWN must reach its
specified diagnostic, rather than merely fail elsewhere.

```sh
cargo test --locked -p miren --test rust_capabilities
cargo build --workspace --release --locked
python3 tools/rust_capability_survey.py --output /tmp/miren-rust-capabilities-001 \
  --solver "$PWD/.venv/bin/z3"
```

The Cargo test and standalone runner consume `tests/capabilities/rust.json`. The runner freezes
analyzer binaries, records source revision and fixture/manifest hashes, retains full reports and
commands, and checks inputs again at completion. A successful run means expectations matched;
UNKNOWN and REFUTED cases are deliberate controls. Counts describe cases, not language feature
percentages. The existing larger integration suite remains necessary.

## UNKNOWN categories

Reports add an optional `unknown_category` to unfinished obligations and grouped coverage gaps:
`semantics`, `missing_compiler_evidence`, `solver`, `resource_limit`, `external_environment`, or
`unclassified`. These categories describe a producer's reason; they never change proof status.
Legacy reports without the field remain readable. Regenerated legacy gaps are unclassified.

The current engine still propagates string errors. Producers register explicit categories, and
frame-wrapped errors retain those recorded causes. Unregistered or conflicting causes stay
unclassified; no keyword classifier infers that an error is solved or that a limit increase will
help. The initial tags cover selected semantic frontiers, unavailable MIR/evidence, solver failures,
execution/query/retry budgets and external event instructions. Producer coverage remains partial.

## Architecture direction

| Layer | Responsibility | Device knowledge |
| --- | --- | --- |
| Compiler adapter | MIR, instances, types, layouts and evidence | Target facts only |
| Rust engine | Execution, allocations, initialization and access | No chip registers |
| Model interface | Symbolic transitions, storage effects and evidence | Model identity |
| Model packages | Peripherals, interrupts or scheduling policies | Device/library specific |

This is the intended boundary, not four already-separated crates. The current engine consumes
rustc MIR directly, and STM32 selection is still implemented inside its hardware module. The
public configuration and report types provide the first host-facing boundary. Future extraction
should keep compiler identities private, exposing stable descriptors rather than rustc lifetimes
or internal symbolic `Value` variants.

An external operation should carry its kind, arguments, target properties and relevant access
facts. A model returns symbolic results and validated state transitions, including alternatives,
preconditions and Rust-storage effects. The engine owns path branching, allocation provenance,
reference validity, invalidation and obligations. No adapter may invent Rust allocation rights,
ignore unsupported MIR or claim that an annotation is verified.

Model identity, version, configuration and used assumptions must remain in evidence. Conditional
models remain distinguished from strict language semantics. A concrete emulator trace demonstrates
one execution; symbolic proof requires coverage of the admitted states and transitions. Missing
operations stay UNKNOWN. The current declarative API does not register executable callbacks,
correlated register state or a complete Embassy scheduler.

Ordinary Embassy code should execute as Rust. A future environment adapter supplies external
interrupt/scheduling behavior, not replacements for arbitrary Rust bodies. Likewise, the engine
understands volatile accesses while an STM32 package supplies the meaning of its registers.

## Open access-validity blocker

Tracked volatile reads and raw byte-slice views currently lack a certificate for temporal
access permission. A live allocation, matching type, aligned address and retained writable
flag do not establish that an old pointer remains valid after competing reference access.
The [Rust pointer documentation](https://doc.rust-lang.org/std/ptr/index.html#safety)
describes temporal permission and a limited reference-to-pointer access guarantee; precise
aliasing rules are not fully settled. The audit is a missing-certificate finding, not a
claim that every probed sequence is necessarily undefined behavior under every model.

Four old-pointer access sequences currently report PROVED on host and ARM at O0/O2 without
assumptions. Those results do not certify the omitted access condition. Preserve their
reports at `/tmp/miren-raw-alias-validity-audit` while implementing conservative rejection
or a justified access model. Do not use these results as evidence of full Rust parity.

A future model needs path-local access tokens, derivation lineage and invalidation at
actual MIR reads, writes, borrows and call boundaries. Re-registering the same address
must not resurrect revoked rights, and forming a pointer from a stale reference must not
create permission. Raw slices also require valid retained reference rights after their
construction. Internal snapshot or validation reads must remain distinct from actual
program accesses. Until this foundation is certified, defer broad raw-pointer expansion.

## Next implementation stages

1. Migrate common allocation, typed projection, initialization and access checks incrementally.
   Compare obligation queries for representation-only changes before enabling additional behavior.
   See the existing [typed storage design](storage-model.md).
2. Expand typed slices, symbolic composite indexing, reference-containing aggregates, partial
   initialization, concrete dispatch/shims and drop behavior. Add P/R/U and mutation controls for
   each new capability; preserve unsupported reference-validity boundaries.
3. Establish allocation/deallocation semantics before executing `Box`, `Vec` and `String` bodies.
   Finite capacities and resource limits must remain explicit.
4. Expand resumed futures, cancellation/drop, loop invariants and recursive summaries. Treat
   concurrent execution as a separate explicit model.
5. Extract the external-operation boundary and move device selection into model packages once the
   Rust storage/effect vocabulary is stable.

Feature admission and proof completion are separate. Supporting a MIR operation does not make all
programs using it decidable or eliminate solver and resource limits. Add families to the manifest
as features become supported; retain historical evidence rather than changing an expected UNKNOWN
just to make a run green.

## Dependency fixture sources

`tests/vendor` contains pristine registry archives unpacked for portable-atomic 1.15.0 and
static_cell 2.1.1, with original licenses, manifests and per-file hashes. They are external compiler
fixtures, outside the host workspace. Their unsafe internals do not grant the analyzer any new
semantics. The atomic integration test compiles their actual bodies and mutates only a temporary
copy to check rejection.

The archive checksums match the pinned workspace lockfile. `tools/test_vendor_sources.py` checks
complete file sets and contents. Manual formatting hooks exclude these upstream files to preserve
identity. Change the source version and provenance manifest together when intentionally upgrading.
Vendoring these fixtures does not replace the normal Cargo cache for miren's own dependencies or
all optional upstream features. The core-only capability suite has no third-party dependency.
