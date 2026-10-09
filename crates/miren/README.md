# miren

Formerly mir-check. The binaries and Cargo package now use `miren`, the metadata crate is
`miren-contracts`, and project settings use `miren.json` and `MIREN_*` environment variables.

Host compiler adapter, project orchestration and report model for checking Rust MIR with Z3.
The adapter requires the exact nightly compiler in the repository's toolchain file.

## Commands

Install all three binaries with `cargo install --path crates/miren --locked`:

- `miren`: checks the current Cargo project, reads saved results, or drives rustc directly.
- `cargo-miren`: the Cargo subcommand; delegates to the same project implementation.
- `miren-rustc`: retains dependency MIR through Cargo's outer compiler wrapper.

```sh
miren --entry module::function --lib
miren --async-entry task --bin firmware
miren report
miren inventory --verbose --lib
```

Project verification is enabled by default. An optional flat `miren.json` stores entry
selectors, Cargo arguments, limits and explicit analysis policies. CLI selectors replace configured
roots and CLI limit options override configured values. Configuration cannot enable native replay.
There are no built-in presets or named check profiles. See the [usage guide](../../docs/usage.md).

## Build and result lifecycle

Project discovery uses the pinned Cargo's workspace metadata. Cargo supplies target, profile,
features, dependency paths and compilation environment. Project analysis owns an isolated cache
under the Cargo workspace's `target/miren`, with separate retained-MIR and plain dependency
builds. Before checking, it cleans only workspace package artifacts in that cache, so current
roots are always recompiled and reanalyzed. Dependency source/configuration changes remain subject
to Cargo's ordinary fingerprints. An OS file lock serializes access to the shared analysis cache;
waiting reports progress, and process exit releases the lock.

Each attempt writes fresh per-crate JSON reports into its own run directory. `latest.json` records
completion and run success; it is published before analysis as incomplete and replaced after
reporting. The default report command checks that record and cannot return success for a failed
or interrupted run. Reading an explicit JSON/JSONL file retains the existing per-report policy.
Saved display never establishes a new proof or validates current source provenance.

Dependency retention appends `-Zalways-encode-mir=yes` and `-Zmir-opt-level=0` without rewriting
Cargo's target/profile flags. It does not rebuild precompiled sysroot libraries or give foreign
functions a Rust body. `-Zbuild-std=core` can expose core MIR on a configured target. Missing bodies
and unsupported operations remain UNKNOWN.

## Compiler integration

The proof engine consumes typed MIR directly. Inventory strings are diagnostics, not parsed
solver input. `miren rustc` preserves the direct compiler interface; existing explicit Rust
source/argument commands and `--from-report` remain supported. Direct mode retains its explicit
`--verify` flag. Saved invocation reuse checks the compiler identity, analyzes current source and
requires the original dependencies and working directory. Project commands rebuild through Cargo
instead of asking users to manage those artifacts.

Fresh reports retain the compiler working directory and Cargo source environment (`CARGO_PKG_*`,
features, target configuration, manifest/crate names, `OUT_DIR` and `DEP_*`). Independent survey
replays restore those inputs without inheriting analysis policies or registry credentials.
Non-Unicode source environment values make the environment capture unavailable. Custom environment
inputs outside those Cargo variables are not captured; reports are not hermetic build artifacts.

The pinned compiler retains evaluated dependency static allocations but omits their initializer
MIR. Immutable dependency constants can still be decoded. Retained dependency builds now emit
`.rmeta.miren-origins.json` metadata from an additional compiler pass. That pass checks a bounded
typed construction graph and emits the artifact it certifies before recording its SHA-256 hash.
Compiler, target, crate/static identities, schema and a payload checksum must match on consumption.
The retention cache is versioned so older builds cannot silently omit the new evidence.
The wrapper buffers compiler output and publishes final artifact notifications only after both
passes finish, preventing pipelined Cargo consumers from racing replacement metadata.

The supported origins are declared typed construction and narrowly checked `u32` return
transmutes, including the pinned core atomic constructor. Newly constructed outer aggregates keep
their declared type; direct returned constructors retain their checked primitive origin. Rust types
come from compiler metadata, not serialized display strings. Missing, stale, corrupt or unsupported
origin evidence remains UNKNOWN. These records establish construction provenance, not runtime
values, synchronization or a verified callee summary. Ordinary atomic interference stays
conservative; startup histories still require explicit assumptions.

Whole mutable Rust `bool` statics and certified boolean fields inside compiler-identified
`UnsafeCell` storage support typed direct reads and writes through compiler-backed allocation
provenance. This includes core `Cell<bool>` storage. Interior reads require matching declared
and original types and an exact bounded struct/tuple field path through the core `UnsafeCell`
lang item; unions and uninitialized payloads remain unsupported. Each read admits either valid
boolean value, including after writes;
initializers and critical sections establish no startup or shared-state history. Counterexamples
that depend on this abstraction record its reason. Foreign storage, numeric addresses, different
scalar types, unauthenticated interior offsets and mismatched storage origins remain UNKNOWN.
Readonly pointers
cannot authorize writes.

Ordinary and async entry scopes differ: selecting an async constructor with `--entry` checks
construction; `--async-entry` also polls its fresh future through Pending and Ready states.
Executor scheduling, cancellation and unbounded suspension require additional models or proofs.
Startup entry assumptions are explicit and are not inherited by async entry analysis.

Contracts are metadata. Callee bodies and configured bounds are checked; annotations do not become
unchecked verified summaries. Explicit trusted boundaries and startup domains remain listed as
assumptions. Replay executes supported native inputs only with `--replay`, reports its independent
evidence, and never upgrades a passing execution to PROVED.

Reference graph validation is shared by tracked-value checks, frame-escape checks and returns.
It traverses nested aggregates, pointer backing storage, iterator sources and static epochs before
accepting dependent operations. The implementation lives separately from memory projection and
mutation; this separation does not change the supported reference domain.

Tracked thin raw addresses support MIR `Offset` within a compiler-sized reference extent, including
one-past formation and reverse offsets. Compiler pointee layout supplies the stride; scaled signed
displacement and allocation bounds produce explicit validity obligations. Array casts retain their
known extent. Numeric pointer offsets, zero-sized strides, wrapping arithmetic and raw loads/stores
outside the separately documented static-view domains remain UNKNOWN. Retained references still
undergo liveness and frame-escape checks.

Compiler-identified `volatile_load` reads initialized retained whole scalar allocations with an
exact registered compiler pointee type, allocation identity and live backing value. It preserves
stored floating-point bits, including NaNs and signed zero. Numeric/MMIO and static addresses,
incoming raw pointers, type punning, projected addresses and displaced cursors remain UNKNOWN;
volatile reads grant no synchronization or floating-point environment model. Dead, uninitialized
or externally invalidated backing cannot supply a value.

Compiler-typed `u8` MIR repeats use one constant SMT array and a target-width length. Their byte
count does not expand host storage, and the compiler checks the target array layout. Bounds checks
and byte updates remain active. Explicit byte aggregates and evaluated constant tables keep their
existing budgets; nonbyte repeats stay limited to 128 elements and 256 owned values.

Compiler-identified `size_of_val` uses target layouts or retained slice length and element stride.
The compiler's zero-validity guard creates a panic obligation without initializing storage.
Initialized byte arrays can become equal-sized primitive integers or f32/f64 using target endian
order, retaining exact IEEE bits. Character, restricted integer, reference and Boolean byte casts
remain UNKNOWN.

Reborrowing a shared Freeze pointee snapshot retains its projected snapshot instead of creating
an allocation owned by the temporary reference local. The compiler reference type and leading
dereference must match this domain; nested dereferences and retained allocation references use
ordinary tracked borrowing. Embedded reference graphs remain validated. These snapshots have
readable values but cannot establish raw address provenance.

The compiler-identified `mem::zeroed` model checks the compiler zero-validity guard and constructs
initialized zero values only for supported scalars, tuples, bounded arrays, structs and fieldless
direct-tag enums with a compiler zero discriminant. Byte arrays remain compact. Unions,
MaybeUninit, pointers, niche/payload enums and restricted integer reconstruction remain UNKNOWN.
This models the checked core operation; it does not make uninitialized storage readable.

Compiler-typed shared byte slices can retain a tracked source allocation and length. Reads encode
the live backing value using its recorded compiler type, field offsets and target endian order;
supported integers, arrays and padding-free structs occupy at most 128 bytes. Bounds, liveness and
frame-escape checks apply. Shared prefixes and borrowed-array conversions retain that backing
reference; owned copies retain their copied values. Numeric origins, mutable raw slices, padding
and raw subobject formation remain UNKNOWN. Raw byte access does not enable arbitrary pointer loads
or writes.

Shared non-Freeze root references retain incoming read-only storage identity, including nested
fields such as a task spawner's executor reference. One interior/mutable root storage graph is
supported; additional potentially aliased graphs remain UNKNOWN. Stores preserve reference escape
and liveness evidence. This does not supply executor startup history or enable shared writes.

Metadata-only dependency builds retain the compiler's exported symbol index. A foreign Rust ABI
call can execute a unique, strong, explicitly exported, signature-matched retained Rust body.
Missing, ambiguous, native, dynamic, weak and unsupported targets remain UNKNOWN. Declaration
contracts are not substituted for an implementation; target contracts and the actual body execute.

Exact Cortex-M PRIMASK read/write and interrupt mask instructions have a conservative model for
supported compiler assembly shapes. Reads have arbitrary 32-bit values and do not establish stable
interrupt state. Writes invalidate published atomic/startup history. Other assembly remains UNKNOWN;
these operations do not prove critical-section exclusion or interrupt scheduling.

Compiler-typed inhabited zero-sized aggregates use bounded shared input shapes, including large
peripheral token structures. They create no scalar symbols and preserve the root input budget.
Unions, uninhabited types and unsupported references remain UNKNOWN.

Checked dependency origins can certify uninitialized MaybeUninit containers through exact core
cell constructors. Certification grants no initialized payload or read history. Only the exact
bool-to-u8 scalar encoding needed by portable atomics is added to construction checking.

Fieldless enum inputs admit at most 256 compiler-declared variants, including sparse signed tags.
Payload enums remain limited to 64 variants. Exact discriminant validity constraints and the
512-value root budget remain active; no undeclared variant becomes an input.

Concrete reference coercions to trait objects retain the compiler type and vtable witness.
Virtual calls execute the exact resolved implementation with the original storage and permissions.
Arbitrary trait-object roots, unsupported upcasts and raw/boxed trait objects remain UNKNOWN.

Compiler-layout raw addresses of bounded struct/tuple fields and array elements retain allocation
provenance, offsets and subobject extents. The exact initialized pointer-array to reference-array
conversion used by each_mut requires live typed backing and disjoint mutable projections. Numeric
origins, raw dereferences and unsupported reference-array selection remain UNKNOWN.

The [coverage guide](../../docs/coverage.md) is the maintained feature reference. The
[proof guide](../../docs/proofs.md) explains the encoding and limitations, and the
[development guide](../../docs/development.md) lists required checks.

Arbitrary function-pointer inputs retain their exact compiler signature as opaque values, including
unsafe callbacks and Waker table fields. Unused or copied fields do not choose a callback target.
Calls, address casts, pointer comparisons and native replay of these inputs remain UNKNOWN.
Concrete function-item pointers continue executing their actual bodies and effects.

Owned non-byte arrays share immutable host payloads and detach changed paths on writes. Rust copies
retain independent storage. Evaluated constants check every occurrence before reusing exact typed
initialized values, with at most 2,048 visits, sixteen levels and 256 scalar or 128 composite array
elements.
Owned repeats retain the 256-value budget but charge validated shared payloads once and bounded
clone handles separately; unsupported payloads and interior mutation remain UNKNOWN.

Mutable byte ranges use the exact compiler `Range<usize>` SliceIndex implementation. Analysis checks
start <= end <= slice length and preserves the backing allocation through nested projections.
Non-byte ranges and missing writable provenance remain UNKNOWN.

Compiler inventories record whether each function directly returns a coroutine. Fleet surveys
separate those future-construction roots from function-body roots; explicit async polling remains
a separate capture. Older inventories without this metadata remain unclassified.

Initialized scalar constant arrays support up to 256 exact bool, integer or f32/f64 elements.
Composite arrays retain the 128-element cap, with the existing total and depth budgets. Every
constant element is decoded and validated; indices require bounds checks and float bits survive.

Dependency origin schema 2 includes exact typed associated-constant construction edges. Retained
builds use a new cache generation so prior certificates are not reused. Construction certificates
establish origin metadata, without granting initialized payload reads or startup history. Local and
foreign declarations without bodies are rejected before any compiler CTFE MIR query.

Closed constructor calls accept aggregate parameters only after checking each actual operand's
origin, exact compiler type and monomorphized signature. Straight-line construction preserves
whole scalar carrier origins; composition recognizes only exact compiler atomic types with
matching layouts. This certifies construction metadata without selecting atomic values or history.

Core unchecked slice iterator access requires retained live backing and proven index/cursor bounds.
Mutable access also records distinct issued indices and rejects later conflicting ordinary access.
Bare value snapshots do not grant unchecked liveness; unsupported backing and uncertain bounds
remain UNKNOWN. This is a bounded adapter model, not a general raw-pointer interpreter.
