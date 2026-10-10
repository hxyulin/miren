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
The fleet survey tooling has separate, opt-in STM32H723VG and STM32F407IG initialization
hypotheses in [its README](../../tools/README.md). They use ordinary recorded trusted contracts;
no device assumption is enabled by selecting an ARM target or by running strict verification.


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
boolean value, including after writes, in ordinary analysis. Initializers and critical sections
establish no startup or shared-state history. Explicit `--startup` records fresh initial values and
no external changes to tracked static storage before pointer publication or opaque calls. In that
conditional domain, certified boolean reads use initializer values and exact branch-local writes,
sharing storage footprints and invalidation with integer atomics. Unsupported static writes, mixed
or overlapping views and opaque boundaries discard precision; later writes cannot restore it.
Conditional first use proves, repeated initialization refutes, and unsupported pointers remain
UNKNOWN. This does not establish reset execution or enable startup facts in async roots.
Counterexamples that depend on arbitrary-read abstraction record its reason. Foreign storage, numeric addresses, different
scalar types, unauthenticated interior offsets and mismatched storage origins remain UNKNOWN.
Readonly pointers
cannot authorize writes.

Primitive integer payloads use the same certified whole mutable static or bounded `UnsafeCell`
field paths. Ordinary reads admit a fresh arbitrary value with the compiler's target width and
signedness; writes establish no shared-state history. Explicit `--startup` reads checked initialized
scalar bytes and retains exact branch-local integer writes, sharing the 128-location budget with
other startup facts. Disjoint fields and scalar atomic histories remain independent. Incompatible
or overlapping cached reads remain UNKNOWN; conflicting stores discard startup history. Pointer
publication and interrupt-mask writes invalidate ordinary startup history. Opaque calls invalidate
both startup domains, including unseen facts; subsequent writes cannot restore them. Unions, arrays, numeric pointer origins, `MaybeUninit` payloads and type
punning remain unsupported.

Ordinary and async entry scopes differ: selecting an async constructor with `--entry` checks
construction; `--async-entry` also polls its fresh future through Pending and Ready states.
Executor scheduling, cancellation and unbounded suspension require additional models or proofs.
Startup entry assumptions are explicit and are not inherited by async entry analysis.

Reports also retain up to 512 symbolic body entries after argument validation and a satisfiable
start-block path. Each record identifies the concrete instance, compiler coroutine-poll kind,
source and call chain. Constructor analysis alone supplies no poll-entry evidence. Truncation is
explicit; these records establish neither native reachability nor completed panic freedom.

In explicit startup mode, certified Copy/Freeze enum places can inspect their declared initializer
tag through rustc's typed discriminant decoder, including niche pointer options and signed tags.
Exact Copy/Freeze enum stores with only primitive scalar fields retain branch-local tags under that
same premise. Pointer, callback and aggregate fields remain outside retained enum history. Reads
still expose only tags; publication and opaque effects discard both known and unseen facts.
The bounded read-only host snapshot preserves initialized bytes and provenance; it does not enable
runtime payload reads. Overlapping histories, unsupported static writes and opaque boundaries still
discard precision. Ordinary enum tags remain arbitrary legal observations.

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

Compiler-identified `volatile_load` checks exact compiler pointee type, allocation identity,
liveness and initialized whole-scalar backing. Even matching storage returns UNKNOWN because
these checks do not certify temporal access permission. Numeric/MMIO and static addresses,
incoming raw pointers, type punning, projections and displaced cursors also remain UNKNOWN.
No retained scalar value is exposed by an uncertified volatile read.

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

Compiler-typed const raw byte-slice pointers retain a source pointer and target-width length.
Their snapshots preserve pointer metadata instead of converting it into byte values. Metadata
formation and length queries grant no Rust reference rights and do not require the length to fit
an allocation. Numeric source pointers may supply metadata, never storage rights. Mutable raw
slice pointers remain unsupported.

Creating a shared byte reference, reading raw byte storage, or converting a nonempty tracked raw
pointer array into Rust references remains UNKNOWN without temporal permission evidence. Exact
layout, initialization, liveness, bounds and disjointness checks remain active, but do not supply
that missing certificate. This includes safe core `array::each_mut` bodies at their internal
reference-array conversion; ordinary safe tracked references and slices remain supported.

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
interrupt state. Writes invalidate published history outside isolated startup. Other assembly
remains UNKNOWN. Exact `sev`, `wfe` and `wfi` templates report unmodeled hardware event/wait
semantics
before checking PRIMASK-specific options. These operations do not prove critical-section exclusion
or interrupt scheduling. Unsupported assembly errors identify the selected root in `function` and
`source`;
`call_chain` retains the deepest failing call, which may be a dependency body.

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
conversion used by `each_mut` checks live typed backing and disjoint mutable projections, but
nonempty conversions remain UNKNOWN without temporal access certification. Numeric origins,
raw dereferences and unsupported reference-array selection also remain UNKNOWN.

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

Byte-view writes count generated SMT array stores against a 128-write budget. Fixed short copies
can update larger compact byte allocations while preserving all other bytes. Symbolic copy lengths
still require capacity-many stores and remain UNKNOWN when that bound exceeds the budget. Exact
modular cancellation keeps `(offset + length) - offset` at the retained length term, including
fixed-size copies with symbolic offsets. Region bounds, equal copy lengths,
writable provenance and allocation liveness remain checked. Typed-byte encoding and expanded-value
limits are unchanged. Same-term cancellation applies at the exact bit-vector width and does not
remove Rust overflow checks or memory-region obligations.

Symbolic indexing can select fieldless enum input values when every element retains the same
complete variant inventory. Selection changes only the signed, target-width integer discriminant;
type names, variant positions, exact tags, Option metadata and empty payloads must agree. Bounds
checks remain authoritative. Payload enums, mixed constructed/input choices and incompatible
inventories remain UNKNOWN. No new pointer identities, contracts or entry assumptions are added.

The NonZero getter model requires the actual core inherent method, its instantiated diagnostic
owner and the exact safe primitive signature. User functions or local trait methods named get
execute their retained bodies; a missing body stays UNKNOWN.

Actual core NonZero constructors support the primitive integer to `Option<NonZero<T>>` transmute
when compiler identity, scalar layout and the exact zero-only niche agree. The original integer
selects None at zero and supplies Some's payload otherwise; no nonzero assumption excludes None.
Different primitive types, wrappers and pointer niches remain UNKNOWN. A missing constructor body
stays UNKNOWN, and Some payload access still requires a proven variant check.

The reverse core `NonZero<T>` to exact primitive T transmute requires the same compiler storage
certificate and a proven nonzero source under existing path conditions. The intrinsic ctlz_nonzero
reuses exact leading-zero counting only for a proven nonzero operand. MIR unchecked left shifts
require the original count to be proved below the primitive width before casting or masking; zero
values/counts remain valid. Unproved preconditions stay UNKNOWN without new path assumptions.

Lazy input descriptors include bounded compiler-certified Freeze enums with supported payload
shapes. A full-domain unsigned selector maps to exact valid compiler tags, including sparse signed
tags; no enum-validity assumptions are added. Variant payload and array-occurrence symbol ranges
remain disjoint. The 64 payload / 256 fieldless variant caps, 512 descriptor nodes, depth 16 and
262144 reserved-symbol slots remain enforced. Reference, pointer, interior, union and restricted
payloads keep their existing eager or UNKNOWN fallback.

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

Constructor evidence uses shared compiler-body validation, return-type binding and certificate
finalization. Scalar-only and closed aggregate checking retain separate argument/cache policies;
U32 carriers and exact `Atomic<usize>` constructors retain their separate layout requirements.

Explicit `--startup` additionally retains initialized null or numeric address bits from certified
static pointer atomics. Reads share the integer atomic footprint and budget checks. Returned raw
addresses grant no pointee access; provenance-bearing initializers remain UNKNOWN. Stores, CAS,
opaque calls and interrupt-mask writes discard startup history, including unseen locations.
Ordinary roots retain arbitrary pointer reads, and async roots cannot select startup assumptions.

Integer and pointer compare-exchange share ordering validation and the success formula. Each weak
operation creates a fresh possible spurious failure. Receiver certification, primitive value types
and storage updates remain specific to each model. Pointer equality supplies no shared-state
history.

`--startup-isolated` selects a separate conditional zero-argument entry domain: fresh Rust statics
and no external task, thread or interrupt changes to tracked Rust storage throughout the entry,
including after publication. Both premises appear in reports. Typed writes retain exact values;
partial overwritten ranges cannot reuse initializer bytes. Exact destructor-free retirement affects
its footprint and still requires matching reinitialization. Opaque calls invalidate all history.
Supported local/static pointer atomic operations retain actual values; uncertain provenance joins
retain address bits only. This grants no MMIO validity or hardware instruction support, and cannot
be selected for async roots or induction. Ordinary and `--startup` domains remain separate.

Isolated pointer weak-CAS retry cycles use a bounded exploration policy after at least one real
return has passed escape and postcondition checks. A fourth visit on that retry path records
UNKNOWN and discards only the unfinished frontier. Checked returns can continue into the caller,
but the incomplete obligation remains. Each weak operation still has a fresh spurious failure; no
eventual success or retry fairness is assumed. Ordinary loops and other entry domains keep their
existing exploration.

Known function items can be reified directly as unsafe function pointers when the actual body is
safe and every other normalized signature component matches. Foreign Rust symbol binding shares
this check: a safe exported body may satisfy an unsafe declaration. ABI, argument and return types,
variadic status and bound variables remain exact; the reverse safety change stays UNKNOWN. Actual
retained bodies still execute, and separate safe-pointer-to-unsafe-pointer conversions remain
unsupported.

Isolated retained struct/tuple stores support exact compiler-certified child reads and updates.
A child write reconstructs the retained parent and preserves actual sibling values; it does not
reuse initializer bytes. Transparent equal-footprint fields require a real declared field path.
Paths are bounded to eight levels, 128 fields per aggregate and 256 visited types. Unions, arrays,
enum paths, type punning and ambiguous overlapping identities remain UNKNOWN. Existing typed
validity, initialization, retirement, reference escape and opaque-effect checks still apply.

Core slice Iterator::for_each supports finite tracked Iter/IterMut backing and concrete function
items, closures or known safe Rust function-pointer callbacks. It executes actual callback bodies in
source order, retains their conditions and memory changes, advances borrowed cursors and retires
closure environments. Completion requires an exhausted iterator and unit callback results.
Fold/rfold, all/any and find_map share concrete callback resolution. Known pointer values require an
exact registered signature and retained body; arbitrary pointers, callback references, unsafe or
non-Rust signatures and missing bodies remain UNKNOWN. Callback destructors, unsupported backing and
ambiguous mutable projections also remain UNKNOWN.

Shared slice iterator stepping validates retained backing before exhaustion as well as element
access, and repeats that check after callbacks. Retired empty backing remains UNKNOWN.

Typed SMT queries retain the existing per-condition serialization when it fits the configured byte
budget. Oversized queries retry with one Boolean conjunction and shared local let bindings across
all original conditions, under the same whole-script budget. This preserves floating-point
conditions and separate non-floating probes; unsupported or still oversized queries remain UNKNOWN.
Handwritten solver queries retain their original representation.

Bounded homogeneous constant integer array choices use shared SMT arrays instead of repeated
conditional chains. The representation preserves target width, signedness, exact element values
and the previous last-element default for every unmatched index. Index keys must fit their bit
width, and actual term sorts and analysis contexts must match declared metadata. Existing compiler
bounds, origin and liveness checks remain authoritative. Symbolic, mixed, Boolean, floating-point
and pointer choices keep their prior behavior. The representation adds no assumptions or larger
budgets.

SMT array reads skip intervening stores only when the read and stored keys are same-width literal
bit vectors with unequal values. Traversal is iterative, preserves the latest matching write and
constant-array default, and stops at symbolic keys. This exact read-over-write simplification adds
no memory rights or assumptions; compiler bounds and storage-lifetime checks still apply.

A single top-level incoming shared reference to bounded `Freeze` storage retains caller-owned
allocation identity for the duration of root analysis. Pointees may contain plain scalars, fixed
arrays, tuples, structs and enums, with no reachable references, raw pointers or interior mutation.
Plain owned arguments may coexist; competing borrowed or pointer-bearing inputs retain the prior
snapshot domain. This restriction governs the new retention capability. Existing input budgets,
mutable/interior/static models and unchecked iterator liveness checks remain active. Returned and
reborrowed views preserve the actual allocation; retiring a reference local does not retire caller
storage. Opaque memory effects still invalidate backing, and shared references grant no write
rights.
The model uses valid incoming Rust borrows and adds no entry assumptions or hardware facts.

Checked mutable ranges over finite arrays of primitive integers and tuples of integers can
retain their original allocation and projection through mutable slice iterators. Compiler
receiver/output element types, integer widths/signs and tuple fields must match the stored
values. Each element read/write proves the region and index bounds before translating its
address; exhausted consumers still validate the original backing. Retained slice projections
can materialize integer/tuple snapshots with a uniquely proven length of at most 128 elements.
Nested slices and element/tuple-field writes retain the original allocation and update its
actual elements; shared reborrows narrow write permissions. Scalar reads may select a symbolic
offset, while tuple selection and writes require a uniquely determined element. Variable-length
snapshots, whole-view assignment, arbitrary incoming non-byte slices and reference/interior-mutable
payloads remain unsupported. Snapshot budget exhaustion records `resource_limit`; oversized
backing allocations do not by themselves prevent a bounded small view.

Concrete core `Iterator::find` executes its predicate in order, preserves each callback's
memory effects and returns the original first matching item. The predicate receives a shared
reference to a temporary item slot; that slot retires after the callback, and escaped temporary
references are rejected. Compiler `Use(Copy(place), WithRetag::No)` dereference copies through
shared storage retain their allocation/projection with mutation permission narrowed to false.
Ordinary copied/moved mutable handles through shared storage remain unsupported. Compiler
mutable-reference positions, including tuple/array/ADT fields, reject narrowed handles at
ordinary ownership exposure and return boundaries. Shared reads and valid nested mutable
reborrows keep their existing behavior.

The public host model API exports `HardwareModel`, `HardwareDevice`, `MmioRegion` and
`MmioWriteRegister`, with builders and validation. `ContractConfig::with_hardware` composes an
explicit hardware policy with existing function summaries. The optional field is omitted when
absent, preserving strict defaults and legacy schema-1 configuration. The
[STM32 builder example](examples/stm32_model.rs) emits JSON using the same public API.

The first backend admits bounded numeric byte-pointer transport and exact write-only unsigned
u32 GPIO register stores, including compiler-certified transparent register values. Actual
callbacks and Rust arithmetic execute. Configured device/pointer-width evidence must agree;
physical validity and unmodeled hardware/Rust effects are assumptions. Numeric addresses never
become retained Rust allocations, references or read permission. Each actual model use records
its premise even on refuted/unknown roots. Unsupported operations remain UNKNOWN. See the
[external model guide](../../docs/contracts.md#external-model-api) for limits and future
state models.


Hardware schema 2 adds `MmioReadRegister` and `with_read_register`. Exact numeric u32 reads return
independent fresh words with an explicit device-correlation abstraction reason; they do not cache
readback or assume ready bits. Compiler-certified transparent scalar values share the write
certificate. Actual read-modify-write callbacks and their Rust effects execute, and each read
conservatively invalidates publication/startup history. Tracked RAM reads retain existing behavior.
Schema 1 stays write-only with its empty read list omitted. Native replay refuses configured or
recorded hardware models, including an unused policy on an earlier counterexample.

Fieldless enum-to-integer transmutes require an explicit integer repr and exactly that primitive
as the target. Compiler layout must certify an initialized direct scalar tag with matching size,
alignment, width, signedness and zero offset. Concrete variants and complete symbolic inventories
must match compiler identity and discriminants; symbolic tags must already have proven membership
in the exact legal set, including sparse signed tags. The result preserves those bits without an
extra premise. Default/C repr, payloads, layouts without an initialized direct tag, reverse
integer-to-enum reconstruction and mismatched primitive types remain UNKNOWN. PAC methods execute their actual MIR.

The public `TrustedStorageEffect::PreserveExistingOrdinaryStorage` can be selected through
`FunctionContract.storage_effect` on an exact trusted boundary with a reason and no modifies/alias
return declaration. It explicitly promises no mutation, publication or retirement of pre-existing
ordinary tracked storage. Compiler types and raw symbolic boundary inputs must certify bounded
pure owned values before snapshots; pointer/reference/interior mutable and opaque inputs remain
unsupported. Constructed fieldless enum inventories admit at most 1024 variants; payload
inventories stay bounded at 256 and complete symbolic inventories consume the 512-value budget.
Ordinary root-input and transmute limits stay unchanged. Existing dead storage stays dead, while
static views, startup values and atomic precision are invalidated. Every used effect records its exact versioned selector/reason premise.
This provides an opt-in frame boundary for future external state models without inferring privacy
from call arguments. Legacy unknown effects stay conservative; native replay refuses this mode.

`TrustedStorageEffect::PreserveExistingOrdinaryStorageAndStaticValidity` additionally promises
preservation of already-live Rust static allocations, initialized declared-type validity and
existing modeled static borrow/access rights. A dead static epoch cannot be restored. Retired
subobjects and uninitialized `MaybeUninit` payloads stay unavailable, and static/startup values and
all atomic precision are still invalidated. The distinct effect premise is recorded only on use;
configured or recorded effects refuse native replay.

Raw constants backed by an exact nonforeign Rust static retain address provenance only when their
whole pointee and original declared storage type match at offset zero. Numeric and anonymous
allocation constants acquire no static rights. Raw mutability grants writes only for a mutable
static; immutable interior access still requires the existing certified `UnsafeCell` operations.
Initialized elements of mutable `[u8; N]` statics, with `N <= 128`, admit arbitrary byte reads
through exact typed bounded projections. This recovers neither zero initializers nor write history after
an external effect. Counterexamples using arbitrary reads retain their abstraction reasons.

Exact mutable Rust static `[u8; N]` references, with `N <= 128`, can unsize to mutable byte slices.
The retained slice records its parent allocation, typed extent, epoch and mutability; the actual
core `get_mut` body returns the same uniquely selected element or `None` for an out-of-bounds index.
Parent lifetime and initialization are checked even for empty slices, `None` and escaping views.
Ambiguous symbolic element addresses and mutable static iterators remain UNKNOWN. Shared reborrows
and iterators narrow both parent and element permissions, and shared copies cannot expose an owned
mutable static handle. Reads after opaque effects still admit arbitrary valid bytes; neither zero
initializers nor precise write history are restored. Overflow counterexamples retain that
abstraction reason. This adds bounded access support without a general alias or concurrency theorem.

The actual portable-atomic shared `AtomicBool::as_atomic_u8` method can retain a live static
address as its core-backed byte-atomic wrapper. This separate certificate checks the concrete
inherent method signature, bounded pure-cast MIR, declared typed origin, and exact one-byte
`UnsafeCell<u8>`/core `Atomic<u8>` layouts, including the compiler alignment wrapper and marker.
It grants no initialization, values, mutable rights or general reinterpretation capability.
Actual Boolean conversions and CAS bodies execute normally; opaque reads retain the unrestricted
byte abstraction and its reasons. A byte counterexample is not evidence of a reachable logical
Boolean state. Native already-used cell controls are separate from those abstract assignments.
Core Boolean CAS, numeric or foreign origins, other backends, changed method bodies and the
`MaybeUninit<[u8; 256]>` write frontier remain unsupported.

Uninitialized stores retain the original certified `UnsafeCell` raw capability. A shared
`&MaybeUninit<T>` reborrow with a `Freeze` payload makes its `as_ptr` address read-only; converting
that pointer to mutable cannot restore write permission. Stores through that path remain UNKNOWN.
A payload containing an actual compiler-certified `UnsafeCell` can obtain interior write rights
through its exact raw access operation, without pretending its uninitialized payload is readable.
Uninitialized payload reference validity, including `&UnsafeCell<T>` before its payload is
initialized, remains unsupported; exact raw access requires no such reference. Native mutation
controls execute only the valid original raw-pointer store path.

UNKNOWN obligations optionally record `unknown_category`: `semantics`,
`missing_compiler_evidence`, `solver`, `resource_limit`, `external_environment`, or
`unclassified`. These are diagnostic causes, never assumptions or proof outcomes. Explicit
producer tags currently cover solver decisions, query/step/depth/time budgets, retained-body
absence, uninitialized static payload-reference refusal, incoming function-pointer/trait-object
and non-byte slice frontiers, finite slice snapshot ambiguity/budgets, and Cortex-M event/wait
instructions.
Other propagated string errors remain `unclassified`; the transitional reporter does not infer
causes from keywords. PROVED and REFUTED obligations omit the field. Legacy reports lacking it
still deserialize; regenerated coverage treats missing categories as `unclassified` and groups
gaps by category and exact reason, preserving all root names. Saved coverage gaps also accept an
absent optional category. Existing schema version and safety statuses are unchanged.

The Rust capability baseline is independent of fleet and hardware contracts. Run
`cargo test --locked -p miren --test rust_capabilities`; its shared manifest selects 67 cases across
24 families on host/ARM at O0/O2, with positive/refuted/unknown and actual source-mutation controls.
The standalone [survey](../../tools/rust_capability_survey.py) retains full reports and provenance.
The typed SMT foundation supports explicit universal and existential Symbol bindings. Free-symbol
metadata is lexical: the same Symbol may be bound in one term and free in another, and nested
bindings may shadow it. Binder-dependent expressions stay inside their scope during shared-term
printing. Queries declare and request models only for free symbols, retain floating-point metadata,
and keep existing byte and solver budgets. Ground shortcuts and Horn clauses refuse quantified
terms. This foundation admits no additional Rust consumers, input assumptions or storage rights.

See [the Rust roadmap](../../docs/rust-capabilities.md) for scope and intended model boundaries.
Portable-atomic/static-cell integration fixtures use pristine versioned sources under
`tests/vendor`, with upstream licenses and a checked provenance manifest. They remain analyzed
inputs outside the host workspace, not trusted summaries or a replacement for Rust semantics.

Compiler-identified `cttz_nonzero` executes exact trailing-zero counting for primitive integers
only when existing path conditions prove its operand nonzero. A feasible zero operand or an
unfinished nonzero proof remains UNKNOWN; the model adds no nonzero premise. Safe
`NonZero::trailing_zeros` follows its actual core body, preserving primitive width, signedness
and the exact `u32` count. Local lookalike functions execute their bodies rather than this model.

Fixed arrays support bounded symbolic selection of pure tuple and fixed-array values, including
nested bool, integer, float, char and unit fields. Tuple arities and array lengths must match
exactly; tuple and array carriers remain distinct. Every field follows the same index, preserving
correlations after existing bounds proofs. Selection validates exact leaf shapes, widths, sorts and
term contexts, with a 16-level and 512-node budget. Retained references, identity-bearing values,
ADTs and symbolic composite writes remain outside this capability. Existing incoming shared-
reference snapshots may already contain primitive values; selecting those values restores no
reference identity, liveness or access rights. Float selection preserves raw bits only when every
candidate has a certificate, including exact signed-zero and NaN storage bits. Byte-array snapshots
and views remain outside conditional aggregate selection; their metadata does not certify an owned
fixed-array carrier.

The same value-selection domain handles bounded tuple reads through checked finite slice
snapshots. A symbolic offset can select correlated values after the region is proved in bounds.
Symbolic composite writes still require a uniquely determined location and report a Semantics
UNKNOWN otherwise; read support does not grant additional write or reference rights.

The conditional aggregate domain does not replace existing unique-index or singleton selection
of retained handles. Those paths keep their prior behavior; only pure values obtain new
conditional field selections.

Compiler-certified core `MaybeUninit` construction records a valid wrapper separately from its
payload's initialization. The bounded owned value domain covers `Copy + Freeze` primitive bool,
integer, float, unit and tuple payloads without destructors. Actual core bodies and the compiler
inhabitance guard execute before exact retained payload extraction. An uninitialized nonempty
payload remains UNKNOWN; only compiler-certified unit-only zero-byte tuples have a unique value
without initialized bytes. Restricted scalar patterns are rejected before normalization. Wrapper
copies and whole assignments preserve branch-local typed values and available float bits; aggregate
padding is not exposed as initialized bytes. Arbitrary incoming wrappers, reference or pointer
payloads, raw partial writes, zeroed raw writes and reference-returning APIs remain unsupported.
This value state grants no allocation identity, liveness or raw-access rights.

The owned `MaybeUninit` value domain also covers exact constant-length arrays of its supported
primitive and tuple leaves, including nested arrays. Counts are bounded at 128 and expanded shapes
retain the existing 256-node and 16-level budgets. Each element type is certified even for empty
arrays. Initialized byte arrays require exact target-width length and array-sort metadata; other
arrays retain exact typed elements and available float bits. Closed unique zero-byte arrays use
only their exact empty or unit-only values. Whole copies and assignments preserve payload state.
Partial initialization, raw/reference access, wrapper repeats and `array_assume_init` remain
UNKNOWN.

Character values keep their unsigned 32-bit representation, with the compiler's Unicode scalar
validity checked against the existing path before scalar formation, assignment, use, return, or
retained typed storage. Actual core `char::from_u32` and guarded `from_u32_unchecked` bodies execute
through their checked integer transmute. Valid integer, float-bit, and existing numeric pointer
representations remain supported; a surrogate, out-of-range encoding, or unproved encoding is
`UNKNOWN` rather than silently restricting the path. Existing refined integer/character targets
also require their original compiler scalar pattern, without erasing that metadata. Fresh reads
of already certified initialized character statics encode arbitrary observations into the Unicode
scalar domain, covering every valid character without restoring an initializer, history, or access
rights. Raw access to uninitialized storage remains outside this capability.


Owned `MaybeUninit` payloads now include exact compiler `char` types, retaining their original
Unicode scalar bits. Constructors, copied wrappers, helpers, tuples, and bounded whole arrays
validate initialized characters under the current path conditions through the existing exact
union/type certificate. These checks add no assumptions and never map or repair stored payloads.
Actual core construction, extraction, and inhabitance guards execute. Uninitialized nonempty
character payloads remain `UNKNOWN`; `[char; 0]` can produce its unique empty value. Restricted
scalar patterns, raw/reference payloads, partial initialization, and all existing budgets keep
their earlier boundaries.

Ordinary Rust binary32/binary64 `%` now uses exact truncating remainder semantics. The typed SMT
operation retains IEEE nearest-even remainder, then corrects a nonzero residual with the opposite
sign by adding the dividend-signed absolute divisor. The finite corrected residual is exactly
representable in the original binary format; no rounded quotient is constructed. Strict ordered
comparisons preserve dividend-signed zero and the existing NaN/infinity/zero-divisor behavior.
Arithmetic results retain no raw-bit certificate, so NaN payload choices keep the existing storage
abstraction. Exact format, sort, and context checks remain mandatory, and ordinary solver budgets
and missing-body refusals still apply. Equality between actual floating bit conversions and a finite
nonzero constant can use exact bit equality; its unique encoding justifies the rewrite without a
path premise. Comparisons against zero, infinity, and NaN retain their floating semantics.
Fast/algebraic remainder intrinsics are not included.

A single incoming immutable slice of exact primitive Bool, integer, f32/f64 or Char elements can
retain caller-owned storage under the existing immutable root certificate. Its arbitrary length
is bounded by the target's valid allocation extent, without a finite element-count cap. Checked
indexing, metadata and exact core Range/RangeTo/RangeFrom/RangeFull indexing preserve that source
and compose element projections; copied handles do not renew dead storage. Primitive values use
logical SMT arrays, with floating storage bits preserved. Char observations encode every valid
Unicode scalar; their unrestricted seed is not physical storage or a native Char witness. Exact
compiler element identities, layout, array sorts and contexts are checked at typed boundaries.
Competing borrowed roots, mutable slices, refined elements, raw access and unbounded
iteration retain their existing unsupported frontiers. Byte slice
representations and their input policy remain unchanged.

Read-only scalar and certified pure tuple/array slices support exact core shared iterator cursors
with arbitrary valid lengths.
Forward/reverse skips, exhaustion, length/count/size hints and cloning preserve the retained
immutable source and validate its lifetime even for metadata or exhausted cursors. Selected ordinary
core APIs require their available concrete Rust bodies before modeled success. Cursor bounds
use checked target-usize terms and the original compiler element identity; no raw access or mutable
iterator rights are added. Floating reads retain storage bits and Char reads decode valid scalars.
Whole-slice callbacks still require complete execution or a separate loop proof; step exhaustion
returns ResourceLimit UNKNOWN rather than narrowing the admitted input length.

Supported read-only primitive scalar-slice membership and equality cover every valid input
length with scoped logical predicates. Membership uses an existential guarded index; equal-length
slice equality uses universal guarded numeric comparisons. Descriptor, source, original element
type, allocation extent and available compiler body checks precede even empty or mismatching-length
returns. Floating NaN and signed-zero behavior and decoded Char equality are preserved. Logical
selection creates no borrow, alias roots, assumptions or raw access rights. Byte, finite-counterpart
and custom comparisons retain their existing comparison work bounds. Custom finite comparisons
execute actual `PartialEq` bodies and retain their effects. Solver limits, unresolved results and
budget exhaustion in iterative consumers remain explicit `UNKNOWN`.

Single incoming immutable Rust borrows also support arbitrary-length slices of exact pure tuple,
fixed-array and local plain-struct elements. A compiler type descriptor preserves each expanded
primitive field occurrence in its own logical array; checked indexing reconstructs all fields with
the same index. Nested Float fields retain storage bits and Char fields decode valid Unicode
values. Reads, owned copies, caller-backed field borrows and checked range views retain the
original allocation and projections. Runtime length has only the valid Rust allocation-size bound;
type shapes retain the existing depth and node budgets and a 128-element fixed-array shape limit.
Exact pure zero-sized tuple/array elements retain the full target-usize length domain and
reconstruct only their unique values; original element types are certified even beneath empty
arrays. Their source lifetime and iterator bounds remain checked. Refined or identity-bearing
leaves, mutable/competing roots and raw access remain unsupported. Logical field storage gives no
padding-byte or physical representation rights. Whole composite membership and equality remain
explicit semantic `UNKNOWN` boundaries. The exact safe core `size_of_val` API uses retained
composite length and the compiler's complete element size, including padding. Pure zero-sized
elements have byte size zero at every valid target-usize length. Source lifetime, original element
type, extent and the selected API body remain certified before size results. The exact safe core
`align_of_val` API also returns the compiler element ABI alignment for certified readonly scalar
and composite slices, including empty and zero-sized views, after the same type, extent, source
lifetime and selected-body checks. Raw dynamic layout APIs, deprecated aliases and trait-object
metadata receive no new support. The exact safe core `align_of_val` API additionally supports
sized primitive and certified pure owned products, including nominal aligned zero-sized structs.
It validates the original shared receiver graph, live projections, exact original pointee and
complete typed carrier before requiring the selected API body and returning compiler ABI
alignment. Closed deferred zero-observable products retain their nominal metadata. Scalar deferred
products can additionally use actual Engine-issued root reservations: exact original pure root type,
immutable descriptor identity, seed and descendant offsets certify existing symbols before
bounded preparation. Copies preserve their correlations; separate roots and array occurrences
retain distinct reservations. Unregistered scalar descriptors remain unsupported. Enum-origin
and newly encoded Char descriptors receive no support. This gives no raw/static decoding or padding
access rights. Existing sized `size_of_val` and raw sized size behavior remains unchanged.
Readonly shared iteration retains the same compiler type, source
graph and original caller allocation.

Ordinary local and dependency struct slice elements retain the exact original compiler type and
complete declaration-ordered field identities and compiler layout. Zero-sized ordinary structs
remain nominal ADT values after
complete recursive field certification and an empty primitive-storage inventory check. Their
readonly slice lengths span the full target-usize domain; no physical address rights follow.
Unit, tuple and empty-array fields remain supported. Recursive field certification rejects
restricted patterns before normalization, including beneath empty arrays. Packed/SIMD layouts,
core or compiler-special dependency ADTs, enums, unions, reference/raw fields, interior mutation
and destructor-bearing types remain unsupported. Compiler scalar validity must match the actual
typed fields and offsets. Observations reconstruct exact struct metadata with every field selected
at the same index; owned copies and caller-backed field borrows add no raw, write or padding-byte
rights. Custom methods, Clone and
PartialEq receive no purity inference from Copy; whole composite comparison remains unsupported.

Dependency structs use the same original-field, layout and type-budget certificates as local
structs. The actual compiler core-crate identity and special ADT flags exclude builtin ownership,
pinning and wrapper policies; missing core identity evidence refuses new dependency admission.
Field privacy and constructors add no input invariant. Available ordinary dependency methods
execute their actual MIR, and unavailable bodies remain UNKNOWN.

Actual MIR assignments can update one complete element or a compiler-identified tuple/struct
field or fixed nested-array subtree of a direct owned finite array at a symbolic, checked index.
Primitive, pure tuple/fixed-array and eligible ordinary struct elements use exact original
compiler types and complete candidate/replacement validation. All fields of
one candidate share the same conditional update; other elements retain their prior values.
Field updates preserve exact untouched leaf terms and rebuild the complete nominal element.
The original compiler field types and declaration order certify each logical field span; no
physical offset or padding rights follow.
Owned byte-array elements keep their exact u8/count certificate. Writes to existing owner
allocations validate live writable storage and commit to that same allocation. These updates
preserve the existing 512-node/depth-16 budgets, Char validity and Float bit certificates.
Fixed nested-array paths require literal target-usize values or start-relative compiler constant
indices, exact original fixed-array types and checked bounds. Exact u8 arrays retain their byte
annotation when selecting one byte. One symbolic nested fixed-array index can update certified,
disjoint logical child spans using the joint outer/inner index condition. Every complete old
candidate is flattened once, and replacement fields share one condition at each target; untouched
leaf terms and Float bit certificates survive the complete nominal rebuild. Both index bounds and
exact homogeneous child types are certified before the same owned-storage transaction. A second
symbolic nested index, reference/raw/static destinations, dereferences, downcasts and call
destinations retain their existing unsupported frontiers. Known outer-index stores retain their
existing paths. After the old writer returns an exact unsupported nonunique-index frontier,
a known literal or path-entailed outer index can use the same certified symbolic-inner update.
This fallback validates the complete original parent and every candidate before committing to the
same owner allocation. Untouched rows retain their exact values; only the proven outer row receives
jointly correlated inner updates. Existing successful byte stores and their queries run first and
remain unchanged. The rvalue and destination validity checks execute once. Missing bodies,
permission failures and solver/resource errors cannot trigger this fallback. Reference/raw/static
and call destinations gain no support.
Owned tuple and ordinary-struct roots can also update an array reached through leading compiler
field projections. This uses the same exact unsupported-boundary fallback after the old writer.
The complete original root and replacement share one validation budget; original field types
resolve disjoint logical target spans. One symbolic index controls all leaves in each selected
subtree, and untouched sibling terms survive the complete nominal rebuild and same-owner commit.
Existing successful field and byte writes retain their earlier paths and queries. This adds no
symbolic second index, dereference, retained-reference, raw, static or call-destination writes.
Assignment targets retain complete parent and replacement validation, including siblings and
zero-leaf fields. Deferred input products with no observable scalar leaves can be reconstructed
after exact original-type and descriptor validation. Nominal zero-sized structs
retain their names and fields; tuple/array children retain their exact shapes. Descriptor kinds,
counts, ordered field identities, slot/height metadata, seeds and checked ranges are validated
before expansion. Expanded occurrences share the existing candidate budget. Closed-zero
reconstruction emits no symbols and adds no assumptions. Registered pure scalar products observe
only their existing reserved symbols after exact root/path and descriptor certification;
unregistered products remain unsupported. Constant and uniquely determined stores keep their
prior behavior.

Actual MIR Copy/Move reads can select a finite ordinary-struct array at a symbolic checked index.
Pure tuple and fixed-array candidates containing deferred inputs use that same typed path.
Scalar-bearing descriptors require actual issued root and descendant reservation certificates;
closed-zero products retain their existing symbol-free schema certificate. A bounded eligibility
search observes no values. Each deferred descriptor is certified before its symbols are observed.
Every candidate is validated before shared-index selection. Unregistered scalar-bearing products
and primitive-only deferred choices remain unsupported. Existing eager scalar/aggregate, constant
and uniquely determined reads
retain their earlier selection paths and queries.
The original compiler array-prefix type certifies every candidate's exact nominal fields and
primitive metadata before a shared-index value merge. Float storage bits survive only when all
alternatives carry them; Char leaves require validity under the current conditions. Existing
constant, singleton and solver-unique handle reads retain their prior behavior. Untyped retained
reference projection chains and ambiguous writes gain no support; this owned-value operation
adds no reference, raw address, method-purity or constructor-invariant assumptions.
An original compiler `u8` array annotation also permits finite owned byte-array alternatives,
including empty arrays. Exact Elements and Bytes carriers share the same checked byte domain;
length, target-usize sorts and analysis context must agree with the original fixed array.
Every byte counts toward the existing candidate budget. Selected arrays rebuild canonical owned
byte values, while incoming composite observations and generic byte-slice selection remain
unchanged. Untyped views cannot supply this original compiler array certificate.

Shared borrows of direct owned arrays can retain compiler-certified symbolic index projections.
The actual MIR array-prefix type supplies an immutable type certificate; the reference retains the
same owner allocation and index, rather than a detached value snapshot. Each later read validates
live current storage, the complete original pure array, all candidate metadata and the index bounds.
Scalar-bearing deferred products retain their issued reservation requirements. Copying the borrow
preserves source identity and observes later owner updates. Ordinary calls and comparison bodies
retain their existing execution and body-availability rules. These projections cannot grant mutable
access or raw addresses, and frame-owned borrows cannot escape through returns or closure captures.
Owned tuple and ordinary-struct field prefixes can use the same retained projection. Its immutable
certificate records the complete original root type and declaration-ordered field path. Every
observation certifies and prepares the live complete root before materializing any leading field;
array inventory, index bounds and exact scalar metadata remain checked. The reference keeps the
same owner allocation, rather than a detached selected copy. Empty-prefix array certificates keep
the earlier reader and query construction. Field-prefix certificates supply no mutable, raw-address
or frame-escape permission, and unsupported siblings remain unsupported even when the target field
is pure.
Existing eager, constant and uniquely determined borrows keep their prior paths. Raw, static,
reference-source and mutable destinations gain no new borrow support.

Concrete synchronous closures can carry supported read-only scalar slices and initialized pure
`MaybeUninit` values through their exact compiler capture types. Shared capture metadata checks
validate the closure identity, kind, numbered fields and original capture types; each payload
retains its own validity and reference policy. Captured mutable handles keep their declared rights,
and returning a closure cannot convert frame-owned captured borrows into owned snapshots. Ordinary
closure bodies and compiler-generated Fn-to-FnOnce and FnMut-to-FnOnce adapters execute actual MIR,
including their receiver borrows and drops. This adds no mutable slice, raw access, asynchronous
closure or unbounded loop proof permission.
