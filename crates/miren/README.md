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

## Mutable backing representation

Mutable slice owners distinguish scalar storage from typed product leaf columns in one owner and
role namespace. Pure tuple, bounded array and plain local struct elements retain exact compiler
Copy/Freeze/layout facts, target-usize extent and current initialized Memory. Direct root metadata,
guarded whole-element operations and constant field/array suffix observations and writes use
logical primitive columns. Floating leaves preserve f32/f64 raw bits, including NaN payloads and
signed zero; stores require exact producer pairs and valid Char leaves before updating columns.
Other columns, indices and branches retain their original storage.

Representation conversions issue no certificate, allocation or lease. The owner marker occupies
one allocation; the backing slot covers the scalar/first product column, and further columns add
storage slots within the existing backing accounting pass. Columns create no new allocation ids,
addresses or physical access rights. Existing scalar counts and Armed fee expressions are retained.

Whole mutable product helper calls reuse issued whole staging, one child generation and actual
available Body/frame checks. Primitive helper arguments and returns, direct child metadata and
constant-suffix stores retain current returned storage. Pending tips grant no observation; old
metadata and Root are suspended while a child is active. Caller release requires the complete
current frame/grant/returned-memory checks. Representation validation alone grants no access.

Nested owner child calls, proper intervals, symbolic suffix indices, Armed access, Ghost/contract
snapshots, replay of arbitrary original payloads, and sum/niche/pointer/reference products remain
unsupported. Unbound entry diagnostics record a live owner id; they never expose current payload
as frozen original inputs. Copied primitive/product values may enter actual available helpers.
Dedicated four-profile positive, negative and unknown controls pass. Actual helper/store changes
refute unchanged caller claims; native originals pass and mutants fail at O0/O2. Missing dependency
bodies remain UNKNOWN. The compiler probe includes original-type, Context, initialization, extent,
atomic Char/Float and actual fake-pointer metadata controls.

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

Readonly slices also admit bounded pure ordinary local enum shapes with compiler-certified direct
initialized tag encoding, and exact direct-tag `Option<u16>`. Original variant inventories, sparse
or signed discriminants, payload field identities, ABI ranges/offsets, Copy/Freeze/NoDrop and
all original child types are checked, including inactive and zero-length payloads. A total legal
tag decoder and independent per-variant payload columns retain each selected logical occurrence;
inactive payload columns confer no initialized bytes or raw rights. Checked indexing, matches,
readonly views, cursors and safe layout APIs preserve the retained source and actual body gates.
Exact `Option<bool>` and ordinary local two-variant empty/Bool enums also admit the compiler's
one-byte niche layout. Its initialized ABI must cover exactly false, true and the reserved empty
tag; the original Bool payload and overlapping variant layouts are checked independently. Logical
variant selection preserves active Bool values without initializing the empty variant's latent
payload. NonZero, reference and multi-alternative niches, other core wrappers and whole sum
comparison summaries remain UNKNOWN. Mutable/raw/static access policies and
owned product choice/write admission are unchanged.

Exact `Option<char>` and ordinary local empty/sole-Char enums also admit their checked I32 niche
layout. The initialized wrapping ABI reserves exactly `0xffffffff` for the empty variant, while
the original Char field keeps its compiler range. Logical active Char observations cover every
Unicode scalar and exclude surrogates; the ABI interval alone is never a Unicode validity proof.
Empty values do not initialize their latent Char field. Original type, source lifetime, extent,
layout and body gates apply before metadata, indexing or cursor success. Raw access, other niche
families, owned enum choices/writes and whole sum comparison summaries remain unchanged.

Direct-tag sums also admit ordinary local nominal struct payloads, including nested structs,
fixed arrays and zero-sized members. The original instantiated fields, declared identities,
Copy/Freeze/NoDrop, alignment, scalar validity and complete type budgets are certified before
recording any descriptor. Nominal payload observations keep exact struct carriers and independent
same-index columns; inactive variants supply no initialized object bytes. External nominal
payloads, unsupported ABI compositions and Bool-newtype niches remain UNKNOWN. Getters and other
methods execute their actual Rust bodies. Whole sum comparators and owned enum writes/choices,
mutable/static/raw source rights and all existing budgets remain unchanged.

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
Arbitrary trait-object roots, uncertified upcasts and raw/boxed trait objects remain UNKNOWN.

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

Symbolic indexing into initialized owned arrays of known safe Rust `fn(A) -> R` pointers
supports independently chosen primitive signed, unsigned and pointer-sized integer arguments and
results. Both original compiler types retain their own width and sign certificates, even when two
types have the same SMT sort. Selection preserves the index-to-target relation and executes each
feasible target's actual MIR body, including generic and associated functions. Actual casts and
checked arithmetic retain their own semantics and overflow obligations. Fixed owned fields,
duplicate targets and repeated calls retain the existing sixteen array-element and shared analysis
budgets. Calls consume operands once, validate actual returned integers against the original result
type and carry their current returned memory. Missing feasible bodies, opaque targets, shared input
tables, Bool/Char/Float/NonZero, unsupported ABIs and arities remain UNKNOWN. Infeasible targets are
pruned only after solver checking.

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
padding-byte or physical representation rights. Full-length membership and equality support exact
pure tuple/array elements with primitive or unit leaves. Scoped predicates observe all fields at
the same index and use numeric Float equality and decoded Char values. Admission checks complete
pinned compiler MIR reference bodies, actual core identities and selected comparator, specialization
and callback instances. Available reachable bodies remain required; unsigned cursor proofs exclude
only the exact overflow panic edges. Source validity and extent checks precede binders, empty
results and length mismatch. Nominal struct comparison, mixed composite/finite equality and
one-byte bytewise membership transport remain semantic `UNKNOWN` boundaries. The exact safe core
`size_of_val` API uses retained
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
rights. Custom methods, Clone and PartialEq receive no purity inference from Copy; whole nominal
struct slice comparison remains unsupported.

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
destinations gain no support through this assignment fallback.
Owned tuple and ordinary-struct roots can also update an array reached through leading compiler
field projections. This uses the same exact unsupported-boundary fallback after the old writer.
The complete original root and replacement share one validation budget; original field types
resolve disjoint logical target spans. One symbolic index controls all leaves in each selected
subtree, and untouched sibling terms survive the complete nominal rebuild and same-owner commit.
Existing successful field and byte writes retain their earlier paths and queries. This adds no
symbolic second index, dereference, retained-reference, raw or static writes.
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

Function results can be stored into direct pure owned array, tuple and ordinary-struct paths with
symbolic indices. Rust evaluates these destination indices before the callee executes. An
immutable certificate records their values and the caller owner identity; no caller locals are
overwritten to simulate this timing. Original field types, fixed indices, complete root metadata,
pre-call bounds and current write rights are checked before execution. Each returned continuation
uses those captured indices with the current complete owner and exact replacement validation.
The existing writer runs first; only its precise unsupported-index frontier can invoke the
existing typed transaction. Callee effects run once, untouched fields retain the returned state,
and unsupported siblings remain unsupported even when empty. No-return calls still execute their
actual bodies for certified destinations. Whole-local result stores retain their existing policy.

A leading dereference through an unprojected tracked mutable reference to a complete pure owner
can also capture its original allocation and typed field/index path before the callee. Redirecting
the reference inside the callee does not redirect the returned value. Storage validates the
captured allocation's current live contents and exact replacement before a single commit, keeping
sibling effects. Shared, raw, static and inherited reference projections remain unsupported;
compiler type evidence does not grant new access rights. Symbolic writes retain the existing
writer's bounds and uniqueness requirements.

Concrete witnessed reference trait-object upcasts authenticate both compiler Unsize obligations
and the actual supertrait vtable transport. A compiler-selected TraitVPtr must identify the exact
target with the same concrete type; reused vtables must contain the exact target prefix. The
original allocation, projections and access rights are retained or narrowed. Target methods still
resolve to their exact compiler vtable Item and execute actual available MIR. This includes
associated-type bounds, chained and second-supertrait upcasts and existing mutable receiver
rights; it supplies no arbitrary trait-object input, physical vtable or raw pointer capability.
Missing method bodies and dead or escaping backing storage remain UNKNOWN.

Ownership consumption has a bounded initialized-place ledger carried with memory across calls and
branches. Actual operands consume owned locals and exact active fields in evaluation order; later
loads or borrows of those places remain UNKNOWN until an exact write repairs them. Sibling places
and allocation identity survive, and moving a reference handle does not consume its target.
Assignment Move handling is a conservative compiler initialization boundary: the pinned compiler
leaves its physical deinitialization effect unsettled. Drop consumes storage only after an actual
normal destructor return; compiler-elaborated drops of types without drop glue remain no-ops.
An authenticated retained enum tag remains observable after exact payload consumption, including
niche-encoded enums. This logical tag observation preserves payload masks; whole or ancestor
consumption, payload loads and malformed nominal metadata remain UNKNOWN.

Compiler coroutine state and original saved-field mappings govern active storage independently of
retained historical payloads. State updates preserve initialization masks. Exact tracked coroutine,
Pin, and compiler PinMacroHelper observations validate active fields and preserve source rights;
ordinary partial aggregates receive no exemption. Ghost snapshots detach active values and scrub
consumed inactive fields to unavailable markers, so pre-state bindings cannot observe later writes.
Typed reference returns retain their original caller-owned allocation and validate active reference
edges. Whole future or owned helper moves and returns with initialization holes remain UNKNOWN.

Calls capture their destination before the function operand and ordered arguments. Definite or
unresolved same-storage Move input overlap with a call's return place remains UNKNOWN under the
pinned compiler's unresolved alias contract; ordinary Rust reassignment through distinct return
temporaries remains supported. Induction can omit an unaddressed private temporary's consumed
footprint only after an exact bounded scan proves no observation before a covering assignment.
Arguments, return storage and addressed memory remain strict at inductive continuations; storage
markers do not repair masks. A terminal return can preserve consumed, unaddressed by-value argument
masks for an exact reference-free, Freeze, no-drop primitive or plain local product type. It
validates
the returned value and never encodes the consumed callee locals into a successor state. Entry ghosts
remain immutable, while current post-state argument observations still require initialization.

Full-domain read-only slice membership and equality can certify an ordinary struct's actual
selected `PartialEq` body before constructing structural numeric comparisons. The complete
original type must be pure, Copy, Freeze and have no drop glue. Exact shared receiver origins,
recorded field types, branch-local initialization and Move consumption, every reachable effect,
selected child comparers and the full Boolean result are checked. A bounded Boolean DAG must equal
the conjunction of every corresponding primitive field; derive markers and method names grant
nothing. Nested ordinary structs and tuples reuse exact certificates, and the actual default `ne`
body is checked separately. Nominal CFG work and existing core-template work have separate bounded
counters. Certificates are rechecked against the selected instantiated MIR without a cache.

The slice source and comparator certificate are checked before empty or unequal-length shortcuts.
Float fields retain numeric NaN and signed-zero semantics; Char observations retain their existing
Unicode validation. Struct carriers must match exact nominal identity, field order and primitive
width, signedness, sort and context. Ineligible array-field comparers, aggregate-to-integer casts
and effects outside the certificate grammar remain UNKNOWN. Actual invoked
missing helpers remain UNKNOWN; their diagnostic does not stand in for a missing comparator body.
Existing finite custom-comparison calls still execute their actual bodies. The certificate supplies
no new borrow, write, raw-pointer or allocation rights and imposes no input slice length cap.

Ordinary external nominal slice comparers use the same complete original-type certificate as
local comparers. The selected safe Rust `PartialEq` body must be available and compute all
corresponding field equalities without unsupported effects. External crate identity, exported
symbols, derive markers and field visibility do not replace this proof. Missing selected MIR
remains unknown before empty, unequal-length or zero-field shortcuts. Separate identical-source
retained/omitted dependency builds exercise this boundary; existing array casts, special types
and nonstructural comparers remain unsupported.

Exact `Box<(), Global>` construction now uses a complete compiler-backed semantic certificate for
selected Box, Global and drop bodies. The certificate matches every executable MIR byte, checks
actual core/alloc identities and original signatures, and derives the zero-size, alignment-one
branches and their unreachable allocator/panic edges. Reported models distinguish this certificate
from the actual user helper bodies that execute. Nominal payloads require the separate complete
original-type certificate described below.

The resulting logical owned region has a distinct lifecycle from frame allocations and numeric
addresses. Move transport preserves its identity; ordinary executable owner copies are refused.
The selected `mem::drop` lowering may copy its single authenticated owner before retiring the same
region. Automatic drop uses the selected drop-glue certificate. Readonly Unit borrows remain tied to
that live region, and returned owners must account for every live region created or received by
value. Detached contract snapshots confer no executable ownership or access rights. Constructors,
owner transfer and drop retain the existing initialization masks and combined storage budget.

Mutable borrows, raw/address exposure, pointer equality, arbitrary incoming Box handles, allocator
failure paths, custom allocators, `leak` and `forget` are not admitted by this certificate. A
readonly compiler-generated Box temporary cannot acquire mutable authority, move, escape as an
owner, or become caller-owned storage. Duplicate drops and shared borrows escaping a retired
region remain UNKNOWN. No allocation-success premise or raw-memory grant follows from a zero-sized
payload.

Nominal comparison certificates expand fixed integer-array fields into distinct typed field and
array-element paths. Whole-array child calls must pass their actual selected core comparator
certificate before supplying a conjunction or excluding cleanup. Every occurrence is charged
against the existing expanded type budget, including vacant arrays and their original children.
Nested signed/unsigned integer arrays retain the existing count128, depth16 and node512 bounds.
Nominal MIR indexing, casts, loops and raw transports remain unsupported. The initial integer-
array increment excluded Float, Bool and Char array children. Scalar Float and Char siblings keep
numeric equality and decoded observation semantics. Missing bodies and unsupported original N0
children remain unknown before empty or zero-field shortcuts.

Nominal whole-array child comparers also admit exact Bool, Char, f32 and f64 leaves through
recursive fixed arrays. The complete selected core body, original type, layout and effect
certificate remains mandatory before any conjunction or empty shortcut. Numeric Float equality
preserves NaN inequality and signed-zero equality; Float arrays do not acquire bitwise comparison
eligibility. Char leaves reuse validated decoded Unicode observations. Every original child,
including a vacant array's child, retains the existing expanded type budgets. This adds no nominal
MIR indexing, cast, raw transport or ownership permission. Genuine missing selected dependency
MIR remains unknown even for empty, unequal-length and zero-leaf slices.

A single original incoming `&mut [u16]` can supply direct element reads and whole-element writes
with other inputs limited to owned primitives. Its private current backing is an SMT array across
the full valid target extent. A write proves bounds, checks the original element type and context,
and changes only the branch's current array. Actual scalar helper calls retain that backing.
Detached prestate snapshots keep old terms; contract length observations never grant executable
access, and ghost element indexing remains unsupported.

Compiler length lowering uses a private metadata-only role. The actual selected core SliceLen
body must be available and return exactly its receiver's pointer metadata. Compiler fake metadata
pointers carry length only. These roles cannot acquire shared data or mutable access, enter
aggregate/caller storage, ordinary borrowed helper calls, raw pointers, or returns. Root handle
Copy/Move outside the child protocol, retained shared views, multiple incoming borrows,
and inductive backing transport remain UNKNOWN. Existing readonly slice,
finite mutable byte storage, ownership initialization and raw permission policies are unchanged.

The private zero-sized Box protocol also accepts exact local ordinary nominal payloads with
compiler size zero, exact ABI alignment, Copy/Freeze/no-drop eligibility and no observable scalar
leaves. Original child types are checked even under zero-length arrays. The immutable payload
certificate retains the original type, nominal field identity and bounded product shape across
construction, readonly access, snapshots, owner transfer and retirement. Region storage charges
the complete original payload node count against the existing shared frame/region budget.

Generic Box/Global constructor and drop bodies retain their complete selected-body certificates.
A separate exhaustive typed synthesized-glue certificate checks every local type, block, effect,
receiver projection and selected delegate for the original nominal payload. Its successful report
labels describe a certified semantic model, without claiming that summarized library bodies were
stepped. User methods and custom Clone/PartialEq bodies execute normally. Unit protocol labels and
completed queries are preserved. Nominal inlined constructor lowering, external payloads and
shared dereference-plus-field borrowing remain unsupported. A copied nested nominal
payload can be read through ordinary owned field projections; this grants no shared field rights.

Tracked raw-local, iterator-find temporary and async-factory storage growth also charge the
existing cumulative budget, including owned region nodes and private mutable backing. Weighted
regions cannot bypass that budget by creating ordinary frame temporaries. The corrected weighted
boundary reports a resource UNKNOWN; raw permissions and the old frame-only refusal remain.

A direct safe Rust function can receive the whole mutable u16 slice for one synchronous child
call and return Unit or an owned primitive. The selected signature and actual compiler body
must be available, with abort-only edges. The caller's root suspends while a branch-private
generation grants the child access to the same current array. Actual Copy at that call and
fixed private mutable reborrow staging carry one grant; generic handle copying remains refused.
Normal child return revokes its generation and resumes the parent with current data, preserving
all source consumption masks. An actual moved parent remains outside this first protocol.

The child may execute ordinary primitive-only functions under an authenticated bounded stack
of actual compiler bodies. Each normal scalar return restores only that ancestor frame; only
the owning child can release the grant. Compiler pointer-metadata Copy observes only length
under original mutable-slice, initialization, generation and current-source checks. Prestate
ghosts remain detached. Nested mutable children, shared views, role-bearing aggregates,
reference returns, stale aliases, unwinding and missing selected bodies remain UNKNOWN.
Private backing, frame entries and ordinary allocations share the existing storage budget.

The zero-sized nominal Box protocol accepts the exact original compiler ABI alignment.
A single immutable zero-layout certificate authenticates constructor Layout fields, target-width
rounding, power-of-two alignment, nonnull zero-branch sentinel and typed drop arithmetic.
The complete selected zero-size Global branch needs no allocator-success premise. Logical
region ownership remains separate from numeric dangling addresses; no raw, mutable or shared
field access is added. Original payload/shape budgets, lifetimes and Unit inline lowering remain.

The same single-root and whole-child protocol also admits original plain signed integer
slices i8/i16/i32/i64/i128/isize and unsigned u32/u64/u128/usize, alongside u16. Each backing
is issued with its exact original compiler element type, width, signedness and ABI layout.
Reads, replacements, staging, selected child signatures and metadata receivers must match
that certificate; equal SMT sorts do not equate i32 with u32 or usize with a fixed-width type.
Detached ghosts retain their immutable codec and frozen data without executable authority.
Current stores preserve exact integer values without truncation, sign conversion or casts.
Reference extents use the actual element byte size and target usize. Existing u16 formulas
and the shared storage/frame budgets remain unchanged. The private internal carrier retains
its historical u16 name; that name adds no rights. u8 keeps its existing byte-model priority;
Bool, Char, Float, refined aliases and additional spatial/temporal lease features remain
outside this integer extension.

Mutable Bool slices share the existing single-root primitive lease protocol. The original Bool
compiler type and size-one/alignment-one layout issue a logical Bool-array certificate; typed
reads and stores accept only same-context Bool values. Whole synchronous children retain their
actual selected bodies and current backing, while detached entry ghosts retain frozen data.
Integer codecs and completed queries remain unchanged. No byte coercion, validity assumption,
shared alias, raw access, subslice loan or mutable return permission follows from this codec.

Mutable Char slice roots use an exact original `char` certificate and compiler size4/alignment4.
Their logical BV32 array reads reuse the valid Unicode observation map. Every typed replacement
must prove Unicode scalar validity under the existing path conditions before the unchanged Store;
invalid replacements are refused rather than repaired or assumed valid. Actual scalar child bodies
may receive and return certified Char values. Detached Char ghosts expose only their exact length.
Integer and Bool formulas, source lifetimes, private leases and storage budgets remain unchanged.

A bounded byte-view copy also accepts a promoted immutable byte constant of at most 128 bytes
into a guarded prefix of one original incoming writable `&mut [u8]`. The original arbitrary
length and current BV8 array remain in the same allocation; sequential SMT Stores replace only
the selected cells. Complete selected core copy, intrinsic and precondition bodies are matched
against pinned MIR, with exact operand forwarding, byte layout and guarded failure edges.
Original constant provenance and current source bytes must agree. A branch-local incoming-origin
record and monotone exposure refusal preserve the valid writable Rust region premise; raw,
unsafe, indirect, trusted and unsupported transport cannot restore this eligibility. Compiler
metadata-only byte length observations return no address capability. The update validates current
liveness, initialization, write permission and every nested prefix before one whole-root commit.
Old fixed-capacity byte paths keep their existing priority and formulas. Shifted ranges, dynamic
or returned sources, zero-length constants without initialized compiler bytes, and optimized
foreign bodies with already inlined raw copy transport remain UNKNOWN in this extension.

The direct incoming mutable primitive slice protocol also admits exact compiler f32 and f64.
Storage keeps their BV32/BV64 encodings, while comparisons and arithmetic retain IEEE numeric
semantics. Stores require an exact producer pair and a proved numeric/storage correspondence
before committing data. Decoded values preserve all bits, including NaN payloads and signed zero.
Arithmetic materialization retains every permitted NaN encoding rather than choosing a canonical
payload. Paired negation, absolute value and clamp selections retain their exact
bit transformations.

Pair metadata is enabled only for the new mutable Float root namespace. Other Float analyses
retain their existing query terms and models. Optional metadata uses the existing 512-node and
16-depth bounds; exhaustion cannot fail an old readonly producer, and a new Store refuses missing
authority. Numeric equality or matching FP/BV sorts alone cannot authenticate a copied NaN.

Actual whole-child and scalar-return bodies use the existing exclusive frame protocol. Float
scalar arguments and results need the same pair checks; unavailable invoked bodies remain UNKNOWN.
Detached ghosts expose length only. Retained element borrows, raw transport, nested mutable
reborrows, competing roots and executable role escape remain unsupported. Unauthenticated
aggregate selection pairs remain UNKNOWN. No floating induction, allocator or alias permission
is added. Native controls use valid finite 129-element slices; arithmetic NaN payload claims
remain subject to the analyzer's existing permitted-encoding overapproximation.

Logical scalar slice codecs and detached mutable ghost lengths share one compiler-free sort map.
The map describes Bool, integer, Char and supported Float storage sorts; it issues no compiler
certificate or access permission. Original caller validation order, diagnostics and codec widths
remain unchanged, including executable ghost-index refusal and unavailable-body boundaries.

A checked `Range<usize>` of one incoming `&mut [u16]` may be handed immediately to one direct
synchronous child. Complete selected core range bodies certify the guarded relation; the caller
proves `start <= end <= original length` and authenticates its current private staging tip.
Both compiler reborrows retain one generation and branch-local interval descriptor. Child indices
are checked against view length and translated into the same current full array. Normal owner
Return removes the descriptor and resumes the parent with current data. Metadata and detached
ghost length use view extent; ghost data indexing stays unsupported. Whole-slice formulas keep
their original terms. Retained views, nested child leases, other range types, split operations,
raw pointers, reference returns, induction and non-u16 interval codecs remain unsupported.

One direct whole-u16 child may synchronously hand the same whole slice to one nested child.
A distinct hierarchy namespace authenticates the original root Call and each current compiler
staging occurrence. The parent remains suspended until the nested owner's normal Return; the
returned current array resumes its ancestor without restoring old memory or consumed handles.
Persistent issuance and observation counters reject old child and metadata handles, including
after the final owner returns. The namespace cache grants no access and stays charged while dormant.
Owned primitive calls in a dormant namespace require their original operand paths, actual selected
body, safe Rust signature and normal continuation. They preserve the same origin and current data.
Metadata requires the current lease and epoch; detached ghosts retain length-only observation.
Explicit root reborrow staging, retained views, deeper nesting, shared child arguments, intervals,
raw pointers, reference returns, induction and noninteger hierarchies remain unsupported. Missing
selected bodies remain UNKNOWN; optimized dependency bodies with unsupported store shapes also
remain UNKNOWN. The test-only scoped issuer switch exercises the same public routing and lifecycle
checks, including ordinary noncandidates and missing-cache refusal.

Readonly slices of `Option<NonZero<u16>>` and ordinary local empty/payload enums may use the
compiler's exact zero-only niche. The original wrapper, associated restricted inner type,
all variants and layouts are certified even under zero-length arrays. One raw column supplies
both the legal tag and latent payload; zero denotes the empty variant and is never repaired
into a standalone NonZero. Copy and Move projections authenticate original local declarations
and raw recorded field types through a bounded linear original projection walk. Whole aggregate
copies do not scan unrelated descendants; later standalone extraction still authenticates the
actual leaf. Unresolved extraction paths refuse, and depth exhaustion remains ResourceLimit.
Standalone operand, helper argument and return admissions require
exact wrapper storage and a nonzero proof under current conditions. The selected core getter
requires an available complete instantiated body matching its exact receiver-to-result
transmute; this is a body certificate, not fabricated executed-body attribution. Its bounded
scan rejects cleanup, spread, tainted and coroutine metadata. Pointer niches, other widths,
mutable niches, whole-slice comparison and the new shape's induction reconstruction remain
unsupported. Existing source, lifetime, single-root and shape-budget restrictions apply.

The whole-slice nested hierarchy also accepts original signed integer types and unsigned integer
types except u8, using their issued type/layout/codec certificate at every staging and call
boundary. Exact original type correlation excludes same-width signed/unsigned and pointer-width
substitutions. The existing single nested child, persistent generations, primitive scalar returns
and cumulative budgets apply. Bool, Char, Float, intervals, retained views and deeper hierarchies
remain outside this extension. Original u16 paths retain their terms and permissions; actual
selected bodies remain required before effects.


Checked proper intervals of incoming mutable `i32` and `usize` slices now use the same bounded
single-child protocol as `u16`. Issuance requires exact original element layout and the complete
selected core wrapper and delegated Range bodies, including the instantiated pointer stride.
The caller must prove `start <= end <= current length`; the child runs its actual available body
against current backing storage. Parent reads and disjoint siblings observe the returned state.
Empty intervals still require selected child compiler evidence. Retained intervals, nested calls,
splits and returned ordinary references receive no additional permission. Integer interval
certification preserves typed missing-body and resource refusals; no allocator or input premise
is added.

Stage 207 admits metadata-only `is_empty` for original issued u16 mutable slice roles. The selected
available core body, exact shared receiver and Boolean signature are certified before evaluating
the current view length. The relation grants no data, alias, retained-reference or split rights;
other primitive elements remain outside this bounded certificate. Existing `len` paths remain
unchanged. Diagnostic host/ARM O0/O2 captures prove root, whole child and proper empty/nonempty
views, refute wrong claims and actual scalar-helper mutations, and retain genuine missing-child
body refusal. Full ROOT validation, release replay and commit remain pending.

The whole-slice nested hierarchy also accepts exact original Bool with its logical Bool codec,
layout1/1 and existing current-memory/epoch/owner checks. Actual nested body and scalar-return
results are checked. Retained library O0 bodies support
selected and empty callers, omitted bodies stay MissingCompilerEvidence UNKNOWN even when empty,
and an optimized retained store may reach the existing unsupported shape frontier. No new raw,
retained-reference, interval or deeper hierarchy permission is granted.

The whole-slice nested hierarchy also accepts exact original Char with its BV32 Char codec and
existing Unicode validity checks at scalar argument, result and store boundaries. Actual public
Call/stage/Return tests preserve current backing data and sibling elements. No validity premise,
value repair or extra lifetime permission is added. Actual helper mutations refute unchanged
claims; wrong claims and out-of-bounds observations refute, while deeper nesting remains UNKNOWN.
Retained O0 Char helpers support selected and empty callers. Omitted bodies remain
MissingCompilerEvidence UNKNOWN even when empty. Optimized retained selected callers currently
reach an unsupported ConstantIndex observation; this is separate from Unicode validity.

Stage209 actual208 upkeep preserved the committed Bool, metadata and interval foundation. The
original actual203 plus pending208 disabled history remains separate. Production changes were
limited
to the reviewed Char selector flag. Full ROOT validation completed before the actual209 commit.

Issued non-u8 integer, Bool and Char backings support metadata-only `is_empty` after the complete
selected core body, original receiver and current type/layout/codec/context checks. Existing u16
metadata behavior and element/alias/return/retained permissions are unchanged. Float and bytes are
excluded from this scalar metadata route. Actual209 disabled and sole-flag checkpoints are kept
separately; full ROOT validation completed before the actual210 scalar-metadata commit.

The separately archived actual210 disabled Float prototype and sole-flag diagnostic remain
historical.
Exact f32/f64 whole-child hierarchy now uses authenticated current backing and existing
producer-pair
validators for scalar arguments, Return values and typed stores. Copied NaN payloads and signed-zero
bits retain their issued raw/numeric pair; no numeric equality shortcut grants bit identity.
Selected and sibling readback, scalar return and sequential calls support actual nested bodies.
Wrong claims and actual identity-to-negation helper mutations refute; deeper nesting stays UNKNOWN.
Genuine omitted selected bodies remain MissingCompilerEvidence UNKNOWN, including guarded empty
callers. Compiler-only malformed Return clones preserve refusal before frame release or continuation
publication, rather than claiming whole-call rollback.
Corrected ROOT validation passes all 22 required checks, including 843 workspace tests.
Fresh native and debug/release comparisons preserve strict unknown and missing-body boundaries.

Stage212's actual211 migration adds checked local static associated hierarchy routing. Original
function arguments and normalized signatures remain tied to the selected complete compiler instance.
The associated route bounds borrowed type and body inventories before its own re-resolution,
normalization and body cloning; sampled cached bodies receive the same checks. These bounded passes
leave the earlier dispatcher resolution unchanged. Compiler controls cover associated Char Unicode
returns and Float raw-pair validation without granting new element domains. Receiver methods,
virtual calls and nonlocal associated bodies gain no permissions. Legacy free-function dispatch
remains unchanged. This source checkpoint precedes migrated fixture and compatibility captures.

Measured local associated fixtures support inherent, implemented-trait, default-trait and generic
static calls. Wrong claims and actual scalar-body mutations refute. Deeper and retained-view
boundaries remain unknown. Genuine omitted dependency bodies also remain unknown for empty callers;
optimized retained element stores keep their direct-element frontier. The append-only three-case
global upkeep and broad compatibility captures precede independent ROOT validation.

Stage213 accepts exact compiler `ConstantIndex` read and Store projections on already issued
scalar backing. Original element, codec, current Memory and typed Char/Float validity checks
remain required. Target `usize` representability, minimum view length and forward/reverse bounds
are proved before index construction. No new backing, alias, hierarchy or allocation authority
is issued. The fresh committed Stage212 checkpoint preserves all original guest claims and
advances retained optimized Char, integer interval and local associated dependency callers.
Omitted selected bodies remain unknown, including empty incoming-slice callers. The original
empty array control retains its earlier unsupported boundary. Compiler mutation, transactional
negative and finite native controls remain required. Broad compatibility and full validation
are separate from the completed targeted checkpoint; the earlier Stage211 preparation is retained
as historical evidence.

Stage214 adds bounded owned u16 symbolic suffix writes after the existing Single/Indexed
planner refuses a suffix with at least two unresolved indices. Original types, compiler usize
indices, current or captured destinations, correlated masks and cumulative 512-work/depth-16
preflight remain checked before one current local or Memory publication. Existing guest assertions
stay unchanged. Helper mutations refute, omitted bodies stay unknown, and excessive work stays
ResourceLimit UNKNOWN. All 22 ROOT checks pass, including 856 Rust tests and 68 Python tests;
four surveys cover 236 cases across 80 families with 97 proved, 82 refuted and 57 unknown each.
Fresh ROOT debug/release comparisons preserve all queried obligations/models on frozen owner
inputs. References, other scalar domains, from-end paths and input or return rights gain no
permissions. See the Stage214 capability evidence for scope and limitations.

Stage215 unifies six test-only hierarchy flag guards while retaining the previous thread-local
value across nested scopes and panic unwinding. Thread controls create and drop guards within
each thread. Production enable functions, constants and Float Return fault handling remain
unchanged. All 22 ROOT checks pass, including 859 Rust tests and 68 Python tests; four surveys
retain 236 cases across 80 families. Fresh release compatibility preserves all 4,644 rich
queried obligations/models on frozen owner inputs. Exact query-free fold timeout differences
remain UNKNOWN under separately recorded comparison rules. See the Stage215 capability evidence.

Stage216 supports known two-argument integer function tables with exact compiler A/B/R types,
safe Rust signatures, all-target validation and actual selected bodies. Argument evaluation
occurs once in order before branch cloning; current returned Memory is preserved. Repeat-produced
pointers remained UNKNOWN at Stage216. All 22 ROOT checks passed, including 864 Rust tests
and 68 Python tests;
four surveys cover 239 cases across 81 families. Fresh release compatibility preserves all
5,228 rich queried obligations/models on frozen owner inputs. Actual helper/order mutations
refute unchanged assertions and fail natively; omitted bodies remain UNKNOWN. See Stage216 in
the stage history for complete evidence. Historical actual213/214 preparations keep their scope.

Stage217 adds authenticated MIR Repeat assignments for known safe integer function pointers.
Exact full Instance, live cached Body/Assign occurrence, original types and target metadata remain
required. Construction is limited to 128 entries and the existing 256-value budget; symbolic
function-table dispatch remains limited to 16 targets. Shared 512-work/depth-16 preflight bounds
original metadata before the new route's queries, normalization and materialization. MIR operand
evaluation occurs once, including zero length; refusal does not publish the destination or restore
a consumed Move. Actual selected bodies remain required even for constant-return helpers.
Retained-body controls prove and omitted-body controls reach MissingCompilerEvidence UNKNOWN;
zero construction makes no selected-body availability claim. Helper identity and binary argument-
order mutations refute unchanged assertions and fail natively. Opaque targets and pointer-bearing
product repeats remain unsupported. Current validation and comparison evidence are in Stage217
of the stage history; these measurements do not establish full Rust parity.

Float numeric/storage correspondence uses a checked decoding relation for exact f32/f64 terms.
The relation preserves SMT equality, NaN storage payloads and signed zero. Mutable float validation
still authenticates the issued producer pair before constructing or proving that relation; this
refactor adds no scalar-call permissions or producer certificates.

Known integer table calls share one private dispatch loop after callable and argument evaluation.
Unary and binary preparation retain validation and Move order; target branches preserve actual
returned Memory and existing result certificates. This refactor adds no callable family, Repeat
permission or execution budget.

The compiler lease probe combines two actual symbolic helper Returns with caller continuation,
captured-index publication, consumed-place masks and independent branch memory updates. The
projected destination is a direct typed boundary control; this test adds no hierarchy depth rights
or persistent activation-history carrier.

Unary Bool-to-Bool and Char-to-Char tables execute actual known nongeneric safe Rust bodies.
The route preserves exact compiler signatures, argument evaluation once and current returned Memory.
Bool values require their original sort/context; Char arguments and results require proven Unicode
scalar validity under actual conditions. Primitive caller grammar and all-target body preflight use
separate bounded 512-work/depth-16 passes before the new route's normalization and cloning.
Unsupported grammar, opaque targets and missing bodies refuse. Integer unary/binary and integer
Repeat admission are unchanged. Reference and mixed-signature rights stay excluded.

Known safe Rust unary `fn(f32) -> f32` and `fn(f64) -> f64` tables execute actual selected
available bodies, preserving exact original signatures and checked scalar numeric/raw consistency.
Identity and negation preserve copied raw bits; arithmetic NaNs retain existing payload/sign
nondeterminism. Decoding equality cannot authenticate arbitrary substituted NaN payloads. Scalar
transport does not issue mutable Float pair authority or extend Float Repeat, mixed widths or
two-argument signatures. Compiler Return faults, genuine helper mutations and dependency omission
controls are validated. Completed ROOT checks and the four-profile 253-case survey are recorded in
[Stage223](../../docs/stages.md#stage223-unary-float-function-tables).

Known Repeat arrays of unary same-original Bool and Char function pointers execute actual available
selected bodies. Construction evaluates its operand once even for zero count, preserving Move
consumption and all existing admission bounds. Integer Repeat and Float table calls are unchanged;
Float Repeat remains unsupported. Opaque, generic, ABI, count, dispatch and selected-body controls
retain conservative refusals. Six appended survey cases are measured across four profiles;
completed ROOT checks and release comparison are recorded in
[Stage224](../../docs/stages.md#stage224-unary-bool-and-char-function-pointer-repeat-arrays).

Known Repeat construction accepts exact original unary f32-to-f32 and f64-to-f64 pointers.
Existing Bool/Char and integer routes, Move evaluation, selected-body/returned Memory checks and
all admission bounds remain unchanged. Float raw-copy and sign-bit claims require actual bodies;
decoder consistency does not authenticate substituted NaN payloads. Arithmetic NaN behavior
retains its existing limitations. Dedicated compiler, unchanged-claim mutation and omitted-body
controls pass, and the two existing Float Repeat survey cases prove across four profiles. See
[Stage225](../../docs/stages.md#stage225-unary-float-function-pointer-repeat-arrays).

The isolated activation-carrier prototype explicitly transports Unarmed or Armed receipts through
current State and Return values. Only compiler controls can arm it. A caller-owned expected call
nonce, immutable incoming and retained floors, exact live cached bodies and current hierarchy
generations are checked before returned Memory is adopted or a Call result is published. Sibling
Returns retain independent receipt histories; Armed-empty cannot silently become Unarmed.
Current Memory origins require exact issued receipts, and observed generations must match exactly;
immutable incoming and retained floors remain monotone even after release.
Unsupported armed adapters refuse before target execution. Experimental activation structural
work has an independently named shared2048 limit; body/type/input and registry extents remain512,
and depth remains16. Admission visits charge local512 and shared work before each operation;
actual clone/substitution passes are charged separately. Ordinary execution keeps its existing
step/time/SMT limits; this structural counter is not a universal CPU or queue-size bound.
The old512 controls and exact520 Resource measurements remain historical evidence. Earlier
provisional controls measured four main/scalar positives and exact smaller-fixture Resource.
Actual224 scoped controls and ordinary comparisons are archived against their original source.
Actual225 compiler controls and four ordinary profiles validate this composition.
Completed ROOT checks are recorded in
[Stage226](../../docs/stages.md#stage226-activation-state-transport-infrastructure).
Exact cached bodies receive a full current inventory and original signature check; original MIR
is inventoried before actual instantiation on cache miss. Narrow Armed shape checks refuse
recursive owned values and snapshots before production. Local continuation validation and cloning
share one bounded pass; backing and array COW costs are charged before detachment.
This prototype enables no additional hierarchy depth or production arming path.

Exact read-only `Option<NonZeroU16>` slice membership uses a live, admission-local certificate
for the actual core comparison and transport bodies. The application checks the original niche
schema, current typed descriptor and needle, applies equality once, and retains current conditions,
Memory and Unarmed flow. Other widths, custom equality and mutable or raw transport remain
unsupported by this route. Missing dependency bodies remain `UNKNOWN`.

The cumulative graph, private comparison law and application work limits are 131,072, 1,024 and
2,048 respectively. These are host work limits and add no guest premises. Every phase retains its
charges; certificate application is single-use. Compiler controls measured 551–779 application
units across host and ARM profiles. Earlier graph and application limit failures remain recorded.
The compiler controls and integration evidence cover successful membership, false claims,
unchanged-claim helper mutations, unsupported widths and genuine omitted dependency bodies.
All required repository checks pass. Four shared survey profiles each measure 111 PROVED,
90 REFUTED and 63 UNKNOWN across 264 cases and 88 families; the original membership entry now
proves. Validation and conservative limits are recorded in
[Stage227](../../docs/stages.md#stage227-exact-nonzero-niche-slice-membership).


An actual Stage227 source migration carries finite known shared trait-object selection from local
fixed arrays and retained slices. The complete receiver backing bundle remains in the value;
engine receipts authenticate masks and original witnesses. Virtual alternatives execute actual
compiler-selected bodies and transport each returned Memory. Shared reborrows, caller-backed
returns and per-candidate supertrait upcasts retain all sources; mutable choices and arbitrary
incoming objects remain unsupported. Array16, registry512, Repeat128, depth16 and engine execution
limits remain unchanged. Shared choice work uses a separate cumulative2048 engineering policy; it
supplies no guest premise or permission. The preceding512 policy stopped the first host callback
at repeated dispatch. Historical actual226 controls and its small direct corpus validate named
selection, mutation and retained/omitted bodies under2048. Those artifacts remain scoped to their
original source; the owner migration preceded the separate ROOT checks described below. Whole
Proofs are retained before test assertions; test-only fee refusal diagnostics record current work,
attempt and call site.

The committed activation carrier is preserved. Choice selection and dispatch refuse Armed before
receipt cloning or fee/type work; validated continuations transport the actual returned Flow.

ROOT Stage228 validates this migration with the full repository checks and fresh host/ARM O0/O2
surveys. Each survey reports 114 PROVED, 91 REFUTED and 64 UNKNOWN across 269 cases and 89 families.
Five new shared-choice cases preserve every prior case object and original fixture assertion.
Current integration tests validate helper mutation/native failures and retained versus omitted
actual methods; the earlier direct corpus remains explicitly historical. All 1,988 existing rich
queries and models remain unchanged under qualified source-fingerprint comparisons. Array16,
registry512, Repeat128, depth16 and cumulative choice2048 bounds remain explicit host limits.
No guest premise, mutable receiver right or arbitrary incoming dynamic target is supplied.
See [Stage228](../../docs/stages.md#stage228-finite-shared-trait-object-choices).

Readonly u16/u32 zero-only niches share compiler primitive/range and layout services.
Payload width stays distinct from discriminant/index width; size and alignment come from the
original compiler primitive layout. Actual getter and Eq/Ne Instances, same-live cached bodies,
current descriptors and Unarmed flow remain required. The u32 membership route admits only
certified non-byte transport; u8's byte/memchr path remains UNKNOWN pending a separate actual-body
certificate. Other widths and signed types remain excluded. Metadata services are prepaid;
application2048, graph131072, LAW1024 and existing type/string limits are unchanged.

The archived provisional source completed four compiler callbacks and 16 synthetic applications
within application2048. Its focused 52-Proof corpus measured 20 Proved, 20 Refuted and 12 Unknown,
with genuine helper mutations, native failures and retained/omitted external bodies. The unchanged
unconditional u32 assertion is Refuted, and the guarded zero-array legacy claim is Proved in all
four measured profiles. That source-only Stage228 composition preserved those exact
expectation edits;
its current-parent validation was pending at that checkpoint.

ROOT Stage229 validates the composed ordinary u16/u32 implementation with all 24 required commands.
Four fresh host/ARM O0/O2 surveys each measure 117 PROVED, 93 REFUTED and 64 UNKNOWN across
274 cases in 89 families. The old unconditional u32 membership claim is now REFUTED; five new
u32/byte-frontier cases are appended without changing old guest assertions. Current compiler,
mutation, native and missing-body integration controls pass. Two stale private width controls
were corrected to use an actual u32 external wrapper and an actually malformed opposite-width
column; all rejection assertions and production checks remain intact. Earlier test101 runs are
preserved. All 2,028 rich queries/models in the 268 unchanged parent roots remain exact under
qualified appended-source comparisons; actual differing whole Proofs remain distinguished.
See [Stage229](../../docs/stages.md#stage229-shared-u16u32-niche-semantics).

One private `Engine::new` now serves root verification and fourteen compiler-control wrappers.
Its 52 production fields retain their prior expressions and order. Options, limits, configuration,
fresh Context and Solver, timer and initial Proof state stay explicit; root execution and status
reduction determine the result. Construction adds no success, assumption, law or permission.
Feature algorithms and mutable State/Return Flow are unchanged. Thirteen test initializers now
follow production order; this is not a claim of identical test timer or allocation order.

Current host/ARM O0/O2 controls preserve a nondefault step-limit refusal, reject invalid
startup/async options before entry premises, and reject terms from another Engine context.
All 24 required checks pass, including 907 outer Rust tests and 91 Python tests. The unchanged
274-case survey reports 117 PROVED, 93 REFUTED and 64 UNKNOWN in each profile. All 2,044 rich
queries/models are exact; 1,095 whole Proof pairs are literal FULL and one retains the existing
query-free fold resource context allowance. No guest fixture, contract or domain is changed.
See [Stage230](../../docs/stages.md#stage230-one-concrete-engine-constructor).

Issued original f32/f64 mutable-slice roles support exact metadata-only is_empty.
The exact actual core body must compare current pointer metadata with target-usize zero; the
current live backing, original scalar/layout certificate and metadata-only role remain required.
No Float payload or NaN encoding is read, changed or certified by this Boolean relation. Existing
Float producer-pair authority and all other metadata operations retain their separate checks.
Armed Float is_empty is explicitly refused before body certification or terms. Ordinary Unarmed
flow is preserved, without new child, proper-slice, snapshot or activation rights.

The archived private Stage228 plus frozen Stage229 prototype completed four compiler callbacks
covering both widths and early Armed refusal. Its focused 52-Proof corpus measured 24 Proved,
16 Refuted and 12 Unknown, with 16 queried obligations, unchanged helper-mutation assertions,
genuine retained/omitted external bodies and four exact native tests (original0/mutant101).
The unchanged float_excluded and issued_scalar_float_unknown claims were Proved in four profiles
each. The integration expectation for float_excluded now records that measured result. Nested
Float remains Unknown at input admission; no body, metadata relation or payload support is claimed
for it. These private measurements retain their original source association.

ROOT Stage231 validates the composition with all 24 required commands, including
909 outer Rust tests and 91 Python tests. Fresh surveys each report 119 PROVED,
95 REFUTED and 64 UNKNOWN across 278 cases and 89 families. The old Float metadata root advances
from UNKNOWN to PROVED; four new cases retain metadata counterexamples and nested input refusal.
All 273 other old case objects and assertions remain exact. Whole Proof pairs retain actual
source-fingerprint differences; existing rich queries/models remain exact. Three stale guarded
Float-store expectations were corrected only after twelve current safety Proofs. Separate helper
store mutations preserve assertions and are REFUTED in all four profiles; native O0/O2 originals
pass and mutants fail. The preceding test101 and synthetic target-setup failures remain recorded.
Armed, nested and payload boundaries retain their independent checks and UNKNOWN outcomes.
See [Stage231](../../docs/stages.md#stage231-issued-float-slice-emptiness).

Local byte-copy support authenticates a same-block original shared borrow of a bounded initialized
local byte array and its live tracked allocation. A safe retained local helper with scalar inputs
may return that array; its actual body executes. Copying uses the current source snapshot, checks
separate destination storage and preserves the untouched tail. Opaque, unsafe and missing-body paths
remain unsupported. Four-profile proof and mutation tests cover concrete and symbolic payloads,
tails and unsafe transport. Current storage controls reject stale, overlapping and incomplete source
storage.

The separate `local_byte_copy_boundaries` fixture targets a retained first element after an empty
copy, the exact 128-byte source limit and a 129-byte refusal. Its payload mutation changes only the
actual local helper body while preserving the caller assertions. These tests add no production
model, resource policy or analysis premise.

Ordinary nominal comparison field construction now validates its fresh compiler shape by borrowing
that shape, then moves the validated root field names and compiler types into the ordered field
list. It avoids constructing a discarded owned annotation tree and repeating root field extraction.
Original type, layout and unsupported-domain checks remain required, including legacy Float fields.
This host refactor adds no Rust feature, comparison relation, analysis premise or resource policy.

Readonly `Option<NonZeroU8>` slices retain the exact core zero-only niche, with an 8-bit
payload, target-width indices and signed tags. Guarded observations and `get` calls
execute or authenticate their actual available bodies, and actual `Eq` and `Ne` calls retain
those original types. Equal-width signed niches, mutable niches, pointer niches and local
u8 empty/payload enums remain unsupported. The existing local u16 enum domain is unchanged.
One-byte `contains` transport remains UNKNOWN: its actual byte specialization requires a
separate available-body certificate. Dedicated asserted membership, helper mutation and
missing-body controls exercise these boundaries without changing caller claims.

Dedicated whole product helper tests record seven PROVED, three REFUTED and five precise UNKNOWN
outcomes at host/ARM O0/O2. Actual store and scalar-helper payload mutations refute unchanged
caller claims; retained dependencies execute and omitted bodies remain UNKNOWN. Native originals
pass and mutants fail. Compiler controls exercise authentic staging/call/Return, revoked metadata,
current frame/Body, initialization, Context, extent and branch-local Memory. Exact shared float-bit
recognition routes current product frames to the existing model without widening scalar call gates.

The private Option8 membership entry now observes the current caller Call, selected Instance,
evaluated raw-argument occurrence, original operand types and live shared storage in one invocation.
These observations retain current descriptor, offset, extent and symbolic Context associations;
they do not reexecute operands or require a moved reference carrier local to remain initialized.
The borrowed origin has no raw-read, reference-issuance or escape API. It does not authenticate the
helper path's no-write behavior or turn current storage into a temporal permission certificate.
Byte-sized niche membership still refuses until the genuine transport and memchr bodies have
independent semantic certificates. Ordinary raw access and Option16/32 membership retain their
existing gates.

Private frame-local receipts can retain the compiler origin of an exact promoted shared
`&Option<NonZeroU8>` None constant beside its ordinary decoded value. The producer evaluates the
constant once, preserves the existing checked decoder and its budgets, and independently checks
the complete closed original/current promoted None construction, shared borrow and Return bodies.
Only initialized immutable one-byte compiler Memory with shared provenance at offset zero is
recorded; static identities, numeric pointers and unmatched bodies receive no receipt. Whole-local
Copy/Move transport retains occurrence keys before consumption, while writes, storage changes and
call results invalidate local keys. Continuations clone private keys without inventing runtime
Memory allocations. These observations issue no raw-read, reference or byte-membership permission;
the current live-reference and byte-helper refusal boundaries remain required. Standalone compiler
controls cover actual producers and hostile transport; they do not certify an application Body.

Compiler constant observations retain the actual `WithRetag` tag, including the genuine promoted
constant producer's `Yes` tag, and require exact original/current producer metadata. Retagged
local Copy/Move assignments do not transport receipt keys. Recording compiler constant origin
does not model a Rust retag or grant reference, raw-read or byte-membership permission.

Typed mutable product payload projections can select fixed-array suffixes with genuine symbolic
Rust usize indices. Each current initialized index is captured once; exact original array counts,
FieldTy, target width/Context, bounds and complete target coverage precede observation. Nested and
correlated indices use conjunctions of their real equality guards across pure tuple/array/plain
local struct compositions. Integer, Bool, Char and f32/f64 columns preserve their original codecs.
Whole selected subproducts use the same typed observation and replacement validation as fixed paths.

Masked stores compute every selected column in temporary storage and publish one COW update only
when type, Char/Float validity, Context and all expressions succeed. Unselected suffixes, other
outer indices and branches retain current storage. Root and current whole-child
frame/generation/cache checks remain; symbolic selection creates no alias, lease or reference
permission. Existing constant paths and scalar/owned behavior retain their original checks. Proper
intervals, general aliases, Product Ghost, Armed execution and uncaptured dereferenced call
destinations remain conservative. One operation budget512/depth16 spans new traversal, guards,
column selection and stores; exhaustion refuses before publication. No assumption or cap is widened.
Host/ARM O0/O2 compiler assertions cover fifteen valid claims, three refuted claims and three
exact alias/budget refusals. Actual helper/index mutations refute unchanged claims; native originals
pass and mutants fail. Retained dependency bodies execute; omitted bodies remain UNKNOWN.

Owned initialization paths additionally distinguish exact compiler fixed-array elements, including
nested arrays and compiler from-end projections. Actual Body local types, field identities, concrete
array lengths and projection bounds determine those keys. Element consumption preserves siblings;
whole or ancestor loads still refuse holes, and only exact successful writes repair them. Addressed
array paths retain bounded Engine-scoped original-type evidence, separate from borrow permissions,
values and actual Body services. Branch clones preserve masks and retirement; retired allocation
identities cannot regain that evidence. Unresolved indices, ordinary raw/Deref/Subslice ownership
and partially initialized whole-array destructor carriers remain unsupported. This adds no general
IntoIter, partial MaybeUninit, allocating Box or unwinding certificate. Compiler controls exercise
precise paths, foreign/type/retirement refusal and branch-local masks.
Four-profile compiler claims cover array and nested destructuring, whole covering repairs and
actual helper mutations. Native originals pass and mutations fail; the prior invalid indexed-Move
MIR remains UNKNOWN. Host compiler controls check masks and original-type/lifetime associations.

Owned aligned fieldless local zero-size Box payloads can have an independently certified
custom Drop implementation. This separate certificate requires the original local unpacked Freeze
struct, zero physical fields, exact zero size/alignment and selected Drop trait/self/full Instance.
It validates the original fieldless value directly; it does not use or broaden the Copy product
certificate. Raw and current payload shim/destructor bodies must have the complete specified
receiver, forwarding and effect-free normal Return schemas. The original Box/Global protocol
remains certified, with current forwarding bodies independently compared to their raw instances.
Only the exact certified payload type can extend the private forwarding encoder; its crate and
arbitrary local functions remain excluded.

Certification models absence of destructor effects. It does not execute an application Drop
callback or grant its mutable receiver, raw or shared payload reference rights. Every body/type,
value and live/sealed owner gate completes before the normal single region retirement. Missing,
effectful, panicful or incompatible bodies stay UNKNOWN; nonzero allocation, nested/array payload
Drop and general destructors are separate unsupported domains. Existing Unit and Copy/noDrop
routes preserve their original schemas. The new route is ordinary Unarmed execution, with actual
additional type, body clone/cache, complete encoding and comparison work; it gives no Armed fee
or resource discount. Existing per-body template and cumulative owner/storage limits remain.

A separate fixed-array destructor path interprets terminal compiler Subslice Drop ranges. The
current instantiated Body, exact original array/count/field path and initialized selected children
are checked before effects. Each complete selected element executes actual DropGlue and adopts
returned Memory before its Element key is consumed. Nested compiler ranges retain their emitted
order; covering assignment cannot replace old storage before those drops succeed. Ordinary Subslice
reads/borrows, incomplete element receivers and IntoIter elements needing Drop remain unsupported.
Host/ARM O0/O2 controls measure actual order and effects, including genuine destructor mutations.

Compiler array DropGlue can use a private complete array/slice protocol when its independent raw
and current Bodies, source Instances, original types, loop and normal returns match. Its Slice
call enters the normal frame, retaining argument/snapshot/contract policy, call depth and exit
checks; only the exact finite element loop is interpreted through tracked child references.
Real child DropGlue executes and returned Memory carries its effects. Whole-array type evidence
is issued only by actual Unarmed typed mutable fixed-path borrowing, separate from permissions.
Ordinary raw-slice/static layout rules and IntoIter destructor exclusions remain unchanged. The
nested/covering and symbolic order controls pass on host/ARM O0/O2. Wrong claims and real helper
mutations refute, and native controls corroborate them. Missing dependency bodies stay UNKNOWN.
The hostile shim/owner compiler callback is measured on host O0 only.

Readonly original core Option<NonZeroI8>, Option<NonZeroI16> and Option<NonZeroI32> niche
observations retain exact signed payload codecs alongside the existing unsigned domain. Enum
discriminants and slice indices keep their separate word-sized metadata. Original compiler
primitive/inner/payload/tag representations must agree on width and signedness, initialized
zero-only ranges, size/alignment and offsets. Negative two's-complement bits remain correlated
with Some; only raw zero chooses None. Ordinary signed comparisons use those original payload
bits rather than treating negative values as unsigned.

Original/current getter and comparison bodies, original core identities, anchored inner Pat,
current FieldTy/signature/cache/Context and readonly initialized storage gates remain required.
The old local empty/payload enum domain stays u16-only. Signed byte membership still needs its
separate available-body transport certificate; mutable/pointer/other-width niches and arbitrary
Pat values remain unsupported. The separate signed primitive dispatcher leaves the old unsigned
helper and its accepted set intact. Existing fees/caps remain, with additional performed metadata
checks paid in their actual membership phases. No source review, type inventory or recorded
constant origin alone supplies execution, reference authority or a completed proof.


Readonly integer niche admission includes original core Option<NonZeroU64>,
Option<NonZeroU128>, Option<NonZeroUsize>, Option<NonZeroI64>, Option<NonZeroI128> and
Option<NonZeroIsize>. Target-sized payload width follows the actual compiler target's 32/64-bit
pointer width; discriminants and indices keep separate compiler metadata. Exact original primitive,
initialized zero-only ranges, alignment, fields, core anchors, inner Pat, readonly storage and
current Body/Context checks remain mandatory. Wide and target-sized getters authenticate original
and current bodies before modeling. The original unsigned 8/16/32 helper stays unchanged.
128-bit range maxima retain the existing u128::MAX branch for compiler-admitted widths. Local enums,
mutable/pointer niches and arbitrary Pat payloads retain their separate conservative domains.
Source inventory and compiler control declarations are not behavioral coverage evidence.
