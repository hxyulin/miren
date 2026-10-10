# Rust capability baseline and extension boundaries

The next development priority is general Rust execution. Fleet remains a regression workload;
its hardware and executor assumptions do not define the language semantics. The capability suite
runs without a firmware checkout, hardware policy or trusted function contract.

## First milestone

The first Rust-first milestone requires a shared machine-readable case manifest, host and ARM
execution at O0 and O2, positive/refuted/unknown controls, a source mutation that breaks a proof,
structured UNKNOWN reporting, and passing repository checks. Completion establishes a repeatable
baseline. It does not establish full Rust support or a completed memory-model refactor.

The manifest contains 100 cases across 35 families. Each build configuration expects 41 PROVED,
36 REFUTED and 23 UNKNOWN results. Stage 133 originally had 23 cases with 10 PROVED, 9 REFUTED
and 4 UNKNOWN; stage 134 closed its retained-prefix projection gap. Stage 136 adds raw-pointer
metadata P/R controls and a safe core reference-array grant that remains UNKNOWN without a
temporal permission certificate. Stage 137 adds tuple-array P/R and unsupported symbolic-write
controls. Stage 138 adds initialized `MaybeUninit` P/R and uninitialized extraction U controls.
Stage 139 extends that family with bounded whole-array initialization P/R/U controls. Stage 140
adds checked character conversion P/R and invalid character formation U controls. Stage 141 adds
owned initialized character payload P/R and uninitialized character extraction U controls.
Stage 142 adds floating remainder P/R and a missing external remainder body U control.
Stage 143 advances the original incoming word-slice assertion to REFUTED and adds read-correlation
P and aggregate-slice U controls. Stage 144 adds arbitrary iterator cursor P/R controls and
an unrestricted fold U that reaches the default execution time budget. Stage 145 adds bounded
primitive slice membership P/R and unrestricted membership U controls. Its comparison work bound
is proved on the actual call path without capping incoming input lengths.
Stage 146 adds returned scalar-slice closure capture P/R and missing invoked body U controls.
Synchronous captures retain exact compiler types and original backing; admitting a closure does
not summarize its body or permit a borrowed local to escape.
Stage 147 adds scoped universal and existential SMT terms, lexical free-symbol metadata and
solver/printer controls. It adds no Rust consumer or baseline case; full-sequence models require
a separate semantic implementation.
Stage 148 advances the unchanged unrestricted scalar membership root to PROVED and adds full-length
predicate P/R and missing invoked body U controls. Primitive scalar descriptors use scoped
existential membership and universal equal-length comparison after source/type/extent validation.
Byte and finite/custom comparison policies retain their separate work bounds and actual effects.
Stage 149 advances the unchanged original aggregate-slice false claim to REFUTED and adds
composite slice view P/R and deferred iterator U controls. Exact pure tuple and fixed-array element
shapes use independent per-occurrence primitive arrays and checked common-index observations.
Stage 150 adds pure nested-array conditional read P/R and deferred byte-array choice U controls.
Checked reads select exact matching tuple and fixed-array shapes while preserving every field's
condition, Float storage bits and existing valid Char values.
Stage 151 advances the unchanged composite iteration-count root to PROVED and adds shared cursor
nth P/R and missing invoked body U controls. Exact core Iter element types, retained read-only
sources and ordered live cursor bounds remain checked before metadata and element operations.
Stage 152 adds pure zero-sized slice cursor P/R and missing invoked body U controls. Exact
zero-byte shapes retain the full target-usize length domain with existing source and bounds checks.
Stage 153 adds safe composite size_of_val P/R and missing invoked body U controls. Exact
compiler element size includes padding; source/type/extent and selected ordinary body are checked.
Stage 154 adds safe dynamic slice alignment P/R and missing invoked body U controls. The exact
core function is resolved through compiler module identity; live descriptors precede alignment.
Stage 155 adds local ordinary struct slice read P/R and deferred membership U controls. Original
field identities/types and exact compiler layout validity are certified before arbitrary inputs.
Stage 156 adds nominal local zero-size struct cursor P/R and missing invoked body U controls.
Zero-byte struct nodes retain exact Adt identity and certify every original child before success.
Stage 162 adds exact safe sized alignment P/R and missing invoked body U controls. Original
primitive or pure product receivers retain their existing type and live-source certificates;
the selected safe core API body precedes compiler ABI alignment metadata.
Stage 163 adds registered scalar product choice P/R and missing invoked body U controls. Actual
lazy input construction records original pure root types and exact symbol reservations;
bounded typed preparation validates the requested descendant before observing those symbols.
These additions change the denominator, not a coverage percentage.
Covered examples exercise arithmetic, enum payloads, array indexing, reference effects, concrete
generics, closures, iterator callbacks, finite loops, destructors, fresh future polling and raw
pointer metadata and typed initialization wrappers. Open dispatch and unsupported slice element
shapes retain explicit frontiers. Exact primitive shared slices use an arbitrary-length logical
array behind the existing single immutable caller-root certificate. Their length domain follows the
actual target byte extent; it has no 128-element input cap. Exact pure tuple and fixed-array
primitive elements likewise admit arbitrary runtime lengths. Their expanded type shapes retain
node/depth limits and a 128-element array shape budget, independently of the slice length.
Ordinary local and dependency structs with exact original pure fields also use this domain. Copy,
Freeze,
no-drop, compiler scalar validity and original field identities are checked at every struct node.
Zero-byte struct nodes require an empty actual primitive inventory and retain nominal values.
Packed/vector layouts, core and compiler-special ADTs and identity-bearing fields remain
unsupported; constructor policies do not constrain arbitrary valid input values.
Pure zero-sized tuple/array elements are supported with an empty primitive inventory and full
target-usize length metadata. Original inner types are certified even beneath zero-length arrays.
Safe size_of_val uses their certified compiler stride and validated length, including zero stride.
Safe align_of_val uses the exact compiler element alignment after validating the live typed
read-only descriptor and selected body. Raw size/alignment and other DST APIs retain their
separate boundaries.
Refined and identity-bearing element shapes remain unsupported. Whole composite
membership and equality require separate consumer models. Shared composite iteration uses the
same checked cursor protocol as primitive slices. Checked symbolic selection between
whole pure nested tuple and fixed-array values is supported by stage 150 under the existing
16-level and 512-candidate-node limits. Byte snapshots, identity-bearing alternatives and
ambiguous symbolic writes retain separate unsupported boundaries. Mutable and competing incoming
references retain conservative boundaries. Indexed retained mutable integer/tuple prefixes use
checked projection snapshots with a uniquely determined length of at most 128. Bounded tuple reads
can select symbolic offsets while preserving field correlation; symbolic composite writes still
require a unique location. Pure tuple and fixed-array choices are bounded to depth 16 and 512 total candidate nodes,
validate exact sorts/contexts and restore no identity or reference rights. Existing immutable
incoming shared-reference snapshots can supply values in this domain. Retained handles, ADTs and
Drop-bearing identities remain excluded.
An expected UNKNOWN must reach its specified diagnostic rather than fail elsewhere.
The manifest also records its expected producer category on that same obligation; a missing body
cannot satisfy a semantic frontier or silently acquire a semantic success result.

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

Stage 157 adds compiler-typed finite local-struct array selection P/R and missing invoked body U
controls. Only actual MIR Copy/Move reads supply the original array-prefix type certificate.
Every candidate must match its complete original local struct schema, primitive metadata and
context; Char fields require valid values under current conditions. All fields use the same
symbolic index, and Float storage bits survive only with certificates from every alternative.
Generic operation types come from compiler MIR, rather than names or matching scalar widths.
Untyped retained reference projections and ambiguous writes remain separate frontiers. User
methods still execute their actual bodies, and no constructor invariant constrains input fields.

Stage 158 extends the same actual MIR owned-choice path to exact original fixed byte arrays.
A private original-type annotation preserves u8 identity even at zero length, after the existing
complete pure type certificate. Bytes and Elements carriers require exact count, byte metadata
and context; compressed byte arrays still charge every byte against the candidate budget.
All bytes and sibling fields use the same index. The result is a canonical finite byte value,
with no storage identity or new borrow permission. Bare snapshots and untyped reference reads
retain their prior behavior. The original nested byte-array choice source now proves.

Stage 159 admits ordinary structs from separately compiled dependencies under the same original
field, Copy/Freeze/no-drop, compiler layout and source certificates. An actual compiler core-crate
anchor and exact ordinary structural flags exclude core and compiler-special wrappers. Missing
anchors and unknown future flags refuse the new domain. Private fields and constructors add no
input invariant. Actual dependency method bodies remain required; unavailable MIR stays UNKNOWN.
A dedicated dependency rlib fixture covers all four profiles, including rebuilt dependency
mutations and genuine omitted-MIR controls. The core-only shared 88-case manifest is unchanged.

Stage 160 supports symbolic whole-element assignment to a direct owned fixed array local with
one Index projection. Actual MIR destination types certify primitive and pure tuple/array/ordinary
struct/byte products; all old candidates and the replacement are checked within existing budgets.
One index comparison controls every field of each rebuilt element. Existing allocated owners
retain the same live allocation and write checks. Constant and uniquely determined writes keep
their earlier paths. Nested post-Index stores, reference destinations and deferred lazy nominal
input candidates retain separate UNKNOWN frontiers. The unchanged tuple symbolic write now
proves; shared P/R/missing-actual-replacement-body controls record the additional family.

Stage 161 supports closed deferred input products with no observable primitive data in the
compiler-typed owned read/write protocols. Complete original compiler types and descriptor
metadata are checked, including unused N=0 children. Expanded occurrences consume the existing
candidate budget before reconstruction. Nominal fields remain exact and no symbols are generated.
Ordinary scalar-containing deferred inputs require future source reservation evidence and stay
outside this admission. The unchanged nominal-zero write now proves. Owned align_of_val on a
nested copied product still has a separate intrinsic frontier; successful reconstruction does
not supply that API model. Actual custom methods, Clone and equality retain their bodies/effects.

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

Tracked volatile reads, raw byte-slice views and nonempty raw-pointer-to-reference arrays lack
an implemented certificate for temporal access permission. These boundaries now return UNKNOWN
before exposing a value or reference. A live allocation, matching type, aligned address and
retained writable flag do not establish that an old pointer remains valid after competing
reference access.
The [Rust pointer documentation](https://doc.rust-lang.org/std/ptr/index.html#safety)
describes temporal permission and a limited reference-to-pointer access guarantee; precise
aliasing rules are not fully settled. The audit is a missing-certificate finding, not a
claim that every probed sequence is necessarily undefined behavior under every model.

Four old-pointer access sequences previously reported PROVED on host and ARM at O0/O2 without
assumptions. Their historical reports remain at `/tmp/miren-raw-alias-validity-audit`; stage-136
regressions now require Semantics UNKNOWN for the missing access certificate. Fresh access and
safe `array::each_mut` also remain UNKNOWN at the same boundary. Raw byte-pointer metadata
formation and length queries remain supported without supplying reference or read rights.
Do not use the historical results as evidence of full Rust parity.

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


Stage 162 extends safe `core::mem::align_of_val` to sized primitive and certified pure product
receivers. The original shared receiver graph and retained projection are checked before exact
original type, bounded product metadata and the selected safe API body. Copied nominal zero-byte
products keep their alignment even though they have no primitive leaves. The result is compiler
ABI alignment, including explicit alignment, rather than a leaf count or payload size.
Static views, raw/mutable receiver handles, opaque and unsupported product carriers acquire no
new alignment path. Existing dynamic slice alignment and safe/raw sized size-query semantics
remain separate; a sized raw metadata query does not establish pointee access or validity.


Stage 163 records immutable reservations only for lazy inputs actually issued by the Engine.
Exact root seed, descriptor identity, checked offset and original compiler type distinguish
cached shapes in different roots and repeated array occurrences. Copies retain the same symbols.
The complete original pure root certificate and bounded requested product preflight precede
scalar observation. The shared typed product preparation serves owned reads, complete writes and
safe sized alignment; the closed zero-observable path still emits no symbols. Generic input
observers and symbol budgets remain unchanged. Enum-origin, newly encoded Char, forged or
unregistered descriptors retain conservative boundaries; namespace evidence grants no storage
lifetime, reference rights or raw access.
