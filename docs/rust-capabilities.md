# Rust capability baseline and extension boundaries

The next development priority is general Rust execution. Fleet remains a regression workload;
its hardware and executor assumptions do not define the language semantics. The capability suite
runs without a firmware checkout, hardware policy or trusted function contract.

## First milestone

The first Rust-first milestone requires a shared machine-readable case manifest, host and ARM
execution at O0 and O2, positive/refuted/unknown controls, a source mutation that breaks a proof,
structured UNKNOWN reporting, and passing repository checks. Completion establishes a repeatable
baseline. It does not establish full Rust support or a completed memory-model refactor.

The current manifest contains 357 cases across 94 families.
The completed Stage241 host/ARM O0/O2 surveys measured 166 PROVED, 111 REFUTED and 80 UNKNOWN.
Fixed-array moves retain typed initialization holes, distinguish siblings and nested elements,
and support covering whole-array repair. Whole reads over holes and invalid indexed MIR remain
unsupported; partial-array destruction is a separate boundary.
The preceding Stage240 surveys measured 163 PROVED, 109 REFUTED and 80 UNKNOWN across 352 cases.
Typed mutable products support guarded symbolic fixed-array suffix reads and stores, including
nested and correlated indices, mixed scalar leaves and selected whole subproducts. Actual helper
mutations refute unchanged assertions; aliases and budget exhaustion retain explicit UNKNOWN.
The preceding Stage239 surveys measured 146 PROVED, 106 REFUTED and 79 UNKNOWN across 331 cases.
The preceding 295-case surveys measured 127 PROVED, 99 REFUTED and 69 UNKNOWN per profile.
Ten exact readonly `Option<NonZeroU8>` cases cover correlated payload observations, actual Eq/Ne
helpers, false claims and unsupported domains. Actual observer and equality mutations refute
unchanged caller claims and fail native execution. Missing dependency bodies remain UNKNOWN.
One-byte membership reaches its semantic transport-certificate refusal; it is not established by
admitting the niche. Mutable, signed, pointer and local u8 enum niches remain unsupported.

The historical Stage232 survey measured 285 cases across 90 families: 124 PROVED, 97 REFUTED and
64 UNKNOWN per profile.
Seven local byte-array cases cover concrete and symbolic payloads, wrong claims, tail preservation,
empty copies and unsafe transport refusal. The unchanged dynamic byte-copy claim advances from
UNKNOWN to PROVED. The other 277 old case objects and literal old fixture prefix remain unchanged.
Current storage, original array type, initialization, Context and source snapshot must agree;
unsafe or opaque transport remains unsupported. Full old-proof comparisons retain literal query
and model equality, with recorded source-fingerprint and existing resource-context qualifications.
See [Stage232](stages.md#stage232-current-local-byte-array-copy-sources).
The historical Stage231 survey measured 278 cases across 89 families: 119 PROVED, 95 REFUTED and
64 UNKNOWN per profile. It added exact Float metadata and false empty-slice claim controls without
relaxing payload, nested-borrow or hardware boundaries.
The historical Stage229 survey measured 274 cases across 89 families: 117 PROVED, 93 REFUTED and
64 UNKNOWN per profile, including shared u16/u32 niche semantics in
[Stage229](stages.md#stage229-shared-u16u32-niche-semantics).
The historical Stage228 survey measured 269 cases across 89 families: 114 PROVED, 91 REFUTED and
64 UNKNOWN per profile, including the shared trait-object choices described in
[Stage228](stages.md#stage228-finite-shared-trait-object-choices).
Readonly NonZeroU16 membership was validated in
[Stage227](stages.md#stage227-exact-nonzero-niche-slice-membership).
These are selected capabilities, not a Rust parity percentage.

Historical Stage217 host/ARM O0/O2 surveys
measure 99 PROVED, 83 REFUTED and 57 UNKNOWN each
after fresh validation.
Required ROOT check results and limitations are recorded in Stage217 in
[the stage history](stages.md). The measured existing Repeat entry advances from UNKNOWN to
PROVED; the other 238 case objects and all original guest assertions remain unchanged.
The historical Stage213 surveys measured 96 PROVED, 81 REFUTED and 56 UNKNOWN per profile
across 79 families. The historical committed Stage211 survey measured 230 cases across
78 families: 95 PROVED, 80 REFUTED and 55 UNKNOWN per profile.
The historical committed Stage210 survey measured227 cases across77 families:93 PROVED,79 REFUTED
and55 UNKNOWN per profile. The committed Stage209 survey measured224 cases across76 families, with
91 PROVED,78 REFUTED and55 UNKNOWN each.
The historical committed Stage208 survey measured 221 cases across 75 families, with
89 PROVED, 77 REFUTED and 55 UNKNOWN per profile.
The historical committed Stage207 survey measured 218 cases across 74 families, with
87 PROVED, 76 REFUTED and 55 UNKNOWN in each host/ARM O0/O2 profile.
The historical committed Stage203 survey measured 212 cases across 72 families, with
85 PROVED, 74 REFUTED and 53 UNKNOWN in each profile.
The historical Stage 202 survey measured 209 cases across 71 families, with
83 PROVED, 73 REFUTED and 53 UNKNOWN per profile.
The historical actual Stage 201 commit
`c0d47e17238cdbf8a269d83a34838c303fbe36a2` had 200 cases across 68 families, with
79 PROVED, 69 REFUTED and 52 UNKNOWN per profile. Stage 133 originally had 23 cases with
10 PROVED, 9 REFUTED
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
Stage 164 adds owned symbolic array field-write P/R and missing rvalue body U controls. Original
numbered Field projections resolve a certified child and logical leaf span; complete candidates
retain their existing bounds, source and typed preparation certificates.
Stage 165 adds constant nested owned-array write P/R and missing rvalue body U controls.
Original fixed-array element types, lengths and constant index metadata resolve the child span;
dynamic nested indices remain outside that stage's extension. Its initial read-before-write
control reached a separate lazy reader frontier, closed by stage 166. A distinct write-first
source covers the issued-input writer. The frozen stage 165 survey passes.
Stage 166 adds registered pure tuple/array read P/R and missing invoked body U controls. Actual
deferred candidates use the existing complete original-type and issued symbol certificates;
the original read-before-write control proves unchanged. Its longer borrowed-array comparison
frontier is closed by stage 168. The frozen stage 166 survey passes.
Stage 167 adds owned nested symbolic-index write P/R and missing replacement body U controls.
One original fixed-array inner index selects certified disjoint spans with a joint outer/inner
condition; complete typed candidates and existing bounds precede the same-owner update.
Stage 168 adds retained shared owned-array projection P/R and missing getter body U controls.
A projection-carried compiler type certificate preserves the actual owner and validates current
storage during later reference reads. Compiler-reference return checks reject eager and typed
frame-owned escapes before snapshot conversion. Seven older unchanged claims independently
advance to PROVED. Frozen surveys and all required validation pass.
Stage 169 adds known outer and symbolic nested owned-write P/R and missing replacement body U
controls. The earlier writer runs first; only its precise unsupported index boundary admits the
existing typed transaction. Already supported byte writes retain identical completed queries.
Original full parent types, complete candidates, bounds, context and owner checks precede commit.
Frozen surveys and all required validation pass.
Stage 170 adds owned tuple/ordinary-struct array-field write P/R and missing replacement body U
controls. The shared typed product plan validates the complete original enclosing root, compiler
field identities, disjoint logical spans, candidates and replacement before one same-owner commit.
Already supported byte paths retain identical completed queries. Frozen surveys and all required
validation pass.
Stage 171 adds retained shared owned-field array projection P/R and missing getter body U
controls. An immutable original root-and-field-path certificate validates the complete current
live root before field projection on every read. Existing direct-array paths retain identical
completed queries, with unchanged owner, lifetime, raw and mutable-access boundaries. Frozen
surveys and all required validation pass.
Stage 174 adds direct owned call-result destination P/R and missing callee body U controls.
Original indices and owner identity are captured before the callee; returned values update the
current owner using those indices. Complete root types, bounds, liveness and replacement checks
remain required. Dereference destinations require a separate base-location certificate and return
UNKNOWN. The original false proofs and valid native countercontrols remain recorded.
Stage 175 adds tracked mutable call-result location P/R and missing callee body U controls.
The original allocation and typed path are captured before the callee; changes to its reference
handle cannot redirect the returned value. Current whole-owner and replacement validation precede
one writable live-location commit. Unsupported reference forms retain their explicit frontiers.
Stage 172 integrates full-domain pure tuple/fixed-array slice predicate P/R and missing body U
controls after Stage 175. Original types, complete actual core bodies, selected transitive
comparators and layout constants certify scoped numeric equality and membership. Runtime length
has no new cap. Nominal custom comparisons and uncertified transport paths remain explicit UNKNOWN.
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


Stage 164 extends actual owned Array-local Assign writes from a whole element to compiler Field
paths within certified pure tuple or ordinary struct elements. The original field type and exact
logical leaf span determine the replacement. Complete original candidates and child replacement
are validated under existing budgets before a conditional span update and complete nominal
rebuild. Untouched leaves retain their exact values, and commit uses the same owned local or live
allocation. Rvalue effects and destination validators still precede the hook. Field spans convey
no physical padding, alias or pointer access information. Retained-reference, raw, call destination
and second-Index projections keep their separate frontiers; constants and solver-unique stores
retain their prior writer.


Final validation passes all 709 Rust tests and 68 Python tests. Formatting, lint, debug/release
builds, cargo deny, documentation and manual hooks pass. All 760 tracked main files match the
final snapshot byte for byte; fresh main builds, sixteen related integration tests, four metadata
tests and 68 Python tests pass. Both frozen surveys yield 212 PROVED, 188 REFUTED and 136 UNKNOWN
at `/tmp/miren-stage172-capabilities-20261010` and
`/tmp/miren-stage172-merged-capabilities-20261010`. All 392 previously completed parent roots
retain identical outcomes, obligation details and query text. All 536 main/isolate outcomes,
queries, models, premises and diagnostic details match. Source, input and release hashes are
verified. Independent source, composition and canonical correction reviews approve the final
implementation; the correction review is `/tmp/miren-stage172-canonical-review.md`. The interrupted
initial hook run remains excluded from these checks. No assumptions, input caps or resource-budget
changes are introduced. This independently authored stage integrates after actual Stage 175.


Stage 176 adds readonly logical slices of certified ordinary direct-tag enums and exact direct-tag
`Option<u16>`. Complete original variants, payload types and compiler layouts are checked before
input construction. Legal tags and independent payload columns share the selected logical index;
inactive payload access requires a feasible actual variant guard. Existing lifetime, extent and
body checks apply. Niche encodings, unsupported children even at N=0, raw accesses, owned enum
writes and whole enum comparison summaries remain UNKNOWN. No input assumptions or length caps
are introduced.

The dedicated thirty-two-root matrix yields thirteen PROVED, four REFUTED and fifteen UNKNOWN
per host/ARM O0/O2 profile. Exact sources return UNKNOWN under the immutable Stage 175 build.
Actual helper payload mutation refutes the unchanged claim in all profiles; valid native originals
pass and mutant guards exit 101 at O0/O2. Reports, commands, hashes and ten-second timeouts remain
at `/tmp/miren-stage176-final-evidence`. Two new metadata tests cover legal-tag decoding and
original enum shape rejection. The global triplet yields P/R/missing-body U with actual helper
mutation and native evidence at `/tmp/miren-stage176-global-evidence`; the expanded manifest has
137 cases in 47 families. Counts describe selected controls, not a Rust coverage percentage.

The unchanged vendored CAN `bus::check` now refutes arbitrary enum slices: a valid FdFrame with
ID 0x800 reaches its 11-bit assertion. The exact old source changes from UNKNOWN to REFUTED in
all four profiles; native checks confirm the actual panic and accept empty/valid-ID controls.
The obsolete expectation failure remains at `/tmp/miren-stage176-old-enum-initial.log` before
harness-only upkeep. Evidence remains at `/tmp/miren-stage176-old-enum-evidence`. Ambiguous
owned enum indices retain UNKNOWN. These initial captures preceded full validation and final parent
adoption.


The initial full suite retained an obsolete UNKNOWN expectation for the unchanged
`struct_slices::enum_field` length control. Its certified local struct contains a supported
direct-tag enum. Exact old sources return UNKNOWN under Stage 172 and PROVED under Stage 176
across all four profiles. The initial failed suite and expectation remain at
`/tmp/miren-stage176-initial-checks`; harness-only outcome/model upkeep follows the actual evidence
at `/tmp/miren-stage176-old-struct-enum-evidence`. The corrected full suite was rerun in full.
The initial documentation failure was a missing local dependency link; restoring that link
passes the build without changing source, with the original log preserved separately.


Final validation passes the corrected full suite of 713 Rust tests and 68 Python tests. The
initial failed suite remains excluded. Formatting, lint, debug/release builds, cargo deny,
documentation and manual hooks pass. All 762 tracked main files match the final snapshot byte
for byte. Fresh main builds, fourteen related integration tests, eight metadata tests, the CAN
compiler control and 68 Python tests pass. Both frozen surveys yield 216 PROVED, 192 REFUTED
and 140 UNKNOWN at `/tmp/miren-stage176-capabilities-20261010` and
`/tmp/miren-stage176-merged-capabilities-20261010`. All 400 previously completed parent roots
retain identical outcomes, obligations and query text; all 548 main/isolate outcomes, queries,
models and premises match. One ARM O0 fold has the same thirty-second resource UNKNOWN with a
closure-context prefix in only one diagnostic; both original details are retained explicitly.
Source, input and release hashes are verified. Independent review approves the source and
counterexample boundaries at `/tmp/miren-stage176-source-review.md`; the final global eight-report
recapture is `/tmp/miren-stage176-global-final-evidence`. Historical dedicated/global binary
identities retain their original scope. No assumptions, input caps or resource-budget changes
are introduced. Stage 176 integrates after actual Stage 172 commit `fbb58ca`.


Stage 177 adds readonly slices of exact compiler `Option<bool>` and local two-variant enums
with one original Bool payload and one empty alternative. The separate niche layout certificate
checks the actual one-byte overlap, Bool range 0..1, complete enum range 0..2, niche value 2,
variant identity and original fields. Reversed variant order is supported from compiler evidence.
Existing legal-tag logical decoding, guarded active payloads, source lifetimes and extent checks
are reused; no physical pointer, owned-write or comparison rights are added. Char, NonZero,
reference and broader niche layouts remain UNKNOWN.

The dedicated thirty-two-root matrix yields thirteen PROVED, five REFUTED and fourteen UNKNOWN
per host/ARM O0/O2 profile. Exact final sources return UNKNOWN under the frozen Stage 176 build.
Actual helper Bool-flip mutation refutes the unchanged claim in all profiles; seven valid native
originals pass and mutant guards exit 101 at O0/O2 with ten-second timeouts. Evidence, commands
and hashes remain at `/tmp/miren-stage177-final-evidence`. Full actual compiler layout probes
remain at `/tmp/miren-stage177-final-layout`. Nine composite metadata units include the new
malformed niche-certificate controls.

The unchanged old `tagged_sum_slices::niche_bool` length control becomes PROVED across all four
profiles. The initial stale expectation failure remains at
`/tmp/miren-stage177-old-direct-initial.log` before harness-only upkeep. Thirty-one other old
controls retain exact outcomes and obligations; 68 completed root/profile pairs and 156 completed
queries remain identical at `/tmp/miren-stage177-direct-fidelity`. The global triplet yields
P/R/missing-body U, with actual Bool-flip and native controls at
`/tmp/miren-stage177-global-evidence`. Its manifest contains 140 cases in 48 families; these
selected controls do not establish a Rust coverage percentage. These focused captures preceded full
checks,
final parent adoption and final-survey fidelity.


Final validation passes all 716 Rust tests and 68 Python tests. Formatting, lint, debug/release
builds, cargo deny, documentation and manual hooks pass. All 764 tracked main files match the
final snapshot byte for byte. Fresh main builds, sixteen related integration tests, nine metadata
tests and 68 Python tests pass. Both frozen surveys yield 220 PROVED, 196 REFUTED and 144 UNKNOWN
at `/tmp/miren-stage177-capabilities-20261010` and
`/tmp/miren-stage177-merged-capabilities-20261010`. All 408 previously completed parent roots
retain identical outcomes, obligation details and query text; all 560 main/isolate outcomes,
queries, models, premises and diagnostic details match. Source, input and release hashes are
verified. Independent source and focused-evidence review approves the actual narrow niche
certificate at `/tmp/miren-stage177-source-review.md`. Current global after/mutation evidence is
`/tmp/miren-stage177-global-final-evidence`; historical dedicated/layout/native artifacts retain
their original source and binary scope. No assumptions, input caps or resource-budget changes
are introduced. Stage 177 integrates after actual Stage 176 commit `80beb48`.


Stage 178 supports local ordinary Copy/Freeze structs inside certified readonly direct-tag enum
payloads. The existing struct shape builder is extracted into a concrete helper; original field,
layout, scalar validity, nominal identity and zero-length checks remain in place. The caller policy
admits local payload structs while preserving the existing top-level struct policy. Exact Bool
niches, owned storage, physical access and whole enum comparisons retain their existing boundaries.

The dedicated 31-root matrix yields twelve PROVED, five REFUTED and fourteen UNKNOWN per
host/ARM O0/O2 profile. Exact final sources are UNKNOWN under the frozen Stage 177 build.
Actual getter left-to-right mutation refutes the unchanged claim in all profiles. Six native
original tests pass and mutant guards exit 101 at O0/O2 with ten-second timeouts. Actual custom
PartialEq and Clone bodies execute and refute their false claims. Evidence and original binary
hashes remain at `/tmp/miren-stage178-final-evidence`; the source review is
`/tmp/miren-stage178-source-review.md`. All 216 previously completed focused queries retain
identical outcomes, details and query text at `/tmp/miren-stage178-query-fidelity`.

The unchanged old `tagged_sum_slices::nominal_payload_zero` case becomes PROVED in all profiles.
Its initial stale expectation failure is preserved at `/tmp/miren-stage178-old-tagged-initial.log`
before harness-only upkeep. Global controls include a proof, a counterexample, a genuinely missing
body and an actual getter mutation, with native originals and mutant guards. Their evidence is
`/tmp/miren-stage178-global-evidence`. The manifest now contains 143 cases in 49 families;
selected controls do not establish a Rust coverage percentage. These focused captures preceded
full validation and final survey comparison. No assumptions, input caps or increased resource
budgets are introduced. General niches, external nominal payloads and unsupported physical or
comparison operations remain UNKNOWN.


Final validation passes all 720 Rust tests and 68 Python tests. Formatting, lint, debug/release
builds, cargo deny, documentation and manual hooks pass. The initial formatting failure in the
old harness is retained before a whitespace-only correction and fresh formatting, lint and
harness checks. All 766 tracked main files match the isolated snapshot byte for byte. Fresh main
builds, eighteen related integration tests, eleven metadata tests and 68 Python tests pass.
Both frozen surveys yield 224 PROVED, 200 REFUTED and 148 UNKNOWN at
`/tmp/miren-stage178-capabilities-20261010` and
`/tmp/miren-stage178-merged-capabilities-20261010`. All 416 previously completed parent roots
retain identical outcomes, obligation details and query text. All 572 main/isolate outcomes,
queries, models and premises match. One query-free ARM O0 resource-limit UNKNOWN differs only
in its diagnostic call-context prefix; both original details are retained in
`/tmp/miren-stage178-main-query-comparison.json`. No status, query or execution budget changes.
Source, input and release hashes are verified. Current global after/mutation reports remain at
`/tmp/miren-stage178-global-final-evidence`; historical dedicated and native captures retain
their original binary scope. Independent source and focused evidence review approves the bounded
local payload policy at `/tmp/miren-stage178-source-review.md`. No assumptions, input caps or
increased resource budgets are introduced. Stage 178 integrates after actual Stage 177 commit
`98dfc95`.


Stage 179 adds readonly exact `Option<char>` and local two-variant empty/Char niche enums.
A separate certificate checks the original Char field, actual unsigned 32-bit layout, payload
and tag overlap, opposite empty variant and wrapping range 0xffffffff..0x10ffff. Compiler probes
on host/ARM O0/O2 establish the reserved niche 0xffffffff. Logical Char observations exclude the
surrogate interval using the existing Unicode decoder, preserving all valid Unicode scalars.
Direct-tag, Bool, nominal payload, owned storage, physical access and comparison boundaries remain
unchanged. General NonZero, reference, wrapped Char and broader niche layouts remain UNKNOWN.

The dedicated 34-root matrix yields fifteen PROVED, six REFUTED and thirteen UNKNOWN per profile.
Exact final sources are UNKNOWN under the frozen Stage 178 build. Actual getter Char mutation
uses only valid characters and refutes the unchanged claim in all four profiles. Eight native
original tests pass and mutant guards exit 101 at O0/O2 with ten-second timeouts. Actual compiler
layouts remain at `/tmp/miren-stage179-layout-initial`, with focused evidence at
`/tmp/miren-stage179-final-evidence`. Twelve composite metadata units and the existing Unicode
solver control validate the layout certificate and Unicode decoder.

The unchanged old Bool `char_niche` and direct-tag `niche_char` controls become PROVED in all
profiles. Both initial stale expectations remain at `/tmp/miren-stage179-old-harness-initial.log`
before harness-only upkeep. All other focused outcomes and diagnostics remain identical;
216 completed root/profile pairs and 448 completed queries retain exact text at
`/tmp/miren-stage179-old-fidelity`. Global proof, counterexample and genuine missing-body controls
plus actual getter mutation and native evidence remain at `/tmp/miren-stage179-global-evidence`.
The manifest contains 146 cases in 50 families; selected controls do not establish a Rust coverage
percentage. These focused captures preceded full validation and final survey comparison.
No assumptions, input caps or increased resource budgets are introduced.


Final validation passes all 723 Rust tests and 68 Python tests. Formatting, lint, debug/release
builds, cargo deny, documentation and manual hooks pass. All 768 tracked main files match the
isolated snapshot byte for byte. Fresh main builds, twenty related integration tests, twelve
metadata tests and 68 Python tests pass. Both frozen surveys yield 228 PROVED, 204 REFUTED and
152 UNKNOWN at `/tmp/miren-stage179-capabilities-20261010` and
`/tmp/miren-stage179-merged-capabilities-20261010`. All 424 previously completed parent roots
retain identical outcomes, obligation details and query text. All 584 main/isolate outcomes,
queries, models, premises and diagnostic details match, with no diagnostic context differences.
Source, input and release hashes are verified. Independent source and focused-evidence review
approves the exact Char layout and Unicode validity model at
`/tmp/miren-stage179-source-review.md`. Current global after/mutation reports remain at
`/tmp/miren-stage179-global-final-evidence`; historical dedicated, layout and native artifacts
retain their original binary scope. No assumptions, input caps or increased resource budgets
are introduced. Stage 179 integrates after actual Stage 178 commit `4d692c3`.


Stage 181 supports compiler-certified supertrait upcasts of an existing concrete reference
witness. Actual source-to-target and concrete-to-target Unsize selection must succeed. The
compiler's supertrait slot is authenticated against an exact TraitVPtr, or its reused vtable
against the complete target prefix. Target substitutions and descriptor identity remain exact;
source storage, lifetime and write rights are preserved. Virtual dispatch still executes the
compiler-selected actual implementation body. Arbitrary incoming objects and forged metadata
remain unsupported. No physical vtable identity or extra pointer rights are inferred.

The dedicated twelve-root source matrix yields six PROVED, three REFUTED and three UNKNOWN per
host/ARM O0/O2 profile. A genuinely separately compiled dependency with omitted implementation
MIR adds an UNKNOWN control in each profile, for thirteen controls with six P, three R and four U.
Exact final source controls are UNKNOWN under the committed Stage 179 binary. Compiler vtable
probes verify reused-prefix and second-supertrait pointer slots in all profiles at
`/tmp/miren-stage181-vtables`. Actual parent implementation mutation refutes the unchanged claim
in all profiles, with the same failing obligation retaining query and model. Four-test native
original suites pass; mutant guards exit 101 at O0/O2 with ten-second timeouts. Final source,
binary, commands and outputs remain at `/tmp/miren-stage181-final-evidence`.

The unchanged old `trait_objects::upcast_unknown` becomes PROVED across all four profiles.
Its initial stale expectation failure is retained at
`/tmp/miren-stage181-focused-related-initial.log` before harness-only upkeep. All eleven other
old roots retain exact outcomes and obligation details; 44 root/profile pairs and eight completed
queries remain identical at `/tmp/miren-stage181-old-fidelity`. Independent source and focused
review approves the narrow witness transport at `/tmp/miren-stage181-source-review.md`.
Global proof, counterexample and missing-body controls plus actual implementation mutation
and native evidence remain at `/tmp/miren-stage181-global-evidence`. The manifest now contains
149 cases in 51 families; selected controls do not establish a Rust coverage percentage.
These focused captures preceded full validation and final survey comparison. No assumptions,
input caps or increased resource budgets are introduced.


Final validation passes all 725 Rust tests and 68 Python tests. Formatting, lint, debug/release
builds, cargo deny, documentation and manual hooks pass. All 770 tracked main files match the
isolated snapshot byte for byte. Fresh main builds, twelve related integration tests and
68 Python tests pass. Both frozen surveys yield 232 PROVED, 208 REFUTED and 156 UNKNOWN at
`/tmp/miren-stage181-capabilities-20261010` and
`/tmp/miren-stage181-merged-capabilities-20261010`. All 432 previously completed parent roots
retain identical outcomes, obligation details and query text. All 596 main/isolate outcomes,
queries, models and premises match. One query-free ARM O0 resource-limit UNKNOWN differs only
in its diagnostic call-context prefix; both original details remain in
`/tmp/miren-stage181-main-query-comparison.json`. No status, query or execution budget changes.
Source, input and release hashes are verified. Independent source and focused-evidence review
approves the concrete witness certificate at `/tmp/miren-stage181-source-review.md`.
Current global after/mutation reports remain at `/tmp/miren-stage181-global-final-evidence`;
historical dedicated, compiler vtable, omitted-dependency and native evidence retains its
original binary scope. No assumptions, input caps or increased resource budgets are introduced.
Stage 181 integrates after actual Stage 179 commit `eebf727`; ownership Stage 180 remains a
separate implementation rather than an implicit part of this validated snapshot.


Stage 180 extends the capability matrix with owned-move initialization controls. Actual helper
execution proves the valid claim and refutes its false counterpart; compiler-only stale-load
MIR returns UNKNOWN. The dedicated matrix covers whole and field moves, repairs, drops,
coroutine captures, consumed unit returns and call overlap. Safe ordinary reassignment remains
supported. Invalid custom MIR is excluded from native companions. The combined manifest now
contains 152 cases in 52 families. No assumptions, input caps or larger budgets are introduced.

Retained-tag controls distinguish payload movement from whole-enum or ancestor consumption.
Return-only induction supports owned argument transfer while retaining its consumed source mask.
Reference arguments, addressed storage and current-final contract observations remain strict.


Final corrected validation passes all 737 Rust tests and 68 Python tests. Formatting, lint,
debug/release builds, cargo deny, documentation and manual hooks pass. All 777 tracked main files
match the isolated source byte for byte. Fresh main builds and 98 relevant Rust tests pass.
Both frozen surveys yield 236 PROVED, 212 REFUTED and 160 UNKNOWN at
`/tmp/miren-stage180-upkeep-capabilities-20261010` and
`/tmp/miren-stage180-upkeep-merged-capabilities-20261010`. All 440 previously completed parent
roots retain identical outcomes, obligation details and query text. All 608 main/isolate outcomes,
queries, models and premises match, with no diagnostic context differences. Source, input and
release hashes are verified. Initial and repaired failing full runs remain historical evidence;
the final passing run is `/tmp/miren-stage180-upkeep-checks`. Independent source, terminal,
retained-tag and no-drop upkeep reviews approve the bounded changes. Current dedicated/global
captures remain at `/tmp/miren-stage180-repair-final-evidence` and
`/tmp/miren-stage180-repair-global-final-evidence`; their recorded binary scopes are preserved.
The combined manifest contains 152 cases in 52 families. No assumptions, input caps, firmware
rewrites or increased resource budgets are introduced.


Stage 183 certifies the actually selected structural `PartialEq` body for local ordinary structs
in full-domain read-only slice membership and equality. The original type remains Copy, Freeze
and without drop glue. Exact shared receiver paths, recorded field types, local initialization,
Move consumption, child comparisons, all reachable effects and the complete Boolean result must
establish equality of every corresponding field. Derived markers and method names grant no proof.
Float fields use numeric equality, including NaN and signed zero; Char keeps its existing validity
checks. Source lifetime and extent checks precede empty and unequal-length shortcuts. Certificates
are revalidated against instantiated MIR without a cache. Array-field casts, external nominal
comparers, custom effects and missing selected bodies remain conservative boundaries.

The dedicated 22-root matrix yields 11 PROVED, three REFUTED and eight UNKNOWN per host/ARM O0/O2
profile. Changing the actual data helper refutes the unchanged claim, with its body entered and
query/model retained on the failing obligation. Changing a comparator to compare the wrong field
returns UNKNOWN. Safe native originals pass and data mutants exit 101 at O0/O2 with ten-second
limits. Commands, source and binary hashes, reports and native outputs remain at
`/tmp/miren-stage183-final-evidence`. Its missing-body control invokes a foreign helper after the
comparison; it is not evidence of omitted selected-comparator MIR. Global controls and their
independent actual-helper mutation remain at `/tmp/miren-stage183-global-after-evidence`.

Two unchanged `struct_slices` roots advance from UNKNOWN to PROVED in all four profiles. Three old
nonstructural or panicking comparator roots remain UNKNOWN with a more precise certificate refusal.
The initial stale diagnostic expectation failure remains at
`/tmp/miren-stage183-related-initial.log`. Harness upkeep changes no original fixture or claim.
The focused fidelity ledger retains 56 query-bearing completed root/profile pairs and all 96 query
texts. Twelve additional completed pairs are query-free; 68 outcome/detail pairs are unchanged. The
eight promotions and twelve query-free diagnostic
changes are recorded separately at `/tmp/miren-stage183-query-fidelity`. Final integrated repository
validation and the combined frozen surveys follow these focused captures. No assumptions, input
length caps, write permissions or increased resource budgets are introduced.


The initial full run passed 737 Rust tests and failed four Cargo tests. Two solver-unit failures
came from the root validator setting `MIREN_Z3`, which selects custom solver behavior rather than
the default persistent session those tests inspect. The other failures were stale expectations in
typed-struct arrays and zero-sized struct slices. The expected native-mutant child failure is
separate. Original logs remain at `/tmp/miren-stage183-checks`; the environment correction is
recorded at `/tmp/miren-stage183-validation-environment-correction.json`.

Sixteen unchanged-source before/after runs verify two typed-struct-array roots advancing from
UNKNOWN to PROVED in all four profiles. Two zero-sized struct roots remain UNKNOWN because their
original array fields fall outside the nominal structural grammar, including zero-length fields.
The actual categories and reasons remain at `/tmp/miren-stage183-extra-frontiers`. Two additional
harness updates preserve every fixture and claim, pin the promoted producer models and keep the
unsupported array-field cases strict. Corrected full validation follows this recorded first run.


Final corrected validation passes all 741 Rust tests and 68 Python tests. Formatting, lint,
debug/release builds, cargo deny, documentation and manual hooks pass. Fresh main validation passes
30 relevant Rust tests and 68 Python tests. All 780 tracked files match the isolated source byte
for byte. Both corrected surveys yield 244 PROVED, 216 REFUTED and 160 UNKNOWN across four profiles:
`/tmp/miren-stage183-corrected-capabilities-20261010` and
`/tmp/miren-stage183-corrected-merged-capabilities-20261010`. All 448 previously completed parent
roots retain identical outcomes, obligation details and query text. All 620 main/isolate outcomes,
queries, models and premises match. One query-free host-optimized resource refusal has a different
context prefix; its unchanged 30-second limit and original diagnostics remain in the comparison
ledger. Source, input and release hashes are verified. The manifest contains 155 cases in 53
families. Current release global captures remain at `/tmp/miren-stage183-global-final-evidence`;
the native evidence retains its original binary scope. Initial failures remain preserved, and no
assumptions, input caps, firmware rewrites or increased resource budgets are introduced.


Stage 185 extends structural comparison certificates to already eligible ordinary dependency
structs. The original complete product, ABI/layout, Copy/Freeze/no-drop and raw-field checks stay
in force. Only the additional comparer-local restriction is removed. Actual selected comparator
MIR, exact signatures, all reachable effects and the complete field-equality relation remain
mandatory before empty, unequal-length or zero-field shortcuts. No dependency name or derive
marker grants a proof.

A genuine dual-rlib compiler matrix builds identical dependency and consumer sources with selected
MIR retained or omitted in host/ARM O0/O2. Each retained profile yields nine PROVED and three
REFUTED roots; all twelve omitted roots return selected-comparer MissingCompilerEvidence. The
actual data-helper mutation refutes the unchanged claim with its body entered and query/model on
the failing obligation. A wrong-field comparator mutation remains UNKNOWN. Safe native originals
pass five tests and the data mutant exits 101 at O0/O2 with ten-second limits. Exact commands,
source/archive/binary hashes and complete outputs remain at `/tmp/miren-stage185-final-evidence`.
The committed-parent before captures remain at `/tmp/miren-stage185-before`.

Focused fidelity preserves 176 status/detail/premise pairs and all 216 queries byte for byte.
Of 132 completed root/profile pairs, 116 have queries and sixteen are query-free. Evidence remains
at `/tmp/miren-stage185-query-fidelity`. The global fixture,
manifest and runner remain unchanged: 158 cases in 54 families. This dedicated external-domain
matrix is separate from that global inventory. No assumptions, input caps, compiler-special type
rights, write permissions or increased resource budgets are introduced. Integrated full validation
and fresh-main checks follow the frozen focused captures.


The initial full run passed 742 Rust tests and failed one stale expectation in
`external_struct_values`; its separate native-mutant child failure is expected. Original logs
remain at `/tmp/miren-stage185-checks`, and actual counts are retained at
`/tmp/miren-stage185-initial-full-actual-counts.json`. Sixteen unchanged-source before/after root
results show retained `whole_contains` advancing from UNKNOWN to PROVED in all four profiles,
while the dead-source empty control remains UNKNOWN. Commands, original sources, dependency
archives and analyzer hashes remain at `/tmp/miren-stage185-extra-frontiers`. One harness update
pins the real full-domain producer and changes no fixture, dependency or claim. Corrected full
validation follows this recorded first run.


Final corrected validation passes all 743 Rust tests and 68 Python tests. Formatting, lint,
debug/release builds, cargo deny, documentation and manual hooks pass. Fresh main checks pass
34 relevant Rust tests and 68 Python tests. All 783 tracked files match the isolated source byte
for byte. Both frozen surveys yield 244 PROVED, 216 REFUTED and 160 UNKNOWN:
`/tmp/miren-stage185-corrected-capabilities-20261010` and
`/tmp/miren-stage185-merged-capabilities-20261010`. All 460 previously completed parent roots
retain identical outcomes, obligation details and queries. All 620 main/isolate outcomes, queries,
models and premises match, with no diagnostic context differences. Source, input and release
hashes are verified. Fresh release captures of the complete external matrix remain at
`/tmp/miren-stage185-main-release-final-evidence`; unchanged native records explicitly retain their
original frozen-author execution scope. Initial failing logs remain preserved. The global
manifest stays at 155 cases in 53 families; no assumptions, input caps, firmware rewrites or
increased resource budgets are introduced.


Stage 182 adds exact locally constructed `Box<(), Global>` ownership. Private branch-local
regions track initialization, sealing, liveness and retirement separately from frame storage.
Original compiler Box/Global identities, Unit type and layout (size zero, alignment one), selected
constructor/dereference/destructor bodies and complete effect certificates are required. The
actual zero-size allocation branch cannot reach allocator or OOM calls. Initialization is tied
to its exact source occurrence, including the certified optimized Unit-store lowering. Region
identity grants no numeric address, pointer inequality or raw-access right.

Move transfers one owner; destruction retires the region and retained executable borrows.
Ghost observations detach Unit without executable ownership. Borrowed virtual owners remain in
authenticated private readonly temporaries. Mutable borrowing, raw exposure, ordinary owner Copy
and escape stay UNKNOWN. The narrow consuming optimizer Copy boundary is certified against the
actual Unit mem::drop call. Non-Unit payloads, general ZST structs, nonzero allocation, raw
constructors and general heap mutation remain unsupported. Existing cumulative budgets apply.

The dedicated 23-root matrix yields seven PROVED, three REFUTED and thirteen UNKNOWN per host/ARM
O0/O2 profile. Actual selected-helper mutation 19 to 20 refutes the unchanged claim with body entry
and query/model on the failing obligation. Safe native originals pass seven tests; the mutant
exits 101 at O0/O2 with ten-second limits. Current captures remain at
`/tmp/miren-stage182-parent185-final-evidence`; unchanged native records retain their historical
execution scope. All 92 refreshed original proof objects exactly match historical parent-183
captures. Old source, binary, freeze and handoff remain at
`/tmp/miren-stage182-historical-parent183`. Exact-source before captures under committed Stage 185
return UNKNOWN for all 23 roots in four profiles at
`/tmp/miren-stage182-parent185-before-final-source`. Historical async/induction fidelity preserves
136 outcome pairs and 72 query identities under its original parent-183 scope.

Actual compiler metadata and source/template corruption controls are separate from proof
inventory. Global Unit P/R and non-Unit U controls have an independent actual-helper mutation and
native guard at `/tmp/miren-stage182-global-after-evidence`. The non-Unit control reaches the exact
Unit-payload admission refusal; it does not model allocator failure. The combined manifest has
158 cases in 54 families. Integrated full validation follows the frozen captures. No assumptions,
input caps, firmware rewrites or increased resource budgets are introduced.

Final Stage 182 validation passes 751 Rust tests and 68 Python tests in the isolated workspace;
fresh main passes 50 relevant Rust checks and 68 Python tests. Formatting, lint, workspace debug
and release builds, documentation, dependency denial and manual hooks pass in both. All 810
tracked files match byte for byte. Both surveys yield 248 PROVED, 220 REFUTED and 164 UNKNOWN:
`/tmp/miren-stage182-capabilities-20261010` and
`/tmp/miren-stage182-merged-capabilities-20261010`. All 460 previously completed parent roots
retain identical outcomes, obligation details and queries. All 632 main/isolate outcomes, queries,
models and premises match, with no diagnostic context differences. Source, input and release
hashes are verified. Fresh release captures at `/tmp/miren-stage182-main-release-final-evidence`
match 96 dedicated original and mutant proof objects after explicitly mapping source paths;
unchanged native records retain their original execution scope. Global fresh release captures are
at `/tmp/miren-stage182-global-final-evidence`. The historical author freeze remains immutable;
a root README line reflow is recorded separately. No assumptions or resource budget changes are
introduced.


Stage 186 supports recursive fixed integer arrays inside ordinary nominal fields and tuples.
Typed logical paths distinguish fields from array elements. Complete original owned-product
eligibility, child types beneath zero lengths, compiler layout and the existing array, depth and
expanded-node budgets are checked before a comparison is admitted. Whole-array child calls require
the actual selected core family, signature, body, effects and totality certificate. The complete
Boolean relation must compare every corresponding leaf. No nominal Index, Cast, raw transport,
loop or new allocation operation is admitted.

The dedicated retained-body matrix yields eleven PROVED, three REFUTED and twelve UNKNOWN per
host/ARM O0/O2 profile. Genuine omitted external comparer bodies remain MissingCompilerEvidence,
including empty and mismatched-length controls. Actual scalar helper mutation refutes the same
claim with body entry and query/model; a same-receiver comparator mutation remains UNKNOWN.
Safe native originals pass five tests and the mutant exits 101 at O0/O2 with ten-second limits.
Parent-182 captures are `/tmp/miren-stage186-parent182-final-evidence`; historical parent-185
sources, binary and evidence remain archived. Native evidence retains its original execution scope.
Float, Bool and Char array fields, unsupported original children beneath zero lengths and default
optimized external aggregate transport remain UNKNOWN.

Three unchanged older roots advance from UNKNOWN to PROVED: nominal array-backed membership and
zero-sized struct membership/equality with integer-array fields. Exact-source before/after
captures are `/tmp/miren-stage186-parent182-old-frontiers-before` and
`/tmp/miren-stage186-parent182-old-frontiers-after`; all four previous bounds queries retain their
exact prefixes. Harness upkeep changes only those expectations and pins the actual full-domain
models. Global controls and their independent actual-helper mutation/native guard are at
`/tmp/miren-stage186-global-after-evidence`. The combined manifest has 161 cases in 55 families.
Full integrated validation follows the frozen captures. No assumptions, input caps, firmware
rewrites or resource budget increases are introduced.

Final Stage 186 validation passes 753 Rust tests and 68 Python tests in the isolated workspace;
fresh main passes 52 relevant Rust checks and 68 Python tests. Formatting, lint, workspace debug
and release builds, documentation, dependency denial and manual hooks pass in both. All 813
tracked files match byte for byte. Both surveys yield 252 PROVED, 224 REFUTED and 168 UNKNOWN:
`/tmp/miren-stage186-capabilities-20261010` and
`/tmp/miren-stage186-merged-capabilities-20261010`. All 468 previously completed parent roots
retain identical outcomes, obligation details and queries. All 644 main/isolate outcomes, queries,
models and premises match, with no diagnostic context differences. Source, input and release
hashes are verified. Fresh release captures at `/tmp/miren-stage186-main-release-final-evidence`
match 124 dedicated original and mutant proof objects, including 148 queries, after explicitly
mapping source/replay paths. Native records retain their original execution scope. Fresh global
release captures are at `/tmp/miren-stage186-global-final-evidence`. Dedicated historical fidelity
preserves 172 unchanged outcome pairs and all 216 previous queries, including the four prefixes
on advanced roots. Parent adoption preserves original fixtures and the archived evidence scope.
No assumptions or resource budget changes are introduced.


Stage 187 extends nominal whole-array child comparisons to exact Bool, Char, f32 and f64 leaves.
Original child validation beneath zero lengths, typed logical paths, layout, Copy/Freeze/noDrop,
expanded-node budgets and actual selected core body/effect/totality certificates remain required.
Float equality stays numeric: NaN is nonreflexive and opposite signed zeros compare equal. Float
bitwise comparison remains excluded. Char values retain decoded Unicode validity requirements.
No nominal MIR Index, Cast, loop, raw transport or new permission is admitted.

The dedicated 27-root matrix yields seventeen PROVED, four REFUTED and six UNKNOWN per host/ARM
O0/O2 profile. Unrestricted f32/f64 self-equality claims refute; signed-zero and non-NaN membership
controls prove. Genuine omitted external comparer bodies remain MissingCompilerEvidence before
empty/mismatch shortcuts. An actual Bool-leaf helper mutation refutes the unchanged claim with
body entry and query/model; a malformed comparer remains UNKNOWN. Native originals pass five
tests and the mutant exits 101 at O0/O2 with ten-second limits. Current captures are
`/tmp/miren-stage187-final-evidence`; exact-source before captures under committed Stage 186
are `/tmp/miren-stage187-before-final-source`.

Historical fidelity preserves 324 unchanged outcome/detail pairs, including 248 completed roots
(160 query-bearing and 88 query-free), and all 364 completed queries. Three unchanged older
primitive-array functions advance to PROVED. The old global Float-array function also becomes
PROVED: it returns the numeric comparison result, without asserting universal reflexivity.
Harness upkeep changes only those expectations and pins their actual full-domain equality model;
original fixtures stay unchanged. Global controls, actual-helper mutation and native guard are at
`/tmp/miren-stage187-global-after-evidence`. Unsupported reference children beneath zero lengths
remain UNKNOWN. The combined manifest has 164 cases in 56 families.

Scratch native evidence uses finite length129. A linear maximum-length zero-sized equality probe
timed out; its source claim remains unchanged. The initial timeout handler did not save its output
streams, and no native maximum-length success is claimed. Preparation records retain that limit
at `/tmp/miren-stage187-prep`. No assumptions, input caps, firmware rewrites or resource budget
increases are introduced.

Final isolated validation passes 755 Rust tests and 68 Python tests; fresh-main focused validation
passes 54 Rust tests and 68 Python tests. Formatting, lint, debug/release builds, dependency denial,
documentation and manual hooks pass in both. All 816 tracked files match byte for byte. Both
surveys yield 260 PROVED, 228 REFUTED and 168 UNKNOWN across four profiles. All 476 previously
completed roots retain identical outcomes, obligation details, queries, models and premises;
all 656 main/isolate results match with no diagnostic context differences. Fresh main release
captures at `/tmp/miren-stage187-main-release-final-evidence` match 128 complete original/mutant
proof objects and 248 queries after explicit source/replay path mappings. Global release captures
at `/tmp/miren-stage187-global-final-evidence` match 20 proof objects and 80 queries. Native records
retain their original execution scope. Source, input and release hashes are verified.

Stage 184 adds one original incoming mutable u16 slice with primitive owned inputs. Branch-local
Memory holds its current full-extent SMT array, original type, initialized storage identity,
generation and source permissions. Direct typed element reads and stores prove bounds; each
store evaluates its actual scalar helper once and updates current data. Rust's valid slice extent
is retained without an analysis input cap. Detached ghost data preserves prestate; configured
contracts observe frozen length. Private executable metadata exposes only length through the
actual selected available core SliceLen body, with a complete signature/body/effect certificate.

Root Copy/Move, aggregate role storage, retained shared data, borrowed helper calls, child reborrow,
raw access, executable return and induction remain UNKNOWN. Existing readonly slice permissions
are unchanged. Recursive role checks prevent metadata laundering; induction refuses the backing
namespace rather than discarding state. No assumptions or resource budget changes are introduced.

The 23-root dedicated matrix yields six PROVED, two REFUTED and fifteen UNKNOWN per host/ARM O0/O2
profile. Separate configured ghost-length equality proves and inequality refutes. Actual selected
scalar dependency bodies prove; genuine omission remains MissingCompilerEvidence. The actual
replacement-helper mutation refutes the unchanged claim with body entry, query and model. Safe
native originals pass two tests and the mutation guard exits 101 at O0/O2, using finite extent129
and ten-second timeouts. Current parent-187 captures are at
`/tmp/miren-stage184-parent187-final-evidence`; exact-source before captures under committed Stage
187 are at `/tmp/miren-stage184-parent187-before-final-source`. All 96 original/mutant proof objects
match the preserved parent-186 captures after explicit source/replay path mappings. Native records
retain their original execution scope. Historical source and failed prototype captures remain
under `/tmp/miren-stage184-parent186-history` and the earlier evidence directories.

Historical fidelity preserves 52 unchanged entry/profile pairs and all 56 completed queries.
Both older mutable_root cases remain Semantics UNKNOWN with the metadata-operation reason.
The unchanged len-only scalar_slices input now proves under the actual selected length certificate;
mutable iterator access stays UNKNOWN at the child-lease gate. Harness upkeep pins these outcomes
and precise models or reasons. Original fixtures and claims stay unchanged. Global P/R/U controls and actual-helper mutation/native guard are at
`/tmp/miren-stage184-global-after-evidence`. The combined manifest has 167 cases in 57 families.

Final isolated validation passes 759 Rust tests and 68 Python tests; fresh-main focused validation
passes 62 Rust tests and 68 Python tests. Formatting, lint, debug/release builds, dependency denial,
documentation and manual hooks pass in both. All 820 tracked files match byte for byte. Both
surveys yield 264 PROVED, 232 REFUTED and 172 UNKNOWN across four profiles. All 488 previously
completed roots retain identical outcomes, obligation details, queries, models and premises;
all 668 main/isolate results match with no diagnostic context differences. Fresh main release
captures at `/tmp/miren-stage184-main-release-final-evidence` match 112 complete original/mutant,
contract and dependency proof objects with 108 queries after explicit source/replay path mappings.
Global release captures at `/tmp/miren-stage184-global-final-evidence` match 16 proof objects and
32 queries. Native records retain their original execution scope. Source, input and release hashes
are verified. Initial full validation's three stale assertions and documentation EOF-hook failure
remain at `/tmp/miren-stage184-checks`; initial main failures and the intermediate model assertion
failure remain at `/tmp/miren-stage184-merged-checks` and
`/tmp/miren-stage184-corrected-merged-checks`. Corrected final checks are
`/tmp/miren-stage184-corrected-checks` and `/tmp/miren-stage184-final-merged-checks`. The newly
supported length-only case checks its mutable metadata model; all other readonly model assertions
remain intact. No production semantic source correction followed the author freeze.

Stage 188 extends the private alignment-one zero-sized Box region to exact local ordinary
Copy/Freeze/no-drop nominal payloads with compiler size zero and alignment one. Complete original
product and zero-leaf certificates preserve Adt, generic and const identity through construction,
initialization, sharing, transfer, detached ghosts and drop. Every original child is checked,
including children beneath zero-length arrays. Weighted payload nodes share the existing cumulative
512-storage budget with allocations and mutable-slice backing. No allocator-success assumption,
numeric heap address or additional field permission is introduced.

Complete selected Box/Global templates retain their original typed signatures and effects.
Synthesized drop glue uses an exhaustive typed original-body grammar, including cleanup, coroutine,
constant-function and receiver checks. Actual selected user methods execute: Copy does not certify
Clone or equality. Unrecognized nominal inline construction, nonzero or aligned payloads, external
payloads, raw access and nested shared-field borrowing remain UNKNOWN. The original nested claim
stays unchanged; a separate owned-copy control proves payload correlation.

The twenty-root dedicated matrix yields seven PROVED, three REFUTED and ten UNKNOWN per host/ARM
O0/O2 profile. All eighteen original nominal controls are UNKNOWN under committed Stage 184.
An actual tag-body mutation
from 17 to 18 refutes the unchanged claim with selected body entries, query and model. Retained
foreign-helper MIR proves; genuine invoked-body omission remains MissingCompilerEvidence. Safe
native originals pass four tests and the unchanged mutation guard exits 101 at O0/O2 with
ten-second timeouts. Fresh adopted-parent evidence is at
`/tmp/miren-stage188-parent184-corrected-final-evidence`; historical provisional-parent sources,
binary and
captures remain at `/tmp/miren-stage188-provisional187-archive` with their original scope.

Historical fidelity preserves 188 unchanged entry/profile outcomes, including 72 completed pairs
and all 80 completed queries, models and obligation details. This includes 32 completed mutable
slice pairs and their 68 queries. Three unsupported Unit-suite/global controls retain Semantics
UNKNOWN with more precise payload diagnostics. Harness and manifest upkeep change only those
reasons; original fixtures and claims stay unchanged. Global P/R/U controls and actual-helper
mutation/native guard are at `/tmp/miren-stage188-global-corrected-after-evidence`.
The combined manifest
has 170 cases in 58 families. No assumptions, firmware rewrites, input caps or resource budget
increases are introduced.

Review also closed three storage-growth accounting gaps in raw locals, iterator-find temporaries
and async-factory storage. A 510-node weighted payload followed by three scalar raw-address
allocations proves under the preserved intermediate build but reaches ResourceLimit UNKNOWN
under the corrected build. A small raw-address control still proves. This is a budget correction;
raw permissions and legacy frame-only refusals are preserved. The weighted control is never run
as a native test.

Final isolated validation passes 764 Rust tests and 68 Python tests; fresh-main focused validation
passes 76 Rust tests and 68 Python tests. Formatting, lint, debug/release builds, dependency denial,
documentation and manual hooks pass in both. All 825 tracked files match byte for byte. Both
surveys yield 268 PROVED, 236 REFUTED and 176 UNKNOWN across four profiles. All 496 previously
completed roots retain identical outcomes, obligation details, queries, models and premises;
all 680 main/isolate results match with no diagnostic context differences. Fresh main release
captures at `/tmp/miren-stage188-main-release-final-evidence` match 100 complete original/mutant,
dependency and resource proof objects with 16 queries after explicit source/replay path mappings.
Global release captures at `/tmp/miren-stage188-global-final-evidence` match 16 proof objects and
eight queries. Native records retain their final corrected author execution scope. Source, input
and release hashes are verified. No production semantic correction followed the corrected
thirteen-path author freeze. Final documentation reflow leaves the validated code unchanged.

Stage 189 executes one whole incoming mutable u16 slice through an actual available safe Rust
child body. An exact callsite Copy or private occurrence-authenticated reborrow issues a
branch-local generation. The parent remains suspended until its owning child's normal Return;
current array data, conditions and initialization masks return together. Primitive scalar
helpers use an authenticated weak body-frame stack and release only their own frame. The owning
child alone revokes the grant and resumes the parent. Abort-only signatures and edges, original
types, available bodies and bounded combined body work are checked before operand effects.

Direct optimized PtrMetadata observes length under the exact original whole Root/Child source,
current generation and initialization mask. It grants no data reference or generic role Copy.
Root Move, nested child, shared/duplicate/escaping roles, unwind, induction and missing selected
bodies remain UNKNOWN. Active frames, mutable backing, weighted owned regions and ordinary
allocations share the existing 512-storage budget. No assumptions, input caps, firmware changes
or increased limits are introduced.

The 21-root dedicated matrix yields eight PROVED, two REFUTED and eleven UNKNOWN per host/ARM
O0/O2 profile; all exact sources are UNKNOWN under committed Stage 188. Both actual child and
scalar-helper mutations refute unchanged claims with actual body entries and a query/model on
the same failing obligation. Safe native originals pass two tests; both mutation guards exit 101
at O0/O2 with ten-second timeouts. Auxiliary evidence covers explicit mir-opt-level-zero staging,
strict unwind refusal and genuine retained/omitted foreign helper MIR. Current evidence is at
`/tmp/miren-stage189-final-evidence`; historical actual-184 source, binary and captures retain
their original scope in `/tmp/miren-stage189-parent184-history`. All 92 original/mutant proof
objects match after the controlled parent adoption.

Historical fidelity preserves 144 entry/profile statuses, models and premises, and all 124
completed queries. Twelve query-free UNKNOWN details change and are explicitly recorded;
no full diagnostic identity is claimed for them. The original direct child-call assertion
advances from UNKNOWN to PROVED in four profiles. Harness upkeep pins the actual child body;
three other old controls remain Semantics UNKNOWN with precise protocol refusals. Original
fixtures and claims stay unchanged. Global P/R/U and scalar-helper mutation/native controls are at
`/tmp/miren-stage189-global-after-evidence`. The combined manifest has 173 cases in 59 families.

Root validation passes 768 workspace Rust tests and 80 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. Initial full/focused stale iterator-reason failures remain in their original logs;
only the harness reason changes, supported by eight actual before/after reports preserving
Semantics UNKNOWN and unchanged fixture bytes. The fresh main release matches 116 dedicated
proof objects and 158 queries, plus 16 new global proof objects and 32 queries. Native executions
retain their final author scope explicitly. All 504 previously completed global pairs preserve
status, inputs, models, premises and obligation queries; append-only replay fingerprints are
excluded from that historical comparison. Of 692 current global pairs, 691 normalized proof
objects match exactly; one query-free
30-second UNKNOWN resource refusal differs only in its active call-stack context. All 829
tracked files are byte-identical.
Checks and ledgers retain their precise scopes under `/tmp/miren-stage189-*`.

Stage 190 derives one immutable private zero-sized layout fact from original nominal T,
recording exact compiler alignment A and target width. Complete Box/Global constructor and drop
certificates authenticate that fact against original types, Layout fields, arithmetic, ctpop,
nonnull sentinel and selected-body reachability. Size zero must pass checked target Layout
rounding, with nonzero power-of-two alignment. The Unit inline path keeps its exact A=1 fact.
The zero-size Global branch invokes no allocator or deallocator. No numeric address, raw
provenance, new borrowing right or allocation-success premise follows from the private region.

Ordinary local zero-leaf Copy/Freeze/noDrop type certificates, original const identity, complete
typed glue, occurrence checks, generations, liveness and weighted 512-storage accounting remain
mandatory. Nested shared-field access, nonzero payloads, external/enum/Drop/reference/raw/pattern
payloads and unsupported ownership transport remain UNKNOWN. No assumptions, input caps,
firmware changes or increased limits are introduced.

The 22-root dedicated matrix yields ten PROVED, four REFUTED and eight UNKNOWN per host/ARM
O0/O2 profile. The identical sources are all UNKNOWN under committed Stage 189. Positives cover
alignment 2/8/4096, natural alignment from zero-length u32 arrays, generic/nested owned copies,
transfer and drop. Actual custom Clone and Eq bodies execute and refute their false claims.
Changing Marker::tag from 17 to 18 refutes the original assertion, with actual selected/tag body
entries and a query/model on the same obligation. Safe native originals pass and unchanged
mutation guards exit 101 at O0/O2 with ten-second timeouts. Genuine retained/omitted foreign
helper MIR distinguishes PROVED from MissingCompilerEvidence; external payload policy remains
separate. Actual-parent evidence is `/tmp/miren-stage190-parent189-final-evidence`.

Historical scopes remain immutable, including actual-188 and pending-189 snapshots and binaries.
The actual-189 fidelity ledger preserves 348 of 356 old entry/profile outcomes, with all 156
previously completed pairs and 196 queries exact. Eight intended alignment promotions and sixteen
query-free UNKNOWN detail changes are recorded separately. The old Unit aligned_zero lacks Copy
and stays UNKNOWN; its original fixture is unchanged. The Copy-derived old nominal/global aligned
controls advance to PROVED. Narrow harness upkeep follows only those captured frontiers.

Global controls add an aligned Box assertion, its wrong claim and a Drop-payload UNKNOWN control.
Changing their actual tag helper refutes the original assertion and fails its native guard.
Commands, hashes and native/proof scopes are at `/tmp/miren-stage190-global-after-evidence`.
The combined manifest has 176 cases in 60 families.

Root validation passes 772 workspace Rust tests and 84 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. The initial author old-nominal reason failure remains in its original log; narrow root
harness upkeep follows actual four-profile evidence and leaves original fixtures unchanged.
The fresh main release matches 108 dedicated proof objects and 20 queries, plus 16 new global
proof objects and eight queries. Native executions retain their final author scope explicitly.
All 516 previously completed global pairs preserve status, inputs, models, premises and queries;
append-only replay fingerprints are excluded from that historical comparison. Of 704 current
global pairs, 702 normalized proof objects match exactly. Two query-free 30-second UNKNOWN
resource refusals differ only in their active call-stack context and are explicitly recorded.
All 831 tracked files are byte-identical between main and the isolated workspace. Checks and
ledgers retain their precise scopes under `/tmp/miren-stage190-*`.

Stage 191 extends the one incoming mutable-slice and whole-child protocol to exact signed
i8/i16/i32/i64/i128/isize and unsigned u16/u32/u64/u128/usize elements. Each backing carries an
immutable issued original element type, scalar codec and compiler byte-size/alignment certificate.
Reads, stores, selected child signatures, reborrow staging, SliceLen and PtrMetadata correlate
that exact type; matching SMT widths cannot substitute i32/u32 or target usize/u64 identity.
Detached Ghost observations retain frozen data, length and their issued certificate without
live read, write or borrowing authority.

Actual safe scalar descendants and complete core metadata bodies remain required. Existing
source initialization, generation, ancestor Weak Body stack, normal-return ownership and combined
512-storage/body-work budgets remain. u8 keeps its existing byte-model priority; Bool, Char,
Float, nominal elements and competing, split, shared or escaping leases remain UNKNOWN. No input
caps, new assumptions, hardware policies, firmware changes or increased limits are introduced.

The 113-root dedicated matrix yields 66 PROVED, 22 REFUTED and 25 UNKNOWN in each host/ARM O0/O2
profile. The identical sources under committed Stage 190 yield six PROVED, two REFUTED and
105 UNKNOWN; existing u16 controls were already supported. Changing the actual noinline i32
helper from word ^ 0 to word ^ 1 refutes the unchanged selected assertion with an actual helper
body entry and query/model on the failing obligation. Safe native originals pass two tests;
unchanged mutation guards exit 101 at O0/O2 with ten-second timeouts. Auxiliary evidence covers
explicit mir-opt-level-zero staging, unwind refusal and genuine retained/omitted foreign helper
MIR. Actual-parent captures are at `/tmp/miren-stage191-parent190-final-evidence`.

Historical actual-189 sources, binary and captures retain their original scope. A narrow wording
fix labels non-u16 Pending staging failures as mutable integer failures using the issued original
type; all u16 details remain unchanged. Forty query-free detail changes versus the prior author
binary are explicitly recorded, with no outcome, query, model or protocol change. Fresh fidelity
preserves all 232 old entry/profile pairs and completed queries, and all 84 old u16 child proof
objects are deeply identical. Compiler negatives exercise wrong original child/staging/metadata
types, layout, width/sign, codec, context and detached Ghost controls.

Global controls add an i32 child assertion, its wrong claim and a nested-child UNKNOWN frontier.
The actual scalar-helper mutation refutes the original assertion and fails its native guard.
Saved before/after evidence is at `/tmp/miren-stage191-global-before-evidence` and
`/tmp/miren-stage191-parent190-global-after-evidence`.
The manifest now has 179 cases in 61 families.

Root validation passes 775 workspace Rust tests and 87 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. The fresh main release matches 480 dedicated proof objects and 966 queries, plus 16 new
global proof objects and 32 queries. Native executions explicitly retain their actual-parent
author scope. All 528 previously completed global pairs preserve status, inputs, models, premises
and obligation queries; append-only replay fingerprints are excluded from that historical
comparison. Of 716 current global pairs, 715 normalized proof objects match exactly. One query-free
30-second UNKNOWN resource refusal differs only in active call-stack context and is recorded.
All 834 tracked files are byte-identical between main and the isolated workspace. Checks and
ledgers retain their precise scopes under `/tmp/miren-stage191-*`.

Stage 192 admits exact original Bool elements through the existing one mutable-root and
whole-child protocol. The immutable type/layout certificate checks raw Bool and compiler
size/alignment 1/1. Logical backing is Array(target usize, Bool); typed reads and stores preserve
same-context Boolean values. BV8 carriers, integer 0/1 replacements, wrong original types,
forged layouts and foreign contexts cannot supply Bool authority. No byte-validity assumption,
coercion, input cap or new borrowing right is added.

Detached Ghost retains its original frozen array, length and issued codec. Configured contract
length observations support exact Bool backing; executable Ghost indexing remains UNKNOWN.
Existing original-type, initialization, generation, parent suspension, selected child body,
normal-return, ancestor stack and weighted storage rules remain. Integer/u16 queries and diagnostic
wording retain their previous behavior. Only issued raw Bool Pending failures use the Boolean
label. Other elements, competing/split/shared/escaping leases and raw transport remain outside
this extension.

The 21-root dedicated matrix yields nine PROVED, four REFUTED and eight UNKNOWN per host/ARM
O0/O2 profile. Identical sources under committed Stage 191 yield one PROVED and twenty UNKNOWN:
the historical u8_unknown write control already works through ordinary writable Reference/Bytes
with arbitrary valid byte extent. It is no new Bool or byte capability. The original panic-format
control remains UNKNOWN at its scalar-frame frontier; a separate child assertion refutes.

Thirty-two fresh proof reports cover the ordinary matrix, actual data mutation, genuine
retained/omitted foreign child bodies and configured Ghost length P/R/index U controls. Changing
the actual replacement helper from !value to value refutes the unchanged claim with actual body
entries and a query/model on the same obligation. Safe native originals pass three tests; the
unchanged mutation guard exits 101 at O0/O2 with ten-second timeouts and valid 129-element arrays.
Actual-parent evidence is `/tmp/miren-stage192-parent191-evidence`.

Historical pending-191 sources, binary and captures retain their original scope. Fresh fidelity
compares 868 prior root/profile pairs: 864 outcomes and obligations remain unchanged, all 568
previously completed pairs and 1,236 queries match exactly, and four original bool_unknown controls
advance to PROVED. No old query-free diagnostic changes occur. Narrow root harness upkeep changes
only that expectation, leaving its original fixture intact.

Global controls add a Bool child assertion, its wrong claim and a nested-child UNKNOWN frontier.
Their actual helper mutation refutes the original claim and fails the native guard. An initial
unshipped assert_eq draft reached unsupported temporary shared references; that source and failed
capture remain immutable. The direct-assertion draft exercises supported typed reads with the same
equality claims. Before/after evidence is at `/tmp/miren-stage192-global-before-evidence` and
`/tmp/miren-stage192-parent191-global-after-evidence`. The manifest has 182 cases in 62 families.

Root validation passes 780 workspace Rust tests and 91 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. The fresh main release matches 108 dedicated proof objects and 158 queries, plus 16 new
global proof objects and 32 queries. Native executions explicitly retain their actual-parent
author scope. All 536 previously completed global pairs preserve status, inputs, models, premises
and obligation queries; append-only replay fingerprints are excluded from that historical
comparison. Of 728 current global pairs, 727 normalized proof objects match exactly. One query-free
30-second UNKNOWN resource refusal differs only in active call-stack context and is recorded.
All 837 tracked files are byte-identical between main and the isolated workspace. Checks and
ledgers retain their precise scopes under `/tmp/miren-stage192-*`.

Stage 194 admits exact original Char elements through the existing single mutable-root and
whole-child protocol. The issued type/layout certificate checks raw Char and compiler layout 4/4.
Logical backing is Array(target usize, BV32). Reads use the existing valid Unicode observation
decoder; writes prove the actual replacement is a Unicode scalar before Store. Invalid surrogate
or above-maximum replacements are refused without repairing data or adding validity premises.
Wrong original u32/i32 types, layout, signedness, width, sort and foreign contexts are refused.
Transactional negatives leave data, phase and generation unchanged.

Scalar Char root companions reuse the existing compiler-typed Unicode input producer. Selected
child/helper arguments and results retain exact type, validity, actual body and effect checks.
Detached Ghost length supports the original issued Char codec; executable Ghost indexing remains
UNKNOWN. Existing initialization, generation, parent suspension, normal return, alias policy and
storage budgets remain. Float, shared element methods, raw transport, competing/escaping/split
leases and nested mutable children receive no new rights.

The dedicated 24-root matrix yields eleven PROVED, four REFUTED and nine UNKNOWN per host/ARM
O0/O2 profile. Identical sources under committed Stage 192 yield one PROVED and twenty-three
UNKNOWN. The existing write-only u8 control remains PROVED on its ordinary byte path. An original
shared-element method remains UNKNOWN; a distinct copied-value method proves its actual body.
Thirty-two fresh proof reports cover the matrix, real helper data mutation, retained/omitted
foreign bodies and Ghost length P/R/index U controls. Changing the actual helper else branch from
'A' to 'C' refutes the unchanged claim with actual body entries and a query/model on the same
obligation. Safe native originals pass three tests; the mutation guard exits 101 at O0/O2 with
ten-second timeouts and valid 129-element arrays. Actual-parent evidence is
`/tmp/miren-stage194-parent192-evidence`.

Historical pending-192 evidence retains its original scope. Controlled committed-192 adoption
changes only parent documentation; all eight feature source paths remain unchanged. Fresh fidelity
compares 952 old root/profile pairs: 944 retain exact statuses and obligations, four original
integer-suite char_unknown controls advance to PROVED, and four Bool-suite char_unknown controls
remain UNKNOWN with a precise metadata-only refusal detail. All 624 previously completed pairs
and 1,356 queries match exactly. Narrow harness upkeep changes only those expectations, leaving
original fixtures intact.

Global controls add a Char child assertion, wrong claim and nested-child UNKNOWN frontier.
Their actual helper mutation refutes the unchanged assertion and fails its native guard. Saved
before/after evidence is at `/tmp/miren-stage194-global-before-evidence` and
`/tmp/miren-stage194-parent192-global-after-evidence`. The manifest has 185 cases in 63 families.
Root validation passes 785 workspace Rust tests and 95 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. The fresh main release matches 120 dedicated proof objects and 264 queries, plus 16 new
global proof objects and 56 queries. Native captures explicitly retain their actual-parent author
scope. All 544 previously completed global pairs preserve status, inputs, models, premises and
obligation queries; append-only replay fingerprints are excluded from that historical comparison.
Of 740 current global pairs, 739 normalized proof objects match exactly. One query-free 30-second
UNKNOWN resource refusal differs only in active call-stack context and is recorded. All 840
tracked files are byte-identical between main and the isolated workspace. Checks and ledgers
retain their precise scopes under `/tmp/miren-stage194-*`.

Stage 193 adds a certified constant byte copy into a bounded prefix of one incoming mutable
byte slice whose overall length remains symbolic. The logical array and allocation are retained;
sequential Stores replace only the selected cells after current liveness, initialization, writable
permission, source provenance and nested-prefix bounds are checked. A single commit applies the
validated update. The existing fixed-capacity byte path retains its priority and formulas.

The replacement must be an authenticated compiler-promoted immutable byte constant of at most
128 bytes. The limit bounds replacement analysis; it does not restrict the incoming slice length.
Complete selected core copy and precondition bodies, actual intrinsic operands, byte layout and
normal-return edges are checked. Source bytes and their original reaching definition must agree.
Executed raw, unsafe, opaque, indirect or trusted transport monotonically revokes the new incoming
origin eligibility. Metadata-only compiler length observations grant no address authority.
Missing bodies, returned or dynamic sources, shifted ranges, competing incoming references and
unsupported raw transport remain UNKNOWN. No allocator or hardware premise is added.

The dedicated 21-root matrix yields nine PROVED, four REFUTED and eight UNKNOWN per host/ARM
O0/O2 profile. The identical final source under committed Stage 194 yields one PROVED, two
REFUTED and eighteen UNKNOWN. A 128-byte payload proves; a 129-byte payload reports the resource
frontier before additional evaluation of the source constant. Ordinary call operands are
evaluated first. Existing arbitrary-length byte operations retain their old path. Actual helper
data mutation refutes the unchanged claim with a query and model on the same obligation. Safe
native originals and mutation guards retain separate compiler-only proof scopes.

A foreign helper compiled at O0 with retained MIR proves under caller O0/O2. Compiling the
retained helper at O2 exposes unsupported raw-pointer transport and remains UNKNOWN. Omitting
the O0 selected helper body yields missing-compiler-evidence UNKNOWN under caller O0/O2. These
actual twelve dependency reports preserve the unchanged source and compiler flags; the optimized
refusal is not relabeled as a successful body check.

Global controls add a correct constant prefix, wrong claim and helper-produced source UNKNOWN.
Changing the actual copied payload from [17, 19] to [17, 23] refutes the original assertion and
fails the unchanged native guard at O0/O2. Safe native arrays have 129 elements and check the
untouched tail. The manifest has 188 cases in 64 families. Scoped global evidence is retained at
`/tmp/miren-stage193-parent194-global-before-evidence` and
`/tmp/miren-stage193-parent194-global-after-evidence`.
Root validation passes 789 workspace Rust tests and 102 focused Rust tests, with 68 Python
checks in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks
pass. Both surveys report 300 PROVED, 260 REFUTED and 192 UNKNOWN outcomes across four profiles.
The fresh repaired main release matches 100 dedicated proof objects and 260 queries, plus 16
global proof objects and 60 queries. Safe native captures explicitly retain their actual-parent
author scope. All 552 completed global pairs preserve status, inputs, models, premises and
obligation queries; append-only replay fingerprints are excluded from the historical comparison.
All 752 current normalized global proof objects match exactly, including query-free resource
refusals. All 860 tracked files match byte-for-byte across main and the isolated workspace. The
initial custom-solver replay and its counterexample-model differences are preserved separately;
a corrected automatic-solver-mode replay matches whole proof objects without model
normalization. The original failed full run remains separate from corrected validation.
Corrected checks and ledgers are retained under `/tmp/miren-stage193-repaired-*`.

Initial full validation exposed an unnamed core closure in the new copy candidate detector.
The detector now checks Item and named Fn/AssocFn definition kinds before querying item_name;
ordinary closure execution is unchanged. The original failed full run and earlier freezes remain
preserved separately. The unchanged closure regression suite passes all three tests, and fresh
repaired captures match 88 prior feature proof objects with 244 queries and 140 old proof objects
with 356 queries exactly. Corrected full validation passes all required checks.

Stage 195 admits exact original f32/f64 elements through the existing single mutable-root and
whole-child protocol. Each compiler type/layout certificate issues a BV32/BV64 logical array;
reads retain both the numerical Float term and exact raw bits. Writes and scalar child boundaries
require private authority for that exact numerical/raw pair before proving correspondence and
committing effects. Numerical equality alone cannot authenticate a copied NaN payload. Actual
arithmetic may select a permitted NaN encoding; it does not promise one fixed payload.

Pair metadata is issued only by authenticated decoding, actual arithmetic materialization and
paired copy/negation/absolute-value/selection paths. Wrong original types/layouts, missing or
changed encoding bindings, forged raw payloads, foreign contexts and absent issuers are refused
transactionally. Metadata work is precharged with 512 nodes and depth 16. Exhaustion leaves old
producers intact and refuses unavailable new consumer authority. Existing storage, lifetime,
generation, parent suspension and normal-return budgets remain unchanged. Ghosts observe exact
length; executable Ghost indexing remains UNKNOWN.

Only an actual new incoming mutable Float root activates the optional metadata namespace.
Inactive hooks return before allocating solver terms. This preserves old read-only Float query
node identifiers and all existing integer/Bool/Char formulas. No raw memory, allocator, device,
shared view, competing root, nested mutable child or reference-return authority is added.

The final 26-root matrix yields sixteen PROVED, five REFUTED and five UNKNOWN per host/ARM
O0/O2 profile. Identical sources under committed Stage 193 yield twenty-six UNKNOWN. Thirty-two
reports cover before/after, real helper data mutation, retained/omitted foreign bodies and Ghost
length P/R/index U controls. Changing the actual helper else branch from 1.0 to 3.0 refutes the
unchanged claim with actual body entries and a query/model on the same obligation. A genuine
missing selected helper body remains missing-compiler-evidence UNKNOWN. Native originals pass
three tests with valid 129-element arrays; mutation guards exit 101 at O0/O2 with ten-second
limits. A permitted arithmetic NaN-encoding counterexample is not a guaranteed native panic.

Controlled committed-193 adoption preserves the complete byte-copy implementation and its
closure definition-kind correction. One new parent test Engine literal gains the default Float
registry; no parent production behavior changes. Earlier pending-194 and actual-194 sources,
binaries, captures and fidelity remain separately scoped. Fresh actual-parent fidelity covers
1,240 old root/profile pairs: 1,236 statuses stay unchanged, four integer-suite Float controls
advance from UNKNOWN to PROVED, and twelve Bool/Char Float controls remain query-free UNKNOWN
at a later metadata-only refusal. Those twelve include input, replay and body provenance changes
as new typed Float issuance reaches farther; they are not whole-object diagnostic-only equality.
The 1,224 strict status/obligation pairs remain unchanged. All 840 previously completed whole
proof objects and 1,980 completed queries match exactly, including 48 old read-only Float pairs
and 52 queries. Old fixtures remain intact; narrow harness upkeep changes only status/reason pins.

Global controls add a finite numerical Float child assertion, wrong claim and nested-child
UNKNOWN frontier. The source guard is explicit Rust code; no analysis input cap or environmental
premise is added. Actual helper +0.0-to-+1.0 mutation refutes the unchanged assertion and fails
its safe 129-element native guard. This control claims numerical equality, with NaN payload and
signed-zero bit behavior tested separately in the dedicated matrix. Saved actual-parent globals
are `/tmp/miren-stage195-parent193-global-before-evidence` and
`/tmp/miren-stage195-parent193-global-after-evidence`. The manifest has 191 cases in 65 families.
Root validation passes 796 workspace Rust tests and 109 focused Rust tests, with 68 Python checks
in each workspace. Formatting, Clippy, debug/release builds, deny, docs and manual hooks pass.
Both surveys report 304 PROVED, 264 REFUTED and 196 UNKNOWN across four profiles. All 560
previously completed global pairs preserve status, inputs, models, premises and obligations;
append-only global replay fingerprints are excluded from this historical comparison. All 762
current normalized global proof objects match exactly; two query-free ResourceLimit objects differ
only in call-stack or exact closure/block time-budget context, recorded separately. All 864
tracked files match byte-for-byte.

The fresh main release matches 128 dedicated whole proof objects and 276 queries, plus 16 global
objects and 32 queries. Original actual-parent native source/executable hashes and 0/101 results
remain explicitly adopted, rather than relabeled as fresh main executions. The initial replay used
automatic solver selection while the author had explicitly selected the solver; its 24 model-only
differences remain archived. Corrected same-mode replay matches complete objects without model
normalization. Final checks and captures are retained under `/tmp/miren-stage195-*`.

Stage 197 shares the compiler-free mapping from primitive slice codecs to logical sorts. Bool,
Char, admitted integer widths and f32/f64 keep their existing representations. Unsupported widths
remain rejected. The proof-local Result wrapper and contract diagnostics are unchanged. The Ghost
codec lookup stays inside the original short-circuit data-sort expression, after length/context
checks, so competing malformed metadata retains the same error priority.

This helper constructs no solver term, compiler certificate, source evidence or permission. It
changes no lease, transaction, original type/layout gate, Float pair authority, public issuer,
Debug representation or budget. Four author paths change; all 860 other committed-parent paths
remain exact. New malformed Ghost tests exercise valid codecs, wrong sorts and contexts, target
widths, unsupported widths, indexing refusal and competing error priority. Changing the Bool
codec to BV8 makes the actual regression test fail; the original source is restored.

Fresh actual-parent fidelity compares 1,368 full proof objects exactly, including 424 UNKNOWN
objects and their full input, replay and body provenance. Of those, 372 are query-free and 52
contain 64 partial queries. All 944 completed objects and their 2,252 queries match; all 2,316
queries match without node renumbering or model normalization. There are no intended promotions,
diagnostic changes or exceptions. Genuine missing bodies remain UNKNOWN; Ghost length and actual
helper mutations retain their P/R/U outcomes. Safe native originals pass three tests and actual
129-element mutation guards exit 101 at O0/O2 under ten-second limits.

The initial baseline-only capture's generic planned-equality label is clarified separately; raw
reports and earlier failed test/script setup checks remain preserved. Final author evidence is
`/tmp/miren-stage197-parent195-query-fidelity`, `/tmp/miren-stage197-parent195-fp-fidelity` and
`/tmp/miren-stage197-aux-fidelity`. Stage 196 is absent from this scope. No global fixture or
manifest case is changed; the baseline remains 191 cases in 65 families.
Root validation passes 797 Rust tests in the full worktree and 114 focused tests in main,
plus 68 Python tests, formatting, lint, debug/release builds, dependency checks, docs and hooks.
Both surveys retain 304 PROVED, 264 REFUTED and 196 UNKNOWN outcomes. All 568 previously
completed root/profile pairs match in both surveys. Of 764 current full objects, 763 match;
the ARM optimized unbounded fold has only a query-free time-budget call-stack difference.
Its status, category, identical detail and every remaining field match; no query or model exists.
Fresh main release replay matches all 1,368 full objects and all 2,316 queries after explicit
source-path aliases only. Fingerprints, models, queries, node IDs and diagnostics remain exact.
Native evidence is adopted with verified source/executable hashes and its original execution
scope. The initial path-only comparison failure is retained separately. Final documentation
checks run after this prose update; no production code changes after validation.

Stage 196 supports a checked `Range<usize>` of one incoming mutable u16 slice handed immediately
to one direct synchronous child. Complete selected core range wrapper and SliceIndex bodies
certify `start <= end <= original length`, pointer offset, view extent and the normal return.
The original valid Rust extent prevents address-size overflow without limiting input length.
Two actual compiler reborrows authenticate the current private staging tip and one generation.
A branch-local descriptor binds original backing, offset, view length, certificate and owner.

Child indices are proved against the view length and translated into the same current backing
array. Normal authenticated owner Return removes the descriptor and resumes the parent with
current data. Parent suspension, exact body identity, current initialization and storage budgets
remain required. Pending issuance precharges seven slots under the existing 512-node limit.
Whole-slice paths keep their original terms. Ghost metadata exposes view length; data indexing
remains UNKNOWN. No retained view, nested interval, split, raw pointer, reference return, induction,
other range or non-u16 interval codec is admitted. Missing actual bodies remain UNKNOWN.

The current parent is committed Stage 197. All 859 other parent files match exactly; fourteen
feature files are unchanged from the earlier Stage 195 capture, while README retains both stages.
Focused formatting, lint, compiler lifecycle and 27 related integration tests pass. Dedicated
host/ARM O0/O2 reports move from 1 PROVED and 12 UNKNOWN roots to 8 PROVED, 3 REFUTED and 2 UNKNOWN.
Changing the actual child from `word ^ 0` to `word ^ 1` refutes the unchanged selected claim.
Genuine retained dependency bodies prove; omitted selected bodies stay UNKNOWN.

All 1,092 prior full proof objects and 2,124 queries match exactly, including 60 partial queries
in UNKNOWN objects. The original direct-u16 induction flags are retained. Earlier captures and
setup failures remain preserved with their historical scope. Safe 129-element native originals
and unchanged mutation guards are adopted with verified source, executable and output hashes;
the original O0/O2 exits are 0 and 101 under ten-second execution limits.

Three append-only global controls bring the inventory to 194 cases in 66 families: valid child
write, wrong claim and unsupported nested interval. Fresh actual-parent controls are UNKNOWN;
new captures produce PROVED, REFUTED and UNKNOWN in all four profiles, plus REFUTED for the helper
mutation. Fresh global native originals pass and the unchanged guard fails at O0/O2. The 16 global
full objects and 72 queries match the historical capture after explicit typed source-path aliases.
An initial missing working-directory alias assertion is retained, without changing any query.
Root validation passes 801 Rust tests in the full worktree and 118 focused tests in main,
plus 68 Python tests, formatting, lint, debug/release builds, dependency checks, docs and hooks.
The initial focused lifecycle filter matched zero tests; its 117-test log and status are retained.
The corrected named lifecycle test actually runs and passes, giving 118 total without a source
or limit change. Both surveys retain 308 PROVED, 268 REFUTED and 200 UNKNOWN outcomes. All 568
previously completed pairs match in both surveys. Of 776 current full objects, 774 match exactly;
two query-free unbounded-fold timeouts differ only in their recorded call-stack/block context.
Their UNKNOWN status, resource category and every remaining field match; no query or model exists.

Fresh main release replay matches 1,172 full objects and all 2,438 queries after explicit typed
source-path aliases only. Automatic solver mode is retained for dedicated, foreign and old codec
captures; global captures retain their separate explicit custom mode. Fingerprints, query node
identifiers, models and non-path fields remain exact. Native evidence is adopted separately with
verified source, executable and output hashes and its original execution scope. Final docs and
hooks run after this prose update; production source stays at the validated freeze.


## Stage 200: correlated known-target function tables

Symbolic indices into initialized owned arrays of safe Rust `fn(u16) -> u16` pointers now
retain their exact index-to-target relation. Feasible branches execute the actual available
callee MIR and carry its returned memory. Dispatch consumes each original operand once;
it does not replay preceding statements. Original compiler array and signature types,
current source elements, initialization, index domain and recorded owned field types are
checked before issuing a choice. The existing sixteen-element and shared execution/registry
budgets remain. Opaque targets, other signatures, shared input tables, reference transport,
configured target contracts and unsupported unwind paths remain UNKNOWN.

The dedicated nine-root matrix has four PROVED, one REFUTED and four UNKNOWN results in each
host/ARM O0/O2 profile. Changing the actual helper body or table order refutes the unchanged
assertion in all four profiles and fails finite native tests. Genuine external archives prove
only with retained MIR for feasible targets; omitted feasible bodies remain missing-evidence
UNKNOWN. Solver-proved infeasible omitted targets are pruned. The original `assert_eq!` scout's
missing panic-formatting body remains separately recorded UNKNOWN, without a replacement summary.

Three append-only global controls bring the manifest to 197 cases in 67 families, with
78 PROVED, 68 REFUTED and 51 UNKNOWN per profile. The 194 old cases retain 1,452 emitted queries;
775 of 776 full proof objects are identical. One query/model-free unbounded-fold timeout changes
only its diagnostic prefix, with every residual field exact. Evidence is retained under
`/tmp/miren-stage200-global-before-evidence` and `/tmp/miren-stage200-global-after-evidence`.

All 805 workspace tests and 68 Python tests pass, alongside formatting, Clippy, release builds,
Cargo deny and manual hooks. All 878 root/isolated source files match. Fresh root release checks
retain 914 of 916 full proof objects exactly and all 1,580 emitted queries: 1,436 from completed
roots and 144 partial queries from UNKNOWN roots. Two named query-free fold timeout contexts
retain exact residual proof fields; their raw prefixes and call chains are preserved in
`/tmp/miren-stage200-root-global-evidence`. This stage adds no assumptions or hardware model.

## Stage 201: original integer function-table signatures

Bounded owned tables now execute actual safe Rust `fn(T) -> T` targets for all twelve integer
types. Original compiler types, widths and signs remain authenticated separately; equal machine
sorts cannot substitute pointer-sized and fixed-width types. The original source, storage,
initialization, index, target-body and once-only operand checks and work budgets remain intact.
Other signature kinds, arities and ABIs remain outside this domain.

The permanent typed fixture has 69 roots per profile: 25 PROVED, 25 REFUTED and 19 UNKNOWN.
All-type helper and table-order mutations break the unchanged claims in compiler and native
execution. Genuine retained helpers execute their bodies; feasible omitted helpers remain UNKNOWN,
while solver-proved infeasible branches are pruned. All cases run at host/ARM O0/O2.

Three append-only isize controls bring this actual Stage 200 parent to 200 cases across 68 families:
79 PROVED, 69 REFUTED and 52 UNKNOWN per profile. The mismatched result signature remains UNKNOWN
with its observed unclassified reason, without changing the producer classification. Old global
queries and unchanged legacy proof objects are preserved, with only explicitly recorded query-free
thirty-second fold diagnostic contexts. This stage adds no assumptions or trusted calls.

Repository validation passes 809 Rust tests and 68 Python tests, formatting, Clippy, release builds,
dependency checks and manual hooks. Initial metadata-only harness failures remain archived.
The immutable owner release matches 1,715 of 1,716 FULL objects and all 2,672 queries against
debug. The sole difference is a query-free ARM O2 fold execution-budget context; all residual
fields match. Fresh release compiler mutations refute all four profiles and native originals
pass while mutants fail. Frozen sources and raw evidence are retained in
`/tmp/miren-stage201-corrected-core-freeze.json` and `/tmp/miren-stage201-release-fidelity`.

## Stage 198: one nested whole-u16 child lease

One direct whole-u16 child can hand its current slice to one synchronous nested child. The distinct
hierarchy namespace is selected at the original root Call; current compiler staging occurrences,
source initialization, original types and live backing remain mandatory. The parent is suspended
until normal child Return publishes current Memory. Persistent issuance and observation counters
reject stale handles, metadata and returned-memory rollback. Dormant primitive calls authenticate
the original compiler operand path and exact caller/selected body before ordinary execution. No
split, retained view, deeper hierarchy, reference return, interval or non-u16 grant is added.

This checkpoint uses actual Stage 200 parent `c86bc0ff48c1d6c537d68571f76645d4ef8e0594`. The
immutable final analyzer is `/tmp/miren-stage198-final-analyzer`; source and scoped compiler
evidence are pinned by `/tmp/miren-stage198-final-core-freeze.json` and
`/tmp/miren-stage198-final-handoff.md`. The dedicated twenty-root matrix is 9 PROVED, 4 REFUTED and
7 UNKNOWN in host/ARM O0/O2. Actual scalar-data mutation refutes the unchanged claim in all four;
safe native originals pass and mutation guards exit 101 at O0/O2 across finite sizes 0..=128 and a
129-element guard. Omitted selected foreign bodies remain MissingCompilerEvidence UNKNOWN; retained
optimized foreign bodies with unsupported store shapes remain UNKNOWN rather than being summarized
from an inventory.

Two unchanged old nested-u16 harness cases and the old global scoped_mutable_nested_unknown case now
prove; their source bodies are preserved. Three append-only global controls add nested-write PROVED,
wrong-claim REFUTED and deeper-child UNKNOWN. The historical actual200 upkeep manifest had
200 cases in 68 families,
expecting 80 PROVED, 69 REFUTED and 51 UNKNOWN per profile. New global payload mutation changes only
nested_whole_word from `word ^ 0` to `word ^ 1`; actual compiler and native guards reject the
unchanged claim. Captures are `/tmp/miren-stage198-global-evidence-final` and
`/tmp/miren-stage198-global-native-final`; the earlier failed no_std native compile is retained.

Old-family replay preserves 1136 of 1144 whole proof objects; only eight intended nested-u16
UNKNOWN-to-PROVED profile results change, with all 2316 old emitted queries exact. Old global replay
preserves 782 of 788 objects, adds four corresponding promotions and records two query-free host
ResourceLimit timing-context differences. All 1468 old emitted global queries remain exact.
Automatic captures strip MIREN_*; custom global pairs use the same explicit Z3 v4.15.4. Original
reports, scopes, diagnostic details and failed captures remain immutable. Final required full/main
validation, final documentation hooks and any later controlled parent adoption remain pending; this
paragraph claims the scoped author evidence, not a completed commit.


Controlled adoption onto actual Stage 201 parent
`c0d47e17238cdbf8a269d83a34838c303fbe36a2` preserves all hierarchy production bytes and
868 disjoint parent files. The current append-only manifest contains 203 cases across 69 families,
expecting 81 PROVED, 70 REFUTED and 52 UNKNOWN per profile. Fresh actual201 compiler captures and
raw comparisons are under `/tmp/miren-stage198-parent201-final-evidence`,
`/tmp/miren-stage198-parent201-fidelity` and `/tmp/miren-stage198-parent201-global-fidelity`.
The dedicated native fixture is byte-identical to the historical source; its historical executions
remain explicitly scoped. Global native controls were rerun against the new complete source in
`/tmp/miren-stage198-parent201-global-native`. The fresh source freeze and handoff are
`/tmp/miren-stage198-parent201-source-freeze.json` and
`/tmp/miren-stage198-parent201-handoff.md`. Root integration and validation remain pending.


Frozen actual201 owner validation passed all 813 workspace Rust tests, 68 Python tests, formatting,
lint, release, dependency checks, documentation, example checks and manual hooks. The fresh survey
of 203 cases
across four profiles matched 81 PROVED, 70 REFUTED and 52 UNKNOWN per profile.
The sealed owner release `/tmp/miren-stage198-parent201-release-analyzer` matches 2067 of 2068
reviewed-debug whole proof objects and all 4034 emitted queries. The one query-free host O0 fold
ResourceLimit detail-prefix difference retains the same status, category and 30-second execution
limit; raw reports are preserved without normalization. Full owner logs, survey and release
comparisons are `/tmp/miren-stage198-parent201-full-checks`,
`/tmp/miren-stage198-parent201-full-survey` and `/tmp/miren-stage198-parent201-release-fidelity`.
Final owner source is sealed by `/tmp/miren-stage198-parent201-final-owner-source-freeze.json`.
Root integration, fresh main validation and commit readiness remain separate pending gates.


Historical Stage 199 actual196 source/focused checkpoint (before actual200 adoption):

Stage 199 admits a bounded readonly NonZero niche domain: exact `Option<NonZero<u16>>` and ordinary
local two-variant empty/payload enums with the compiler's zero-only niche. Every original wrapper,
associated restricted inner, variant, layout and field is certified even under zero-length arrays.
One unsigned16 column supplies the legal tag and correlated latent payload. A zero latent payload is
never repaired into a standalone NonZero. Typed projections authenticate original declarations and
raw recorded field types; standalone operands and helper arguments/returns prove nonzero under
existing conditions. The selected core getter requires its available complete instantiated body;
this certificate is reported separately from actual helper body execution.

Source authentication charges every type and variant, including empty variants, with one cumulative
512-work detector budget and depth 16. Pointer niches, other niche widths, mutable niches,
membership, equality and new-shape Horn reconstruction remain unsupported. Existing source and
single-root policies remain unchanged. A supported producer reaching unsupported whole membership
supplies the global UNKNOWN control; genuine omitted foreign helper MIR is tested by the separate
dual-rlib suite.

On actual committed Stage 196, the unchanged final 27-source baseline is UNKNOWN in every profile.
Enabled host/ARM O0/O2 reports contain 12 PROVED, 4 REFUTED and 11 UNKNOWN roots per profile. The
actual selected helper mutation refutes the unchanged claim with its body entry and a query/model;
finite 129 native originals exit 0 and mutant guards exit 101 at O0/O2 under ten-second limits. No
MAX-length native experiment or invalid custom MIR execution is used. Retained dependency helpers
prove; genuine omitted selected helper bodies remain UNKNOWN with MissingCompilerEvidence.

The original tagged, Bool and Char niche fixtures each advance only their NZ16 control to PROVED,
with all four unchanged-source reports preserved before harness-only upkeep. All other 908 full old
proof objects match exactly: 648 completed pairs, 568 completed queries and 596 queries including
partial UNKNOWN obligations. Models, query node IDs, inputs/replay and body provenance are
unchanged. Detector accounting corrections, earlier disabled checkpoints and stale harness failures
remain preserved. Three append-only global cases give a candidate 197-case, 67-family manifest,
expecting 78 PROVED, 68 REFUTED and 51 UNKNOWN per profile. Their P/R/U and actual-helper mutation
controls pass all four profiles, with safe original/mutant native 0/101 evidence. Core/source review
is complete; parent adoption, full-stage surveys and required root validation remain separate
pending work.

Historical Stage 199 actual200 adoption began on committed Stage 200 c86bc0f in a separate owner.
All Stage 200 source and global cases remain; the three Stage 199 cases append afterward.
The combined candidate has 200 cases in 68 families, expecting 79 PROVED, 69 REFUTED and
52 UNKNOWN per profile. Fresh global captures confirm the three new P/R/U controls in all profiles.
Original actual196
archives retain their original source, binary, solver and native scopes. Refreshed actual200
compiler, source and fidelity evidence now confirm the bounded source checkpoint; final source
review and root validation remain required.


Stage 199's new owner preserves committed Stage 201 c0d47e1 and its complete 200-case prefix.
Three NZ16 controls bring the manifest to 203 cases in 69 families, with 80 PROVED,
70 REFUTED and 53 UNKNOWN per profile. Owner validation passes 813 Rust tests, 68 Python tests,
formatting, lint, debug and release builds, dependency checks, documentation and manual hooks.
The fresh release retains all 1,524 scoped full proof objects and 1,344 queries exactly.
Among 812 global comparisons, 810 full objects match exactly; only the host O0 and ARM O2
query-free, 30-second ResourceLimit fold call chains differ. All other fields and all 1,496
queries match. Raw differences remain recorded without normalization or budget changes.
Eight fresh safe native controls retain original exit 0 and helper-mutant exit 101 at O0/O2.
Root integration and fresh-main validation remain separate readiness gates.
The successful actual200 809-Rust/68-Python history and its release captures retain their
original scope; they are not relabeled as Stage 201 captures.


Stage 199's new owner preserves committed Stage 198 e4ffe01 and its complete 203-case prefix.
Three NZ16 controls bring the manifest to 206 cases in 70 families, with 82 PROVED,
71 REFUTED and 53 UNKNOWN per profile. Owner validation passes 817 Rust tests, 68 Python tests,
formatting, lint, debug and release builds, dependency checks, documentation and manual hooks.
The fresh release retains all 1,604 scoped full proof objects and 1,480 queries exactly.
Among 824 global comparisons, 822 full objects match exactly; only the host O2 and ARM O0
query-free, 30-second ResourceLimit fold contexts differ. ARM O0 also changes the context
prefix of the same timeout detail. All other fields and all 1,524 queries match.
Raw differences remain recorded without normalization or budget changes.
Eight fresh safe native controls retain original exit 0 and helper-mutant exit 101 at O0/O2.
Root integration and fresh-main validation remain separate readiness gates.
The successful actual201 validation and release captures above retain their historical
source, binary, native and solver scopes. They are not relabeled as actual198 validation.


## Stage 202: independently typed integer function tables

Known owned tables admit safe Rust `fn(A) -> R` targets when both original compiler types are
primitive integers. All twelve input types combine with all twelve output types, including signed
casts, narrowing and pointer-width conversions. Argument and result certificates retain their
independent original type, width and signedness; equal SMT sorts do not make Rust types
interchangeable. The actual available target body performs the conversion and produces its result.

Calls authenticate the original full function signature, actual MIR call and operand/destination
fields before execution. They consume a moved argument once, check each actual returned integer
against the result certificate, and retain the current returned memory. Existing ownership,
initialization, index correlation and table size/registry bounds still apply. No result is inferred
from the function signature, and no new assumption or trusted call is added.

The dedicated compiler fixture checks all 144 pairs on host and ARM at O0 and O2, with correct,
incorrect and opaque-target assertions. Actual helper and table-order mutations refute the
unchanged correct assertions. Native boundary controls pass for originals and fail for mutations.
Genuine dependency archives test retained and omitted MIR: feasible missing bodies remain UNKNOWN,
while an infeasible missing target does not block execution of an available local target.

Two unchanged earlier mismatched-return assertions now produce counterexamples: the global
`integer_function_table_signature_unknown` and dedicated `result_unknown` both select a second
body that changes the result's low bit. Native witnesses also fail those original assertions.
Their names and assertions remain unchanged. Boolean, character, floating, refinement/reference
and aggregate signatures, unsupported ABIs and arities remain outside this integer-table extension.

The independent Stage 202 owner on actual Stage 198 `e4ffe01` passes 817 Rust tests,
68 Python tests and all 21 required checks, including the twelve current example checks.
Its fresh debug/release comparison checks 8,044 proof pairs: 8,041 full objects and all
11,546 emitted queries match exactly. Three recorded query-free, 30-second ResourceLimit
fold contexts differ; all other fields match. Twelve native controls retain their expected
exits and test counts. These owner results retain their actual parent and source scope.

Stage 202 is composed onto committed Stage 199 `74c0c1b`, preserving its NonZero behavior and
complete 206-case prefix. Fresh combined host/ARM O0/O2 surveys measure 209 cases in 71 families,
with 83 PROVED, 73 REFUTED and 53 UNKNOWN per profile. Combined validation passes 821 Rust tests,
68 Python tests and all 22 checks, including debug/release builds and twelve example checks.
Fresh native controls rebuild twenty executables: eight exit 0 and twelve expected mutants or
unchanged false assertions exit 101, with exact test counts and ten-second limits.

The combined-parent debug comparison checks 8,836 pairs: 8,815 full objects and all 11,466
unchanged queries match. Twenty specific proof changes record the four-profile global controls
and the unchanged earlier mismatched-return counterexamples. One named query-free ResourceLimit
fold context differs, with all other fields exact. Fresh combined debug/release comparison checks
8,836 pairs: 8,834 full objects and all 11,498 emitted queries match.
2 recorded query-free, 30-second ResourceLimit fold context differences retain all other
fields exactly. Raw contexts remain recorded without normalization, assumptions or budget changes.
Earlier actual Stage 201 and Stage 198 captures retain their historical source and binary scopes.


Stage 203 extends the existing whole-slice nested hierarchy to original plain signed integers and
unsigned integers except u8. Issued original type, layout and codec remain correlated at every
staging, selected signature and current backing boundary. Same-sort types never substitute for
one another. Existing generations, owner release, bounds, masks and storage limits stay intact;
Bool, Char, Float, checked intervals, deeper nesting and retained references remain unsupported.

The actual Stage 202 parent is `ebf857b1ab349a46dff213745ed336db26a47718`. Its function-table pairs
and NonZero models remain intact. Historical Stage 203 actual198 captures stay separately scoped.
The new safe 88-root fixture measures 55 PROVED, 22 REFUTED and 11 UNKNOWN per host/ARM O0/O2
profile. Actual scalar helper mutations refute all eleven integer claims with body entries,
queries and models. The retained foreign body succeeds at library O0; the genuine O2 store shape
and omitted selected bodies retain precise UNKNOWN results. No compiler inputs are bounded by the
finite 129-element native checks.

Fresh comparison checks all 1,144 earlier proof objects: 1,104 remain exact and forty named
integer-nested cases become PROVED. All 2,328 earlier emitted query prefixes remain exact. The
original u16 fixture retains all u16 objects and 136 query prefixes; its signed32 control becomes
PROVED. All 1,836 original current-parent NonZero and integer-pair objects and 2,396 queries match
exactly. Old fixtures and assertions stay unchanged; only measured nested expectations are updated.

Three appended global controls test nested i32 data replacement and sibling preservation, a wrong
claim, and the deeper unsupported frontier. The global manifest has 212 cases in 72 families.
Fresh ROOT validation passes 824 Rust tests and 68 Python tests, formatting, lint, debug
and release builds, dependency checks, documentation, all twelve current example checks and
manual hooks. All 22 required checks pass. Four fresh release survey profiles match 85 PROVED,
74 REFUTED and 53 UNKNOWN for the 212-case, 72-family manifest.

Fresh owner-to-ROOT debug replay compares 4,324 complete proof objects: 4,323 match fully
and all 7,520 emitted queries match exactly. The sole ARM O2 unbounded-fold result differs
only in its recorded query-free ResourceLimit call chain; every other field remains exact.
Fresh ROOT debug-to-release replay compares 4,324 complete proof objects: 4,321 match fully
and all 7,520 emitted queries match exactly. The ARM O0 fold differs in its timeout detail
prefix and call chain; ARM O2 and host O0 differ only in their call chains. Each is the same
query/model-free ResourceLimit at the unchanged 30-second budget, with all residual fields
exact. Literal labeled raw pairs remain recorded without normalization or promotion exemptions.

Eight fresh native executions select two tests for each original and one for each mutant:
four originals pass and four mutants fail with exit 101 under ten-second timeouts. Source,
compiler, executable and output hashes are retained; finite controls impose no proof input bound.
Full logs, surveys, debug/release comparisons and native evidence are retained separately at
`/tmp/miren-stage203-root-full-checks`, `/tmp/miren-stage203-root-full-survey`,
`/tmp/miren-stage203-root-debug-fidelity`, `/tmp/miren-stage203-root-release-fidelity` and
`/tmp/miren-stage203-root-combined-native`. Historical actual202 owner and actual198 evidence
retain their original sources, binaries and counts.


## Stage205: bounded checked integer intervals

This owner is based on committed Stage203 dc1cad57, with its integer hierarchy and all212
capability cases preserved. It adds exact original i32/usize proper-interval certificates,
validated complete core wrapper and delegated Range bodies, and current backing handoff to one
direct child. Original guards prove start<=end<=current length. No nested interval, split,
retained-view or returned-reference authority is added; budgets and input domains are unchanged.

Dedicated compiler controls measure9 PROVED/3 REFUTED per profile; the actual xor0-to1 helper
mutation refutes all four unchanged selected/sibling claims. Retained external O0 stores and
empty children prove; optimized retained stores conservatively remain UNKNOWN at their existing
whole-element lowering, and omitted selected/empty bodies remain MissingCompilerEvidence.
Historical actual202 captures stay separate from refreshed actual203 evidence.

The manifest appends three checked integer interval cases to the exact 212-case parent prefix:
215 cases across 73 families. Fresh ROOT validation passes 827 Rust tests, 68 Python tests,
formatting, lint, debug and release builds, dependency checks, documentation, all twelve current
example checks and manual hooks. All 22 required checks pass. Four fresh release survey profiles
match 86 PROVED, 75 REFUTED and 54 UNKNOWN, with no errors or new assumptions.

The selected wrapper candidate rejects non-Item and non-associated definitions before querying
the compiler signature. This fixes an observed closure compiler panic; actual closure and ordinary
function controls refuse before signature inspection. Exact original types and complete selected
wrapper and Range bodies remain required. Initial failed captures and their source checkpoints
remain separately preserved.

Fresh owner-to-ROOT debug replay checks 1,572 paired complete proof objects: 1,571 match fully and
all 3,368 emitted queries match exactly. The sole host O2 unbounded-fold residual changes only its
literal query-free 30-second timeout detail prefix. Its call chain and every other field are exact.
Fresh ROOT debug-to-release replay checks 1,572 paired complete proof objects:
1,571 match fully and all 3,368 emitted queries match exactly. The sole ARM O0 fold changes
only its call chain, from the root to the root plus closure. Both literal raw pairs retain the same
query/model-free ResourceLimit, 30-second budget and every other field. No proof, query, model or
diagnostic normalization is used.

Eight fresh ROOT native executions select one actual test each: four originals pass and four
helper mutants fail with exit 101 under ten-second limits. Source, compiler, executable and raw
output hashes are retained. Finite native checks impose no proof input bound. Full checks, survey,
debug/release replay and native evidence are separately recorded in
`/tmp/miren-stage205-root-full-checks`, `/tmp/miren-stage205-root-full-survey`,
`/tmp/miren-stage205-root-debug-fidelity`, `/tmp/miren-stage205-root-release-fidelity` and
`/tmp/miren-stage205-root-combined-native`. Historical actual202 owner evidence keeps its original
source, binary and counts; earlier stage histories remain intact.

Stage 207 admits metadata-only `is_empty` for original issued u16 mutable slice roles. The selected
available core body, exact shared receiver and Boolean signature are certified before evaluating
the current view length. The relation grants no data, alias, retained-reference or split rights;
other primitive elements remain outside this bounded certificate. Existing `len` paths remain
unchanged. Diagnostic host/ARM O0/O2 captures prove root, whole child and proper empty/nonempty
views, refute wrong claims and actual scalar-helper mutations, and retain genuine missing-child
body refusal. The exact 215-case Stage 205 prefix is retained and three metadata cases append:
218 cases across 74 families. Four fresh release profiles match 87 PROVED, 76 REFUTED and
55 UNKNOWN with no errors or new assumptions.

ROOT validation passes all 22 required checks, including 831 Rust workspace tests, 68 Python
tests, formatting, lint, debug/release builds, dependency checks, documentation, twelve example
checks and manual hooks. Two historical test expectations required independently reviewed upkeep:
original issued u16 is_empty now succeeds; a mutable closure capture remains Semantics UNKNOWN
at aggregate storage. The latter preserves all 272 queries and 100 of 104 paired proof objects;
only four query/model-free UNKNOWN diagnostic frontiers advance.

Owner-to-ROOT debug replay records 1,130 fully identical objects out of 1,132 pairs
and all 2,260 queries identical. Final ROOT debug-to-release replay records 1,131
fully identical objects out of 1,132 pairs and all 2,260 queries identical. Precisely named
unbounded-fold deadline context differences retain complete raw pairs, query/model-free
ResourceLimit, the same 30-second budget and every residual field. No result normalization is
used. Debug evidence is explicitly adopted across the one test-harness literal change; the
final debug artifact is byte-identical. The initial failed full-run debug binary was overwritten;
its hash and failed logs remain, but its binary bytes are unavailable. No equivalence is claimed.

Eight fresh ROOT native executions select one actual test each: four originals pass and four
actual helper mutants fail with exit 101 under ten-second limits. This native evidence is also
explicitly adopted across that test-only literal change; finite native tests do not bound symbolic
inputs. Earlier failed full runs, owner checkpoints and actual-parent evidence remain separately
recorded. Final evidence is under `/tmp/miren-stage207-root-final-full-checks`,
`/tmp/miren-stage207-root-final-survey`, `/tmp/miren-stage207-root-replay` and
`/tmp/miren-stage207-root-native`. These counts describe Rust capability cases, not fleet coverage.


## Stage208 historical actual203 checkpoint: nested whole Bool child calls

This scoped owner is based on committed Stage203 dc1cad57 and preserves its integer hierarchy.
It admits exact original Bool backing with the issued one-byte layout and logical Bool codec.
Nested calls retain current owner, epoch, generation, masks and returned Memory checks. Char,
shared child arguments, deeper nesting and interval composition remain outside this admission.
No input bound, contract premise, runtime check or missing-body shortcut is added.

Fresh dedicated host/ARM O0/O2 controls measure three Bool PROVED, two REFUTED and one UNKNOWN
per profile; all six Char controls remain UNKNOWN. Actual scalar helper xor-false-to-xor-true
mutations refute all three unchanged selected, sibling and scalar-return claims in all profiles.
Genuine nongeneric dependency controls prove retained O0 selected and empty callers. Retained O2
selected stores remain UNKNOWN at their existing lowering frontier, while empty callers prove.
Omitted selected and empty bodies remain MissingCompilerEvidence, including empty inputs.

Fresh automatic compatibility replay checks 108 prior command groups: 3,472 proof objects,
3,468 exact whole objects and all 5,924 old emitted queries exact. Its only changes are four
measured old mutable_bool_slices::nested UNKNOWN-to-PROVED promotions. The separate new Bool
controls retain their deeper UNKNOWN frontier; they are not counted as prior whole-object matches.

The owner appends three Bool globals to the exact Stage203 212-case source prefix, with the sole
old Bool nested manifest expectation updated to its measured PROVED result. Fresh custom-solver
profiles measure 215 cases across 73 families: 87 PROVED, 75 REFUTED and 53 UNKNOWN each. Of 848
prior global proof pairs, 842 match wholly, four are that Bool promotion and two retain query-free
30-second ResourceLimit call-chain variations. Every remaining field and all 1,580 old emitted
queries match exactly. These are actual203-plus-Bool counts, separate from Stage205 intervals.

Fresh native dependency, dedicated and global controls compile safe current sources with
finite lengths through 129 under ten-second limits; originals pass and helper mutants fail with
exit 101. They impose no proof input bound. Scoped compiler, RAII restoration, dedicated, old
related and closure tests, formatting, lint and debug build pass. An initial unqualified exact
RAII filter selected zero tests; the corrective qualified filter selects one actual passing test.

Evidence is retained under `/tmp/miren-stage208-upkeep-automatic-fidelity`,
`/tmp/miren-stage208-upkeep-full-global`, `/tmp/miren-stage208-upkeep-foreign-final`,
`/tmp/miren-stage208-upkeep-foreign-mutation` and `/tmp/miren-stage208-upkeep-global-mutation`.
Independent upkeep review, latest-parent adoption, full validation, release replay and ROOT
commit readiness remain separate gates. Historical disabled and flag-only checkpoints remain intact.

Current Stage208 adoption is based on committed Stage207 799b714, preserving its u16 metadata
certificate, proper integer intervals and exact 218-case source prefix. Its manifest updates only
the measured old Bool nested UNKNOWN-to-PROVED expectation and appends three Bool controls.
Four fresh 221-case profiles measure 89 PROVED, 77 REFUTED and 55 UNKNOWN across 75 families.
These actual207 scoped counts are separate from the historical actual203 checkpoint above.

Fresh same-source/cwd replay compares actual207 release452ef with candidatee05 in 164 paired
command groups: 4,660 proof objects and 4,602 fully identical objects. Those FULL objects contain
8,164 exact queries; another 12 baseline queries are exact active prefixes in changed Bool objects,
for 8,176 baseline emitted queries exact in total. Old108 compatibility contributes 3,472 pairs,
3,468 full matches and 5,924 queries;
its only changes are four old Bool nested promotions. All44 current207 metadata, interval,
closure and foreign anchors match fully: 244 pairs and 612 queries. New Bool originals and
helper mutants are separate controls, with three PROVED, two REFUTED and one UNKNOWN per
original profile; six Char controls remain UNKNOWN. All three actual Bool helper mutants refute.

Combined globals compare 884 objects, with 866 full matches and 1,624 queries inside FULL objects.
Four more baseline queries match active prefixes in changed new Bool controls: 1,628 ALL exact.
New Bool original/mutant controls separately contain 12 baseline queries: four in FULL Char
objects and eight exact active prefixes in changed Bool sibling objects.
Four old Bool promotions, twelve new control/frontier changes and two named query-free fold
ResourceLimit contexts are explicitly catalogued. Host O0 changes its call chain; host O2 changes
only the literal closure timeout prefix. Every other field matches, with no report normalization.

Eight freshly built nongeneric dependency libraries produce 16 reports: retained O0 selected
and empty callers prove; retained O2 selected stores remain Semantics UNKNOWN at the existing
whole-element lowering, while empty callers prove. Omitted selected and empty bodies remain
MissingCompilerEvidence. Fresh dependency and global helper mutations refute with actual body,
query and model evidence. Twelve native executions select one or two actual tests under
ten-second limits: six originals pass and six safe helper mutants fail with exit101. Finite
lengths through129 do not bound proof inputs. Source, compiler, library, executable and raw
output hashes are retained separately.

Current scoped checks pass29 actual tests, formatting, lint and build. Two setup/filter mistakes
were stopped and archived; corrected metadata and interval filters each select one actual test.
The inherited hierarchy probe initially reused a shared temporary scratch directory. A subsequent
cfgtest-only correction selects a unique per-invocation directory and passes its actual compiler
test, formatting, lint and build. The normal analyzer remains byte-identicale05. Initial capture
source associations are preserved and explicitly adopted across that test-only correction;
no historical scratch-asset equivalence or new execution is claimed. Actual208 historical and
actual207 adoption evidence remain distinct. Full ROOT validation and replay are recorded
separately below. Current scoped evidence is under `/tmp/miren-stage208-parent207-fidelity`,
`/tmp/miren-stage208-parent207-foreign`, `/tmp/miren-stage208-parent207-scratch-upkeep` and
`/tmp/miren-stage208-parent207-core-freeze.json`.

Completed ROOT Stage208 validation passes all 22 required checks: 835 Rust workspace tests,
68 Python tests, formatting, lint, debug/release builds, dependency checks, documentation,
twelve example checks and manual hooks. Four fresh release profiles match 221 cases across
75 families: 89 PROVED, 77 REFUTED and 55 UNKNOWN, with no errors or new assumptions.

Fresh owner-to-ROOT debug replay compares 4,660 proof objects: 4,658 match fully, and all
8,292 emitted queries and models match exactly. ROOT debug-to-release replay compares the
same 4,660 objects: 4,659 match fully, and all 8,292 queries and models match exactly.
Only explicitly named query/model-free unbounded-fold deadline contexts may differ in their
literal detail or call chain; every residual field and the same 30-second budget are retained.
No reports, paths, queries or models are normalized. These candidate-to-candidate counts are
separate from the parent-to-candidate 8,176 baseline queries and measured Bool promotions above.

Twelve fresh ROOT native executions rebuild current originals and actual helper mutants;
foreign libraries are rebuilt too. Each selects one or two actual tests under ten-second limits:
six originals pass and six mutants fail with exit 101, without changing assertions. Finite
native cases impose no bound on symbolic inputs. Final evidence is under
`/tmp/miren-stage208-root-full-checks`, `/tmp/miren-stage208-root-survey`,
`/tmp/miren-stage208-root-replay` and `/tmp/miren-stage208-root-native`. Final documentation
closure preserves all 915 other tested source files. These counts describe capability cases,
not full Rust parity or firmware coverage.

Stage209 actual208 candidate adds exact original Char to the bounded whole-slice nested protocol.
Current backing, epoch, owner and Unicode validity checks remain in force; no assumptions, repairs,
retained-reference or deeper nesting grants are added. Four-profile diagnostics for the original
six Char roots yield three PROVED, two REFUTED and one UNKNOWN per profile. Actual zero-to-'B'
scalar helper mutations refute selected, sibling and scalar-return claims in all four profiles.
The existing Bool fixture's Char routes now have the same measured outcomes; Bool routes retain
their previous results. Actual public compiler tests retain scalar, metadata and interval checks.

Three Char global cases append to the exact committed Stage208 221-case prefix: selected data and
sibling preservation PROVED, wrong claim REFUTED and deeper nesting Semantics UNKNOWN. Their
actual helper mutation refutes unchanged claims. Genuine retained O0 Char libraries prove selected
and empty callers; omitted libraries stay MissingCompilerEvidence UNKNOWN including empty callers.
Retained optimized empty callers prove, while selected callers reach the existing ConstantIndex
read frontier before Char decoding. This is not a missing-body or Unicode-validity success claim.
Fresh safe native Unicode extrema and lengths through 129 impose no bound on symbolic inputs.

This checkpoint describes candidate diagnostics on actual committed Stage208. Historical disabled
and actual203/pending208 evidence remains separate. Completed ROOT validation is recorded below;
capability counts do not establish full Rust parity.

Current actual208-based Stage209 scoped validation passes ten checks with 29 actual tests: current
public compiler lifecycle, Unicode/current-memory refusal controls, RAII restoration, Char and
related integration suites, metadata/interval compiler anchors, formatting, lint and debug build.
Current active compiler assets and their unique scratch are associated with the current e47
analyzer;
the original disabled 728 and sole-flag 6d snapshots remain immutable historical evidence.

Fresh same-source/cwd/mode committed208-to-candidate replay runs 180 command pairs and compares
4,724 proof objects; 4,633 match fully. Its 8,312 baseline emitted query/model
pairs are exact: 8,292 occur in fully matching objects, and 20 are exact prefixes
inside explicitly changed Char objects. Candidate reports emit 8,624 queries in total; newly
reached queries are reported separately from baseline compatibility. Changed objects include the
eight measured original nested Char case promotions, new Char outcomes, existing Bool-fixture Char
outcomes and precise later UNKNOWN frontiers; no whole-object equality is claimed for these.
The only deadline contexts differ at the named query/model-free scalar_slice_unbounded_fold root,
with the same literal 30-second ResourceLimit budget and every residual field exact. Raw observed
profiles and literal details/call chains are retained in the replay ledger, without normalization.

Four complete current 224-case profiles measure 91 PROVED, 78 REFUTED and 55 UNKNOWN. Fresh current
Char global original/mutant controls execute actual helper bodies, with unchanged selected claims
refuted by zero-to-'B' mutation. Four rebuilt safe global native runs select two tests each:
originals
exit 0 and mutants exit 101 under ten-second limits. Earlier four one-test Char native diagnostics
remain explicitly separate, with identical current fixture bytes. The native controls do not bind
symbolic input lengths. Eight genuine Char rlibs are rebuilt for current retained/omitted controls;
optimized selected ConstantIndex refusal and omitted empty-caller body requirements are preserved.

Evidence: /tmp/miren-stage209-parent208-upkeep-fidelity/ledger.json,
/tmp/miren-stage209-parent208-upkeep-global-controls/ledger.json,
/tmp/miren-stage209-parent208-upkeep-native/ledger.json and
/tmp/miren-stage209-parent208-upkeep-core-freeze.json. Owner source and Cargo remain stopped.
These scoped owner captures are separate from the fresh combined ROOT validation below.

Completed ROOT Stage209 validation passes all 22 required checks: 839 Rust workspace tests,
68 Python tests, formatting, lint, debug/release builds, dependency checks, documentation,
twelve example checks and manual hooks. Four fresh release profiles match 224 cases across
76 families: 91 PROVED, 78 REFUTED and 55 UNKNOWN, with no errors or new assumptions.

Fresh owner-to-ROOT debug replay compares 4,724 proof objects: 4,722 match fully, and all
8,624 emitted queries and models match exactly. ROOT debug-to-release compares the same objects:
4,723 match fully, and all 8,624 queries and models match exactly. Only explicitly named
query/model-free unbounded-fold deadline contexts may differ in literal detail or call chain;
every residual field and the same 30-second budget remain exact. No reports, paths, queries
or models are normalized. These candidate-to-candidate counts are separate from the 8,312
parent-to-candidate baseline queries and measured Char promotions above.

Eight fresh ROOT native executions rebuild dedicated and global originals and actual helper
mutants at O0/O2. Each selects one or two actual tests under ten-second limits: four originals
pass and four mutants fail with exit 101. Assertions remain unchanged. Finite native examples
impose no bound on symbolic inputs. Final evidence is under
`/tmp/miren-stage209-root-full-checks`, `/tmp/miren-stage209-root-survey`,
`/tmp/miren-stage209-root-replay` and `/tmp/miren-stage209-root-native`. Final factual docs
closure preserves all 917 other tested source files. These counts describe capability cases,
not full Rust parity or firmware coverage.

Stage210 extends complete-body-certified `is_empty` to already-issued non-u8 integer, Bool
and Char slices. Original element, receiver, body provenance and current storage/length checks
remain required. This observes metadata and grants no element access, borrow, input or nesting
rights. Float and byte cases keep their existing routes and limits. Available selected bodies
execute; omitted bodies remain MissingCompilerEvidence UNKNOWN, including empty callers.

Original caller claims and the 224-case global source prefix remain unchanged. The old Bool
Char-metadata control and global integer-metadata control now prove. The manifest updates that
one old global expectation and adds metadata P/R/excluded-Float U controls. Four current host/ARM
O0/O2 profiles measure 227 cases across 77 families: 93 PROVED, 79 REFUTED and 55 UNKNOWN each,
with no errors or new assumptions. Actual Boolean identity-to-negation and xor-false-to-xor-true
helper mutations refute unchanged claims with entered bodies and query/model evidence.

The actual209 owner checkpoint contains 168 own pairs: 32 FULL matches, 124 UNKNOWN-to-completed
results and 12 query-free omitted-body UNKNOWN frontiers; current reports emit 44 queries. Its
180 compatibility groups contain 4,724 pairs, 4,715 FULL matches and 8,624 exact baseline queries;
eight named promotions and one query-free fold context are separately recorded. The overlapping
four full global groups contain 908 pairs, 893 FULL matches and 1,724 exact baseline queries;
12 named promotions and three query-free fold contexts are separate. These overlapping counts
are not added as unique comparisons. Initial wrong-overflow-profile captures remain historical;
all canonical full global captures enable overflow checks and report that setting explicitly.

ROOT adopts 14 paths on committed209 and corrects one stale flag comment before freezing all
924 effective sources. All 22 required checks pass: 842 Rust workspace tests, 68 Python tests,
formatting, lint, debug/release builds, cargo deny, documentation, example checks/ARM builds,
manual hooks and the four-profile survey. Fresh same-ROOT-source/cwd/mode comparisons contain
4,724 pairs each: owner-to-debug has 4,721 FULL matches, debug-to-release has 4,723, and each
preserves all 8,628 emitted queries/models. Named query-free 30-second fold context differences
retain exact residual fields. One debug ARM O2 third-frame difference is approved only for its
exact sealed raw pair; the general comparison rule is unchanged. Stopped comparison captures
remain historical; continuations preserve completed rows and record fresh numeric CLI exits.

Eight fresh ROOT native executions rebuild dedicated/global originals and actual helper mutants
at O0/O2: originals run one or two tests and pass; mutants run one test and exit101. Ten-second
limits and compiler/source/executable/output hashes are recorded. Finite native cases impose
no symbolic input bound. Final evidence is under `/tmp/miren-stage210-root-full-checks`,
`/tmp/miren-stage210-root-survey`, `/tmp/miren-stage210-root-replay` and
`/tmp/miren-stage210-root-native`. Final factual docs closure preserves all 921 other tested
source files. Capability counts describe selected cases, not full Rust parity or fleet coverage.

## Stage211: nested calls on mutable floating-point slices

Exact original f32/f64 backing, layout and producer-pair checks now support bounded nested
whole-child calls, scalar returns and typed stores. NaN payloads and signed-zero bits retain
correlated raw and numeric values. Actual helper mutations refute unchanged caller assertions.
Missing selected bodies, including empty callers, and deeper nesting remain UNKNOWN.

The unchanged old nested Float claim now proves. Three new controls extend the preserved
227-case source prefix. Four host/ARM O0/O2 profiles measure 230 cases across 78 families:
95 PROVED, 80 REFUTED and 55 UNKNOWN each, with no new assumptions. All 22 ROOT checks pass,
including 843 Rust workspace tests, 68 Python tests, release builds, dependency checks,
documentation, examples and manual hooks.

The initial full run caught a missing test-only std import in the no_std fixture. That failure
and its earlier captures remain historical. The corrected phase adds only the cfg(test) import;
all analyzed functions and assertions remain unchanged. Eight fresh ROOT native runs pass for
originals and fail for actual helper mutants: dedicated runs execute one test, global runs two.
Finite native cases impose no bound on symbolic inputs.

Fresh same-ROOT-source comparisons bind the actual210 parent against debug and release builds.
Each compares 5,948 proof objects, records 148 named changes, preserves all 10,420 baseline
queries/models and records 10,696 current queries. Complete unchanged objects and partial UNKNOWN
query prefixes are checked without normalization. Query-free fold deadline contexts are separate;
the extra debug stopping-frame difference is accepted only for its exact reviewed raw pair.
The general timeout rule remains unchanged.

Evidence is under /tmp/miren-stage211-root-corrected-full-checks,
/tmp/miren-stage211-root-corrected-survey, /tmp/miren-stage211-root-corrected-replay and
/tmp/miren-stage211-root-corrected-native. A final docs-only closure preserves all 923 other
validated source files. These are capability cases, not full Rust parity or firmware coverage.

## Stage212 local static associated hierarchy

Local static associated calls now correlate original function arguments and normalized safe
signatures with the complete selected local instance. Receiver methods, virtual dispatch and
nonlocal associated bodies remain unsupported. Existing Bool, Char and Float validity and return
protocols remain in force; compiler controls exercise the shared Char and Float validators.

Borrowed original and selected arguments and raw signatures are bounded before this route's
re-resolution. Original and cached body inventories are bounded after that resolution, before
subsequent signature normalization and body cloning. The earlier dispatcher resolution is
unchanged. Unsupported aliases, constant substitutions and unsafe-binder projections refuse
conservatively. The shared preflight limits remain 512 work units and depth 16; publication
validation is a separate bounded pass, not a total engine cost bound.

Fresh 13-root measurements give five proved, five refuted and three unknown per profile. An actual
xor-zero to xor-one helper mutation refutes selected claims with unchanged assertions. Eight fresh
dependency archives retain body checks for empty callers: retained O0 selected and empty calls
prove; retained O2 empty calls prove while selected calls stop at direct element stores. Omitted
bodies remain unknown. No missing-body shortcut or new assumption is introduced.

Four completed host/ARM O0/O2 surveys each cover 233 cases across 79 families: 96 proved, 81 refuted
and 56 unknown. All 230 parent entries remain intact. Required ROOT validation passed 22 checks,
including 847 workspace Rust tests, 68 Python tests, lint, release builds, dependency policy and
manual hooks. Eight fresh native runs execute one test each: four originals pass and four actual
helper mutants fail. Finite native inputs do not constrain symbolic analysis.

Fresh ROOT comparisons bind the committed Stage211 release to the Stage212 debug build, then that
debug build to release. Each phase compares 6,952 proof objects. The parent comparison preserves
6,826 literal complete objects, records 120 named changes and six narrowly checked fold deadline
contexts, preserves all 12,284 baseline queries/models, and records 12,490 current queries/models.
The debug/release comparison preserves 6,947 literal complete objects and all 12,490 queries/models,
with five deadline contexts. UNKNOWN partial queries are included. This validates the parent to
release transitively; it does not claim two direct parent captures.

Separate comparisons of existing owner captures with ROOT captures allow only explicit,
byte-equivalent source-path associations. They preserve 6,947 and 6,946 complete objects after
those associations, respectively; no complete object is literally equal across working directories.
All 12,490 queries/models remain exact in both comparisons. Each additional wrapping-add stopping
frame has its own fresh, hash-bound pair review; this creates no general timeout exception.

Evidence is under /tmp/miren-stage212-root-full-checks, /tmp/miren-stage212-root-survey,
/tmp/miren-stage212-root-replay, /tmp/miren-stage212-root-owner-continuation and
/tmp/miren-stage212-root-final-data. Final documentation closure changes only these three coverage
records, preserving the other 929 validated source files and historical captures. These are
capability cases, not full Rust parity or firmware coverage.

## Stage213: typed constant-index reads and stores

Original MIR ConstantIndex projections now use the existing mutable scalar slice machinery.
Forward and reverse metadata must fit the target's 32/64-bit usize and satisfy the compiler's
index relation. The actual current view must establish the required minimum length; reverse
subtraction must not underflow. Existing interval translation, root bounds, original element
types, liveness, Char validity and Float raw/numeric correlation remain required before access
or publication. Local Index projections retain their previous route.

The dedicated unchanged 12-root fixture measures eight PROVED, two REFUTED and two UNKNOWN in
all host/ARM O0/O2 profiles. An actual xor-zero to xor-one helper mutation measures four PROVED,
six REFUTED and two UNKNOWN with unchanged assertions. The dedicated proper-reborrow caller and
composite mutable elements retain their separate unsupported boundaries. This stage adds no input,
borrowing, returned-reference, hardware or assumption grant.

Fresh retained/omitted dependency measurements cover both targets and optimization profiles.
Previously unsupported optimized retained stores now complete, including nested Bool calls;
omitted selected and empty bodies remain MissingCompilerEvidence UNKNOWN. The inherited Bool
harness expectation was changed only after fresh raw recovery confirmed the actual body chain
and preserved every baseline queried obligation. The stopped initial check remains historical.

The committed 233-case/79-family manifest is unchanged. All four fresh surveys measure
96 PROVED, 81 REFUTED and 56 UNKNOWN each. All 22 required ROOT checks pass, including 851 Rust
tests across 195 outer Cargo target summaries, 68 Python tests, lint, release builds, dependency
policy, examples and manual hooks. Four fresh ROOT native executions run one test each:
originals pass and unchanged-assertion helper mutants fail at O0/O2. Native samples impose no
bound on symbolic inputs.

Fresh ROOT parent-to-debug and debug-to-release comparisons each contain 7,152 proof pairs.
The parent comparison preserves 7,122 literal complete objects, records 26 named
changes and 4 separately checked deadline contexts, preserves all 12,800 baseline queried
obligations/models and records 12,832 current ones. Changed roots retain all 38
baseline queried obligations exactly. Debug/release preserves 7,148 literal complete
objects and all 12,832 queried obligations/models, with 4 deadline contexts. Numeric
CLI exits are checked against raw statuses before comparison; build exits also agree exactly.

Separate owner-to-ROOT associations map only explicitly byte-equivalent typed source-file and
replay-working-directory fields. Each preserves 7,148 complete objects after those associations;
12 proof objects also match literally. All 12,832 queried obligations/models remain exact.
The existing query-free 30-second fold detail/root-or-root-plus-closure rule remains unchanged.
One parent-to-debug pair and a distinct owner-to-ROOT pair stop in an additional wrapping_add
frame. Each has its own fresh, independently reviewed exception bound to the exact raw hashes.
No general UNKNOWN exemption is introduced.

Evidence is under /tmp/miren-stage213-parent212, /tmp/miren-stage213-root-full-checks,
/tmp/miren-stage213-root-survey, /tmp/miren-stage213-root-replay,
/tmp/miren-stage213-root-owner-association and /tmp/miren-stage213-root-final-data.
Final factual documentation closure changes four files and preserves the other 933 validated
source files. These measurements describe selected capability cases, not full Rust parity or
firmware coverage.

## Stage214: bounded owned writes through symbolic suffix indices

Owned u16 tuples, plain structs and fixed arrays now support writes whose suffix contains at
least two unresolved compiler usize indices. The existing Single/Indexed planner runs first.
The fallback authenticates original field and element types, current or captured destination
indices, array extents and correlated masks. It preflights cumulative Cartesian rows, leaves
and path depth against the shared 512-work/depth-16 limits before materializing new targets.
A successful update publishes once to current local storage or Memory. It never restores an
older pre-call Memory snapshot. Refusal can retain solver-context and diagnostic metadata;
this is not whole-engine rollback. References, other scalar types and reverse paths gain no
new permissions.

The unchanged ten-root fixture measures seven PROVED, two REFUTED and one UNKNOWN in each
host/ARM O0/O2 profile. An actual xor-zero to xor-one helper mutation refutes seven selected
claims with unchanged assertions. The pre-existing wrong-claim control becomes PROVED under
that mutant, and is reported as such. Eight genuine retained/omitted dependency archives retain
actual body checks; omitted bodies remain MissingCompilerEvidence UNKNOWN. Eight native runs
execute one test each: originals pass and actual helper mutants fail under a ten-second limit.
Finite native samples do not constrain the symbolic input domain.

Fresh recovery justified only the three inherited dynamic-twice harness promotions, preserving
the original guest files and baseline queried obligations. The initial stale-expectation failure
remains historical. The global fixture and manifest preserve all 233 parent entries and append
three guarded symbolic-suffix cases. Each four-profile survey now covers 236 cases across
80 families: 97 PROVED, 82 REFUTED and 57 UNKNOWN. The new oversized suffix stays UNKNOWN with
its specifically measured ResourceLimit frontier; it is never treated as successful.

The proportional owner corpus covers the current full survey, affected families, original and
mutated helpers, and genuine dependencies. Its 1,988 parent-to-candidate proof pairs preserve
1,889 literal complete objects, record 96 named changes and three strict query-free fold timeout
contexts. All 5,440 baseline queried obligations/models remain preserved, with 5,884 current
ones and 308 exact changed baseline prefixes. UNKNOWN partial queries are included.
Full-workspace owner debug/release comparison preserves 1,985 literal complete objects and all
5,884 queried obligations/models. Separate raw comparisons bind the earlier scoped candidate to
both full-workspace builds without assuming binary equivalence or rerunning native evidence.

All 22 required ROOT checks pass, including 856 Rust tests across 196 outer Cargo target
summaries, 68 Python tests, lint, release builds, dependency policy, examples and manual hooks.
The ROOT test suite also executes original and actual helper-mutant native fixtures at O0/O2.

Fresh ROOT debug and release binaries each execute 64 groups with 1,988 proof pairs against the
corresponding full-workspace owner binary. Both comparisons preserve all 5,884 rich queried
obligations/models. Debug preserves 1,986 literal complete objects, with two strict query-free
fold timeout contexts; release preserves 1,985, with three such contexts. Each phase retains
literal owner input paths, archives and working directories. No source-path rewriting, proof
field injection, promotion allowance or inherited extra-frame exception is used. This is execution
of ROOT-built analyzers on frozen owner inputs; ROOT workspace tests and its four fresh surveys
have their own source scope. The independently reviewed parent-to-owner change and fresh
ROOT-after equality compose without repeating the historical full corpus.

Evidence is under /tmp/miren-stage214-parent213, /tmp/miren-stage214-root-full-checks,
/tmp/miren-stage214-root-survey, /tmp/miren-stage214-root-debug-integration,
/tmp/miren-stage214-root-release-integration and /tmp/miren-stage214-root-final-data.
Final factual documentation closure changes five files and preserves the other 934 tested and
captured source files. These are selected capability measurements, not full Rust parity or
firmware coverage.

## Stage215: scoped hierarchy test flags

The six test-only hierarchy overrides share one concrete guard that restores the previous
thread-local value on Drop. Nested scopes preserve an already enabled value; panic unwinding
restores it, and bounded worker-thread controls check isolation when each guard is created
and dropped within its thread. The separate Float Return fault protocol stays unchanged.
The six production enable functions and seven production constants are byte-identical.
This refactor adds no Rust semantic permissions or hardware assumptions.

The current compiler lifecycle test retains 144 Float Return observations across host/ARM
O0/O2, with 145 sealed compiler assets. Nine selected tests pass in the focused owner checks,
including three new restoration controls. All 22 required ROOT checks pass, including 859
Rust tests across 196 outer Cargo target summaries and 68 Python tests. Formatting, lint,
release builds, dependency policy, examples and manual hooks pass. Four fresh capability
surveys retain 236 cases across 80 families, each with 97 PROVED, 82 REFUTED and 57 UNKNOWN.

The proportional parent-release to owner-debug pass contains 56 groups and 2,164 complete
proof pairs. It preserves 2,160 literal complete objects and all 4,644 rich queried
obligations/models, including UNKNOWN partial queries. Three differences satisfy the existing
query-free fold timeout rule. A fourth stops in an additional wrapping_add frame and has
its own independently reviewed exception bound to that exact pair's raw hashes. Every other
complete Proof field remains exact. No general timeout or UNKNOWN exemption is introduced.

The fresh ROOT release executes the same 56 groups on exact frozen owner input paths and
working directories. It preserves 2,161 literal complete objects and all 4,644 rich queried
obligations/models. Two differences satisfy the existing fold timeout rule; a third has a
fresh, independently reviewed ROOT exception for its exact extra-frame pair. It does not
inherit the owner's exception. The stopped datasets are preserved; separate continuations
adopt only their exact reviewed raw pairs and execute previously unrun groups. Both comparisons
preserve all outcomes without assumptions, trusted calls or source-path transformations.
ROOT debug is built and exercised by workspace tests; no separate debug CLI equality is claimed.

Evidence is under /tmp/miren-stage215-parent214, /tmp/miren-stage215-parent214-cli,
/tmp/miren-stage215-cli-arm-o0-continuation, /tmp/miren-stage215-root-full-checks,
/tmp/miren-stage215-root-survey, /tmp/miren-stage215-root-release-integration and
/tmp/miren-stage215-root-final-data. These measurements describe selected Rust capabilities,
not full Rust parity or firmware coverage.

## Stage216: known two-argument integer function tables

The new family records a guarded selected call that proves, an intentionally wrong assertion
that refutes, and a Repeat-produced table that stays UNKNOWN. The Repeat diagnostic expectation
is Unclassified; correcting that metadata did not change code, assertions or the candidate.
Original compiler A/B/R types, safe Rust signatures and actual selected bodies remain required.
Real helper and order mutations refute unchanged assertions and fail natively. Genuine retained
and omitted dependency controls preserve the body-availability boundary. No assumptions or
trusted calls are added. Full validation and raw comparison scope are in
[the stage history](stages.md).

## Stage217: known integer function-pointer Repeat

The existing Repeat control now proves through an authenticated cached assignment and known
integer target. This changes the existing case's expectation rather than adding a new manifest
case. Exact original types, full Instance, Copy/Freeze, source/body and resource checks remain
required. Construction and dispatch have separate limits; opaque/Choice and pointer-bearing
product targets remain unsupported. Retained constant helpers enter their actual bodies and
prove, while omitted helpers reach MissingCompilerEvidence UNKNOWN. Zero construction is not
an availability proof. Helper identity and binary argument-order mutations preserve assertions
and produce actual counterexamples and native failures. Complete validation and strict raw
comparison scope are recorded in [the stage history](stages.md).

## Unary Bool and Char function tables

Known nongeneric safe Rust Bool-to-Bool and Char-to-Char tables execute actual available bodies.
Exact signatures, evaluation once, Unicode validity and current returned Memory remain required.
Caller grammar and all-target body preflight have separate 512-work/depth-16 bounds. Integer
unary/binary and Repeat admission are unchanged. Float tables, references, mixed signatures and
opaque target grants remain outside this family. Retained controls prove; omitted bodies refuse.
Six new P/R/U controls preserve all 239 existing case objects and original source assertions.
Completed owner and ROOT checks, mutations and comparison limits are recorded in
[Stage222 in the stage history](stages.md#stage222-unary-bool-and-char-function-tables).

## Unary Float function tables

Known nongeneric safe Rust unary f32/f64 tables execute actual available selected bodies.
Exact original widths, current term context, evaluation once and returned Memory remain required.
Scalar numeric/raw decoding consistency is proved under actual path conditions. Actual identity
and negation preserve copied raw bits; arithmetic NaNs retain existing payload/sign nondeterminism.
Decoding equality cannot authenticate an arbitrarily substituted NaN payload or grant mutable
Float pair authority. Float Repeat, mixed signatures and opaque body grants remain unsupported.
Eight new cases preserve the original 245-case objects and literal guest source prefix.
Actual helper mutations, omitted-body controls, Return faults and completed ROOT checks are
recorded in [Stage223 in the stage history](stages.md#stage223-unary-float-function-tables).

## Unary Bool and Char function-pointer Repeat arrays

Known Repeat arrays admit exact original unary Bool-to-Bool and Char-to-Char signatures.
Construction evaluates the operand once, including at zero count, and preserves Move consumption.
Actual available selected bodies, Unicode validity and current returned Memory remain required.
Existing integer Repeat and all admission bounds remain unchanged. Opaque, generic, wrong-signature
and missing-body controls remain UNKNOWN; Float Repeat remains unsupported. Six appended cases
preserve all 253 prior manifest objects and the literal guest prefix. Completed validation is in
[Stage224](stages.md#stage224-unary-bool-and-char-function-pointer-repeat-arrays).

## Unary Float function-pointer Repeat arrays

Known Repeat arrays admit exact original nongeneric safe Rust unary f32-to-f32 and f64-to-f64
signatures. Construction preserves evaluation once, Move consumption, zero-count behavior and
existing admission limits. Selected calls execute actual available bodies and validate current
returned Memory. Copy and negation retain raw bits; arithmetic NaN limitations remain unchanged.
Opaque, generic, ABI, mixed-width, count, dispatch and missing-body controls remain UNKNOWN.
Two existing survey expectations advance to PROVED without changing guest assertions or adding
premises. Dedicated tests include unchanged-claim helper mutations with solver counterexamples
and native failures, plus genuine retained and omitted dependencies. Validation is recorded in
[Stage225](stages.md#stage225-unary-float-function-pointer-repeat-arrays).

## Typed mutable product slices

Pure tuple, bounded array and plain local struct elements use one mutable owner namespace with
exact compiler types, layout, Copy/Freeze facts and current initialized storage. Primitive columns
preserve integer, Bool, Char and f32/f64 values; floating stores retain NaN payloads and signed zero.
Direct metadata and guarded whole-element or constant field/array suffix reads and stores are
supported. Every replacement is validated before one branch-local storage update.

Dedicated host/ARM O0/O2 tests each record ten PROVED, four REFUTED and seven UNKNOWN outcomes.
Actual helper and store mutations refute unchanged claims; native originals pass and mutants fail.
Retained dependency bodies execute; unavailable bodies remain UNKNOWN. Compiler controls cover
exact original types, Context, initialization, extent, atomic stores and fake metadata pointers.
One existing nested Float metadata case advances to PROVED without changing its source assertion.
Nested product owner calls, proper reborrows, symbolic suffixes, contract snapshots and Armed
access remain unsupported, as do sum/niche/reference/pointer products. No hardware assumptions
are introduced.

## Whole mutable product helpers

Whole tuple, array and plain local struct helpers execute their actual available bodies and return
current storage through the existing owner/frame protocol. Pending tips suspend observations;
current child generation, issued Body identity and complete Return checks remain required.
Child metadata snapshots retain a live role, never a frozen payload or new access permission.
Exact float bit operations share existing builtin recognition and preserve NaN and signed-zero bits.

The dedicated host/ARM O0/O2 matrix records seven PROVED, three REFUTED and five UNKNOWN cases each.
Actual helper/payload mutants refute sixteen unchanged claims. Dependency controls record four
PROVED, four REFUTED and four missing-body UNKNOWN outcomes. Native originals pass and mutants fail.
The four compiler callbacks complete staging/call/Return and hostile frame/Context controls.
Their MIR optimization level is zero; the alternate PtrMetadata probe branch is not reached.
Nested owners, moved roots, proper intervals, symbolic suffixes and owner escapes remain UNKNOWN.
One existing whole-child survey case proves in all four Root profiles without changing its source.
Fresh host/ARM O0/O2 surveys each record 146 PROVED, 106 REFUTED and 79 UNKNOWN across 331 cases
and 92 families. All 315 other old case objects and the literal fixture prefix remain unchanged.
Their 2,440 queried obligations and models remain exact. Actual appended-source fingerprints and
one inherited query-free fold resource context are retained and qualified separately.

Formatting, lint, 91 Python tests, release builds, dependency policy, manual hooks and documentation
pass. Workspace test completion combines the complete no-fail-fast run with two target reruns,
covering 922 outer Rust tests. One stale child expectation is corrected after four-profile evidence;
two persistent-session tests require the ordinary solver invocation. Solver behavior and guest
claims are unchanged. The stopped runs remain archived; no single green workspace run is claimed.


## Compiler constant provenance receipts

Private frame-local receipts retain the origin of an exact promoted shared
`&Option<NonZeroU8>` None constant beside the ordinary checked decoded value. The actual caller,
producer, original/current promoted bodies, type, retag metadata and initialized immutable compiler
Memory must agree. Compiler allocation identities remain separate from runtime allocations.
Whole-local Copy/Move transport captures keys before consumption; overwrites, storage changes,
call results and dereferenced writes invalidate them. Retagged local uses receive no key.

Receipts provide provenance observations only. They issue no reference, raw-read, retag or
byte-membership permission and cannot replace the live shared-reference requirement. General
promotions, static identities, missing bodies and unmatched producers receive no receipt.
Future permission composition must account for producer, normalization and transport work.

Both compiler callbacks pass on the integrated Root source. The earlier isolated four-profile
membership controls retain six PROVED, two REFUTED and two UNKNOWN cases each. Their 32 P/R Proof
query/model pairs remain exact, and all 40 whole Proofs match after exact guest-path/cwd relocation.
Existing Option8 observer, comparison and actual helper/native mutation controls also pass.
These isolated captures retain their actual Parent237 basis; they are not Root239 proofs.

Fresh Root host/ARM O0/O2 surveys each retain 146 PROVED, 106 REFUTED and 79 UNKNOWN
across 331 cases.
One byte frontier remains UNKNOWN with its measured live-reference diagnostic. All 330 other case
objects and the entire guest fixture remain unchanged. Across 1,320 other comparisons, 1,318 Proofs
match literally; two query-free fold deadline contexts are recorded separately. All 2,640 existing
queried obligations and models remain exact. No deadline-context difference is called FULL.

Formatting, lint, a complete workspace run of 924 outer Rust tests, 91 Python tests, release builds,
dependency policy, manual hooks and documentation pass. The initial producer-tag and composition
initializer failures remain archived. This stage adds no application rewrites or hardware premises.
