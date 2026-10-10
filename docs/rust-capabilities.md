# Rust capability baseline and extension boundaries

The next development priority is general Rust execution. Fleet remains a regression workload;
its hardware and executor assumptions do not define the language semantics. The capability suite
runs without a firmware checkout, hardware policy or trusted function contract.

## First milestone

The first Rust-first milestone requires a shared machine-readable case manifest, host and ARM
execution at O0 and O2, positive/refuted/unknown controls, a source mutation that breaks a proof,
structured UNKNOWN reporting, and passing repository checks. Completion establishes a repeatable
baseline. It does not establish full Rust support or a completed memory-model refactor.

The manifest contains 200 cases across 68 families. Each build configuration expects 79 PROVED,
69 REFUTED and 52 UNKNOWN results. Stage 133 originally had 23 cases with 10 PROVED, 9 REFUTED
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
