# Rust capability baseline and extension boundaries

The next development priority is general Rust execution. Fleet remains a regression workload;
its hardware and executor assumptions do not define the language semantics. The capability suite
runs without a firmware checkout, hardware policy or trusted function contract.

## First milestone

The first Rust-first milestone requires a shared machine-readable case manifest, host and ARM
execution at O0 and O2, positive/refuted/unknown controls, a source mutation that breaks a proof,
structured UNKNOWN reporting, and passing repository checks. Completion establishes a repeatable
baseline. It does not establish full Rust support or a completed memory-model refactor.

The manifest contains 164 cases across 56 families. Each build configuration expects 65 PROVED,
57 REFUTED and 42 UNKNOWN results. Stage 133 originally had 23 cases with 10 PROVED, 9 REFUTED
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
