# Stages

The original four-step outline was:

1. Compiler adapter: pinned rustc_driver integration, typed local MIR bodies, source locations,
   Cargo integration, JSON reports and a metadata-only contract crate.
2. Panic inventory: enumerate checks and calls, classify unresolved boundaries, and show
   conservative local call paths. Inventory results do not establish feasible execution paths.
3. Proof engine: branch-sensitive abstract interpretation for integer ranges, enum variants and
   slice lengths. Add selective symbolic reasoning, exact arithmetic semantics and loop invariants.
4. Verified contracts and effects: check preconditions at callers, postconditions at returns and
   no_panic claims; add preserved type invariants, dependency summaries and restricted effects.

Each completed stage has its own commit. An unsupported operation, absent dependency body or
analysis timeout remains unknown. An annotation never establishes its own truth. Candidate
counterexamples from approximate models require validation before being reported as confirmed.

The starting examples are guarded byte reads, constant index helpers, frame length invariants,
invalid clamp bounds and unresolved dynamic dispatch. Resource and application-state properties
can follow once the foundational semantics are tested.

## Stage 1 evidence

Completed on macOS aarch64 with the pinned compiler. Four compiler integration tests and one
metadata behavior test pass. The tests cover uncalled generics, compiler errors, metadata
collection, Cargo feature forwarding and repeat analysis. Removing an uncalled generic from the
inventory makes its integration test fail; the mutation was restored.

Formatting, warnings-denied Clippy, release builds, dependency checks and manual hooks pass.

## Stage 2 evidence

The inventory detects bounds, arithmetic and explicit panic sites with panic=abort. Tests cover
optional overflow settings, signed division overflow, unknown external/trait/indirect calls,
destructors, guarded accesses, local call paths and recursion. Sites stay unverified and unknown
entry selection fails. A user function named panic_fmt remains an ordinary local call.

The existing CAN frame source was analyzed read-only on aarch64-apple-darwin and
thumbv7em-none-eabihf, with aborting panics and overflow checks enabled. Both reports contained
18 bodies and 33 sites, including five panic language-item calls. These are inventory counts,
not findings that the guarded operations can panic or proofs that they cannot.

The metadata crate also passes its behavior test under stable Rust 1.98.1. It does not evaluate
even unresolved predicate names or false preconditions at runtime. Verification remains future
work; unsupported contracts do not become trusted assumptions.

Removing bounds checks from the inventory makes the abort-mode integration test fail; the
mutation was restored. Formatting, warnings-denied Clippy, release builds, dependency checks
and manual hooks pass. Compiler and metadata integration tests also cover malformed contracts
and report-write failures.

## Stage 3 evidence

The first proof engine uses exact path-sensitive symbolic execution and Z3 bit-vectors before
adding abstract interpretation. It proves guarded byte access, checked integer guards and safe
local calls. Off-by-one guards, overflow, division failures, invalid call arguments and stale
guards are refuted with solver models. Loops and missing solvers fail as unknown. Compiler MIR
lint errors cannot emit a success report.

Independent host checks exhaust all 65,536 u8 argument pairs for guarded addition and replay
five rejected panic cases. This validates representative translations; it is not a proof of
the analyzer implementation. Contract predicates and function-level preconditions remain future
work at this stage. The supported subset and resource limits are explicit in README.md.

## Stage 4 evidence

A restricted pure predicate evaluator checks entry domains, every reachable local call's bounds
and postconditions at feasible returns. Callee bodies and return values are still analyzed,
including when annotations claim no panic or a false return bound. Postcondition parameter
bindings snapshot entry values. Unsupported names, expressions, type/range errors and
inconsistent preconditions fail as unknown.

A guarded call to an identity function requiring value < 16 passes. The same caller with a
value <= 16 guard fails with value=16, although the identity body cannot panic. Removing caller
precondition verification makes that regression test fail; the mutation was restored. Changing
MIR's <= translation to < also makes the panic regression test fail; it was restored.

The proof suite passes on the 64-bit host and thumbv7em-none-eabihf's 32-bit usize. Aborting and
unwinding panic modes and enabled/disabled overflow checks are tested. Cargo verification is
covered with both passing contracts and a failed call bound that retains its JSON report. The
example crate demonstrates guarded byte reads and a bounded increment without runtime checks.

This completes the initial contract slice of stage 4. Loop invariants, abstract interpretation,
generic substitutions, dependency summaries, preserved type invariants and effect contracts
remain future work. The analyzer implementation itself has not been formally verified.

## Stage 5: real-code fixture

Frame and FdFrame are vendored from fleet-2027 at b81a247a3295b13553087f5e328f201944a1eb61.
The original method bodies are preserved and compared against an unmodified source excerpt.
The fixture adds constructor and accessor contracts without changing the original workspace.
Runtime checks exercise valid and invalid IDs and all payload lengths from zero through 65.

## Stage 6: real-code proofs

All six unchanged Frame/FdFrame method bodies now prove on aarch64-apple-darwin and
thumbv7em-none-eabihf, with panic=abort and overflow checks enabled. Constructors establish ID,
accepted-length and exact stored-length postconditions without entry assumptions. Data accessors
prove safe slicing and returned lengths under explicit capacity preconditions; private fields do
not imply an invariant for arbitrary struct inputs.

Two payload harnesses prove the constructor-to-accessor path, each callee's required bound and
exact payload equality at every permitted index. Actual constructor bodies supply caller facts;
annotations are not trusted summaries. Struct fields, constructed core Option variants and local
byte arrays extend the modeled MIR subset. Pure contracts gain named fields, integer casts and
restricted exhaustive Option matches.

Pinned core models cover byte prefix ranges, slice length, u8-to-usize conversion and exact copies
into local arrays. Their range and copy-length panic conditions are checked. They are trusted
parts of the translator and are listed per root in JSON schema version 5. Mutable borrows cannot
cross local calls or escape through aggregates/returns. General mutation, input enums, nested
struct inputs, arbitrary dependencies, loops and derived methods remain unsupported.

Regression tests reject invalid stored lengths at accessor calls, weakened constructor guards,
invalid FD lengths and incorrect or missing payload copies. Removing an accessor precondition
also fails. A user method named copy_from_slice receives no trusted model, and mutable call
boundaries remain unknown. Temporarily disabling the translator's destination-byte updates makes
the real-code round-trip test fail as refuted; the mutation was restored.

The compiler suite has 31 passing tests, plus the metadata behavior test and independent vendored
runtime checks covering IDs, lengths zero through 65 and every accepted payload index. Formatting,
warnings-denied Clippy, release builds, dependency checks and manual hooks pass. These selected-root
results are not whole-crate coverage or a formal verification of the translator.

## Stage 7: larger bus validator

The vendored Use enum, both helper methods and check retain their original bodies. The validator
has 44 MIR blocks in the recorded build, including nested loops, enum matches, ID and slot checks,
pairwise collisions and FD compatibility. Two three-device configuration families prove with
symbolic IDs and slots on aarch64-apple-darwin and thumbv7em-none-eabihf. Five invalid families are
refuted with solver models and replay as runtime panics in the original validator.

The engine now follows constructed local enums and small constructed non-byte arrays. Indexing
requires a uniquely determined index on the current path. Loops are completely unrolled within
the existing execution budget; arbitrary input slices and larger loop domains remain unknown.
The arbitrary &[Use] validator entry itself is unknown, rather than a whole-domain proof.

Negative assertion paths exposed formatting setup before panic_fmt. A narrow compiler/type-checked
model constructs opaque formatting arguments from evaluated static strings. Dynamic formatting
and similarly named user methods remain unmodeled. Finite-loop tests check exact return values and
panics after later iterations. Infinite or over-budget loops fail as unknown. Temporarily treating
the execution limit as successful completion makes the cutoff regression fail; it was restored.

There are 37 compiler integration tests, one metadata behavior test and seven vendored runtime
tests. Formatting, warnings-denied Clippy, host and ARM release builds, dependency checks and manual
hooks pass. docs/proofs.md records the mechanism, trusted components and remaining coverage gaps.

## Stage 8: broader MIR coverage and DR16 parsing

Coverage takes priority over a broader soundness audit in this stage. Concrete generic arguments
are substituted and normalized; static traits resolve to implementation bodies. Available
dependency MIR, read-only closures and function items are executed with actual values. Reports
in JSON schema version 6 list interpreted body instances separately from explicit library models.
Missing MIR, unsupported shims and mutable captures remain unknown.

Constructed Result and ControlFlow variants support core question-mark propagation. Small
integer/bool arrays accept symbolic bounded indices and fixed-array map executes callable bodies
in order. Integer shifts, boolean casts, lossless integer conversion, endian decoding and exact
shared byte-slice-to-array conversion extend the supported operations. Compiler assume intrinsics
are checked as validity obligations rather than silently added as assumptions.

The unchanged Raw::parse body is vendored from the same firmware snapshot in examples/dr16.
Its 42-block body proves panic freedom without entry preconditions on the host and ARM target.
Postconditions establish exact-length rejection, switch bounds and all five channel bounds.
The proof follows core Result/Option methods and three closures. Incorrect byte-index and channel
mask mutations are refuted. Independent runtime tests compare 4,608 frames against separate
decoding formulas and check input lengths zero through 40.

There are 44 compiler integration tests, one metadata behavior test, seven CAN runtime tests and
two DR16 runtime tests. New cases cover generic call bounds, static dispatch, function items,
read-only closures, scalar arrays, endian values, Result success/error propagation and available
dependency bodies, including a refuted dependency overflow. Formal interpreter/model auditing,
general mutation, arbitrary enum inputs, floating point and broader iterator support remain work
for later stages.

Formatting, warnings-denied Clippy, host tests, host and ARM fixture release builds, dependency
checks and manual hooks pass. A separate ARM parser analysis discharges 45 obligations in about
1.5 seconds on the development machine; this includes compiler/solver execution and excludes
building the checker and proc macro.

## Stage 9: selected Cargo roots, coverage reports and aggregate inputs

Cargo accepts exact or crate-qualified entry names, including repeated selections across
workspace members. Crates without matching roots retain inventories rather than attempting
unrelated proofs. Missing names fail at the wrapper after collected reports have been retained.
Failed verification also renders available reports, so summaries expose failures immediately.

JSON schema version 7 includes per-crate root outcome counts, unselected bodies, distinct
interpreted instance counts and unknown reasons grouped by affected root. --summary displays those
results without the full site/obligation listing. Counts explicitly describe roots, not runtime
coverage or whole-crate safety. Workspace tests cover qualified selection, same-named unknown
roots, repeated selections, refuted roots and missing names.

Input modeling adds tuples, nested local structs, concrete generic fields, supported shared
reference fields and small fixed arrays of modeled values. Numeric contract projections preserve
tuple facts. An eight-level depth limit and 128-value budget prevent recursive/oversized input
construction from hanging; exhaustion and mutable fields remain unknown. Positive aggregate
cases and a refuted off-by-one call guard run on the host and ARM target.

The no_std contract example adds guarded_packet_read with a nested Header and shared byte slice.
The root README now leads with a runnable Cargo parser proof. docs/usage.md explains selectors,
targets, outcomes and schema fields; docs/coverage.md records supported behavior and evidence.

There are 49 compiler integration tests and one metadata test. Cargo tests run the real parser
and nested packet example on host/ARM, with one independently selected root per report. Tests
also preserve the inventory-only distinction and ensure input-budget exhaustion cannot pass.

Formatting, warnings-denied Clippy, host tests, release builds, dependency checks and manual hooks
pass. The documented whole-contract, selected DR16 and selected CAN Cargo commands also prove;
the latter two run for ARM, including an explicitly aborting/overflow-checked parser build.

## Stage 10: fleet measurement and published documentation

The unchanged fleet-2027 workspaces were inventoried and their 32 ARM compilation units checked
independently. The [survey](fleet-survey.md) records compiler/profile scope, generated-root skew,
counterexample interpretation and measured time. The actual DR16 parser proves without entry
preconditions. Whole firmware applications remain outside the current supported subset.

The README adds a theme-aware mark, status badges and direct guide links. VitePress publishes the
existing guides with local search, sidebar navigation and light/dark themes. A dedicated Pages
workflow builds pull requests and deploys main. Node dependencies are locked; the patched Vite
override leaves the dependency audit clear. Contribution and issue templates request minimal
examples, build configuration and evidence without treating solver assignments as runtime bugs.

Validation includes the Rust formatting/lint/test/release/dependency checks, manual file hooks,
the documentation production build and browser checks of page links, search and desktop/mobile
themes. No firmware source or dependency was changed. See [development](development.md) for the
documentation build and publication procedure.

## Stage 11: floating point, enum domains and dependency-defined inputs

The engine models f32/f64 with SMT floating-point sorts, nearest-even arithmetic and Rust's
saturating integer casts. Comparisons preserve NaN and signed-zero behavior. Compiler-identified
absolute value and min/max models preserve numeric NaN fallback and allow either equal operand.
Float remainder and raw bit observation stay unknown. Contracts accept typed finite float
literals, float casts and float-dependent call bounds.

Root enums receive legal symbolic discriminants and per-variant payloads; downcasts must prove
the active tag. Explicit signed discriminants are preserved. Local and dependency-defined
structs/enums use the same recursive shape limits. Symbolic Option contract matches have boolean
arms, and postconditions preserve entry snapshots. Unsupported payloads never become successes.
Array/slice pattern projections check minimum lengths and start/end offsets.

Four new compiler integration tests cover positive, refuted and unknown cases on host and ARM,
including foreign no_std inputs, NaN/zero/rounding/cast edge cases and off-by-one call guards.
There are 53 compiler integration tests and one metadata test. The fleet survey reruns the same
32 ARM units to measure newly supported paths without modifying firmware.

## Stage 12: compare fleet coverage and classify remaining blockers

The expanded fleet survey proves 149 of the same 976 function-declaration roots, up from 25.
All previous proved/refuted roots retain their outcomes; 124 unknowns now prove and 21 refute.
The baseline data is preserved, and a separate JSON summary records the new per-unit counts,
changed roots and first reported unknown reasons. Source paths in the published data are relative
to the firmware repository.

The largest remaining groups are mutable inputs, missing dependency MIR and constants. Removing
input blockers exposes these later boundaries, so their counts can grow without regressions.
The docs distinguish available foreign types from available foreign bodies and explain why
independently proving a helper does not automatically summarize it at an unknown call boundary.
Verification of the 32 already-built ARM units took 35.4 seconds, with more paths executed than
the 11-second baseline. No firmware source, configuration or dependencies changed.

## Stage 13: retain dependency MIR in Cargo analysis

Cargo analysis now retains ordinary non-inline dependency bodies by default. The small
miren-rustc outer wrapper appends always-encode-mir and MIR optimization level zero, forwarding
to the workspace analyzer or the pinned compiler. It preserves Cargo configuration, profiles,
features and Rust flags, including encoded arguments containing spaces. The existing fresh target
directory prevents stale metadata from earlier builds. --no-dependency-mir provides a comparison
mode. Prebuilt sysroot libraries are not rebuilt.

Dependency crates are not added to independent root inventories. Their concrete bodies execute
when called, with checked preconditions, actual returns and existing unsupported-operation limits.
A host/ARM regression uses two ordinary no_std dependency crates in a chain. Retention proves a
guarded call, refutes a violated dependency precondition and an overflow in the transitive body,
and preserves an unknown result for unsupported float bit observation. Opt-out calls remain
unknown because their bodies are absent. Tests also preserve configuration and encoded flags.
There are 54 compiler integration tests and one metadata test.

## Stage 14: measure fleet with retained dependency bodies

The same 32 ARM units retain all 149 previously proved and all 46 previously refuted function
outcomes. Dependency retention adds 47 proofs and 25 refutations, leaving 196 proved, 71 refuted
and 709 unknown function-declaration roots. Missing dependency MIR drops from 237 to 16 first
reported blockers. The remainder consists of prebuilt core helpers and a foreign critical-section
function; no missing body is assumed safe.

New passes include engineer arm/head controller constructors, robot PID configuration helpers
and CAN bus constructors/readers. Newly reachable constant and pointer/mutation gaps become more
visible. Independent mutable controller updates remain unsupported. The new survey data preserves
the original/intermediate measurements and records transitions, first-gap reasons and fresh build
costs. Verification of the already-built units takes 63.8 seconds on the development machine.

## Stage 15: inspect initialized aggregate constants

The constant decoder uses rustc_const_eval's inspection context for compiler layouts, active
discriminants, field/index projections and initialized scalar reads. It supports structs, tuples,
active enum fields, bounded arrays/slices and immutable promoted/static references. References to
interior mutable storage, mutable global reads, raw pointers and unions/MaybeUninit remain
unknown. Constants have eight recursive levels and a 256-value budget; byte arrays/slices have
at most 128 bytes and other arrays/slices at most 16 elements. No runtime calls are executed by
the constant inspection context.

Host/ARM integration tests prove guarded Option::as_ref calls, niche variants, explicit signed
tags, nested fields and immutable constants. Off-by-one guards, wrong payload assertions and a
mutated constant index refute. Inactive unsupported payloads need no read; active unions,
interior mutation, unsupported transmutes and shape exhaustion stay unknown. There are 55
compiler integration tests and one metadata test.

## Stage 16: measure fleet after constant decoding

The same 32 ARM units preserve all 196 proved and 71 refuted function outcomes. Constant support
adds 97 proofs and three bounds refutations, leaving 293 proved, 74 refuted and 609 unknown
function-declaration roots. All 54 Option::as_ref first blockers disappear. First constant gaps
fall from 194 to 69; 51 of those remaining reject interior mutable storage, often validation
counters. Mutable inputs still account for 300 first blockers.

New proofs include motor feedback accessors, link decoding, balance-state readers, engineer
commands and board controller/hardware helpers. The three new refutations concern engineer joint
indices under unconstrained root domains. Original and intermediate measurements are preserved;
the new JSON records transitions and remaining gaps. Verification reuses dependency-retaining
metadata and takes 81.3 seconds on the development machine. No firmware source, configuration or
dependencies changed.

## Stage 17: typed storage and mutable writes

References to supported mutable storage carry allocation identities and projections. Per-path
storage crosses calls and preserves writes through reborrows. Entry snapshots remain available in
postconditions, with `final_<parameter>` exposing updated arguments. Root analysis accepts one
mutable reference whose pointee contains no references. General aliases, mutable returns/captures,
partially initialized aggregates and ambiguous non-byte writes remain unknown.

Host/ARM tests cover scalar/aggregate/byte writes, callee updates, branch isolation and post-state
contracts. The vendored PID bodies prove reset and a concrete configured update; invalid limits
and a reset-write mutation refute. Arbitrary floating-point update paths remain expensive.
A root budget of 30 seconds is checked before queries, and storage has at most 512 allocations
per path. There are 57 compiler integration tests and one metadata test.

## Stage 18: scalar cells and conservative atomic counters

Compiler-identified Cell models preserve scalar storage through aliases, branches and callbacks.
Integer atomic models check load/store orderings and support wrapping add/sub/swap operations over
arbitrary current values. Each access permits interference; mutable static initializers are never
frozen. Atomic-only wrappers preserve their structure without reading runtime counter contents.

Host/ARM tests cover positive, refuted and unknown cases. Cell alias/callback updates prove;
unchecked counter arithmetic, invalid ordering and unsupported history assertions refute.
RefCell guards and general raw-pointer operations remain unknown. Ordinary Cargo verification
also proves the unchanged fleet validate::Site::fail and total on ARM. There are 58 compiler
integration tests and one metadata test.

## Stage 19: external checked contracts and explicit trusted summaries

JSON sidecars add contracts to unchanged code without a metadata dependency. Checked clauses
execute actual bodies, constrain root domains and verify call/return obligations. Trusted
summaries require an exact function selector, a no-panic claim and a reason. Generic calls need
an exact compiler instance. Return values remain arbitrary unless constrained, and explicit
memory effects preserve known aliases while claiming a frame for other storage. Omitted effects
invalidate modeled storage; unsupported ownership shapes and inconsistent summaries stay unknown.

Schema version 8 records the configuration, matched selectors and every used summary with its
reason, instance, crate hash and call site. Conditional roots are PROVED_WITH_ASSUMPTIONS,
excluded from ordinary proof counts and rejected unless --allow-assumptions is explicitly set.
Selecting the assumed function itself still checks its actual body.

Host/ARM tests refute out-of-bound calls, erroneous success assumptions and stale state claims.
Cargo tests use unavailable dependency bodies, check configuration forwarding and preserve strict
exits. Malformed/stale selectors, unsupported references and inconsistent summaries fail. There
are 63 compiler integration tests and one metadata test. Report-format and CLI presentation work
is deferred to the next step.

Ordinary ARM Cargo analysis proves the unchanged fleet controller::Pid::reset and its external
final-state postcondition without annotations or a new dependency. The selected check takes
0.25 seconds on the development machine, including compilation. This is selected-root evidence;
the published whole-workspace survey has not been rerun for these memory stages.

## Stage 20: progress, readable results and JSONL

The default CLI view prioritizes failed/incomplete/conditional roots, caps compact rows and long
details, groups the largest gaps, and ends with aggregate outcomes and elapsed time. --verbose
retains the complete inventory/obligations view; --summary remains a compact-view alias. Terminal
colors distinguish all four outcomes without replacing their labels. Auto color honors NO_COLOR;
explicit always/never modes and --quiet support terminals and captured logs.

Builds, active crate/root positions and report processing announce progress on stderr. Five-second
heartbeats keep long solver checks visible without redrawing over compiler diagnostics. JSONL
exports preserve one full raw report per line. Stdout exports redirect all human/Cargo messages
to stderr, including Cargo JSON messages. A report subcommand reads saved schema-7/8 JSON or JSONL,
recomputes cached counts and preserves strict exits; it explicitly states that analysis was not
rerun. Malformed/empty/unsupported inputs and output failures fail the command.

Compiler regressions cover clean machine streams, captured/forced colors, distinct trusted labels,
saved-report exits, legacy input, malformed input, Cargo message forwarding and a deliberately
slow solver that must show active-root progress. There are 67 compiler tests and one metadata test.

## Stage 21: direct compiler-configuration reuse and crate/main selection

--from-report FILE reuses a saved schema-7/8 compiler invocation for fresh source analysis without
calling the Cargo wrapper. --verify without --entry already selects every inventoried crate body;
an explicit main selects only that root and its reachable calls. Saved proof results, selectors
and user-trusted configurations are not reused. Compiler mismatch, missing arguments and mixed
raw/reused arguments fail. Direct compiler probes cannot masquerade as verification, while Cargo
wrapper probes retain their required behavior.

Tests prove a bounded binary main beside an independently refuted helper, then mutate the source
and reject the previously passing main despite loading its saved report. Legacy configurations,
invalid invocations and missing main selectors are covered. Main-related MIR hints help users
select expanded macro names. A coroutine construction case stays unknown; no async execution
semantics were added. There are 70 compiler integration tests and one metadata test.

## Stage 22: integer population counts and checked float clamp

The compiler-identified ctpop model counts every input bit, returns u32 and covers signed,
unsigned and target-width integers. Primitive core f32/f64 clamp has an explicit panic obligation
for ordered, non-NaN bounds, then preserves NaN inputs and signed-zero ties. Compiler identity and
normalized signatures distinguish these models from same-named user functions.

Host/ARM tests prove byte count/complement relationships, masks, integer-width bounds, guarded
float ranges and special values. Invalid bounds and incorrect assertions refute. Mutating a mask
bound or reversing a passing clamp guard also refutes with a counterexample. Unsupported pointer
inputs and raw float bit observations remain unknown. There are 73 compiler integration tests and
one metadata test.

## Stage 23: bounded owned aggregate repeats

The repeat evaluator now accepts nested arrays, tuples, structs and enum values with owned
modeled contents. Copies preserve symbolic fields and variant tags, while independent writes
stay local to the selected copy. The model rejects tracked storage identities and limits each
repeat to 128 elements and 256 modeled values to bound recursive expansion. Input and constant
non-byte array limits remain unchanged.

Host/ARM compiler tests cover six-by-six float matrices, diagonal initialization, tuple/struct/enum
copies, larger generated arrays and nested byte-array writes. Wrong copy assertions and a wrong-row
write mutation refute. Large repeats, ambiguous composite indices and repeated interior-storage
accesses remain unknown. There are 75 compiler integration tests and one metadata test.

## Stage 24: shared slice cursors and checked predicate callbacks

Compiler-identified slice iterators retain their source and front/back positions. Models advance
actual iterator storage, yield source elements and support forward/reverse traversal, symbolic
skips, lengths, count, size hints and independent clones. Generic enumeration, copied and reverse
adapters execute core MIR. all/any execute actual concrete callable bodies, propagate memory
updates and stop at the deciding element. Existing execution budgets bound unfinished loops.

Compiler layouts supply constant discriminants for enum representations with one variant,
including the uninhabited residual used by optimized question-mark MIR. Host/ARM tests cover
ordinary/zero-sized/composite values, bounded byte slices, cursor exhaustion and Cell effects.
Incorrect assertions/callbacks and order/short-circuit mutations refute; 4,096 host cases agree
with direct formulas. Unsupported views and unbounded loops stay unknown. There are 78 compiler
integration tests and one metadata test.

## Stage 25: mutable slice projections and enumeration

Mutable slice cursors yield references into existing typed allocations, preserving writes through
forward/reverse traversal and callbacks. Mutable enumeration and iterator passthrough are explicit
core models with counter-overflow obligations. Known Some mutable payloads preserve reference
identity on unwrap. Legacy byte views attach to typed storage and later copies use that storage.

Host/ARM tests prove array postconditions, independent element writes, tuple and byte updates,
short-circuiting and six-by-six matrix initialization. Wrong writes, alias assertions and unchecked
increments refute. A wrong-column mutation refutes; independent runtime tests cover 4,096 mutable
cases alongside the 4,096 immutable cases. Ambiguous composite writes and mutable returns remain
unknown. There are 80 compiler integration tests and one metadata test.

Borrowed array/slice IntoIterator factories use the same cursor models. Exact primitive float
finiteness classification reduces helper-call steps in numeric predicates, with host/ARM cases
covering NaN, infinities, signed zero and an unconstrained assertion that must refute.

## Stage 26: persistent root-local solver sessions

Feasibility checks request SAT/UNSAT without an unused model. The default backend lazily starts
one Z3 process per root, resets before each query and fetches counterexample models in the same
query context. A root-local exact-query cache holds at most 1,024 entries or two MiB of query
text. Undecided responses never enter the cache. The compatibility executable override retains
its one-shot protocol.

Protocol tests verify declaration/assertion isolation, cache keys and limits, current-context
models, malformed responses, EOF and a stalled writer killed by the six-second host deadline.
The existing compiler, negative, unknown and mutation suites continue to pass.

A local host benchmark used the old and new release binaries, normal Z3 without a profiling
wrapper, one warmup and five alternating measured runs per binary. Median direct analysis times
for the synthetic slice fixture were:

| Root | Before | Persistent session and decision cache |
| --- | ---: | ---: |
| units | 0.359 s | 0.071 s |
| enumerate | 0.957 s | 0.129 s |
| floats | 1.047 s | 0.121 s |

All three roots remained PROVED. These measurements use Apple Silicon, Z3 4.15.4 and the pinned
nightly's host library configuration; they are not a general speed guarantee. Resource limits,
unsupported behavior and the proof domain are unchanged. There is no cross-invocation proof
cache or precomputed standard-library summary store.

## Stage 27: ordered array generation and iterator regression coverage

The core::array::from_fn model runs actual concrete callback bodies in ascending index order,
propagates memory effects and conditions, and checks callable contracts. Empty arrays never invoke
callbacks. Generated results must be owned and fit the existing 128-element/256-value budgets;
destructors, storage identities and unsupported mutable captures remain UNKNOWN. Core identity
and the normalized signature gate the model; a same-named application function runs its own MIR.

Synthetic ticket, parcel and label cases exercise 23 roots on host and ARM: 12 prove, four refute
and seven remain unknown. Tests cover callback order, Cell effects, function items, floats,
zero length and exact shape boundaries. Invalid assertions, arithmetic and call bounds refute,
as does a label-offset mutation. Native tests independently replay 512 inputs and callback effects.

Iterator audit regressions cover mixed forward/reverse skips, usize::MAX exhaustion, zero-sized
mutable elements, skipped byte storage, shared Cell callbacks and disjoint projections. False
alias assertions and an exhaustion mutation refute; unsupported views and owned mutable callback
environments remain unknown. Native execution checks 1,792 bounded cases. The review found no
new reproducible false proof in these paths; the interpreter has not completed a soundness audit.
There are 86 compiler integration tests and one metadata integration test.

## Stage 28: exact ground Boolean and bit-vector decisions

A bounded in-process evaluator validates complete generated SMT scripts and decides supported
fully constant assertions. It implements wrapping bit-vector arithmetic, bitwise operations,
signed/unsigned comparisons and exact sign/zero extension through 128 bits. Symbolic expressions,
floats, arrays, malformed scripts and unsupported operations fall back to Z3. False ground
failure conditions can discharge obligations without a solver process; failing obligations still
request real counterexample models. Custom solver overrides retain their compatibility behavior.

Tests compare 1,158 arithmetic, comparison and extension cases with Z3 at widths 1, 8, 16, 32, 64
and 128, including wraparound and signed boundaries. Removing the signed-order transformation
breaks the differential test. Parser tests cover unsupported content after false assertions,
malformed arity/types, declaration collisions, invalid widths and parser budgets. Integration
with the solver verifies that constant decisions need no process while counterexamples still
require a model. This is exact evaluation of a restricted closed-expression subset, not a new
solver for symbolic floating point or memory.

A follow-up direct-analysis benchmark, with the test suite finished, used one warmup and seven
alternating measured runs per release binary under the same host/solver configuration. Median
old-to-final times were 0.323 to 0.047 seconds for units, 0.699 to 0.087 seconds for enumerate and
0.976 to 0.114 seconds for floats. All remained PROVED. Floating-point queries use Z3; their gain
comes from session reuse and decision caching. These are small synthetic roots, not a promise
about branch-heavy or solver-heavy code.

## Stage 29: compiler identities and parsed contract references

The MIR interpreter already operates on typed rustc enums rather than parsing debug output.
This stage removes remaining semantic substring shortcuts: panic language items have an explicit
typed match, atomic Ordering arguments and variants are checked against the normalized compiler
enum, and array from_fn resolves a module child DefId anchored by ArrayIntoIter. Post-state
contract references are detected in parsed expressions, with Option-arm bindings scoped locally;
fields, comments and unrelated names containing final_ do not activate post-state snapshots.
Internal checked arithmetic selection uses an explicit closed operation set.

Host/ARM identity regressions check seven roots: four prove, two refute and one remains unknown.
Application types and functions with library-like names execute their actual bodies. Existing
Cell/atomic regressions preserve their outcomes. AST tests distinguish free post-state paths,
fields, comments and shadowing Option bindings. Ordinary source selectors and report strings
remain text interfaces; they do not determine MIR instruction semantics.

## Stage 30: owned array cursors, folds and evaluated closure constants

Compiler ArrayIntoIter uses the existing typed cursor representation without modeling general
MaybeUninit or transmute. Owned elements have no tracked identities or destructors and fit the
128-element/256-value limits. Models preserve order, skips, count/last, checked predicates,
fold/rfold callbacks and writable reference passthrough. Harmless wrapper drop glue follows typed
fields only when no user destructor can execute. Owned Clone and iterator views remain unknown.

Shared slice fold/rfold execute actual callback bodies and propagate accumulator, conditions and
memory. Ordinary sum MIR proceeds through evaluated noncapturing closure constants, whose typed
upvars, zero fields and zero-sized layout are checked. Captured constant closures remain unknown,
including zero-sized captures. The coverage work caught a cursor-state bug: count through a
mutable shared iterator reference must exhaust the original cursor. Positive and negative
borrowed-consumption regressions now cover count, last, fold and reference passthrough.

The owned fixture checks 29 roots on host/ARM: 13 prove, nine refute and seven remain unknown.
The closure fixture checks 15 roots: eight prove, four refute and three remain unknown. Native
replay, failing callback/call bounds, element-order and fold-seed mutations exercise these models;
the closure suite checks 1,024 inputs and independently replays four panics. Unsupported views,
captured constant environments, destructors and stateful owned callback captures stay unknown.

## Stage 31: integer primitive intrinsic coverage

Exact compiler identities and normalized integer signatures select min/max, saturating add/sub,
leading/trailing zero counts, byte swapping and bit reversal. Signedness and width are checked
against modeled operands. Saturation uses one extra SMT bit; zero counts return the input width
at zero. Bit rearrangements use exact extracts and concatenation. Scoped operand bindings keep
chained 128-bit operations within existing query limits. Unsafe nonzero-only intrinsics remain
unsupported; no resource caps were increased.

Host/ARM tests check 21 roots: 17 prove, three refute and one remains unknown. All 12 scalar
integer types are exercised, and reports confirm all eight intrinsic models ran. Native tests
cover all 65,536 operand pairs for both unsigned and signed eight-bit properties, all 256 byte
inputs for independent zero-count oracles, 128-bit boundaries and direct byte layout checks.
Three failing mutations are independently replayed. The combined suite has 94 compiler
integration tests, 13 solver/contract unit tests and one metadata integration test.

## Stage 32: tracked aggregate borrows and callback environments

Mutable references retain their allocation IDs and projections inside tuples, structs, enums,
closures and supported iterator adapters. Returns preserve incoming storage references; graph
checks reject callee-local/dead borrows, including references hidden in caller storage. General
root aliasing, legacy mutable byte captures and ambiguous non-byte writes remain unknown.
Core Zip/Flatten bodies can now proceed through tracked mutable aggregate storage.

FnMut calls borrow their actual environment. Map/from_fn, predicates and folds allocate one
tracked environment per modeled invocation, carry owned capture updates and external writes
between callbacks, and retire the environment on completion. Callback destructors remain unknown.
Map preserves reference-valued input elements. Existing false assertions that callback state
resets between calls now refute; borrowing external counters can prove.

The synthetic aggregate fixture checks 19 roots on host/ARM: 13 prove, three refute and three remain
unknown. Native tests exercise 700 bounded calls, stateful callback cases and negative panic
catches. A struct-field swap mutation refutes, and four internal graph regressions cover hidden
local escapes, dead storage, nested incoming references and untracked byte views. These tests are
regression evidence rather than a completed alias/lifetime audit.

## Stage 33: floating-point storage encodings

Float values retain IEEE storage bits alongside numeric SMT values. Inputs, evaluated constants,
from_bits, moves, array selection, negation, abs and clamp preserve the selected encoding,
including quiet/signaling NaN signs and payloads. to_bits and same-width integer/float transmutes
observe that encoding. Arithmetic/cast results get one stable encoding constrained to their
numeric IEEE value. NaN arithmetic outputs conservatively allow every encoding, including
signaling NaNs; bit-level counterexamples can therefore fail to replay on the target.

The synthetic storage fixture checks 17 roots on host/ARM: 13 prove, three refute and one remains
unknown. A sign-mask mutation refutes; native cases cover zero signs, subnormals, infinities,
NaN input encodings and 1,024 integer-cast/arithmetic inputs. Checked sidecars also force actual
core to_bits/from_bits bodies through typed transmutes without library summaries. Float remainder
and wider formats remain unknown.

## Stage 34: incremental queries, ground folding and instantiated MIR reuse

The default solver consumes structured declarations/assertions, retains a common assertion prefix
and uses push/pop for branch suffixes. Declarations are installed outside assertion scopes;
incompatible namespaces reset the session. Counterexamples still come from the current context,
and reports retain complete standalone SMT scripts. Exact decision-cache bounds, protocol
failure handling and the custom executable compatibility path remain unchanged.

Exact closed Boolean/bit-vector folding reduces repeated MIR expression growth. A root-local cache
shares at most 128 normalized bodies through Rc, keyed by the full compiler Instance rather than
DefId alone. It caches no function proofs or unchecked summaries and persists no compiler objects
to disk. Regression tests cover assertion-prefix changes, new/incompatible declarations and
current models, alongside differential ground-expression tests and generic-instance separation.

Default exploration increases from 256 to 2,048 steps and from eight to 16 active call frames.
Finite recursion may complete under those limits; unfinished recursive/loop paths remain UNKNOWN.
The 30-second root budget, 200,000-byte query limit and five/six-second solver/request limits remain
unchanged. Speed improvements reduce repeated work; they do not guarantee that larger limits
finish branch-heavy proofs or justify truncating unfinished paths.

On the development host, alternating release builds were measured after a warm-up, using five
measured samples each and the same Z3/compiler configuration. A bounded symbolic counter loop
remained PROVED and improved from 0.258 to 0.060 seconds. A fixed 256-iteration loop went from
UNKNOWN at the old step limit (0.871 seconds) to PROVED (0.048 seconds); its late-panic counterpart
went from UNKNOWN (0.901 seconds) to REFUTED (0.048 seconds). A twelve-helper call chain went from
UNKNOWN (0.035 seconds) to PROVED (0.040 seconds). These small synthetic cases demonstrate lower
expression overhead and completed exploration, rather than a general speed guarantee.

## Stage 35: optimized unit returns and Option panic boundaries

Unit-returning MIR may leave the return local unassigned; execution now returns the unit value
while preserving tracked memory effects. Missing non-unit return locals still remain UNKNOWN.
Option unwrap/expect panic helpers are identified by the actual Option module, exact function
names and never-returning signatures, then checked as panic entry points before operand decoding.
The model is pinned to the compiler; same-named application functions receive no special behavior.

Original host/ARM cases check successful/guarded Options, reachable unwrap failures,
application-name collisions, primitive AddAssign effects and unknown function-pointer calls.
String reborrows before some expect calls remain UNKNOWN. Native cases and a changed increment
verify that unit-returning calls preserve their writes.

## Stage 36: evaluated constant tables and scalar index selection

Evaluated immutable arrays/slices accept up to 128 elements, including non-byte scalars and
composites. The 256-value total budget and eight-level depth limit remain. Root non-byte inputs
still have at most 16 elements. Constants are fully decoded; this does not add lazy storage or
permit uninitialized/interior-mutable data. Exact ground indices select directly; compatible
scalar symbolic reads use one bounds query and conditional selection, avoiding a solver query
for each possible element. Composite reads still require a uniquely determined index.

Original host/ARM regressions cover integer/Boolean tables, exact float payloads and copied
aliases, structs, nested arrays, bounded slices and resource exhaustion. Wrong bounds and payload
assertions refute; a changed table-spacing mutation refutes and fails under native execution.

## Stage 37: defer unused float representation constraints

Computed float values retain fresh stable raw-bit symbols. Their numeric/encoding equalities are
stored within the root and included in a query only when its expressions reference those symbols.
Exact token matching follows dependencies transitively, including bit-preserving transformations
and roundtrips; uncertain lexical forms include every relation. Numeric expressions, ordinary path
conditions, the NaN overapproximation and resource limits remain unchanged. Exported SMT scripts
contain the required equalities and are independently runnable.

Original host/ARM regressions cover array-based gauge encoding, arithmetic/return/transformation/
selection roundtrips, transitive conversions and stable copied bits. An incorrect assertion
refutes; float remainder stays unknown. Unit regressions distinguish exact variable tokens,
unused declarations, cyclic dependencies and conservative lexical fallback. Native IEEE cases
exercise signed zeros, subnormals, infinities and NaNs.

On the development host, one warm-up plus three measured release runs of the original gauge
fixture improved from a 4.887-second median UNKNOWN result to a 0.056-second median PROVED result.
Other analysis processes were active; this is a small-case measurement rather than a general
speed guarantee.

## Stage 38: immutable static string transport

Evaluated literal strings can move through shared dereferences/reborrows, nested arguments and
returns using the existing opaque marker. Option expect can now reach its compiler-identified
panic helper. Strings receive no length, content, equality or pointer semantics; mutable
string-reference storage remains unknown. Original host/ARM regressions check guarded/unbounded
expect paths, application helper identities and rejected unsupported operations. A guard mutation
refutes, and native execution independently checks the shared-reference cases.


## Stage 39: allocation-backed local bytes and finite chunk views

Local mutable byte references use tracked allocations across calls and returns. Prefix views and
copy_from_slice update the original allocation. Compiler-identified byte-slice as_chunks_mut returns
chunk and remainder projections into one allocation, checking nonzero width and finite bounds. Chunk
writes translate directly to parent byte offsets. Symbolic lengths, excessive views and unresolved
root aliases remain UNKNOWN. Fixed byte post-state contracts support checked literal indices.
Original host/ARM cases exercise helper writes, returned views, disjoint copies, parent updates,
impostor methods and failure/unknown cases; native replay and a mutation verify writes.

## Stage 40: resolve dependency function items and encode integer bytes

Function-item callbacks resolve concrete trait dispatch before requesting MIR. Map/from_fn,
predicates, folds and Fn adapters execute actual implementations, including panic paths. Exact
primitive integer endian encoding complements decoding on all signed/unsigned widths. Missing-body
diagnostics distinguish omitted prebuilt core bodies from genuine foreign declarations. The existing
-Zbuild-std=core Cargo path retains core MIR and saved reports can replay it; unsupported pointer
operations remain UNKNOWN after those bodies become available. No foreign bodies are assumed
panic-free. Host/ARM, native boundary cases, mutations and captured replay cover this work.

## Stage 41: retain solver prefixes across declaration growth

Live Z3 sessions use global declarations so newly introduced symbols survive scope pops without
rebuilding shared assertions. Incompatible namespaces and protocol errors still reset the session.
Standalone report query text remains unchanged. Empty deferred-encoding maps skip dependency lexing,
and construction borrows condition strings instead of cloning an intermediate list. Scope-survival,
model-freshness and replay regressions verify answers; removing the global option breaks the new
test. Synthetic optimized workloads improved from 698 to 47.5 ms for 256 growing queries, and from
187 to 99 ms for constructing 5,000 queries, using six alternating samples.

## Stage 42: broader bounded roots and scalar validity

Root inputs allow 512 values, 16 nested levels, 256 non-byte array elements and 64 enum variants.
Constants retain their separate eight-level, 256-value and 128-element budgets. Integer pattern
ranges and alternatives constrain root values to their compiler-described domains. Unicode char
inputs exclude surrogates and values above U+10FFFF. The actual core NonZero getter exposes the
modeled scalar; unrelated get methods execute normal MIR. No constructor invariants are inferred for
other structs. Original host/ARM roots, native valid-domain cases, bound failures and a changed
divisor exercise these extensions. Exhausted or unresolved domains remain UNKNOWN.

## Stage 43: share byte source expressions

Byte region copies and integer endian conversion bind their source expression once with scoped SMT
lets instead of repeating it for each byte. This preserves source snapshots, disjoint writes and
byte order while avoiding expression growth. Resource caps remain enforced. Original numerical
byte-buffer regressions and native cases exercise compact views and subsequent parent reads.

## Stage 44: larger completed paths and leaner loop conditions

The default execution budget increases to 8,192 steps. Call depth remains 16, roots retain a
30-second deadline and queries retain their 200,000-byte bound. Unfinished paths remain UNKNOWN; the
checker never infers completion from budget exhaustion. Literal true path conditions are discarded
before block feasibility checks, avoiding repeated copies and scans on long loops.

Host/ARM regressions complete 1,024-iteration loops and refute a failure after the final iteration.
A longer unfinished loop remains UNKNOWN. Existing bounded-recursion and call-depth failures retain
their outcomes. This increases exploration capacity without adding loop invariants or termination
proofs.


## Stage 45: guarded unchecked arithmetic and compiler check operands

Unchecked MIR AddUnchecked, SubUnchecked and MulUnchecked operations check signed/unsigned
overflow using the existing widened bit-vector arithmetic. Each operation emits a validity
obligation before its result is used; only the non-overflow domain continues. Disabling runtime UB
checks never assumes that unchecked arithmetic is valid. A compiler-identified, signature-checked
cold_path intrinsic models its optimization-only semantics so checked-add overflow branches can
return None.

RuntimeChecks operands delegate to the pinned compiler's RuntimeChecks::value for the active
session, matching code generation for UB, overflow and compiler contract checks. Host/ARM
regressions exercise independent UB/overflow settings, all unsigned widths, signed checked
arithmetic and reachable panic counterexamples. The flattening regression proves core's guarded
unchecked multiplication and remains UNKNOWN at its raw-pointer boundary. Native replay covers all
u8 operand pairs and larger signed/unsigned boundaries; a changed reconstruction refutes. No
unsafe source or foreign-body assumptions are added.


## Stage 46: stop refuted roots after their first counterexample

Verification stops a selected root after its first refuted obligation, retaining that query and
model. Other selected roots still run. The all-failures option continues the former exploration
policy under the same resource limits; it does not promise an exhaustive list of failures.

Reports include a default-compatible stopped_after_counterexample flag, and compact/verbose output
identifies early stops. Cargo forwards the policy to compiler invocations and clears inherited
settings when the option is absent. Original host/ARM cases compare both policies, preserve
positive and unknown roots, replay native failures and expose a late failure after removing its
earlier guard. Caller contracts and postconditions remain checked in either mode.

## Stage 47: avoid unused contract maps and model optimization choices

Ordinary calls build argument name maps only for checked predicates or explicit aliases. Callee
entry snapshots still validate storage, and preconditions, postconditions and alias conflicts
retain their checks. Calls without preconditions avoid a duplicate body/snapshot/name-map pass.
Ambiguous dependency debug names therefore stop blocking ordinary body execution.

The compiler-identified scalar is_val_statically_known intrinsic follows its documented independent
Boolean choice on each call. Both optimization paths must be safe; the checker does not assume
a preferred value or stable repeated results. Pointer operands remain unsupported. Typed
transmute diagnostics identify source and destination types, with unsupported layouts still
UNKNOWN. Original host/ARM, native branch cases, invalid aliases and a guard mutation exercise
these changes. Integer power reaches actual checked_pow MIR but remains unknown at a niche
transmute rather than receiving an unchecked summary.

## Stage 48: typed term DAG and bounded SMT printer

A root-scoped context interns typed Boolean, bit-vector, floating-point and array terms. Node
construction validates sorts, widths, arity and context identity before simplification. Supported
closed Boolean/integer terms fold structurally; wide arithmetic retains its exact solver encoding.
Floating-point numeric equality is separate from structural equality, preserving NaN and signed
zero. The printer visits the DAG iteratively and emits scoped lets when sharing reduces output.
Output budgets fail explicitly instead of emitting incomplete expressions.

Differential tests check all 55 operator encodings and 3,150 closed arithmetic/comparison boundary
cases against Z3, validate array reads/writes and conversions, reject malformed constructions and
check a changed arithmetic formula fails equivalence. Repeated doubling stays compact through 256
levels rather than expanding exponentially. This is the representation foundation; existing MIR
consumers still use strings pending migration. No new language coverage or loop proofs are claimed.

## Stage 49: interpret MIR with typed terms

Symbolic scalar values, byte arrays, path conditions, contract predicates and float encoding
constraints now carry interned terms. Arithmetic, casts, integer intrinsics, population counts,
endian conversion, byte-region copies and atomic ordering use typed operators. Byte offset views
lower to capture-free array lambdas inside the printer. Persistent state snapshots retain immutable
nodes, and copies no longer need manually named source lets. Deferred float encoding constraints
follow structural symbol dependencies, including cycles, rather than lexing SMT text.

Production proofs no longer parse or fold string expressions. Structural constant decisions
validate assertion types and contexts first. Full query budgets apply during printing, including
declarations, assertion wrappers and the prelude. Reports retain standalone text scripts; the Z3
subprocess, assumptions policy and analysis limits remain unchanged.

The operator differential suite covers 57 encodings. Host/ARM byte, float and integer fixtures
retain their outcomes with smaller queries. An original repeated-signal fixture proves a 20-step
wrapping calculation that previously hit the query-size cap; a changed scale refutes and an
unresolved callback remains UNKNOWN. Native replay covers integer boundaries and the changed
assertion. This changes representation and sharing, not language coverage, type invariants or
loop induction.


## Stage 50: experimental induction over real MIR loops

The opt-in induction mode translates cyclic root bodies to constrained Horn clauses through a typed,
budgeted printer. Each MIR block has a state relation. Entry arguments and preconditions initialize
reachability; assignments, branches, assertions, byte-array bounds and backedges become transition
or safety clauses. Z3 Spacer supplies an inductive model only if all encoded reachable paths remain
panic-free. There is no iteration bound in these proofs and no claim of termination.

Integer/Boolean state, tuples, fixed byte arrays, persistent local byte writes and loop exits are
covered. Ordinary calls, recursion, references, coroutines, floats, enum state and function
postconditions still return UNKNOWN in cyclic roots. Unsupported code is never dropped from the
translation. Acyclic/default verification retains the existing interpreter. Cargo explicitly
forwards the mode and clears inherited settings. Raw reports retain models in a backward-compatible
invariants field separate from counterexamples.

Host/ARM compiler cases prove endless counters, tuple state, a register parser/history loop and
an exiting loop. A plain host main proves too. Mask/cursor mutations and a late panic never pass;
native tests replay the failures. Typed Horn tests check SAT/UNSAT polarity, malformed types,
foreign contexts, arity and exact output budgets. Solver tests check mode changes and reject errors.
Inductive UNSAT/timeouts remain UNKNOWN until a real Rust counterexample can be reconstructed.


## Stage 51: concrete callee transitions and inductive contract checks

Induction follows concrete calls using per-call-site MIR block relations. Captured caller parameters
preserve state throughout each callee; actual return values resume the original destination and
continuation. Concrete generic instances and retained dependency bodies have separate contexts.
Acyclic entries can delegate to looping helpers, and callees can contain their own loops. Recursive
contexts, unavailable bodies, references and unsupported types remain UNKNOWN. The aggregate block,
per-relation state and call-depth budgets bound translation rather than iteration counts.

Callee requires are checked at calls, root requires restrict inputs, and ensures are checked at
every actual root/callee return. Independent entry parameters retain snapshots when owned
arguments change; final_ bindings expose current values. False predicates and invalid aliases
cannot inject facts that hide a failure. Bodies are always translated; no verified-contract
summary replaces a callee.

Host/ARM positive cases cover delegation, nested generic and dependency calls, callee loops,
call domains, caller restoration and owned-byte snapshots. Mutated wraps, false contracts,
violated domains, recursive calls and unsupported predicates never pass. Native replay checks
counter mutations and false claims, and existing 256- and 1,024-iteration scalar fixtures prove
through induction.

A supported relational counter query can crash the pinned Z3. A bit-level preprocessing experiment
avoided that crash but returned a false safety answer on the native-replayed late-panic mutation.
That strategy was rejected. Ordinary Spacer inference remains enabled, and crashes/timeouts remain
UNKNOWN. Iterator storage, mutable/shared memory, trusted hardware boundaries and coroutines remain
next coverage requirements rather than assumed effects.


## Stage 52: typed inductive storage and stable references

Frames have fixed typed allocation layouts. Addressed locals and root borrows carry their values in
relation memory parameters; static field aliases retain allocation identity at every transition.
Callee writes update the caller's storage rather than a frozen copy. Entry snapshots for contracts
have independent parameters, and frame-owned references cannot escape into caller storage.

Host/ARM no_std fixtures prove persistent structs, mutable helper calls, shared array inputs and
borrowed byte writes. Bad wraps, off-by-one writes and false snapshot contracts never pass; native
tests replay the mutations. Changing reference targets, indexed borrows and interior-mutable inputs
remain UNKNOWN. Iterator state is the next independent coverage step.


## Stage 53: integer range loops, enum state and concrete custom iterators

Inductive enums carry a tag and typed payloads for every supported variant. Constructors update the
active variant; downcasts require explicit Horn safety guards, including through field references.
Core integer Range into_iter/next models use compiler identities and concrete signatures. Advancing
under start < end cannot overflow; exhausted ranges preserve storage. Custom iterators use actual
callee MIR and receive no range shortcut. Debug-only locals are excluded using rustc's MIR visitor.

Host/ARM positives cover range writes through a borrowed array, signed/maximum endpoints, breaks,
tagged state and a concrete custom iterator. Changed ends, false tag assertions, custom iterator
mutations and a panic beyond the old execution limit never pass. Native replay checks boundaries and
mutations. Slice iterators remain UNKNOWN, as do supported queries that exceed Spacer's inference
budget; a 12,000-element range still reaches that limit on the pinned solver.


Same-fixture release measurements found no speedup on the cheap finite cases: unrolling took
31–36 ms; induction took 44–45 ms for counters and 2.63 seconds for 20 symbolic doublings.
The endless counter proved in 44 ms with induction while bounded interpretation returned UNKNOWN.
Measurements used a warm-up and five sequential samples with identical build flags and JSON output.
Induction remains opt-in because invariant inference can cost more than complete finite execution.


## Stage 54: inductive slice cursors and indexed element references

Slice iterators carry typed source identities and independent front/back parameters. Indexed
references have their own parameters, preserving earlier elements when a cursor advances. Horn
safety clauses check cursor ordering, source bounds and each indexed access. Fixed scalar arrays
use conditional writes; byte slices retain exact SMT array stores. Helper bodies, checked contracts
and independent entry snapshots follow indexed references through actual call transitions.

Core-identified construction, next/next_back, nth/nth_back, length, size_hint, count, borrowed
cursors
and shared cloning are modeled. Host/ARM positives include retained aliases, mixed-end writes,
skips, clones, count exhaustion, initialized local buffers, integer/Boolean arrays and indexed
helper contracts/returned references. False pointer
claims, writes, snapshots and bounds never pass. Native replay and finite unrolling cross-check
small cases. Arbitrary non-byte slices, slice views and general adapters remain UNKNOWN.

Model indentation is disabled without changing solver logic or response limits. The mixed-end
fixture's complete model fell from 570,463 to 131,593 bytes, fitting the existing 256 KiB cap.
Unsupported compiler-inlined pointer/formatting internals remain explicit UNKNOWN cases.

## Stage 55: repeatable fleet surveys

A standalone host runner discovers library/binary units through pinned Cargo metadata, finishes
inventories before independently verifying units, and bounds parallel analysis. Every attempt uses
a fresh directory with atomic partial/complete summaries. Expected missing units, malformed reports,
compiler crashes and mismatched roots cannot disappear or count as proofs. Host build scripts and
the host-only xtask are explicitly outside the embedded scope.

Reports retain the compiler working directory and selected Cargo source environment. The runner
freezes analyzer binaries, ignores project proof configuration, fingerprints source/build inputs,
and records compiler, solver, target, profile, features and limits. Outcome diffs retain stable
unit/root identities and distinguish configuration incompatibilities from changed evidence.

Ten host runner tests include full fake surveys with positive, refuted and unknown roots, missing
units, compiler crashes, malformed reports, configuration/source mutations and frozen binaries.
Compiler integration checks source environment capture without registry credentials. A completed
survey establishes collection completeness, not a proof of every root or firmware safety.

## Stage 56: isolate reference graph validation

Tracked-value, frame-escape and recursive graph validation move from memory projection code into
one reference graph module. Six existing unit tests move with their helpers. The traversal,
initialization checks and escape rules are unchanged; sibling returns retain the same validator.

Before/after host and ARM runs over reference lifetime, tracked pointer, coroutine and local atomic
fixtures produce identical complete proof records and SMT queries for 173 root reports. The full
compiler/runtime suite passes. This refactor creates a focused validation boundary without adding
reference permissions or language coverage.

## Stage 57: unavailable dependency static origins remain unknown

The fleet survey exposed rustc query panics when storage-origin reconstruction requested dependency
static initializer MIR. The pinned metadata format retains evaluated static allocations but omits
their CTFE bodies. Origin reconstruction now checks that boundary and returns UNKNOWN before the
query. Supported immutable dependency scalar/slice reads still decode the evaluated allocations.

Host/ARM debug and optimized fixtures cover ordinary/startup domains, local initializer proofs,
changed initializer refutations, immutable dependency reads and incorrect constant claims, and
dependency mutable origins remaining UNKNOWN. Ordinary dependency bodies remain interpreted.
No unavailable body, initializer annotation or storage layout becomes a proof assumption.

## Stage 58: bounded tracked pointer offsets

Tracked raw address identities retain the exact compiler-sized reference extent and a byte cursor.
MIR `Offset` obtains its stride from the compiler pointee type, checks signed scaled displacement
and cursor bounds with double-width arithmetic, and preserves the original symbolic base.
Array-to-element casts retain their array extent; one-past formation and reverse offsets are
supported without granting raw memory access. Liveness and frame-escape validation remain active.

Host/ARM debug and optimized tests cover address relationships, later panic preservation, signed
overflow and bounds validity failures, and stride/bounds mutations. Native tests cross-check valid
relationships and the incorrect-stride assertion. Numeric pointers, zero-sized strides, wrapping
arithmetic, untracked snapshots and raw dereferences remain UNKNOWN. Validity failures are recorded
separately from panic-safety failures.

## Stage 59: survey dependency and generated-input integrity

The survey fingerprints explicit dependency artifacts, transitive metadata and proc-macro
candidates, adjacent origin sidecars including their absence, generated `OUT_DIR` files and native
search-directory inputs. Captured compiler working directories resolve relative arguments;
symlink-adjacent sidecars retain their original spelling. A bounded traversal records each unit's
inputs after inventory, immediately before and after verification, and at completion.

Changed, added or missing inputs invalidate affected results and leave collection partial.
Twelve standalone tests cover complete nested-cwd surveys, transitive changes, new sidecars,
artifact/generated-file mutations, symlinks and traversal limits. Artifacts remain live Cargo
inputs; these integrity checks do not claim hermetic capture of arbitrary custom environment data.

## Stage 60: checked dependency static origins

Retained dependency compilation emits origin sidecars from an additional compiler pass. That pass
checks a bounded monomorphized construction graph, emits its own metadata artifact, and only then
hashes and seals the evidence. Compiler, target, crate/static identities, schema, artifact SHA-256
and payload checksum must match. A versioned cache ensures dependency evidence is regenerated.

Typed construction establishes declared origins. Narrow scalar-copy/return-transmute bodies retain
their checked `u32` origin, covering the pinned core atomic constructor. A new outer aggregate
establishes its declared storage shape; a direct returned constructor retains its primitive origin.
Unsupported casts, opaque constants, union projections, aggregate parameters, missing bodies and
unrecognized operations cannot produce a certificate. Compiler types are reconstructed directly;
matching display names or storage sizes never create an origin.

Host/ARM debug and optimized cases cover atomic/Site construction, conservative ordinary atomic
reads, explicit startup values, source mutations, missing/stale/corrupt evidence and changed-source
same-pass emission. Origin records do not prove runtime values or callee contracts. Missing
evidence remains UNKNOWN, while local reconstruction and immutable dependency reads keep their
existing behavior.

## Stage 61: deterministic survey publication

A standalone exporter validates complete collections, root/unit identities, classification counts
and source/artifact checkpoint consistency before producing compact documentation data. It sorts
units, files and blockers deterministically, preserves every root, and compares status transitions,
configuration compatibility and proof regressions. Missing older artifact evidence remains explicit.
Later surveys also retain the already-enforced pre-verification artifact map.

Seventeen host tool tests include full 2,336-root compact round trips, deterministic output, partial
and malformed collections, count mismatches, changed artifacts and outcome comparisons. The fresh
32-unit fleet scan resolves 57 previous unknown source functions: 28 prove and 29 refute, with no
previously proved or refuted root regression. Numeric MMIO pointer offsets remain unsupported.

## Stage 62: compact typed byte repeats

MIR repeats of compiler-typed `u8` use one constant SMT array and a target-width length after
compiler layout validation. Byte count no longer consumes an expanded element budget. The
interpreter checks actual compiler types, so a shared byte-reference snapshot cannot become a
byte array. Expanded nonbyte repeats retain their element and owned-value limits.

Host/ARM debug and optimized cases cover 4,096-byte repeats, symbolic guarded indexing, updates
and unaffected cells. Incorrect contents and missing index bounds refute; reference, oversized
nonbyte and oversized owned repeats remain UNKNOWN. A changed repeat operand refutes and fails
native execution. This does not expand raw memory or slice/chunk support.

## Stage 63: compiler layout guards and exact byte scalar encodings

Compiler-identified size queries use sized target layouts or retained slice metadata and element
stride. The compiler zero-validity guard emits a panic-safety obligation without supplying any
initialized payload. Equal-sized initialized byte arrays decode into primitive integers or f32/f64
using the target endian order, preserving exact float storage bits.

Host/ARM debug and optimized tests cover sized and slice queries, invalid zero guards, later panics,
signed zero, signaling NaN payloads and a same-name guard that executes its own body.
Value and guard mutations refute. Character, restricted integer, Boolean and reference byte casts
remain UNKNOWN; return-type mutations confirm these boundaries.
Native checks agree with supported layout/encoding
claims. Option/NonZero niche casts and arbitrary unsized pointer metadata remain unsupported.

## Stage 64: shared Freeze snapshot reborrows

Reborrowing an immutable snapshot no longer invents a temporary allocation whose StorageDead can
incorrectly reject a returned static reference. Compiler shared-reference/Freeze types and an
initial dereference select the snapshot domain. Additional dereferences and actual retained
allocation references use the ordinary tracked path. Embedded graphs are validated before and
after projection; no storage retirement or escape rule is weakened.

Host/ARM debug and optimized fixtures cover whole/projected static values, retained dependency
static returns, shared inputs and mutation of actual local tracked storage. Initializer and field
mutations refute. Dead and nested-dead references, escaping local pointers and snapshot address
observation remain UNKNOWN with their original diagnostic boundaries.

## Stage 65: classified outcome and blocker comparisons

Survey publication separates transitions by both previous and current source classification.
A changed source-span heuristic stays visible instead of appearing as a proof gain. UNKNOWN roots
whose first blocker changes are counted separately even when their status stays unchanged. These
diagnostic strings do not promise support for later paths or define stable semantic categories.

Eighteen standalone host tool tests cover deterministic comparisons, classification shifts and
previously unrecorded blockers alongside complete collection and artifact-integrity checks.

## Stage 66: second complete fleet pass and bounded diagnostic publication

The next complete 32-unit scan retains all 2,336 root identities and resolves five previous
unknown source functions into proofs. Source outcomes are 490 PROVED, 226 REFUTED and 303 UNKNOWN;
all earlier proofs and refutations retain their outcomes. Another 20 inspected source roots pass
an earlier unsupported operation and stop at a newly exposed gap. Hardware MMIO stays unsupported.
All source inputs and four dependency/generated-input checkpoint maps remain unchanged.

Compact publication counts first-blocker text changes for every classification and retains detailed
transitions for roots classified as source functions in either collection. Large generated closure
diagnostics remain in raw reports; every current root remains in the compact data. Crate hashes
and debug-type ordering can change without semantic progress, which the survey guide distinguishes
from inspected blocker advances. Null and empty blocker text sort distinctly and deterministically.
Twenty host tool tests verify these publication boundaries alongside the existing collection checks.

## Stage 67: checked initialized zeroed storage

The compiler-identified core zeroed operation checks its zero-validity guard, then reconstructs
supported initialized scalar, tuple, struct and array values. Byte arrays use compact SMT storage.
Fieldless direct-tag enums select their compiler zero discriminant, even when it is not the first
declared variant. Reconstruction remains bounded by 16 levels, 256 values and 128 expanded array
elements. Unions/MaybeUninit, pointers, niche/payload enums and restricted integer reconstruction
remain UNKNOWN; no general uninitialized payload or padding read is enabled.

Host/ARM debug and optimized tests cover exact zero fields, later panics, invalid zero domains,
name spoofing and model budgets. Value/type/tag mutations fail; native checks cover valid payloads
and a changed assertion. Targeted fresh-future main probes clear ClockMux configuration, then stop
at foreign critical-section acquisition or numeric MMIO reset-cause access.

## Stage 68: tracked typed shared byte slices

Address formation retains its compiler pointee type before raw casts erase it. Shared byte slice
aggregates keep the source allocation and length; reads encode live backing storage with compiler
field offsets and target endian order. Integers, arrays and padding-free structs are bounded by
128 bytes and 16 levels. Slice bounds, liveness, initialization graphs and frame escapes apply;
static stores retain source reference evidence. Other backends explicitly reject this new domain.

Host/ARM debug and optimized fixtures cover byte copies, partial offsets and live updates.
Wrong endian claims and field/value mutations refute and fail native checks. Numeric origins,
mutable raw slices, padded storage, raw subobjects, invalid bounds, dead storage and escaping
locals remain UNKNOWN. This is not a general raw-pointer memory interpreter.

## Stage 69: preserve backing storage through shared slice adapters

Shared prefix indexing and borrowed-array conversion retain the typed raw slice's backing
reference, including when reached through reference wrappers. Returning an owned byte copy keeps
its copied value. Shared adapter reads still resolve current storage, and returned views cannot
escape frame-owned backing storage or survive its retirement.

The new host/ARM debug and optimized regressions reproduce an incorrectly proved prefix escape
before the fix. Prefix and borrowed-array escapes now remain UNKNOWN at frame-escape checks;
dead backing storage remains UNKNOWN at liveness checks. Valid reads and owned copies prove,
and native checks agree.

## Stage 70: third complete fleet pass and Embassy main boundaries

A fresh scan freezes the corrected analyzer and collects all 32 units and 2,336 roots. Source
outcomes are 492 PROVED, 226 REFUTED and 301 UNKNOWN. Two link encoders now prove; five more source
functions clear their first blocker but stop at mutable range indexing, numeric MMIO or foreign
critical-section acquisition. All earlier proofs and refutations retain their outcomes, with no
root/classification changes. Application sources and dependency/generated-input maps stay unchanged.

Separate fresh-future async main probes pass ClockMux zeroed configuration and reach the platform
boundaries in both RM-C and engineer-upper. Ordinary task-registration probes record the separate
executor storage boundary. Their compact evidence preserves call chains, settings, fingerprints
and scope exclusions without mixing them into the default survey counts or claiming whole-main
coverage. The pass validates 408 Rust tests and 20 survey-tool tests, lint, formatting, release
builds, dependency policy, manual hooks and the documentation build.

## Stage 71: repeatable coverage of every Embassy main

The main survey runner replays all 12 binary factories in distinct async-body, task-registration
and runtime-entry scopes. Source/dependency/generated inputs and report scope/settings are checked
at every boundary. Missing, malformed, timed-out and mutated collections cannot reach the milestone.
The baseline has 12 UNKNOWN bodies, 12 UNKNOWN registration roots and 12 REFUTED runtime roots;
arbitrary runtime state is not boot-failure evidence. The milestone requires a supported PROVED
or REFUTED async-body outcome for every expected main. Explicit, fingerprinted assumption profiles
record a separate conditional milestone. Thirty-two host tool tests pass.

## Stage 72: retained incoming shared storage

Compiler-typed root values retain incoming read-only non-Freeze reference storage, including nested
Spawner executor fields. One interior/mutable storage graph is supported; additional alias-sensitive
graphs remain UNKNOWN. Static stores validate Freeze snapshots against exact pointee shapes and
retain tracked reference escape/liveness evidence. Non-Freeze snapshots remain unsupported.

Host/ARM debug and optimized tests cover guarded stores, refuted assertions, type and value
mutations, dead/frame-owned borrows, alias rejection and invalidating effects. Native mutation
checks agree. Recorded RM-C and engineer-upper registration wrappers prove without startup
assumptions;
this stage does not execute their deferred future bodies.

## Stage 73: retained compiler foreign Rust exports

Metadata-only builds retain compiler reachability and exported-symbol queries. The dependency cache
policy changes so earlier metadata without this evidence is rebuilt. Exact foreign Rust ABI symbols
resolve only to unique, strong, explicit, signature-matched retained Rust bodies. No declaration,
annotation, missing body or native-library boundary becomes a successful implementation. Target
contracts and actual MIR execute.

Compiler integration uses temporary third-party dependency copies and unsafe-forbidden entry
fixtures. Positive return values prove; assertion and implementation-panic mutations refute;
missing or unsupported bodies remain UNKNOWN on host/ARM debug and optimized builds.

## Stage 74: conservative Cortex-M interrupt-register assembly

Exact compiler PRIMASK read/write and interrupt mask assembly shapes use typed operand, target,
option and fallthrough guards. Reads remain arbitrary 32-bit abstractions, with no stable-state or
startup claim. Mask writes invalidate published atomic/startup facts and do not grant
critical-section exclusion. Other assembly remains UNKNOWN. Safe compiler fixtures call existing
Cortex-M dependency
APIs, exercise reachable panics and reject instruction/operand/option mutations.

## Stage 75: compact zero-sized input structures

Compiler-typed, inhabited zero-sized structs, tuples and bounded arrays use shared input shape
information without symbolic scalar values. The existing root input budget remains unchanged;
shape depth and type/field edge budgets remain enforced. Unions, uninhabited types and unsupported
references remain UNKNOWN. Host/ARM debug and optimized fixtures verify large trusted peripheral
outputs with explicit assumptions, failing assertion mutations and unsupported shape boundaries.

## Stage 76: certified uninitialized storage containers

Dependency origin checking recognizes the compiler-identified MaybeUninit uninitialized unit
field and exact core cell constructor forwarding. A narrow bool-to-u8 encoding supports portable
atomic construction. This certifies container provenance without initializing payload bytes.
Shared payload reads before or after stores remain UNKNOWN. Host/ARM compiler fixtures check
stores, refuted mutations, spoofed/initialized unions and stale artifact rejection. The retained
origin cache policy refreshes certificates for these construction rules.

## Stage 77: arbitrary mutable Rust boolean static state

Whole compiler-backed mutable Rust bool allocations at offset zero support valid boolean loads
and typed writes. Each read has a fresh abstraction; neither initializer nor preceding write nor
critical-section assembly establishes startup or exclusion history. Already-taken and stable-read
claims refute with explicit abstraction labels. Numeric addresses, incorrect declared types,
immutable storage and readonly writes remain UNKNOWN. Safe custom MIR fixtures cover host/ARM
and debug/optimized compilation plus initializer mutations.

## Stage 78: compact all-main evidence publication

The main exporter validates complete strict and optional conditional captures against their
inventories and raw proof reports. It rejects subset collection, mismatched paired provenance,
changed policies and unsupported milestone claims. Compact output preserves root scopes, blocker
chains, assumptions, trusted calls and exact source fingerprints without raw solver queries.
Publication is atomic; invalid input cannot replace the previous evidence file. Seven focused
host tests cover capture/report mutations and failed publication.

## Stage 79: certified boolean cell payloads

Boolean static reads extend through exact certified compiler struct/tuple field paths containing
core UnsafeCell, including `Cell<bool>` and nonzero-offset wrappers. Reads remain arbitrary valid
booleans with abstraction reasons. No initializer, write or critical section supplies stable
history. Field/type/origin checks remain bounded; unions and MaybeUninit payloads remain UNKNOWN.
Host/ARM debug and optimized fixtures cover core cells, typed writes and failing history claims.

## Stage 80: all-main conditional first milestone

The fourth full fleet pass at d94334c collects all 32 units and 2,336 roots: 1,075 PROVED,
251 REFUTED and 1,010 UNKNOWN. All 12 registration wrappers gain proofs; rm_c::init gains a
refutation. No previous supported outcomes regress, and all source/artifact checkpoints match.

Final all-main release captures at 7257e00 use the same retained artifacts and default limits.
Strict async bodies have four REFUTED and eight UNKNOWN outcomes. With exactly one recorded
reset-cause hypothesis for each of eight DM robot mains, all 12 async bodies are REFUTED and the
conditional milestone is reached. The unconditional milestone remains false. Each failure records
arbitrary boolean state with startup/exclusion unverified; no boot-time failure is claimed.
Both runs have 12 PROVED registration roots and 12 REFUTED runtime roots under separate atomic
abstractions. Deterministic compact exports preserve scope, assumptions and input fingerprints.

## Stage 81: initialization counterexample domain audit

The twelve main counterexamples use already-initialized arbitrary shared boolean state. Source
inspection finds one board-init call per main and distinct RTT initialization in three mains;
no duplicate boot initialization is demonstrated. Rust runtime reset initializes data/BSS before
calling the selected Rust entry, but reset/hardware/exclusion reachability remains unverified.
Survey and compact evidence explicitly distinguish solver abstractions from native and boot
confirmation. Safe local lifecycle fixtures prove fresh initialization and refute repeated or
arbitrary-state initialization, with native checks and failing initializer mutations.

## Stage 82: bounded larger fieldless enum inputs

Fieldless input enums support at most 256 compiler-declared variants, including sparse signed
and negative discriminants. Exact validity constraints preserve the allowed variant domain.
Payload enums retain the 64-variant cap and all enums retain the 512-value root budget.
Host/ARM debug/optimized fixtures cover valid ranges, refuted bounds, native guard mutations,
256/257 boundaries, oversized payload enums and exhausted multi-argument budgets.

## Stage 83: concrete compiler trait-object dispatch

Concrete reference unsizing retains a compiler-certified type/vtable witness. Exact Virtual
method slots resolve to the actual implementation, preserving reference permissions, mutation,
liveness and effects. Arbitrary dyn roots remain UNKNOWN rather than enumerating implementations.
Host/ARM debug/optimized tests cover associated types, inherited slots, mutable updates, native
implementation mutations, rejected forged coercions and dead/frame-escaping backing.

## Stage 84: compiler-layout raw subobject addresses

Bounded struct/tuple fields and array elements retain containing allocation identities, compiler
layout offsets and child extents. Actual each_mut MIR executes its loop and converts only exact
initialized raw pointer arrays to reference arrays, checking live typed projections, permissions
and pairwise mutable disjointness. Numeric pointers, unions, incompatible anchors, dead or escaping
backing and unsupported symbolic reference-array selections remain UNKNOWN. Host/ARM compiler
and native mutation tests preserve child bounds and reject overlapping or permission-forged data.

## Stage 85: initialized tracked scalar volatile reads

Compiler-identified volatile_load reads only initialized whole retained scalar allocations with
an exact compiler pointee and registered location. Loads preserve integer and floating-point bits,
including NaNs and signed zero. Numeric, static, punned, projected, offset, dead and uninitialized
origins remain UNKNOWN. This grants no MMIO validity, synchronization or hardware effects.
Host/ARM compiler fixtures check positive, refuted and unknown cases with native mutations and
invalidating effects.

## Stage 86: Fifth fleet measurement and refreshed main evidence

The frozen clean `fe25949` analyzer collects all 2,336 roots in 32 units with no assumptions:
1,084 PROVED, 251 REFUTED and 1,001 UNKNOWN. The 1,019 source-function heuristic roots comprise
501 proofs, 227 refutations and 291 unknowns. Nine constructor roots gain proofs; every prior
proof and refutation is preserved. Twenty source roots clear their first blocker but remain
UNKNOWN. Compiler diagnostic identity changes are distinguished from substantive progress.

Fresh all-main captures use the same analyzer and default limits. Strict bodies remain four
REFUTED and eight UNKNOWN; the exact recorded reset-only profile gives twelve REFUTED with
one trusted reset call on each of eight DM mains. Registration remains twelve PROVED and runtime
entry twelve REFUTED. Explicit domain and counterexample labels retain unverified boot reachability
and absent native confirmation. Source and all four artifact checkpoints remain unchanged.

The full implementation passes 446 Rust tests, 41 Python tool tests, formatting, Clippy, release
builds, dependency checks, documentation builds and manual hooks. Compact exports validate both
complete captures before publication; fleet application sources remain untouched.

## Stage 87: Stable compiler diagnostic grouping in fleet comparisons

Compact comparisons preserve raw blockers and outcome transitions while separately grouping
compiler DefId indices, crate hashes and reordered complete dyn Binder entries. Types, array
lengths, paths, operations and malformed lists are not collapsed. The grouping is diagnostic
metadata, not semantic equivalence or proof progress. Mutation tests distinguish actual type and
operation changes. Replaying the fourth-to-fifth comparison separates twenty changed source
keys from nineteen compiler-display-only changes without modifying their UNKNOWN outcomes.

## Stage 88: Typed opaque function-pointer inputs

Valid arbitrary callback inputs retain exact compiler signatures without selecting targets,
addresses or effects. Eager and lazy input fields, Waker tables and exact typed stores support
unused witnesses within the existing input and registry budgets. Opaque invocation, identity
comparisons, address casts and native replay remain UNKNOWN. Concrete known function-item targets
retain ordinary execution and contract behavior. Compiler tests cover positive, refuted and unknown
cases on host/ARM, unsafe signatures, signature mutations and native guard mutations.

## Stage 89: Shared initialized array storage and bounded constants

Owned arrays use concrete immutable shared host storage, detaching changed paths on writes while
preserving Rust copy and allocation identities. Constants validate every initialized occurrence
before lossless exact-type reuse, with 2,048 visits, sixteen levels and 128 array elements. Repeats
validate bounded operands and charge actual shared clone handles within the existing 256-value
budget. Unsupported initialization, payloads and interior mutation remain UNKNOWN. Compiler and
native mutation tests check large tables, repeat values, copy independence and resource boundaries.

## Stage 90: Retained mutable byte slice ranges

Exact compiler core `Range<usize>` SliceIndex::index_mut checks start <= end <= length and returns a
writable byte projection into its original allocation. Nested and empty ranges preserve offsets,
lengths and updates. Invalid bounds refute; readonly, non-byte, arbitrary raw and dead backing stay
UNKNOWN. Host/ARM positive, negative and unknown tests plus native mutations check the model;
lookalike user methods execute their own bodies. Unchecked non-byte iterator adapters remain gaps.

## Stage 91: Sixth fleet measurement and main replay

Frozen clean `901304a` collects all 2,336 roots in 32 units with no assumptions: 1,112 PROVED,
252 REFUTED and 972 UNKNOWN. The source-function heuristic counts 517 proofs, 228 refutations
and 274 unknowns. All previous proofs and refutations remain. Five ordinary configuration/default
helpers gain proofs; eleven async future-construction roots and twelve generated wrappers also
prove, without establishing task-body execution. The new private referee helper refutation
requires a content length outside its two current callers' domains; native confirmation is absent.

Twenty-nine source roots reach different blocker keys, while nineteen diagnostic changes are
compiler display only. DMA storage origins, nested mutable slices, alias constraints, constant
array limits and step limits remain explicit gaps. Every source fingerprint and all four artifact
checkpoints stay unchanged. Fresh strict/reset-only main captures retain the prior outcomes and
exact eight-call conditional policy; boot reachability remains unverified.

All 457 Rust tests, 42 Python tool tests, formatting, Clippy, release builds, dependency checks,
documentation builds and manual hooks pass. Compact exporters validate both complete captures
before publication. Fleet application code remains untouched.

## Stage 92: Compiler-backed root scope in fleet measurements

Inventories expose direct coroutine return types as optional backward-compatible metadata.
The fleet runner checks matching inventory/verification metadata and separates construction from
function-body roots. Exported counts and row indices retain that distinction; legacy missing
metadata remains unclassified. Polling proofs cannot enter a function-only capture. Compiler/native
host/ARM tests prove construction of a panicking future and refute its reached poll; metadata and
scope mutations fail collection without changing proof outcomes.

## Stage 93: Initialized scalar constant tables

Exact bool, integer and f32/f64 constants support 256 elements while composite arrays keep 128.
Every value remains typed, initialized and within the existing 2,048-visit/sixteen-level budgets.
Nested CRC-shaped tables preserve symbolic bounds and raw float encodings. Host/ARM and native
mutations check data, guards, NaN payloads and signed zero; unsupported initialization, 257 scalars
and oversized composites remain UNKNOWN. Older scalar-cap fixtures now test the correct boundary.

## Stage 94: Typed associated-constant storage origins

Schema 2 construction evidence recursively certifies exact monomorphized aggregate constant
items and associated constants from available compiler MIR. The bounded DAG includes every
constant dependency and exact operand/body types. Missing edges, obsolete certificates and
unsupported operations remain UNKNOWN. Retained-origin cache generation four prevents prior
certificate reuse. This grants provenance metadata without payload reads or startup history.
Aggregate constructor parameters still need checked callsite dataflow in the following stage.

## Stage 95: Closed aggregate constructor argument origins

A separate bounded straight-line checker validates actual argument origins and exact fully
monomorphized compiler types before accepting aggregate constructor parameters. Context identities
preserve U32 origins through whole forwarding; composition requires exact diagnostic `Atomic<u32>`
layout. Exact core `Atomic<usize>::new` checks initialized scalar input and layout separately.
Compiler `Option::None` and inhabited fieldless ZST constants retain typed construction evidence.
Callback/reference/union arguments, lookalike atomics and missing graph leaves stay UNKNOWN.
Host/ARM and native data mutations check arbitrary-state reads and constructor changes. Evidence
certifies origins without asserting runtime values, synchronization or startup history.

## Stage 96: Retained unchecked slice iterator access

Exact core unchecked iterator access requires live retained backing, proven cursor/index bounds
and matching compiler element types. Mutable access records at most 256 distinct issued absolute
indices and rejects later conflicting ordinary access. Missing backing, bare snapshots, uncertain
bounds, duplicates and induction histories stay UNKNOWN. Host/ARM compiler tests and safe native
mutations check shared reads, float zip updates and cursor offsets; invalid custom MIR is analyzed
without native undefined behavior.

## Stage 97: Guard unavailable local associated-constant bodies

The fresh fleet inventory exposed a compiler ICE when construction checking queried CTFE MIR for
an abstract local trait associated constant. Both construction checkers now reject definitions
without available bodies before querying compiler MIR. A trait declaration regression checks
continued collection, supported concrete implementations and explicit UNKNOWN for unresolved
construction evidence. The failed capture remains separate and contributes no published outcomes.

## Stage 98: Seventh fleet measurement and main replay

Frozen clean `c908598` collects all 2,336 roots in 32 units without assumptions: 1,113 PROVED,
253 REFUTED and 970 UNKNOWN. All prior 1,112 proofs and 252 refutations remain. Dr16::parse gains
an ordinary body proof; sentry Can1Bus::receive refutes for arbitrary ESC ID 65024 overflowing
512 + esc_id. Its actual constructor uses IDs 2, 1, 4 and 3; firmware reachability and native
confirmation remain unverified. No future factory gains a proof in this pass.

Compiler scope metadata distinguishes 2,232 function-body roots from 104 direct future factories;
50 factory proofs do not execute task polls. Twenty-two source UNKNOWN roots reach different
blocker keys: seventeen DMA origins to numeric MMIO, three CRC tables to byte-view limits and two
iterator callers to retained-source liveness. Nineteen source and 455 generated diagnostic changes
are compiler display only. The missing local associated-constant body failure is guarded and its
incomplete attempt remains excluded. All 243 source fingerprints and four artifact checkpoints
stay unchanged. Complete strict/reset main replays retain four strict refutations/eight unknowns
and twelve conditional refutations under the byte-exact eight-call reset-only policy.

All 464 Rust tests, 44 Python tool tests, formatting, Clippy, release builds, dependency checks,
documentation builds and manual hooks pass. Both compact exporters validate the complete captures
before publication. Fleet application code remains untouched.

## Stage 99: Shared constructor evidence validation

Both conservative constructor languages share body availability, monomorphized MIR loading,
128-block/512-local caps, constant return binding and certificate finalization. The scalar transmute
flow matcher is shared while U32 carrier and exact `Atomic<usize>` identity/layout policies remain
separate. Argument origin admission, context caches and language acceptance stay in their callers.
Focused host/ARM regressions pass; frozen/refactored fixture metadata and certificates are byte
identical. This removes duplicate checks without introducing new construction grants.

## Stage 100: Shared compare-exchange semantics

Integer and pointer CAS share success/failure ordering validation and strong/weak success formulas.
Each weak call still creates a distinct spurious-failure symbol. Primitive receiver/value checks,
integer owned/startup updates and pointer publication invalidation retain their original order and
separate models. Host/ARM regression cases refute equality of two independent weak choices and prove
matching strong-choice properties; existing negative, UNKNOWN and native mutation cases remain.

## Stage 101: Main failure audit and unchanged refactor replay

Source/model audit separates numeric RCC MMIO UNKNOWNs from singleton/RTT/task-pool state-domain
counterexamples. Strict async roots have four refutations and eight unknowns; the existing exact
reset-only profile retains twelve refutations with eight trusted calls. Runtime wrappers unwrap
failed main-task allocation before spawner.spawn. The arbitrary old-word witness 0xffffffff exceeds
safe AtomicBool history, but a valid busy word 0x101 remains SAT in all twelve captured panic
queries. Compiler byte-storage validity alone does not supply the missing safe-library invariant.
The audit retains source/query/model/capture hashes and unverified boot reachability. Fresh global
initialization and exclusive first use are not established by these selected roots.

Frozen clean `a65192d` replays all 2,336 fleet roots with exactly unchanged outcomes: 1,113 PROVED,
253 REFUTED and 970 UNKNOWN. There are no substantive blocker or resource-limit outcome changes;
nineteen source and 455 generated diagnostics change compiler display only. All 243 source hashes
and four artifact checkpoints remain unchanged. Fresh strict/reset main replays also preserve their
outcomes and policy, with no new assumptions. All 464 Rust tests, 44 Python tool tests, formatting,
Clippy, release builds, dependency checks, documentation builds and manual hooks pass. The compact
exporters validate complete evidence before publication. Application code remains untouched.


## Stage 102: Explicit startup history for certified boolean statics

The existing opt-in startup domain now retains certified whole mutable bool and exact core
UnsafeCell/Cell boolean payload values. Integer atomics and booleans share allocation/offset/size
identities, one branch-local history map and scalar initializer decoding. Boolean bytes must be
initialized, provenance-free and encoded as 0 or 1. Typed boolean writes update only their exact
location; nonboolean writes, mixed/overlapping histories and opaque effects discard precision,
including unseen initializers. Writes after invalidation do not restore the premise.

Entry assumptions explicitly cover no external changes to tracked static storage before pointer
publication or opaque calls. Conditional proofs remain PROVED_WITH_ASSUMPTIONS. Default shared
boolean reads remain arbitrary, and async roots still cannot inherit startup facts. This stage does
not verify reset execution, MMIO, interrupt exclusion or any fleet main's boot reachability.

Host/ARM O0/O2 cases cover first/repeated initialization, Cell storage, nonzero-offset payloads,
independent fields, disjoint integer atomic updates, weak-CAS branch histories, boundary and typed
write invalidation, unsupported pointers and initializer mutations. Separate native runs confirm
fresh/repeated outcomes and the mutation. Full workspace tests, lint, formatting, release builds,
dependency checks, tool tests, documentation builds and manual hooks pass.

A diagnostic replay of all twelve runtime wrappers preserves every strict obligation, SMT query
and model from pass eight. Selecting the explicit startup domain instead clears task allocation
and reaches Spawner::spawn, then refutes the Cordyceps stack's next-link-is-empty debug assertion
at stack.rs:129. All twelve failures depend on the still-arbitrary initialized static Option
discriminant; Links::new declares None. This is a missing enum-history model, not a confirmed boot
panic. The existing integer-atomic startup premise enables this traversal; it is not a new default
proof or an effect of boolean history. Local captures remain under
`/tmp/miren-startup-bools-runtime-comparison`, with binary/report hashes and dirty-source
provenance.


## Stage 103: Conditional enum tags and symbolic body-entry evidence

Startup enum discriminants now use rustc's exact typed initializer layout for certified Copy/Freeze
places, including signed sparse tags and niche pointer options. A read-only host snapshot preserves
initialization and provenance with a 1 MiB allocation cap; it grants neither runtime immutable
storage nor payload access. Writes, overlapping histories and opaque effects discard precision.
Host/ARM O0/O2 cases prove fresh tags conditionally, refute initializer mutations and retain UNKNOWN
for uninitialized, unrelated or unsupported payload storage. Independent native runs confirm the
original and mutated initializer outcomes. Ordinary enum observations retain their existing domain.

Proof reports now record bounded symbolic body entry after argument validation and a satisfiable
start-block path. Records retain concrete instance, compiler coroutine identity, source and call
chain; constructors and rejected roots do not establish application poll entry. The 512-record cap
has an explicit truncation flag. Old reports deserialize with no entry evidence. Traversal records
never change proof status or establish native boot reachability.

The main survey separately measures entry into every selected application coroutine from a fresh
future. Missing records, constructors, another coroutine, truncated evidence or incomplete captures
cannot satisfy this milestone. Existing supported-outcome milestones retain their original meaning.
No executor scheduling or hardware instruction is skipped to manufacture a runtime-to-poll proof.
Full workspace tests, lint, formatting, release builds, dependency checks, tool tests, documentation
builds and manual hooks pass.


## Stage 104: All twelve fresh-future application entries reached

Frozen clean analyzer `03e66a2` records entry into the exact application coroutine poll for all
twelve expected Embassy binary mains in both strict and existing reset-profile captures. All traces
fit the 512-entry budget without truncation; sources, concrete instances and factory-rooted call
chains are retained. The fresh-future entry milestone is true with no new assumptions. The
supported-outcome milestones remain separate: strict async bodies have four REFUTED and eight
UNKNOWN outcomes; the exact reset-only hypothesis retains twelve conditional refutations and eight
trusted calls. Registration and runtime outcomes remain twelve PROVED and twelve REFUTED
respectively.

All 72 strict/reset root obligation arrays, including SMT queries, models and call chains, match
pass eight exactly. Sources and dependency/generated artifacts retain their captured hashes.
The compact exporter validates both complete captures before publication. This does not establish
runtime-to-first-poll, hardware boot reachability or complete application panic freedom.

All 470 Rust workspace tests, 48 Python tests, workspace Clippy, formatting, release builds,
dependency checks, documentation builds and manual hooks pass. Application code remains untouched.
Local captures are `/tmp/miren-fresh-entry-{strict,reset}-20261009`; the comparison manifest has
SHA-256
`ce28d8505179a52f167815107df379b5af5000e073f331dd6c80f5e903c3b443`.

## Stage 105: Conditional static pointer-atomic initializer addresses

The explicit startup domain retains null and numeric initializer address bits from exact certified
static pointer atomic storage. Returned values remain raw addresses without pointee provenance;
relocation-bearing initializers and nonzero pointee reads remain UNKNOWN. Ordinary roots and async
entry analysis keep their previous domains. Stores, CAS, opaque calls and interrupt-mask writes
retain conservative global invalidation, including locations that have not yet been read.

Integer and pointer startup reads share overlap and 128-location admission checks after typed cache
lookup. Exact overlapping footprints with incompatible cached types invalidate history. Compiler
receiver, allocation, initialization, extent and target-width checks remain prerequisites.

Host/ARM debug and optimized integration cases cover conditional proofs, refutations and unknowns,
disjoint integer/pointer storage, pointer/integer overlay rejection and opaque-boundary
invalidation.
Changing the null initializer refutes its conditional assertion and fails native execution. Native
ordering mutation coverage remains in place. No application code or assumption profile changes.

Strict and reset-profile main replays still enter all twelve application futures, with all 72
obligation arrays matching the prior captures exactly. The diagnostic startup runtime probe still
refutes Cordyceps' `links.next.is_none()` assertion at `stack.rs:129`: its static Option tag is
abstract after history invalidation. This remains an abstract-model counterexample, with boot
reachability unverified. Static pointer address reads alone cannot establish that queue history.
Captures are `/tmp/miren-startup-pointer-main-{strict,reset}-20261009` and
`/tmp/miren-startup-pointer-runtime-comparison`.

All 472 Rust workspace tests and 48 Python tests pass, as do formatting, workspace Clippy, release
builds, dependency checks, documentation builds and manual hooks.

## Stage 106: Conditional scalar enum store history

Exact certified Copy/Freeze enum stores now preserve startup facts for subsequent tag observations
when every variant contains only bool, integer or float fields. The stored value passes the existing
typed shape and validity checks; tag reads validate it again. Whole enum footprints share the
128-location history budget, and incompatible overlapping cached values invalidate precision.
Branch-local stores and disjoint initializer reads retain their identities. Runtime payload reads
remain unsupported, and ordinary-root tags remain arbitrary legal discriminants.

All variants must meet the scalar restriction, even when storing None. Pointer, callback and
aggregate payload types remain outside this domain. Publication, opaque calls, interrupt-mask writes
and retirement keep their existing invalidation behavior; later enum writes cannot restore history.
Host/ARM debug and optimized cases cover conditional proofs, refutations and unknown payload reads,
branch isolation, disjoint locations and publication. Changing a stored sparse variant refutes the
tag claim and fails native execution.

The queue audit identifies callback/future stores followed by executor pointer publication before
Cordyceps' `links.next.is_none()` guard. Publication ends the existing no-external-change premise.
This stage does not silently reuse the declared None afterward or establish native boot reachability.
Advancing that boundary requires justified publication/exclusion history or a separately recorded
execution premise. Application code and assumption profiles remain unchanged.

Both main profiles still reach all twelve fresh application futures, and all 72 root obligation
arrays match stage 105 exactly. The diagnostic startup runtime probe still stops at the queue guard
in all twelve wrappers; strict runtime obligations also remain unchanged. Captures are
`/tmp/miren-enum-history-main-{strict,reset}-20261009` and
`/tmp/miren-enum-history-runtime-comparison`.

All 474 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass; independent review found no required
soundness fixes.

## Stage 107: Explicit isolated initialization and certified integer payloads

A separate opt-in startup-isolated domain records fresh static initializers and absence of external
Rust storage mutation throughout a zero-argument entry, including after publication. Actual typed
writes retain exact values and compiler type identities; overwritten footprints prevent initializer
resurrection. Destructor-free retirement affects its footprint and requires exact reinitialization.
Opaque calls remain irreversible boundaries. CLI, Cargo configuration and saved-report reanalysis
keep domain selection explicit. Async roots and induction still reject startup premises.

Compiler-identified pointer atomic operations receive original allocation-backed receivers before
value snapshotting. Loads and stores retain actual values; strong CAS compares observed bits and
weak CAS retains fresh spurious failures. Mixed symbolic pointer origins lose pointee rights while
retaining selected address bits. Existing escape/lifetime and receiver validation remain in force.
Concrete stored callbacks execute their actual bodies. No hardware instruction or MMIO validity is
assumed.

Certified primitive integer static reads additionally admit arbitrary valid bits in ordinary roots
and checked initializers/exact writes in startup roots. Bounded UnsafeCell struct/tuple paths require
matching declared origins. Unions, arrays, uninitialized payloads, numeric origins and type punning
remain UNKNOWN. Disjoint scalar histories and the 128-location budget are tested.

The isolated runtime probe passes Cordyceps' queue guard and pointer-CAS validation in all twelve
wrappers. Each remains UNKNOWN when weak-CAS retry exploration reaches the query-size budget; no retry
fairness, hardware validity or successful boot is inferred. Strict runtime obligations remain
unchanged. Both ordinary main profiles still enter all twelve fresh application futures, with all
72 root obligation arrays matching stage 106. Captures are
`/tmp/miren-isolated-main-{strict,reset}-20261009` and
`/tmp/miren-isolated-runtime-comparison`. These diagnostic captures precede the stage commit.

All 490 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Review corrected an invalidated local
pointer store that could otherwise leave stale backing while reporting success; it now remains
UNKNOWN, with a regression. No application code or hardware assumption profile changes.

## Stage 108: Checked returns beyond unfinished weak-CAS retries

Isolated execution now carries branch-local retry counts for compiler-validated pointer weak-CAS
calls in cyclic MIR blocks. After three attempts, revisiting that call block can discard an
unfinished retry frontier only when the current function already has a checked real return. The
frontier records UNKNOWN at its actual callee, source and current call chain before further query
construction. Existing completed return conditions and memory flow into the caller unchanged.
No global budget is reset, and missing returns never become success. Other entry domains and
ordinary finite loops retain their existing execution.

Host/ARM and debug/optimized compiler tests cover caller continuation, a reachable panic, unsupported
pointer access, no-return loops, independent spurious failures and frame escape. A failing actual
postcondition stops continuation; changing the real return value refutes the caller assertion and
fails native execution. The exploration policy provides no retry fairness or loop proof.

All twelve isolated runtime wrappers now continue through checked queue returns to Pender::pend.
Each retains the unfinished weak-CAS obligation and stops next at foreign Rust signature matching;
none reaches SEV or establishes runtime boot. All twelve ordinary runtime obligation arrays match
the prior baseline exactly. Capture: `/tmp/miren-retry-runtime-comparison`.

Strict and reset-profile fresh-future replays remain complete at twelve application entries. All
72 root obligation arrays match stage 107 exactly. Captures are
`/tmp/miren-retry-main-{strict,reset}-20261009`; diagnostic captures precede the stage commit.

All 494 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. No application code or hardware
assumption profile changes.

## Stage 109: Directional callable signature compatibility

Foreign Rust symbol resolution and direct known function-item reification now share an exact
polymorphic signature check. A safe implementation may satisfy an unsafe declaration or pointer;
only the safety qualifier changes. ABI, argument/return types, variadic status and bound variables
remain exact. Reverse changes, unknown targets and separate safe-function-pointer conversions stay
UNKNOWN. Strong unique exports, retained MIR, lifetime, native-library and contract guards remain
in force, and actual bodies execute.

The runtime Pender mismatch came from overly strict signature comparison: its unsafe extern Rust declaration
has the same pointer input and unit output as a safe exported implementation. This was not a
REFUTED panic. Host/ARM and debug/optimized cases prove valid safe exports and direct reifications,
refute bad claims and actual panicking bodies, and retain UNKNOWN for incompatible declarations.
Body and callback mutations also fail native execution.

All twelve isolated runtime wrappers now enter the actual platform __pender body. Each retains
unfinished retry UNKNOWN and stops at unsupported assembly options for the bare SEV instruction
(embassy-executor 0.10.0 platform/cortex_m.rs:13). SEV remains a hardware boundary before the first
executor poll; no event semantics or boot reachability are inferred. All twelve ordinary runtime
obligation arrays remain unchanged. Capture: `/tmp/miren-callable-runtime-comparison`.

Strict and reset-profile fresh-future replays still enter all twelve applications; all 72 root
obligation arrays match stage 108 exactly. Captures are
`/tmp/miren-callable-main-{strict,reset}-20261009`; diagnostic captures precede the stage commit.
All 498 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. No application code or hardware
assumption profile changes.

## Stage 110: Retained aggregate field history

Isolated actual struct/tuple stores now support certified child reads and child updates that
reconstruct the retained parent. Compiler field types and offsets identify the path; transparent
equal-footprint wrappers are accepted through declared fields, while type punning and ambiguous
overlapping identities remain UNKNOWN. Bounds cap depth, fields and visited types. Retained actual
values are validated before and after projection/update, including initialization and reference
liveness. Retirement and opaque effects retain their existing conservative behavior.

Writing Pair { left: 3, right: 4 }, then left = 5 preserves right = 4. The prior test claiming
right = 2 now REFUTES that claim from the actual write instead of remaining UNKNOWN. Host/ARM and
debug/optimized tests cover nesting, tuple/struct padding, transparent fields, branch isolation,
disjoint storage, stale references, retirement, wrong types and opaque boundaries. A stored-value
mutation refutes the claim and fails native execution. No initializer bytes are resurrected.

All 502 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Independent review found no required
soundness fixes. No application code or hardware assumption profile changes.

A complete ninth ordinary fleet pass froze the clean stage 109 analyzer at 80030b0. All 32 ARM
units and 2,336 roots completed collection, with unchanged outcomes: 1,113 PROVED, 253 REFUTED and
970 UNKNOWN, without assumptions. Its source heuristic remains 518/229/272. There are no added,
removed or changed outcomes and no incompatible provenance. Raw capture:
`/tmp/miren-fleet-pass9-20261009/summary.json`. This function-root measurement does not use isolated
startup or establish application polling/boot.

## Stage 111: Ordered slice for_each callbacks

Compiler-resolved core Iterator::for_each now uses the existing tracked slice iterator protocol.
Finite Iter/IterMut backing advances in source order and invokes each actual concrete function-item
or closure body. Callback conditions and memory effects persist, borrowed cursors update, and
closure environments retire only after exhaustion. Exact argument/unit signatures and destructor
guards remain explicit; function-pointer callbacks, unsupported typed slices and ambiguous symbolic
mutable projections stay UNKNOWN. No physical NonNull layout is inferred.

Host/ARM and debug/optimized tests cover nested controller-array resets, captured state, traversal
order, empty/shared iteration, borrowed cursor exhaustion, late-element panic, overflow and wrong
effects. Skipping the final controller reset fails both symbolic analysis and native assertions.
Existing fold and mutable-slice tests retain their outcomes.

Diagnostic ordinary-root replays clear the previous physical NonNull blockers in both
chassis::Chassis::update and arm::Arm::update. Chassis reaches count subtraction at chassis.rs:109:
i32::MIN minus KEY_STEP (2) overflows before clamp. Controller Pid clamp at lib.rs:132 refutes
negative integral_max, including the negative smallest subnormal. Actual reset callback bodies are
entered; no reset summary or input invariant is assumed. Independent rechecks validate complete
queries, feasible paths, reported model bindings and negated safety; adding safety makes each
witness query UNSAT. Native O0/O2 exact key-count helper and actual controller crate reproducers
panic, while exhaustive bounded count/button controls pass.

These are valid arbitrary-root states, not confirmed application defects. Chassis::new/history
keeps counts within ±2000; Arm::new uses nonnegative gains, although standalone public Pid builders
permit negative limits. Full Chassis/Arm application reachability remains unverified. Audit, MIR,
source hashes and native evidence: `/tmp/miren-for-each-stage111/replay/audit.md`. Diagnostic captures
precede the stage commit.

Independent review identified missing retained-reference backing validation before an exhausted
iterator returned. Shared iterator stepping now validates its source against current memory before
either branch, including after every callback continuation. Dead empty backing remains UNKNOWN
through for_each, fold, all and next; corresponding live controls prove on host/ARM and O0/O2.

All 505 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Final strict and reset main replays
retain all 72 obligation arrays exactly. All 12 isolated runtime wrappers retain both the unfinished
weak-CAS retry frontier and the reached SEV hardware instruction as UNKNOWN; ordinary wrappers
retain their conservative outcomes. Captures: `/tmp/miren-for-each-final-main-{strict,reset}-20261009`
and `/tmp/miren-for-each-final-runtime`. No application or hardware assumption changes.


## Stage 112: Known function-pointer iterator callbacks

Concrete callback resolution is shared by fold/rfold, all/any, find_map and for_each. Function items
and closures retain their existing target resolution, environment creation and retirement. An
already-known safe Rust function-pointer value now resolves through its registered exact signature
and executes its actual retained target MIR. No target is guessed from the callable type.

Arbitrary root pointer inputs, callback references, unsafe or non-Rust signatures and missing target
bodies remain UNKNOWN. Existing capture liveness, iterator backing validation, callback destructor,
contract and frame-escape checks remain in place. The change uses ordinary analysis and adds no
entry assumptions or scheduler guarantees.

Four new compiler integration tests cover host/ARM and O0/O2 outcomes, forward/reverse fold order,
last-element mutable effects, conditionally selected targets, predicate and find_map short-circuit
cursor state, callback contract failures and unsupported boundaries. A retained pointer with missing
dependency MIR stays UNKNOWN. Mutating an actual fold callback breaks both analysis and native
execution. The existing slice for_each known-pointer example now proves; closure and function-item
regressions keep their outcomes. All 16 focused iterator tests and the positive native controls
pass.

All 509 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Independent review found no required
soundness fixes. Known pointers to foreign declarations remain conservatively outside this callback
model, even when a Rust export could be resolved elsewhere. No application or assumption changes.

## Stage 113: Hardware event and wait diagnostics

Cortex-M assembly recognizes exact templates before enforcing PRIMASK-specific options and unwind
shapes. `sev`, `wfe` and `wfi` remain UNKNOWN and report that hardware event/wait semantics are
unmodeled. The change adds no hardware execution model, scheduler premise or assembly shortcut.
Supported PRIMASK template, operand, target, option and fallthrough checks are unchanged.

Compiler regressions retain PRIMASK positive, refuted and unknown controls and check all three
hardware instructions in debug and release ARM builds. An isolated copy of the dependency fixture
removes SEV options to match Embassy's bare `asm!("sev")`; it still reports the specific UNKNOWN
boundary without assumptions, trusted calls or modeled execution.

Assembly recognition errors currently bubble to the selected root's function and declaration source
while preserving the deepest failed call chain. This stage documents that attribution limit and
does not change the error representation or claim a full runtime-to-application traversal.

All four ARM assembly and five isolated-startup integration tests pass, including the existing
PRIMASK instruction/option mutation boundaries. Formatting and Clippy pass.

All 510 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Final strict and reset main captures
retain all 72 obligation arrays exactly. All twelve isolated runtime wrappers now retain both their
unfinished weak-CAS retry frontier and a specific unsupported SEV diagnostic, with the actual
__pender call chain. Captures: `/tmp/miren-stage113-main-{strict,reset}-20261009` and
`/tmp/miren-stage113-runtime`. No application or assumption changes.

The complete tenth ordinary fleet pass freezes clean stage 111 analyzer 2169311. All 32 ARM units
and 2,336 roots completed collection: 1,113 PROVED, 255 REFUTED and 968 UNKNOWN, without assumptions.
Exactly the two independently audited Chassis/Arm roots move UNKNOWN to REFUTED; no previous proof
regresses and no roots are added or removed. Source-heuristic counts are 518/231/270. Firmware and
all 243 source-input fingerprints match the ninth pass; every unit's four artifact checkpoints
remain consistent. Raw capture: `/tmp/miren-fleet-pass10-20261009/summary.json`. Deterministic export
validation passes before publication. This function-root survey does not establish runtime polling
or constructor-state reachability.

## Stage 114: Byte-view write budgets

Byte-view updates now bound actual generated array stores rather than the destination allocation
capacity. A fixed five-byte copy into a 136-byte compact array generates five stores; a symbolic
length retains the conservative capacity-many-store bound. The 128-write budget, fixed allocation
capacity, target-width index sorts, exact source/view length equality, region bounds and writable
allocation liveness remain enforced. Typed-byte encoding and chunk-view budgets are unchanged.

Two new compiler integration tests cover host/ARM and O0/O2 with positive, refuted and unknown
outcomes, empty end ranges, guarded offsets, nested regions, 128-store boundary copies and preserved
neighbors in 136-, 256- and 4,096-byte allocations. Retired destinations and writes exceeding the
budget remain UNKNOWN. Guarded symbolic offsets retain proved bounds but can have unsimplified
length expressions and remain UNKNOWN. Mutating an actual copied source byte breaks analysis and
native execution.

Diagnostic ordinary replays clear the allocation-capacity blocker in referee::encode and its two UI
callers. Encode now REFUTES an oversized arbitrary-root payload: reported length 262,135 makes
7 + length exceed the 136-byte buffer. Independent SMT rechecks validate the complete model/path
and failing bounds; adding safety is UNSAT. Under data.len() <= 127, this failure is UNSAT while
the path remains SAT. Actual UI callers supply payload lengths 8 and 21, so this private-root
refutation does not establish a caller defect. Both UI helpers now reach actual CRC16 update_table
and remain UNKNOWN at the unchanged query-size limit. Captures: `/tmp/miren-stage114/replay`.
The complete published survey remains frozen at stage 111 until a fresh whole-fleet capture.

All 17 focused byte-view integration tests pass, including existing chunk, repeated-byte, mutable
range and typed-slice regressions. Formatting and workspace Clippy pass. The existing 129-byte
as_chunks_mut fixture remains UNKNOWN at its separate chunk-view budget.

All 512 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Independent review found no required
soundness fixes. No application or assumption changes.

The stage 114 encode witness is also reproduced by a temporary copy of the complete actual referee
module in debug and release, while all payload lengths 0..127 and both UI helpers pass. Existing
module tests remain included. Source/copy hashes and exact commands are recorded in
`/tmp/miren-stage114/replay/audit/audit.md`; fleet application files are unchanged.

The complete eleventh ordinary fleet pass freezes clean stage 114 analyzer d45d34f. All 32 ARM units
and 2,336 roots completed collection: 1,113 PROVED, 256 REFUTED and 967 UNKNOWN, without
assumptions. Exactly referee::encode moves UNKNOWN to REFUTED; no previous proof regresses and no
roots change identity. Source-heuristic counts are 518/232/269. Both public UI roots now reach CRC16
query-size limits. Firmware/source fingerprints and four artifact checkpoints per unit remain
consistent. Raw capture: `/tmp/miren-fleet-pass11-20261009/summary.json`. Deterministic export
validation passes before publication; the all-main publication remains separately frozen at 03e66a2.

## Stage 115: Shared serialization for oversized typed queries

Typed queries keep their existing per-condition representation when it fits the byte budget. On
overflow, the same original Boolean roots share local let bindings inside one conjunction. No
condition folding, global symbols or larger limits are introduced. Context and Boolean-sort checks
precede serialization; floating-point conditions and non-floating probes retain their original
semantics. Handwritten queries and Horn queries are unchanged. Previously oversized queries trade
per-condition incremental prefix reuse for a bounded complete query; ordinary queries keep their
text and cache keys.

The shared-table regression shrinks from 48,560 to 3,528 bytes under the same 16,000-byte limit.
Equivalent legacy and fallback queries agree on SAT models and UNSAT outcomes, and actual fallback
sibling scopes exercise SAT to UNSAT to SAT session reuse. Complex forest serialization succeeds at
its exact byte length and rejects one byte less. Small query text and single-term printing are
unchanged; foreign-context and non-Boolean roots are rejected. Float conditions remain present in
the full fallback while the separate non-floating probe excludes them.

Synthetic CRC16 fixtures include a 136-byte packet buffer, five header bytes and twelve symbolic
payload bytes. Standard checksum and packet roots prove, the wrong checksum claim refutes, and an
untracked raw pointer stays UNKNOWN on host/ARM at O0/O2. Removing the table-index mask refutes and
fails native execution. These are tool fixtures, with no application rewrites or new assumptions.

Diagnostic actual fleet replays now PROVE referee::ui_delete_all without assumptions. The audited
private encode refutation is unchanged, while ui_number remains UNKNOWN at the same query-byte
limit. The remaining large forest repeats sixteen integer-table ITE lookups; no query limit is
raised. Captures: `/tmp/miren-stage115/replay`.

All 517 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Independent review found no required
soundness fixes. All 72 strict/reset main obligation arrays remain identical to stage 113. All
twelve isolated wrappers retain both unfinished weak-CAS retries and unsupported SEV, with their
actual __pender call chains. Captures: `/tmp/miren-stage115-main-{strict,reset}-20261009` and
`/tmp/miren-stage115/runtime`. No application or assumption changes.

## Stage 116: Exact modular add/sub cancellation

Shared SMT folding recognizes subtraction of an identical retained term from a two-operand
bit-vector addition and returns the other addend. Both operand orders work at every accepted
width. Context, width and arity checks precede simplification; cancellation does not cross extension
nodes, identify unrelated symbols or infer path conditions. The identity is valid modulo the
bit-vector width even when addition wraps, while Rust overflow and byte-region checks stay active.

Two term tests cover all widths from 1 through 256, constant and symbolic retained addends, both
orders, repeated terms and Z3 equivalence at width boundaries. Distinct terms, mixed widths,
foreign contexts and extension controls preserve their conservative behavior. The existing guarded
byte-copy fixture now proves on host/ARM O0/O2; genuinely variable lengths stay UNKNOWN and unguarded
bounds failures stay REFUTED. One new compiler mutation test widens the actual range guard and
fails both proof and native execution. No assumptions or firmware changes.

All 34 focused SMT and byte-view integration tests pass, including the actual guard-widening
mutation on host/ARM at O0/O2 and native execution. Formatting and workspace Clippy pass.

All 520 Rust workspace tests and 48 Python tests pass. Formatting, workspace Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Independent review found no required
soundness fixes. All 72 strict/reset main obligation arrays remain identical to stage 115, and
twelve isolated wrappers retain their unfinished weak-CAS retries and unsupported SEV boundaries.
Captures: `/tmp/miren-stage116-main-{strict,reset}-20261009` and `/tmp/miren-stage116/runtime`.
No application or assumption changes.

The complete twelfth ordinary fleet pass freezes clean stage 115 analyzer 62c944a. All 32 ARM units
and 2,336 roots completed collection: 1,114 PROVED, 256 REFUTED and 966 UNKNOWN, without assumptions.
Exactly referee::ui_delete_all moves UNKNOWN to PROVED; all previous proofs/refutations retain their
outcomes, with no added/removed roots or incompatible provenance. Source-heuristic counts are
519/232/268. Five source UNKNOWN budget-group changes retain UNKNOWN, as does ui_number's changed
CRC query-size diagnostic. Firmware/source fingerprints and artifact checkpoints remain consistent.
Raw capture: `/tmp/miren-fleet-pass12-20261009/summary.json`. Deterministic export validation passes
before publication; main evidence remains separately frozen at 03e66a2.

## Stage 117: Shared constant integer lookup tables

Bounded homogeneous constant integer array choices use shared SMT arrays instead of repeated
conditional chains. The representation preserves target width, signedness, exact element values
and the previous last-element default for every unmatched index. Index keys must fit their bit
width, and actual term sorts and analysis contexts must match declared metadata. Existing compiler
bounds, origin and liveness checks remain authoritative. Symbolic, mixed, Boolean, floating-point
and pointer choices keep their prior behavior. The representation adds no assumptions or larger
budgets.

Independent Z3 equivalence covers full index domains, including out-of-range indices, with signed
and unsigned payload widths through 128 bits and 256-entry tables. Context and forged-width cases
are rejected. Host/ARM O0/O2 compiler fixtures prove guarded table reads, signed exact-value claims
and a CRC16 packet with 21 symbolic payload bytes; wrong checksums refute and untracked pointers
stay UNKNOWN. Changing a signed array entry refutes and fails native execution.

The earlier ui_number query contains sixteen independent 255-branch CRC16 choices, dominating
its 194,879-byte shared forest. A textual prototype replacing those exact choices with one shared
array reduces it to 27,109 bytes; independent Z3 checks establish lookup equivalence over every
32-bit index, including unmatched indices, and retain whole-query UNSAT. These measurements use
saved stage115 evidence; actual caller replays follow release validation.

All 73 binary SMT/symbolic tests and 44 affected integration tests pass, including existing term,
byte-view, scalar-table and owned-iterator regressions. New compiler tests cover host/ARM at O0/O2
and failing native execution after an array-value mutation. Formatting, workspace Clippy and diff
checks pass. No application or assumption changes.

All 525 Rust workspace tests and 48 Python tests pass. Release builds, dependency checks,
documentation builds and manual hooks pass. Actual referee::ui_number now PROVES through both
CRC bodies, with 380 checked obligations, no trusted calls and no entry assumptions. ui_delete_all
remains PROVED and the audited encode refutation remains unchanged. Captures:
`/tmp/miren-stage117/replay`. All 72 strict/reset main obligation arrays match stage 116 exactly.
All twelve isolated runtime wrappers retain unfinished weak-CAS retry frontiers and unsupported
SEV before the first executor poll. Captures: `/tmp/miren-stage117-main-{strict,reset}-20261009`
and `/tmp/miren-stage117/runtime`. These replays do not establish hardware or boot validity.

## Stage 118: Literal-key array reads

SMT Select reads walk Store chains iteratively, skipping only writes at unequal same-sort literal
bit-vector keys. Exact key identity returns the latest matching write; a constant-array base returns
its default. Unknown or symbolic keys stop traversal, preserving that store and the remaining
array. Residual selects are interned directly, avoiding recursive rewriting of long store chains.
No application, library-name rule, memory permission or entry assumption changes.

Three term regressions compare simplified reads with independent Z3 array formulas across
8/16/32/64/128-bit keys, repeated writes, symbolic barriers and conditional payloads. A 512-store
chain checks iterative traversal; foreign-context and mismatched-key-sort controls verify rejection
before folding. Existing byte-view and iterator lifetime compiler tests retain ordinary P/R/U and
native mutation checks. This removes residual layout terms; it does not claim additional CRC or
application coverage before fresh survey evidence.

All 26 focused term, byte-view, lifetime and compact-table tests pass, including host/ARM O0/O2
compiler outcomes and failing native mutations. Formatting and Clippy pass.

Byte-expression cost tests retain their exact P/R/U outcomes, nonempty complete-query requirement,
60,000-byte ceiling, native positives and trailer-mutation refutation. They no longer require
particular let/extract syntax: exact read-over-write folding can remove resolved byte reads.
The trailer mutation is checked on both host and ARM targets.

Full workspace execution passes all 525 tests outside the affected byte-cost suite; its three
updated tests pass on targeted replay, completing 528 passing Rust cases. All 48 Python tests,
formatting, Clippy, release builds, dependency checks, documentation builds and manual hooks pass.
Actual referee replays retain ui_number/ui_delete_all PROVED and encode REFUTED without assumptions.
All 72 strict/reset main obligation arrays match stage 117 exactly; twelve isolated wrappers still
record unfinished weak-CAS retries and unsupported SEV. Captures: `/tmp/miren-stage118/replay`,
`/tmp/miren-stage118-main-{strict,reset}-20261009` and `/tmp/miren-stage118/runtime`.


The complete thirteenth ordinary fleet pass freezes clean stage 117 analyzer 2d183c7. All 32 ARM
units and 2,336 roots completed collection: 1,115 PROVED, 256 REFUTED and 965 UNKNOWN, without
assumptions. Exactly referee::ui_number moves UNKNOWN to PROVED; all previous proofs/refutations
retain outcomes, with no added/removed roots or incompatible provenance. Source-heuristic counts
are 520/232/267. Nineteen source and 455 generated UNKNOWN diagnostics change only compiler display;
three source solver/step/time grouping changes retain UNKNOWN. All 243 source fingerprints and
artifact checkpoints remain consistent. Raw capture: `/tmp/miren-fleet-pass13-20261009/summary.json`.
Repeated deterministic exports are identical before publication. Main evidence remains separately
frozen at 03e66a2; hardware and boot validity are unverified.

## Stage 119: Fieldless enum array choices

Bounded fieldless enum input arrays can select an element at a symbolic index by selecting the
integer discriminant and preserving the unchanged complete variant inventory. Every inventory must
agree on the enum's Adt names, ordinal positions, exact discriminants, Option metadata and empty
fields, as well as signedness and actual SMT width. Foreign analysis contexts and forged width
metadata are rejected, including singleton index choices. Duplicate tags are checked by their
represented bits, retaining legitimate sign extension without admitting truncated collisions.
Payloads and mixed constructed/symbolic choices remain UNKNOWN. The existing bounds obligations and
array budgets remain unchanged.

Two binary unit tests cover retained signed sparse tags and malformed inventories, payloads, context
and width controls. Two compiler tests cover host/ARM O0/O2 positive/refuted/unknown cases, returned
enum values, casts, matches, unguarded bounds failure and actual index mutation. Native positives
pass; shifting the actual selected index breaks proof and native execution. All 75 binary tests, 17
SMT term tests and ten affected integration tests pass in the applied checkout. Formatting and
workspace Clippy pass. Full checks and fleet outcomes are separate.

Pass 12 has one exact source first blocker for this capability:
devices::dr16::keys::KeyTracker::state (shared/devices/src/dr16/keys.rs:107), whose body reads its
18-element Press array at key as usize. The report call chain contains only
dr16::keys::KeyTracker::state. Unchecked-iterator source-liveness
checks remain intact; they require a separate root-lifetime view rather than accepting Freeze
snapshots as retained allocations.

All 532 Rust workspace tests and 48 Python tests pass. Formatting, Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Actual KeyTracker::state now PROVES
without assumptions; ui_number/ui_delete_all remain PROVED and encode retains its audited bounds
refutation. Capture: `/tmp/miren-stage119/replay`. All 72 strict/reset main obligation arrays match
stage 118 exactly; twelve isolated runtime wrappers retain unfinished weak-CAS retries and
unsupported SEV. Captures: `/tmp/miren-stage119-main-{strict,reset}-20261009` and
`/tmp/miren-stage119/runtime`. No application or hardware assumption changes.

## Stage 120: Incoming immutable storage lifetime

Exactly one eligible top-level incoming shared `Freeze` reference retains its pointee in
caller-owned environment memory before root execution. Valid incoming Rust borrow semantics supply
in-call liveness; a copied immutable snapshot supplies no lifetime evidence. The allocation belongs
to neither the reference local nor a callee frame. Returned and projected reborrows preserve the
actual allocation and read-only capability. Root reference-local `StorageDead` therefore leaves
caller storage live, while actual frame-owned and dead backing remain subject to existing guards.

Eligibility inspects every root argument and all normalized compiler fields and enum variants,
within depth 16, 512 type nodes and 256 fixed-array elements. Primitive scalars, plain arrays,
tuples, structs and enums qualify. Reachable references, raw pointers, interior mutation, unions,
function pointers, unsized slices and competing borrowed/pointer-bearing arguments cannot acquire
this new identity. Plain owned scalar aggregates may coexist. Ineligible roots retain their
existing snapshot/interior domains; original input construction and depth budgets stay unchanged.
No entry assumptions or hardware facts are added.

Shared byte borrowing keeps an actual tracked allocation path before the existing byte snapshot
shortcut. Snapshot-only values receive no invented allocation. Atomic and static shortcuts remain
unchanged. Unchecked iterator cursor, bounds, alias and liveness checks, frame escape checks and
opaque memory invalidation remain active. Opaque effects cannot revive invalidated storage, and
shared incoming references grant no ordinary write rights. The model establishes caller storage
through the analyzed call, not an unbounded post-return lifetime.

Compiler fixtures cover shared/projected/byte zip, actual returned views, reference-local
`StorageDead`, address identity and nested motor/Option feedback field views. Wrong claims refute;
competing shared/mutable/interior/raw-pointer inputs, owned nested references/pointers, shared
writes and dead root/callee backing stay UNKNOWN. Host/ARM O0/O2 controls report no entry
assumptions or trusted calls. Changing the actual zipped payload assignment refutes and fails
native execution.
A separate labeled fixture-only trusted summary omits memory effects; reading its retained incoming
byte view stays UNKNOWN with dead-storage evidence and exactly one reported trusted call. This
regression adds no application assumptions.

Source inspection finds plain scalar/array fields in dr16 Raw and scalar/Option motor fields in
Can1Bus. A similarly shaped feedback-view fixture proves; actual fleet outcomes are left to
post-validation replays. Missing bodies, hardware boundaries and remaining budget/iterator
restrictions stay unsupported. No firmware files are changed.

All 75 binary tests and 60 affected integration tests across fourteen suites pass, including
reference lifetime, unchecked/owned iterator, byte, atomic, lazy-input and term regressions.
Formatting, workspace Clippy and diff checks pass. Independent review found no required soundness
fixes. No application or assumption changes.

Four earlier UNKNOWN fixture expectations now follow actual retained provenance. Single incoming
scalar references support raw address creation and zero offset, and an incoming array reference
supports its checked element address. Three stale snapshot names become incoming-reference names.
The raw byte-subobject fixture also proves because its real caller-frame Wire allocation stays live
through the helper and assertion; it has no incoming arguments and no escaping reference. Each
suite adds a multiple-shared-input UNKNOWN counterpart, preserving snapshot-only provenance
coverage. Existing native tests check the three returned address identities and execute the live
byte-subobject assertion. All thirteen tests across these four suites and the new immutable suite
pass, including existing raw-read, dead-backing, alias, extent and mutation controls. No additional
implementation changes are needed.

Full workspace execution passes all 523 tests outside the four affected provenance suites; all
eleven updated tests in those suites pass on targeted replay, completing 534 passing Rust cases.
All 48 Python tests, formatting, Clippy, release builds, dependency checks, documentation builds
and manual hooks pass. Actual dr16::Dr16::from_raw and hardware::Can1Bus::velocities now PROVE
without entry assumptions or trusted calls, with 32 and 16 checked obligations respectively.
KeyTracker::state and both UI helpers retain their proofs; encode retains its audited bounds
refutation. Captures: `/tmp/miren-stage120/replay/{devices,sentry}`. All 72 strict/reset main
obligation arrays match stage 119 exactly; twelve isolated runtime wrappers still record unfinished
weak-CAS retry frontiers and unsupported SEV. Captures:
`/tmp/miren-stage120-main-{strict,reset}-20261009` and `/tmp/miren-stage120/runtime`.

## Stage 121: Certify NonZero getter identity

The old getter model accepted any function named get with a NonZero input and integer output.
A local get returning zero therefore made assert!(get(value) == value.get()) falsely PROVED,
although valid value=1 fails natively. The defect reproduced on host/ARM O0/O2 with the actual
lookalike body retained.

Recognition now requires the diagnostic NonZero crate, an associated method under an inherent
implementation, an instantiated owner exactly matching the receiver, and the safe nonvariadic
Rust signature returning `NonZero<T>`'s exact primitive T. Existing typed wrapper and value checks
remain. User free functions and local trait methods execute their actual bodies; missing bodies
and unrelated unsupported input types stay UNKNOWN. No constructor capability is added.

Three integration tests cover host/ARM O0/O2 return/panic lookalikes, real unsigned/signed/usize
getters, wrong claims, unrelated inherent/string methods and an unavailable dependency getter.
Model attribution assertions ensure only the core getter receives the NonZero model. Changing an
actual free getter body refutes the positive claim and fails native execution. All nine focused
integration tests pass, including existing root-domain and zeroed-value regressions. Formatting
and workspace Clippy pass in the applied checkout. Full checks and coverage replays follow.

All 537 Rust workspace tests and 48 Python tests pass. Formatting, Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. The original saved false-proof
reproducer now REFUTES on host/ARM at O0/O2 using the release analyzer. Captures:
`/tmp/miren-stage121/reproduction`. Actual Dr16, KeyTracker, Can1Bus and UI proofs remain intact;
encode retains its audited bounds refutation. Captures: `/tmp/miren-stage121/replay`.
All 72 strict/reset main obligation arrays match stage 120 exactly, and twelve isolated runtime
wrappers retain unfinished weak-CAS frontiers and unsupported SEV. Captures:
`/tmp/miren-stage121-main-{strict,reset}-20261009` and `/tmp/miren-stage121/runtime`.

A separate compiler-identity audit checks 23 free/trait lookalike roots on host/ARM at O0/O2.
All 92 outcomes agree with actual return/panic bodies, native controls pass, and no lookalike
receives a library model or trusted call. No additional defect was found in this bounded audit.
Evidence: `/tmp/miren-model-dispatch-audit/audit.md` and `validation.json`. Constructor/niche
dispatch is excluded from this audit and remains unsupported here.

## Stage 122: Exact optional NonZero integer representation

The actual core NonZero::new body lowers to an integer-to-Option transmute. Support now requires
the exact Option lang item, core NonZero diagnostic identity and the same primitive integer type.
Compiler layouts must certify matching width, signedness, size and alignment; initialized full
integer validity; nonzero-only inner validity; zero field offsets; and exactly the None-at-zero,
Some-untagged niche with the canonical variant and field shapes. No constructor-name shortcut,
body fabrication or entry assumption is added.

The original integer expression supplies the two-layer core NonZero payload and selects the
actual semantic None/Some discriminants. No nonzero constraint removes the None case. Existing
variant projection checks require a proven Some branch before accessing its payload. Different
primitive types, non-core wrappers, pointer/bool niches and missing metadata retain conservative
outcomes; missing bodies remain UNKNOWN.

Two integration tests cover every signed/unsigned primitive family and target pointer width on
host/ARM at O0/O2, including zero, negative values, wrong claims, unwrap refutations and forged
layout/projection controls. Reports establish that actual core constructor bodies execute. A real
None-branch mutation refutes and fails native execution. Before application, 75 binary tests and
19 integration tests across six suites passed (94 total), alongside formatting and affected Clippy.
Both new integration tests pass in the applied checkout. Formatting, affected Clippy and diff
checks pass. Full required checks and actual coverage replays follow.

All 539 Rust workspace tests and 48 Python tests are accounted for by the full run plus the
three-test contract-work replay. The full run passed 536 tests outside that suite; its stale
forward-transmute diagnostic expectation was updated to the next unsupported reverse
NonZero-to-integer transmute. guarded_power remains UNKNOWN, and the suite's status, native
and mutation controls pass. Formatting, Clippy, release builds, dependency checks, documentation
builds and manual hooks pass.

The actual dm_mc02::nominal_bit_timing now PROVES without assumptions. Dr16, KeyTracker,
Can1Bus and both UI proofs remain intact; encode retains its audited bounds refutation.
Captures: `/tmp/miren-stage122/replay`. All 72 strict/reset main obligation arrays match stage 121
exactly; twelve isolated runtime wrappers still record both startup premises, unfinished
weak-CAS retry frontiers and unsupported SEV. Captures:
`/tmp/miren-stage122-main-{strict,reset}-20261009` and `/tmp/miren-stage122/runtime`.

## Fleet publication 15: Preserve corrected models and new software proofs

The complete frozen clean 9f2c7c9 collection has 1,118 PROVED, 256 REFUTED and 962 UNKNOWN roots
across all 32 units, with no assumptions. Among 1,019 source declarations, 523 PROVE, 232 REFUTE
and 264 remain UNKNOWN. Compared with published pass 13, KeyTracker::state, Dr16::from_raw and
Can1Bus::velocities move UNKNOWN to PROVED; every previous proof and refutation retains its
outcome. No roots were added/removed and no analysis configuration is incompatible. The corrected
core NonZero getter identity is included; stage 122 constructors are outside this frozen run.

All 243 firmware input fingerprints and four artifact checkpoints per unit remain unchanged.
The exporter repeats byte-for-byte; raw diagnostics remain separate from normalized display
changes. The separately frozen 03e66a2 main evidence is preserved. Raw capture:
`/tmp/miren-fleet-pass15-20261009`; deterministic publication compares against pass 13.

## Stage 123: Bounded lazy enum inputs

Lazy input shapes include compiler-certified Freeze enums whose complete payload graph already has
supported lazy shapes. Tags use a full-domain unsigned selector mapped through exact compiler
discriminants. Every variant stays possible and no invalid tag is introduced, including sparse
signed representations. Complete names, ordinal positions, fields and Option metadata remain
available to the ordinary interpreter. Payload symbols are independent across variants and repeated
array occurrences; repeated access to one occurrence retains its identity.

Shared enum caps stay at 64 payload or 256 fieldless variants. Descriptor nodes remain bounded by
512, depth by 16 and reserved symbols by 262144. Every variant reserves its wrapper slot before
payload slots. The first unused wrapper slot holds the selector, preserving the Boolean root context
seed even for direct large enum inputs. Unions, references, pointers, interior mutation and
restricted payload shapes retain eager/UNKNOWN fallback. No entry assumptions, application edits or
constructor shortcuts.

One binary test checks exact selector/payload symbol ranges and repeat materialization. Two compiler
tests cover host/ARM O0/O2 positive/refuted/unknown outcomes, direct root enum payloads, signed
sparse tag reachability, same-occurrence identity, independent occurrences, immutable copies with
late mutation and refusal/budget controls. Payload/fieldless variant caps remain UNKNOWN past
64/256, as do reserved-symbol exhaustion and unsupported nested payloads. Changing the actual
observed Boolean field refutes and fails native execution. All 76 binary and 15 affected compiler
integration tests pass in the isolated preparation checkout; formatting and Clippy pass.

Pass 14 and completed pass 15 record eight source roots stopped by eager Bench.motors expansion. The
primary replay is bench::Bench::watching, bench.rs:554, whose body returns only self.watching; its
call chain contains only that root. Bench source uses plain integer/float/byte-array records, Option
and driver enums; source inspection finds no unsupported reference, NonZero, raw pointer, union or
interior payload. Compiler descriptor eligibility and actual fleet outcome still require root-owned
replay. Other roots can encounter later formatting, alias or solver boundaries.

All 542 Rust workspace tests and 48 Python tests pass. Formatting, Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Actual bench::Bench::watching
now PROVES with its real compiler input shape, executing the method body with no assumptions or
trusted calls. Dr16, KeyTracker, Can1Bus, nominal_bit_timing and both UI proofs remain intact;
encode retains its audited bounds refutation. Captures: `/tmp/miren-stage123/replay`.
All 72 strict/reset main obligation arrays match stage 122 exactly. Twelve isolated runtime
wrappers retain both startup premises, unfinished weak-CAS retry frontiers and unsupported SEV.
Captures: `/tmp/miren-stage123-main-{strict,reset}-20261009` and `/tmp/miren-stage123/runtime`.

## Fleet publication 16: Exact optional integer constructor proof

The complete clean frozen 738c142 collection has 1,119 PROVED, 256 REFUTED and 961 UNKNOWN roots,
with no assumptions. Source declarations have 524 PROVED, 232 REFUTED and 263 UNKNOWN outcomes.
Only dm_mc02::nominal_bit_timing changes UNKNOWN to PROVED versus pass 15; all previous proofs
and refutations remain intact. No roots were added/removed and no analysis configuration differs.
Stage 123 lazy enums are outside this frozen run. All 243 firmware fingerprints and four artifact
checkpoints per unit remain unchanged. Export repeats byte-for-byte. The separately frozen main
evidence remains preserved. Raw capture: `/tmp/miren-fleet-pass16-20261009`.

## Stage 124: Certified NonZero extraction and guarded bit operations

Actual u8::checked_pow advances through the reverse `NonZero<u8>` to u8 MIR transmute, intrinsic
ctlz_nonzero and ShlUnchecked. A small shared compiler inner-type/scalar certificate preserves
stage 122 identity, range, size, alignment and field-offset checks. Reverse extraction retains the
original scalar only when exact modeled storage agrees and zero is infeasible under existing
conditions. No source-validity assumption is injected.

Compiler-identified core ctlz_nonzero reuses exact leading-zero counting with a proven nonzero
operand and exact primitive signature. Possibly-zero or zero operands remain UNKNOWN. MIR
ShlUnchecked validates compiler scalar identity and proves the original count below the left width
before any narrowing or masking; negative signed, out-of-range and unproved counts remain UNKNOWN.
Zero shift counts/values execute normally. The guarded-power fixture becomes PROVED; unchecked
power reaches unavailable core overflow-panic MIR and remains UNKNOWN.

Two integration tests cover primitive widths/signs, guarded branches, negative values, exact count
results, bit-position native controls, shift boundaries, invalid layouts/projections and lookalike
bodies on host/ARM O0/O2. Mutating reverse extraction or the actual guarded-power claim refutes and
fails native execution. Existing constructor, getter-identity and integer-intrinsic regressions
remain checked. No direct fleet pow call site or reverse-transmute blocker was found in the saved
survey/source audit, so no fleet outcome gain is claimed. Applied-checkout validation passes 76
binary tests and 11 integration tests across five suites (87 total). Formatting, affected Clippy
and diff checks pass. Full required checks and actual coverage replays follow.

All 544 Rust workspace tests and 48 Python tests pass. Formatting, Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Bench, Dr16, KeyTracker,
Can1Bus, nominal_bit_timing and both UI proofs remain intact; encode retains its audited bounds
refutation. Captures: `/tmp/miren-stage124/replay`. All 72 strict/reset main obligation arrays
match stage 123 exactly. Twelve isolated runtime wrappers retain both startup premises, unfinished
weak-CAS retry frontiers and unsupported SEV. Captures:
`/tmp/miren-stage124-main-{strict,reset}-20261009` and `/tmp/miren-stage124/runtime`.

## Fleet publication 17: Lazy enum proof and audited root bounds failure

The complete clean frozen b6d154e collection has 1,120 PROVED, 257 REFUTED and 959 UNKNOWN roots,
without assumptions. Source declarations have 525 PROVED, 233 REFUTED and 261 UNKNOWN outcomes.
Only Bench::watching moves UNKNOWN to PROVED and run UNKNOWN to REFUTED versus pass 16.
No previous proofs/refutations are lost, roots added/removed or analysis configurations changed.
All 243 firmware fingerprints and four artifact checkpoints per unit remain unchanged; export
repeats byte-for-byte. Stage 124 guarded bit operations are outside this frozen run.

run reaches actual Line::as_str with a compiler-valid Typed::Line len=88 and byte capacity 80.
Saved SMT/path/witness checks are SAT; adding len<=80 makes that failure UNSAT. Unchanged console
source and actual Bus/Kind declarations pass nine native tests at O0/O2, reproducing the exact
bounds panic and covering valid lengths, UTF-8 and feed controls. Source branch induction from
LineReader::NEW preserves len<=80, so this is an audited arbitrary root-input refutation, not a
confirmed firmware-entry defect. No assumption or application rewrite. Audit:
`/tmp/miren-stage123-run-audit/audit.md`; raw capture: `/tmp/miren-fleet-pass17-20261009`.

## Fleet publication 18: Preserve outcomes after guarded bit-operation refactor

The complete clean frozen 6d83034 collection retains every pass 17 outcome: 1,120 PROVED,
257 REFUTED and 959 UNKNOWN, with no assumptions. Source declarations remain 525 PROVED,
233 REFUTED and 261 UNKNOWN. No proof/refutation regressions, roots added/removed or incompatible
analysis configurations occur. Stage 124 compiler improvements introduce no observed fleet gain.
All 243 firmware fingerprints and four artifact checkpoints per unit remain unchanged; export
repeats byte-for-byte. The audited run bounds witness and separately frozen main evidence remain
preserved. Raw capture: `/tmp/miren-fleet-pass18-20261009`.

## Stage 125: Retained finite mutable ranges and ordered find

Finite compiler-typed integer/tuple array ranges retain their original tracked allocation and
projection through mutable iterators. Scalar widths/signs/sorts/context and recursive tuple
arity are checked against the actual element type. Checked region/index translation preserves
writes and source liveness, including empty/exhausted `for_each` and `fold` consumers. Existing
allocation, shape, iteration and solver limits are unchanged.

Core `Iterator::find` invokes the actual concrete predicate with a temporary shared `&Item`,
keeps false-predicate effects before the next item, and returns the original first match.
Retiring each temporary checks for escaped references. Storage paths preserve every enclosing
shared restriction. Actual compiler no-retag dereference copies narrow mutable references to
read permission while preserving identity; ordinary forged mutable exposure stays unknown.

Two new compiler integration tests run positive/refuted/unknown cases on host/ARM at O0/O2,
valid native execution, and a callback increment mutation that fails proof and native execution.
Focused validation: 76 binary tests plus 27 affected compiler integration tests (103 total),
formatting and cargo lint. Full required checks and actual fleet replay follow.
Expected workspace Rust test count: 546.

All 546 Rust workspace tests and 48 Python tests pass. Formatting, Clippy, release builds,
dependency checks, documentation builds and manual hooks pass. Four affected integration tests
also pass after refining non-byte range diagnostic names; byte diagnostics remain identical.
Actual Sniff::saw now REFUTES at its 16-element prefix bound, with Bus::Can2 and len=24. Saved
query and witness are SAT; adding len<=16 makes the failure UNSAT. Unchanged struct/method/Bus
source reproduces the exact bounds panic in native O0/O2 controls. Constructor-shaped prefixes,
appends, repeats and full capacity pass. Command::Sniff starts len=0 and saw preserves len<=16,
so this is an audited root-input refutation, not an established firmware-entry defect. Audit:
`/tmp/miren-stage125-sniff-audit/audit.md`; captures: `/tmp/miren-stage125/replay`.

The separate normalized forged-MIR permission audit changes the old PROVED write into UNKNOWN
on host/ARM O0/O2; valid shared reads and mutable reborrows stay PROVED. Invalid MIR is never
executed natively. This corrects a missing capability refusal without claiming a reachable
application bug or a complete borrow/alias model. Audit: `/tmp/miren-stage125-audit/audit.md`.
All 72 strict/reset main obligation arrays match stage 124 exactly. Twelve isolated runtime
wrappers retain both startup premises, unfinished weak-CAS frontiers and unsupported SEV.
Captures: `/tmp/miren-stage125-main-{strict,reset}-20261009` and `/tmp/miren-stage125/runtime`.

## Fleet publication 19: Retained finite ranges reach Sniff bounds

The complete clean frozen 938e9af collection supports one additional root: Sniff::saw moves
UNKNOWN to REFUTED. Totals are 1,120 PROVED, 258 REFUTED and 958 UNKNOWN. Source declarations
are 525 PROVED, 234 REFUTED and 260 UNKNOWN. All previous supported outcomes remain intact;
no roots are added/removed and no incompatible configurations occur. All 243 source fingerprints
and four artifact checkpoints per unit remain unchanged. The new bounds witness is audited
against native execution and the constructor invariant, without claiming boot reachability.
Raw capture: `/tmp/miren-fleet-pass19-20261009`; the separate main publication remains unchanged.

## Stage 126: Explicit STM32H723VG and STM32F407IG initialization hypotheses

Three opt-in ordinary contract profiles target the eleven H723VG DM-MC02 mains, the F407IG
RM-C main, and their combined twelve-unit policy. Every reason names exact device/board clocks,
physical access and ready-poll termination premises, successful first singleton initialization
and Rust-valid exclusively owned tokens. The H7 reset-status boundary retains its narrow
hardware hypothesis. HAL initialization omits modifies, conservatively invalidating tracked
Rust storage. No analyzer default, application source, instruction model or alias rule changes.

The combined actual replay completes all 36 roots without collection errors. Three async bodies
retain unconditional pre-initialization RTT refutations. Eight H7 bodies execute past trusted
initialization into PC15 GPIO construction; the F4 body reaches LED GPIO construction. These
nine are conditional UNKNOWN at actual Gpio::bsrr numeric pointer arithmetic. Registration
remains twelve PROVED and ordinary runtime entry twelve REFUTED. The fresh-future entry milestone
remains reached; neither supported-outcome milestone is reached by this broader profile.
Existing reset-only published outcomes remain distinct. Raw evidence:
`/tmp/miren-stage126-main-stm32-20261009`.

Independent review approves exact device selectors, board-clock premises, initialization effects
and unsupported ownership gates. All 546 Rust workspace tests and 48 Python tests pass;
formatting, cargo lint, release builds, cargo deny, documentation build and manual hooks pass.
The profile uses existing analyzer behavior; strict defaults and the published reset-only main
capture remain unchanged.

## Stage 127: Public external model API and exact conditional GPIO writes

Public HardwareModel/HardwareDevice/MmioRegion/MmioWriteRegister DTOs and builders compose with
ContractConfig. Optional hardware policies serialize only when present; both file and in-memory
validation enforce versions, device32-bit domain, bounded disjoint peripheral regions and exact
aligned u32 write registers. A host builder example emits H7/F4 policies through the same API.

The interpreter admits proven nonwrapping forward numeric byte transports without granting Rust
allocation/reference rights. Original unsigned core add/byte_add counts are checked before
conversion; subtraction/wrapping/negative transports are refused. Actual intrinsic stores require
exact primitive or certified transparent full-range u32 types. Rust callbacks execute. Each used
model records its exact device premise, including later UNKNOWN/REFUTED roots. External writes
conservatively invalidate existing publication/startup histories. There is no readback model,
SEV instruction model, scheduler guarantee, opaque success or firmware rewrite.

Two public API unit tests and two compiler integration tests cover conditional proof, mutation
refutation/native failure, unsupported accesses/device/layout/counts, missing policy, host-width
mismatch and interference invalidation. Three Python policy/export tests preserve exact opt-in
assumptions and reject policy changes or startup/induction leakage. Independent review approves
the final boundaries. Full validation expects 550 Rust and 51 Python tests.

The combined actual twelve-main replay completes all 36 scopes with no collection errors:
nine bodies execute modeled BSRR writes then remain conditional UNKNOWN at PUPDR reads;
three retain earlier unconditional RTT refutations. Registration remains twelve PROVED and
ordinary runtime entry twelve REFUTED. Every fresh application body remains entered. This
conditional traversal progress adds no completed main proof. Capture:
`/tmp/miren-stage127-main-gpio-20261009`; previous profiles/publications stay separate.

All 550 Rust workspace tests and 51 Python tests pass, along with formatting, cargo lint, release
builds, cargo deny, documentation builds and manual hooks. The separate strict twelve-main
capture matches all 36 prior stage125 obligation arrays exactly, without assumptions:
`/tmp/miren-stage127-main-strict-20261009`. Model builder JSON normalizes identically through the
Rust API and Python policy validator for both devices.

## Stage 128: Exact independent MMIO reads and read-modify-write callbacks

Public MmioReadRegister and with_read_register opt into hardware schema 2. Empty read lists
remain omitted, and schema 1 rejects nonempty reads. Schema 2 supports exact independent read
and write permissions, including read-only policies. The primitive/transparent full-range u32
certificate is shared by loads and stores. Each admitted numeric volatile read creates a fresh
arbitrary word with an explicit device-correlation abstraction label. Read-modify-write bodies
and callbacks execute, and reads retain conservative interference invalidation. Ordinary retained
RAM reads keep their existing model. There is no readback, stable register or readiness promise.

Native replay explicitly refuses any hardware configuration or recorded hardware-model premise,
including an unused policy before an earlier counterexample. Three compiler tests plus one DTO
unit cover independent samples, conditional proofs, correlation/constant-claim refutations,
callback mutations with pure native execution, direction/layout/device/width refusals, unchanged
RAM reads, schema compatibility and used/unused native-replay refusal. Two Python tests validate
versioned policy permissions/premises. Independent review approves the implementation and models;
full validation expects 554 Rust and 53 Python tests.

The complete twelve-main schema-2 replay retains three RTT refutations and nine conditional
UNKNOWN outcomes. All nine execute BSRR and read PUPDR, then enter the actual setter callback
and stop at Pupdr::to_bits enum-to-u8 Transmute. This is a strict Rust translation gap now exposed
by the hardware model, not an MMIO read failure. All registration/runtime outcomes and the fresh
application-body entry milestone remain unchanged. Capture:
`/tmp/miren-stage128-main-gpio-rmw-20261009`.

All 554 Rust workspace tests and 53 Python tests pass, along with formatting, cargo lint,
release builds, cargo deny, documentation builds and manual hooks. Positive, negative and unknown
compiler controls include native callback mutation failures; hardware replay remains refused.
The separate strict stage-128 twelve-main capture matches all 36 stage-127 obligation arrays
exactly, without device assumptions: `/tmp/miren-stage128-main-strict-20261009`.

## Stage 129: Compiler-certified fieldless enum representation

Strict enum-to-integer Transmute now requires an explicit integer repr and exactly that primitive
as target. The compiler must certify a bounded non-Drop fieldless initialized direct scalar layout
with matching size, ABI alignment, tag width/signedness and zero offset. Every compiler tag is
checked against scalar validity and every represented variant against exact compiler metadata.
Symbolic inventories must be complete and their existing tag must have proven exact-set membership.
Conversion preserves represented bits without adding a precondition or external premise.

Three internal tests reject forged identities/tags/inventories, wrong context/type metadata and
sparse holes. Two compiler integrations cover host/ARM O0/O2 concrete and symbolic sparse/signed
values, certified singleton, u128/isize, refuted claims and a pure native mutation failure.
Reverse reconstruction, payloads, C/default repr, mismatched types and Drop remain UNKNOWN.
Independent review approves the certificate and controls. Full validation expects 559 Rust tests.

The complete twelve-main schema-2 replay clears the prior PAC Pupdr::to_bits blocker for all nine
conditional UNKNOWN mains. These now progress through GPIO callbacks and stop at a tracked-storage
reference diagnostic in the application future. Three earlier RTT refutations remain; registration
is twelve PROVED and ordinary runtime twelve REFUTED. All twelve fresh bodies are still entered.
This is traversal progress, not a completed main proof. Capture:
`/tmp/miren-stage129-main-gpio-rmw-20261009`.
The separate strict stage-129 capture matches all 36 stage-128 obligation arrays exactly, without
assumptions: `/tmp/miren-stage129-main-strict-20261009`.

All 559 Rust workspace tests and 53 Python tests pass, along with formatting, cargo lint, release
builds, cargo deny, documentation builds and manual hooks. Existing enum-input and NonZero
compiler controls also pass independently.

## Stage 130: Explicit ordinary-storage effects for external models

FunctionContract.storage_effect and public TrustedStorageEffect add a separate opt-in premise
that an exact trusted call does not mutate, publish or retire pre-existing ordinary tracked storage.
It requires trusted/no_panic/reason and rejects modifies or alias-return combinations. Bounded
compiler and raw-value input certificates precede snapshots, rejecting references, raw pointers,
callbacks, interior mutable/atomic storage, opaque shapes and direct/nested pattern restrictions.
Scalar/ScalarPair wrappers must match actual typed-field validity and offsets. Constructed
fieldless inventories admit up to 1024 variants; payload inventories retain 256 and symbolic
inventories consume the existing 512-value budget. Root-input and transmute limits are unchanged.

Existing ordinary allocations are retained, dead allocations remain dead, and the special static
view epoch is retired. Static/startup and local/published atomic precision remain invalidated.
The exact used selector/effect/reason premise is recorded with the trusted call and survives later
REFUTED/UNKNOWN outcomes. Legacy omitted-modifies behavior remains conservative. Configured or
recorded effects refuse native replay, including unused policies and removed configurations.

Four compiler integrations cover host/ARM O0/O2 ordinary/future conditional proofs, mutation
refutation/native failure, legacy UNKNOWN, pointer/alias/restricted-input and return refusals,
dead storage, static/atomic invalidation, replay refusal and 512/1024/1025 fieldless bounds.
One public DTO unit and one ABI unit validate compatibility/conflicts and stricter scalar validity.
Three Python policy tests demand the exact used premise and reject configuration/reason/version,
duplicate, unused and unrelated assumption mutations. Independent implementation/policy review
approves the final certificate and effect rules. Full final validation expects 565 Rust/56 Python.

Separate STM32 GPIO frame profiles preserve previous policies and explicitly record the stronger
initialization premise. The final twelve-main replay clears future-frame loss for all nine affected
bodies; the narrow GPIO policy then stops eight H7 bodies at alternate-function access, and the F4
body at retired USB static storage. Capture:
`/tmp/miren-stage130-main-gpio-frame-final-20261010`.

Additional separate GPIO alternate-function profiles configure GPIOA/B/C/D/E/H, with exact two AFR
words and 40-byte regions using the selected compiler PAC addresses. This is still an unverified
access premise; other ports/registers remain unmapped. Their complete replay gets eight H7 bodies
to RccInfo::enable_and_reset_with_cs at an unsupported pointer constant; the F4 static boundary
remains. Capture: `/tmp/miren-stage130-main-gpio-af-frame-20261010`. All captures retain three
previous RTT refutations, nine UNKNOWN, twelve registration proofs and twelve runtime refutations.
All twelve fresh application bodies are entered. This adds no completed main proof or native boot
claim. Next pointer/static boundaries are under independent audit.

Independent source audit identifies the next H7 pointer as the ordinary Rust REFCOUNTS [u8;3]
static, not an MMIO reference. The raw constant decoder lacks its compiler static provenance.
The F4 target is EP_OUT:StaticCell<[u8;256]>, with its view conservatively retired by the init effect.
Fresh future construction alone proves neither zero refcounts nor an unused USB cell. Exact
constant/allocation identity remains inferred from source and the recorded MIR block because the
capture does not dump the operand; the audit records this limitation:
`/tmp/miren-stage130-next-blockers-audit.md`. No epoch restoration, zero-state assumption or
modifies:[] substitution was introduced.

Final frozen validation passes all 565 Rust workspace tests and 56 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation builds and manual hooks. Four affected
compiler integrations also pass after fixture-only line wrapping. Final strict and legacy GPIO
captures each match all 36 stage-129 obligation arrays exactly:
`/tmp/miren-stage130-main-strict-final-20261010` and
`/tmp/miren-stage130-main-gpio-legacy-final-20261010`.


## Stage 131: static address identity and explicit access-validity effects

A separate public trusted storage effect preserves already-live modeled Rust static allocation,
initialized declared-type validity and existing borrow/access rights. Static value history and
atomic precision remain invalidated; dead epochs and uninitialized subobjects cannot be restored.
Exact whole compiler-named Rust static raw-pointer constants retain identity without borrowing
numeric MMIO rights. Bounded initialized mutable u8-array leaves admit arbitrary values.


Complete strict, ordinary-frame and static-validity all-main captures each contain 36 roots from
12 units with no collection errors. The new conditional profile keeps three async REFUTED and
nine UNKNOWN, reaching mutable static slice coercion on eight H7 paths and a portable-atomic
wrapper cast on F4. Registration remains 12 PROVED, ordinary runtime 12 REFUTED, and all fresh
future bodies are entered. The 36 strict obligation arrays are unchanged. Ordinary-frame
invalidation remains conservative; eight H7 diagnostics advance from unsupported raw constants
to the retained dead-epoch check. The paired compact export validates without replacing the
published evidence. Captures: `/tmp/miren-stage131-main-{strict,legacy,static-validity}-20261010`.


Validation passes: all 566 workspace Rust tests and 57 Python policy/runner tests, focused
host/ARM O0/O2 positive/refuted/unknown controls, formatting, Clippy, release build, cargo-deny,
documentation build and manual hooks. Actual pure Rust mutation and both storage-effect native
replay refusals pass; custom invalid MIR and hardware paths are never executed natively.
Independent review approves the exact provenance, access and history boundaries.


## Stage 132: typed static slice and atomic-wrapper translation

This stage implements bounded mutable static byte-array slices and the exact
portable-atomic bool-to-byte view conversion. These are Rust representation extensions under the
existing conditional profile; the hardware model and initialization premises stay separate.


Bounded mutable byte slices now retain parent identity, typed extent, epoch and mutability.
Actual core get_mut executes, including Some/None branches; shared copies, reborrows and iterators
cannot forward mutable rights. Parent initialization/lifetime is validated before empty, None,
escape and exhausted paths. Ambiguous symbolic addresses and mutable static iterators stay UNKNOWN.
The separate portable-atomic conversion requires exact compiler identity, one-byte full-coverage
layouts and bounded pure-cast instantiated MIR. Changed dependency bodies remain UNKNOWN without
model use; generic pointer casts are unchanged. Exact test-only dependencies make offline fixtures
independent of the firmware Cargo cache.

Complete new-profile collection yields twelve async REFUTED, reaching the conditional
supported-outcome milestone. Eight new H7 results use REFCOUNTS[1] == 255 at checked addition;
F4 reaches StaticCell::uninit's already-full panic. All are explicitly abstract shared-state
counterexamples, with boot/native reachability unverified. Every saved query and model is
independently SAT; excluding 255 makes all eight RCC queries UNSAT. F4 also admits valid already-used
byte 1 and excludes unused byte 0, independently of its saved unrestricted-byte255 witness.
The MaybeUninit write success branch remains unsupported in its separate fixture.

Strict remains four REFUTED/eight UNKNOWN, and every fresh application future body is entered.
Final captures use a freshly collected fleet manifest:
`/tmp/miren-stage132-main-{strict,legacy,static-validity}-verified-20261010`.
The paired compact export validates exact policies, source/artifact checkpoints and frozen binary
hashes. Independent source and solver audits distinguish abstract witnesses from boot reachability.

A permission audit also corrects the old uninitialized-store positive fixture: its shared
Freeze-payload `MaybeUninit::as_ptr` path cannot recover write rights by casting to mutable.
Shared static borrows and that pointer operation retain read-only rights. The positive fixture
now preserves the original certified raw capability; exact `UnsafeCell::raw_get` is separately
supported without forming a reference to its uninitialized payload. Unsupported payload references
remain UNKNOWN, including the actual Embassy `UninitCell::as_mut_ptr` reference/get path.

Consequently, final task registration and runtime captures are each twelve UNKNOWN. The fresh
strict fleet survey contains 32 units and 2336 roots: 1107 PROVED, 237 REFUTED and 992 UNKNOWN,
with no collection errors or assumptions. Relative to pass 19, three UNKNOWN become REFUTED;
13 PROVED and 24 REFUTED become UNKNOWN at this uninitialized-reference boundary. This is a
conservative validity limitation, not a confirmed Embassy bug. The pinned core documentation
recommends raw_get for gradual initialization, while the Rust Reference leaves the exact extent
of reference pointee validity unsettled. No firmware rewrites or implicit validity premises are
introduced. Evidence: `/tmp/miren-fleet-pass20-final-20261010` and
`/tmp/miren-stage132-uninitcell-audit`.

Final validation passes 570 Rust workspace tests and 57 Python tests, formatting, cargo lint,
release builds and cargo deny. Documentation build and manual hooks complete the stage checks.
The public model API remains a declarative hardware/storage policy boundary; correlated peripheral
state and executable emulator callbacks require later work.


## Stage 133: Rust capability baseline and structured UNKNOWN reporting

General Rust execution becomes the next priority; fleet remains a regression workload. A shared
manifest drives a compact core-only compiler suite and a standalone retained-report survey.
The 23 cases cover 12 families on host/ARM at O0/O2: 40 PROVED, 36 REFUTED and 16 UNKNOWN total.
Each unsupported control checks its intended frontier, and an actual helper mutation refutes
on all four configurations while failing the native positive control. These are capability
examples, not percentages of language completeness.

Optional public UNKNOWN categories separate explicit semantic, compiler-evidence, solver,
resource-limit and external-environment causes. Untagged/conflicting errors remain unclassified;
legacy reports stay readable and outcomes/premises remain unchanged. Compiler controls exercise
these categories without changing memory behavior.

Pristine portable-atomic 1.15.0 and static_cell 2.1.1 sources, original licenses and archive/file
hashes are vendored as test inputs. Existing actual-body and temporary-mutation controls consume
these sources; no external unsafe code is added to the host workspace. A hash test prevents
snapshot edits from silently changing compiler evidence.

The [Rust capability roadmap](rust-capabilities.md) documents intended compiler/engine/model
boundaries, the current API limits and the next typed-memory migration. This stage establishes
the repeatable baseline; it does not complete that migration or a pluggable emulator interface.
Final standalone evidence: `/tmp/miren-rust-capabilities-final-20261010`, with unchanged frozen
analyzer binaries and input hashes, exact compiler configurations, no collection errors and no
trusted premises. Final validation passes 575 Rust tests, 67 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks.


## Stage 134: checked finite typed slice projections

Retained integer and nonempty tuple slices now use the ordinary memory projection layer for
bounded snapshots. Compiler target-width terms, compatible initialized values and complete
region bounds are validated before translating indices. Materialization requires a solver-proven
unique length of at most 128; no feasible candidate is selected as a new premise. Existing
references retain allocation identity and access rights, and nested projected writes reach the
original backing. Whole-slice assignment remains unsupported.

Host/ARM O0/O2 controls exercise indexed/nested tuple writes, returned views, shared reborrows,
empty and fixed-length symbolic views, callback order and bounds failures. Variable lengths,
ambiguous tuple offsets/writes, floating shapes, oversized snapshots, escaped/dead parents and
shared writes remain UNKNOWN. The actual increment-helper mutation refutes and fails native
execution; invalid custom MIR controls are never executed natively.

The core-only capability baseline improves to 11 PROVED, 9 REFUTED and 3 UNKNOWN per build
configuration. This closes its retained-prefix projection gap without hardware assumptions or a
new value representation. Existing finite-prefix iterator behavior remains supported, and the
old whole-view-length fixture now proves through ordinary projection semantics.

Final standalone evidence: `/tmp/miren-stage134-capabilities-20261010`, with 44 PROVED,
36 REFUTED and 12 UNKNOWN outcomes and no collection errors. Validation passes 577 Rust
tests, 67 Python tests, formatting, cargo lint, release builds, cargo deny, documentation
build and manual hooks.

## Stage 135: proven-nonzero trailing-zero intrinsic

The integer intrinsic dispatcher now admits the compiler-identified core `cttz_nonzero`
operation with its exact unsafe Rust signature and primitive input/output types. Existing
path constraints must prove the operand nonzero before the exact bit scan executes. A
possible zero operand or inconclusive solver query remains UNKNOWN; no premise is added.
Safe `NonZero::trailing_zeros` executes its actual core bodies to this boundary.

Host/ARM O0/O2 controls cover every primitive integer width, signed values, safe NonZero
methods, wrong counts, zero/possibly-zero operands and method-name lookalikes. Native
controls cover all bit positions and all nonzero u8 inputs. The count mutation refutes
in all four compiler configurations and fails native O0/O2. Invalid intrinsic operands
are never executed natively. The 23-case capability baseline is unchanged.

A separate audit found missing temporal access certification in existing tracked volatile
reads and raw byte-slice views. Four sequences that reuse an old pointer across writes or
competing reference access report PROVED in all four compiler configurations, without
assumptions. Evidence is retained at `/tmp/miren-raw-alias-validity-audit`. These results
do not establish access validity: current checks certify spatial bounds, allocation
lifetime and stored mutability, but not temporal permission. Broad raw dereferences
remain unsupported. Hardening existing access paths takes priority over expanding them;
this stage adds no raw-memory semantics.

Final standalone evidence: `/tmp/miren-stage135-capabilities-20261010`, with unchanged
44 PROVED, 36 REFUTED and 12 UNKNOWN outcomes and no collection errors. Validation passes
579 Rust tests, 67 Python tests, formatting, cargo lint, release builds, cargo deny,
documentation build and manual hooks. Independent review approves the compiler/type gates,
nonzero feasibility refusal, exact scan and valid native mutation controls.

## Stage 136: refuse uncertified temporal raw-access permissions

The raw-access audit exposed a missing certificate in tracked volatile reads, raw byte views
and tracked raw-pointer arrays converted into Rust references. Exact layout, initialized live
storage and spatial disjointness do not establish temporal access rights. These three boundaries
now return Semantics UNKNOWN before supplying a value or reference. No model assumption or
application rewrite fills the gap. The nonempty-array restriction also reaches safe core
`array::each_mut`; zero-element arrays grant no handles and remain supported.

Const raw byte-slice metadata formation is separated from byte access. Source address and
length must have the target width and symbolic context; graph/liveness checks remain active.
The raw descriptor is preserved through snapshots and actual core metadata bodies. A numeric
source and arbitrary/excessive length can supply metadata but never a byte view or reference.
Shared reference formation and raw byte dereferences retain their refusal boundaries. Mutable
raw fat pointers remain unsupported.

Host/ARM O0/O2 regressions require the missing-certificate diagnostic for all four old-pointer
sequences and a nonempty raw reference array. Ordinary references, raw-address identity, empty
reference arrays and raw length queries prove; wrong ordinary/metadata claims refute. Metadata
and field-address mutations refute in all four configurations and fail native controls. Earlier
volatile/byte mutation controls now require UNKNOWN rather than claim unsupported counterexamples;
their valid native mutations still fail. Suspect access sequences are never executed natively.

The capability manifest expands to 26 cases across 13 families, with 12 PROVED, 10 REFUTED and
4 UNKNOWN per configuration. It includes raw metadata P/R and a safe reference-array grant U.
Temporal token lineage and complete invalidation events remain future model work; this stage
repairs the identified proof boundary rather than claiming full alias-model parity.

Final standalone evidence: `/tmp/miren-stage136-capabilities-20261010`, with 48 PROVED,
40 REFUTED and 16 UNKNOWN outcomes and no collection errors. Validation passes 581 Rust
tests, 67 Python tests, formatting, cargo lint, release builds, cargo deny, documentation
build and manual hooks. Independent review confirms that preserved raw metadata cannot
bypass the byte/reference grant boundaries. Hardware-model and ordinary RAM controls both
require the missing temporal-certificate diagnostic for tracked RAM volatile reads.

## Stage 137: correlated immutable tuple-value selection

The symbolic array selector now accepts bounded pure tuple/unit trees with bool, exact-width
integer and f32/f64 leaves. Every term must have its declared sort and active symbolic context;
candidate shapes, widths and signedness must match. One index equality is reused across every
field, preserving correlations and available float raw bits. Candidate trees are bounded to
depth 16 and 512 total nodes. The existing fixed-element caller proves index bounds before
accepting the selection. No feasible candidate or new premise chooses the result.

This domain also handles checked finite-slice snapshots, closing their ambiguous tuple-read
offset gap. Symbolic composite writes still require a uniquely entailed index and explicitly
report Semantics UNKNOWN otherwise. No write or reference capability is added. Retained
reference/address/ADT/Drop identities remain excluded. Existing incoming immutable shared-reference
snapshots can be selected as values, but acquire no allocation, liveness or access rights.

Host/ARM O0/O2 controls cover correlated nested tuples, incoming values/snapshots, exact signed-zero
and NaN payload bits, wrong claims and missing bounds. Retained reference/ADT/Drop and symbolic
write cases remain UNKNOWN. Native valid controls pass at O0/O2, including both finite-slice
offsets. An actual array-data mutation breaks field correlation, refutes in all four compiler
configurations and fails native execution. Unit controls reject forged types, contexts, shapes,
index capacities and oversized/deep trees, and prevent conditional identity-handle choices.
Existing unique/singleton retained-value selection keeps its prior behavior. The safe baseline
expands to 29 cases across 14 families, with 13 PROVED, 11 REFUTED and 5 UNKNOWN per configuration.

Final standalone evidence: `/tmp/miren-stage137-capabilities-final-20261010`, with 52 PROVED,
44 REFUTED and 20 UNKNOWN outcomes and no collection errors. Validation passes 584 Rust
tests, 67 Python tests, formatting, cargo lint, release builds, cargo deny, documentation
build and manual hooks. Independent review verifies bounds, field correlation, exact
float payload bits and the exclusion of new identity/reference/write rights.


## Stage 138: compiler-certified owned initialization wrappers

`MaybeUninit` now has a distinct retained value with an interned exact compiler type and an
optional initialized payload. Actual core `new`, `uninit` and `assume_init` bodies execute.
Union and `ManuallyDrop` lang-item identities, active fields, operand types, offsets, size and
alignment certify construction and extraction. The bounded payload domain admits primitive
bool/integer/f32/f64 and recursive pure tuples that the compiler certifies as Copy, Freeze and
free of drop obligations. Payload trees have depth-16 and 256-node bounds; the descriptor pool
holds at most 128 types. It never decodes padding or infers validity from equal sizes.

Compiler `assert_inhabited` uses its validity query and records a guard obligation. Initialized
extraction preserves typed values and available float raw bits. Uninitialized nonempty extraction
returns Semantics UNKNOWN. Unit-only zero-byte tuples have one value and can extract it without
fabricating bytes; arbitrary zero-sized ADTs remain unsupported. Contextual validation checks
nested descriptors against actual argument, operand, store and return types. Snapshots, returns,
whole assignments and copies preserve initialization state. No raw access permission is added.

Host/ARM O0/O2 controls cover primitive widths, tuple and float-bit round trips, unit-only tuples,
whole assignment, nested containers, copies, refuted claims and uninitialized branches. Unrelated
unions, type-changing extraction, restricted validity, pointer/reference payloads, `zeroed`, raw
writes and reference-forming methods remain UNKNOWN. Native tests execute only valid initialized
or unit-only controls. An actual constructor argument mutation refutes in all four configurations
and fails native tests at both optimization levels.

The capability manifest adds initialized P/R and uninitialized U cases, reaching 32 cases across
15 families: 14 PROVED, 12 REFUTED and 6 UNKNOWN per compiler configuration. General per-subobject
initialization, partial moves and temporal access validity remain separate model work.
The vendored StaticCell `[u8; 256]` write still returns UNKNOWN; its assertion now pins the
explicit unsupported-payload certificate diagnostic instead of the old generic union diagnostic.

Final standalone evidence: `/tmp/miren-stage138-capabilities-20261010`, with 56 PROVED,
48 REFUTED and 24 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 586 Rust tests, 67 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. Independent review approves exact type
correlation, raw pattern refusal, initialization preservation, compiler guard execution and
continued refusal of unsupported access grants.


## Stage 139: bounded owned-array initialization certificates

The `MaybeUninit` retained payload certificate now admits arrays of supported pure Copy/Freeze
values. Exact compiler constant counts and element types are checked before normalization,
including raw restricted types at length zero. Counts are at most 128; expanded nested trees
retain depth-16 and 256-node limits. Element vectors require exact counts and recursively typed
children. Only actual u8 arrays admit byte data, with exact constant unsigned target-usize length
metadata and matching bitvector/array sorts and symbolic contexts.

Whole initialized arrays survive actual core construction and exact extraction, assignments,
copies and returns. Available float raw bits are preserved. Nonempty uninitialized arrays remain
Semantics UNKNOWN unless their closed type has one zero-byte value. Supported empty arrays and
unit-only arrays reconstruct that unique value with the correct typed representation, including
empty u8 byte arrays. Unsupported element types remain unsupported even in empty arrays.
The actual inhabitance guard queries the entire array type, not its element type.

Host/ARM O0/O2 compiler controls cover primitive, byte, bool, tuple, nested and float-bit arrays;
empty and unit-only arrays; copying and whole replacement; wrong claims and missing bounds.
Count 128 versus 129, tuple counts 85 versus 86 at the 256-node boundary, zero-byte node exhaustion,
and depth 17 have precise supported/resource outcomes. Empty reference/raw/NonZero/Never/Drop and
restricted-pattern element cases remain UNKNOWN. Native valid controls pass, and an actual helper
initializer mutation refutes in all four configurations and fails native O0/O2 tests. A separate
metadata guard rejects malformed byte lengths, signedness, widths, sorts and foreign contexts.

No per-element partial initialization, array-of-wrapper extraction, wrapper repetition, raw or
static access, or reference grant is added. The vendored StaticCell `[u8; 256]` write keeps UNKNOWN
at its explicit array-count limit. The capability family expands by P/R/U array cases to 35 cases
across 15 families, with 15 PROVED, 13 REFUTED and 7 UNKNOWN per compiler configuration.

Final standalone evidence: `/tmp/miren-stage139-capabilities-20261010`, with 60 PROVED,
52 REFUTED and 28 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 589 Rust tests, 67 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. Independent review approves the array and
zero-byte certificates, precise metadata guards and continued access-permission boundaries.


## Stage 140: character validity and checked scalar formation

Character representations require unsigned 32-bit terms in the current symbolic context and
proved Unicode scalar validity: at most 0x10ffff, excluding 0xd800 through 0xdfff. Formation,
operands, assignments, returns, stores and trusted-storage boundaries check existing conditions.
Feasible invalid encodings and incomplete solver answers remain UNKNOWN. Compiler pattern types
retain their raw metadata and additionally prove their actual refinement and base validity.
Valid existing refined float-bit and pointer conversions remain supported.

Actual core checked and guarded unchecked character conversions execute. Exact u32/i32-to-char
and char-to-integer transmutation preserves compiler size, alignment and representation checks.
Float bit conversion validates both the float expression and retained bit encoding before use.
Numeric pointer exposure and static-address conversion cannot manufacture invalid characters.
No named callee summary, validity assumption or application rewrite is added.

Fresh reads from already certified initialized character storage use a Unicode domain encoding
that is identical on every valid scalar and maps invalid abstract bit patterns to zero. This
covers every valid character and removes spurious invalid-character witnesses without assuming
the initializer or temporal history. Cached, startup and stored values are checked directly;
uninitialized and uncertified storage never receives this encoding or new access permission.

The audit confirmed earlier invalid float-bit character proofs on host/ARM O0/O2 and invalid
pointer conversions on ARM. It also found false refutations caused by unrestricted initialized
character observations. Compiler controls cover these routes, Unicode boundaries, original
refined patterns, valid conversions and missing initialization. Native tests execute valid
conversions only. An actual checked-conversion argument mutation refutes in all four builds and
fails native O0/O2 tests. A symbolic unit check proves the domain encoding's validity and identity
over the entire 32-bit domain, and rejects forged contexts, widths and float metadata.

The strict capability baseline expands to 38 cases across 16 families, with 16 PROVED,
14 REFUTED and 8 UNKNOWN per configuration. Owned `MaybeUninit<char>` payloads and arbitrary
refined static domain encodings remain separate coverage gaps.

Final standalone evidence: `/tmp/miren-stage140-capabilities-20261010`, with 64 PROVED,
56 REFUTED and 32 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 592 Rust tests, 67 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. Independent review approves the validity
boundaries, preservation of valid refined conversions and full initialized-character domain.


## Stage 141: owned character initialization payloads

Exact compiler `char` joins the bounded pure Copy/Freeze, no-drop payload certificate for
`MaybeUninit`. Initialized payload validation uses the character predicate from stage 140 and
the existing current path conditions. Construction, extraction, root argument validation,
operands, assignments and returns pass those conditions through tuple, array and typed carrier
recursion. Actual core constructors, extraction and inhabitance guards continue to execute.
The descriptor identity, raw type, active union field and exact layout certificates remain required.

No domain encoding repairs an owned payload. Whole copies, helper returns and aggregate payloads
preserve initialized values. Nonempty uninitialized characters and aggregates remain Semantics
UNKNOWN. An eligible empty character array has one empty value and uses the existing zero-byte
reconstruction without materializing a character. Raw pattern types still refuse before
normalization, including at array length zero. All count, node, depth and descriptor budgets stay
unchanged, as do raw/static/reference access and partial-initialization frontiers.

The shared capability manifest adds initialized character P/R and uninitialized extraction U
controls: 41 cases in 16 families, expecting 17 PROVED, 15 REFUTED and 9 UNKNOWN per build.

Host/ARM O0/O2 compiler controls cover symbolic characters and Unicode edges, checked conversions,
helper returns, copied/replaced wrappers, recursive carriers, tuples and arrays, symbolic value
selection, count 128 and empty arrays. Wrong scalar/element claims refute. Missing and conditional
initialization, invalid scalar formation, restricted types, changed extraction types, raw/reference
operations and count/node exhaustion retain precise UNKNOWN diagnostics. Actual core extraction
and inhabitance model attribution are checked. Native complete-value controls pass at O0/O2;
changing an actual helper initializer from e000 to e001 refutes in all four configurations and
fails both native builds. The older character-wrapper control now proves under this certificate.

Final standalone evidence: `/tmp/miren-stage141-capabilities-20261010`, with 68 PROVED,
60 REFUTED and 36 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 594 Rust tests, 67 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. Independent review approves current-condition
propagation, exact character payload proofs and unchanged initialization/access boundaries.


## Stage 142: exact ordinary floating remainder

Ordinary binary32/binary64 MIR remainder now uses SMT IEEE remainder with an exact sign correction
to implement the truncating Rust operation. A typed two-operand `FpRem` term validates equal
floating formats and the printer emits the actual `fp.rem` operator. The numeric model checks
declared width, actual sorts and symbolic contexts. Strict ordered comparisons select a correction
only for a nonzero residual whose sign opposes the dividend. The correction's finite result is
exactly representable, including subnormals; no rounded quotient or bounded integer is introduced.
Signed zero and exceptional results follow the existing IEEE and arithmetic-NaN encoding policy.
Results acquire no retained raw-bit certificate, assumptions or access rights.

The independently reviewed derivation is described in [coverage](coverage.md). Wider formats,
fast/algebraic intrinsics and external declarations without actual bodies retain their own
unsupported boundaries. Resource limits and solver UNKNOWN retain their ordinary meaning.

An unchanged ordinary f64 numeric-guard control exposed a default-budget solver timeout before
checking the remainder. Exact encoding equality for same-format bit-to-float terms against a
finite nonzero constant gives a proof-preserving guard normalization. It adds no input premise
and leaves zero and NaN comparisons unchanged. The original numeric-guard case is retained;
no application rewrite or global budget increase is used to obtain a preferred result.

The capability manifest adds remainder P/R and missing-external-body U cases, reaching 44 cases
across 17 families: 18 PROVED, 16 REFUTED and 10 UNKNOWN expected per compiler configuration.

The missing-body control has a compiler-evidence cause rather than a semantic cause. The shared
manifest now declares each expected UNKNOWN category, and both consumers require the diagnostic
and category to match on the same unfinished obligation. The optional field preserves legacy
runner manifests; malformed categories and category-only mutations fail rather than changing
proof status or accepting an unrelated frontier.

Existing remainder controls in eight compiler fixtures now have their actual supported outcomes:
seven previously unsupported execution/comparison controls prove, and the false storage-bit claim
refutes. The wider full-suite scan includes ordinary intrinsic and numeric-loop fixtures; their
remaining guard, mutation and resource tests keep their original semantics.

Final standalone evidence: `/tmp/miren-stage142-capabilities-20261010`, with 72 PROVED,
64 REFUTED and 40 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 598 Rust tests, 68 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. Compiler controls cover host/ARM O0/O2,
actual helper mutations and valid native execution. Independent review approves the exact
remainder derivation, guard normalization and unchanged missing-body/access boundaries.


## Stage 143: arbitrary read-only primitive slice inputs

Exact primitive shared slices now retain caller-owned storage under the existing single immutable
incoming-root certificate. One symbolic target-usize length and a typed symbolic array preserve
arbitrary valid input lengths and repeated-read correlation. The target allocation byte extent
bounds length; no finite element-count cap or zero-content premise is introduced. Original compiler
element identities are interned separately from width/sign metadata, so same-layout primitive
types do not silently substitute for each other. Sort, context, layout and typed carrier metadata
are validated at root, operand, argument, store and return boundaries.

Boolean and integer observations preserve their full logical domains; floating observations retain
input storage bits, including NaNs and signed zero. Character observations use the surjective
Unicode encoding from stage 140. The raw seed is neither physical storage nor a native character
witness. Byte interpretation and native replay cannot expose it as a valid stored character.

Checked indexing, metadata and exact core Range/RangeTo/RangeFrom/RangeFull indexing validate the
retained source and preserve its allocation/projection chain. Range order and end bounds create
actual panic-safety obligations before constructing the successful view. The range model requires
exact core trait/lang-item identities, primitive readonly signatures, range value metadata and
available selected bodies. Missing bodies and unsupported consumers never become success.
Copied and empty views do not renew dead storage. Mutable or competing borrowed roots, raw access,
refined/composite or zero-sized incoming elements, whole-slice equality and unrestricted iteration
retain separate UNKNOWN boundaries. Existing byte input policy and finite projection budgets remain
unchanged.

The capability baseline preserves the original nonempty-word-slice zero assertion and advances
it to REFUTED. Guarded repeated-read correlation proves, while aggregate slice elements remain
UNKNOWN at their actual type frontier. The manifest now has 46 cases across 17 families,
expecting 19 PROVED, 17 REFUTED and 10 UNKNOWN per configuration. An older floating-slice pattern
control also proves with its actual unchanged body; its obsolete unsupported name is removed.

Dedicated host/ARM O0/O2 controls cover 24 roots: 12 PROVED, 5 REFUTED and 7 UNKNOWN per build.
They include Unicode validity, floating raw bits, target extent, arbitrary inputs above 128
items, nested ranges, empty views, helper returns and bounds failures. Unknown controls require
matching cause and diagnostic on the same obligation. Actual helper index 0-to-1 mutation refutes
in all four profiles; valid native [3,7] controls fail at O0/O2 with an in-bounds changed read.
Invalid custom lifetime and reinterpretation controls are not executed natively. Metadata units
check malformed sorts/contexts and retired backing even for empty copied handles. Independent
review approves the input domain, typed metadata, range semantics and preserved access boundaries.

Final standalone evidence: `/tmp/miren-stage143-capabilities-20261010`, with 76 PROVED,
68 REFUTED and 40 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 602 Rust tests, 68 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. The affected preexisting regression suites
also pass; no application source, environment premise or raw-access permission is added.


## Stage 144: arbitrary read-only scalar iterator cursors

Exact core shared iterator constructors and cursor operations extend the stage-143 primitive slice
domain without a finite input-length cap. Cursor types retain their original compiler element and
caller source; target-usize front/back metadata is checked for context, order and source extent.
Metadata, count, cloning and exhausted cursors validate source backing before supplying results.
Dropping a copied reference handle does not retire live backing. Floating values retain input bits;
character values use decoded observations.

The shared manifest adds nth correlation P, an unchanged false first-value claim R and an
unrestricted wrapping fold U. All four default-budget compiler configurations match: the fold
reaches ResourceLimit at the actual 30-second execution budget. The source and default budget
remain unchanged. Dedicated smaller-budget controls separately reach the symbolic step limit.
Current baseline: 49 cases in 18 families, expecting 20 PROVED, 18 REFUTED and 11 UNKNOWN per build.
Selected concrete bodies are required before new iterator model results.

The isolated comparison worktree exposed an upstream-ignored static_cell lockfile omitted from
version control. Its original bytes match the existing pinned manifest and are now tracked. No
upstream contents or hashes are changed; clean checkouts must retain the complete archive snapshot.

Dedicated controls cover 26 roots per host/ARM O0/O2 configuration: 15 PROVED, 4 REFUTED
and 7 UNKNOWN. They include arbitrary nth/reverse traversal, cloning, count, source-preserving
helper returns, Float storage bits and decoded Unicode. Retired owned backing fails metadata,
clone and exhausted queries; a dead reference handle with live backing remains supported. Actual
nth-index mutation refutes all four builds and fails valid native O0/O2 executions. Malformed
cursor widths, signedness and contexts refuse. Independent review approves all new body gates,
source validity and cursor bounds.

Final standalone evidence: `/tmp/miren-stage144-capabilities-20261010`, with 80 PROVED,
72 REFUTED and 44 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors.
Validation passes 605 Rust tests, 68 Python tests, formatting, cargo lint, release builds,
cargo deny, documentation build and manual hooks. No default proof budget is changed.

## Stage 145: bounded readonly scalar slice comparison

Primitive slice `contains`, `PartialEq::eq` and `ne` now compare readonly scalar descriptors under
actual path-proven scan bounds. Inputs retain their arbitrary valid lengths; the 128-element limit
bounds comparison work only. Equality returns on mismatching lengths before requiring a scan bound.
Original tracked sources are validated even for empty or mismatching-length paths. Each selected
scalar is observed under a feasible in-bounds candidate condition, and the complete guarded result
preserves the original comparison path. Compiler element identities, descriptor contexts and typed
array metadata remain exact. Floating equality follows numeric NaN/signed-zero rules; Char equality
compares its decoded Unicode scalar rather than unrestricted storage seeds. Existing custom finite
`PartialEq` bodies retain receiver order, mutation effects and short circuiting.

Dedicated host/ARM O0/O2 compiler controls cover 17 roots per build: 10 PROVED, 2 REFUTED and 5
UNKNOWN. They cover bounded selected-word membership, Bool and Char, floating NaNs and signed zero,
local array equality, full inputs above 128 items with short views, empty views, mismatching
lengths, false membership/reflexivity claims, unbounded scan frontiers and dead original backing and
an unavailable custom comparison body. Actual helper index mutation preserves in-bounds reads and
must refute the unchanged one-word-prefix claim. No new input cap, environment assumption, alias
root or raw-access permission is introduced. The shared manifest adds a scalar-slice comparison
family with bounded membership P/R and unrestricted scan U controls. This isolated branch has 49
cases across 18 families, expecting 20 PROVED, 18 REFUTED and 11 UNKNOWN per configuration.

Final standalone evidence: `/tmp/miren-stage145-capabilities-20261010`, with 80 PROVED, 72 REFUTED
and 44 UNKNOWN outcomes, unchanged frozen inputs/binaries and no collection errors. This isolated
stage passes 604 Rust tests, 68 Python tests, formatting, cargo lint, release builds, cargo deny,
documentation build and manual hooks. Independent review approves the checked selection, numeric
semantics, source lifetime and selected core body-availability checks. No default proof or solver
budget is raised.

After integration with stage 144, the shared baseline contains 52 cases in 19 families, expecting
21 PROVED, 19 REFUTED and 12 UNKNOWN per configuration. The merged standalone evidence is
`/tmp/miren-stage145-merged-capabilities-20261010`: 84 PROVED, 76 REFUTED and 48 UNKNOWN,
unchanged frozen inputs/binaries and no collection errors. Merged validation passes 607 Rust
tests, 68 Python tests, formatting, cargo lint, release builds, cargo deny, documentation build
and manual hooks. Both independently reviewed feature stages retain their original test domains.

## Stage 146: exact synchronous closure captures and call adapters

A shared compiler certificate checks synchronous closure identity, resolved Fn/FnMut/FnOnce kind,
capture count and numbered fields against original compiler capture types. Read-only scalar slice
and pure `MaybeUninit` carriers reuse it while retaining their own validity rules. Mutable capture
handles retain their declared rights. The return path checks captured reference graphs before
snapshot conversion, including exact enclosing aggregate metadata. Caller-owned references and
owned move captures remain supported; borrowed local backing cannot escape.
Primitive slice references with wholly pure tracked backing retain their existing symbolic views;
closure discovery does not materialize them or require a uniquely determined view length.

Invoking an Fn closure through FnOnce previously replaced the compiler shim with the closure body,
passing an owned receiver where that body expected a borrow. The selected synchronous compiler
shim now executes actual MIR, preserving receiver conversion and actual drop bodies. Both the
original opaque-local and concrete copied-handle retirement controls prove without source or type
normalization changes. A destructor panic refutes instead of being skipped.

Dedicated compiler controls cover 26 roots per host/ARM O0/O2 configuration: 17 PROVED, 4 REFUTED
and 5 UNKNOWN. They include direct, nested, returned, mutable and consuming captures, owned move
arrays, first-match find, Float storage bits, decoded Char and initialized wrappers. Retired
backing, borrowed frame escape, uninitialized extraction, missing invoked bodies and unsupported
mutable roots refuse at their recorded frontiers. Actual captured helper index mutation refutes
all four profiles and fails valid native O0/O2 executions. Malformed capture schema controls and
independent semantic review approve the metadata, rights, escape and actual shim/drop paths.

The shared baseline adds returned scalar-slice capture P/R and missing invoked body U controls:
55 cases across 20 families, expecting 22 PROVED, 20 REFUTED and 13 UNKNOWN per build. Standalone
evidence `/tmp/miren-stage146-final-capabilities-20261010` matches 88 PROVED, 80 REFUTED and
52 UNKNOWN, with unchanged frozen inputs/binaries and no collection errors. No input-length cap,
environment premise, raw-access permission or default proof budget is added.

Final merged validation passes 611 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Independent review approves
the exact capture metadata, return escape checks and execution of actual compiler call shims.

## Stage 147: scoped SMT predicate foundation

Typed terms now support explicit universal and existential quantifiers with an exact same-context
Symbol binder and Boolean body. Free-symbol metadata is lexical: a symbol bound in one term may
remain free in another. Nested scopes and shadowing retain their SMT meaning. Shared expression
printing keeps binder-dependent nodes inside their scope and retains existing query byte budgets.
Model requests and global bindings use only the actual free symbols; a logical binder is not an
application input. Float metadata includes the binder format and full body. Ordinary quantifier-free
terms retain their previous traversal and sharing paths. Ground shortcuts and Horn output refuse
quantified terms explicitly instead of treating a binder as an assigned global value.

Independent solver controls cover mixed bound/free roots, shadowing, unsafe hoist mutations, joint
printing fallback, full-width array offsets, IEEE NaN and signed zero, decoded Unicode observations,
deep terms, context/sort rejection and retained free bindings. This foundation admits no new Rust
operation, input domain, memory permission or environment assumption. Whole-slice consumers remain
a separate stage.

Standalone foundation validation passes 620 Rust tests and 68 Python tests, formatting, cargo
lint, release builds, cargo deny, documentation build and manual hooks. Independent scope and
solver review approves the final implementation. The isolated 52-case baseline is unchanged:
`/tmp/miren-stage147-capabilities-20261010` records 84 PROVED, 76 REFUTED and 48 UNKNOWN,
with unchanged frozen inputs/binaries and no collection errors.

After integration with stage 146, the shared 55-case baseline remains unchanged. Frozen evidence
at `/tmp/miren-stage147-merged-capabilities-20261010` records 88 PROVED, 80 REFUTED and
52 UNKNOWN with unchanged inputs/binaries and no collection errors. The 168 completed P/R roots
retain byte-identical obligation statuses, details and query text across host/ARM O0/O2 builds.
The resource-limited loop controls retain their actual conservative frontiers.
Merged validation passes 624 Rust tests and 68 Python tests, formatting, cargo lint, release
builds, cargo deny, documentation build and manual hooks. Long independent SMT reference
literals are wrapped without changing their bytes; all nine scoped-term integration controls
and all 37 solver units pass again after that formatting change.

## Stage 148: full-length read-only primitive slice predicates

The existing primitive scalar slice consumers now construct scoped predicates after validating
the original tracked sources, exact compiler types, initialized allocation extents and selected
core bodies under free path conditions. Membership uses an existential guarded index; equal-length
equality uses a universal guarded index, and inequality negates that exact result. A pure logical
observer reuses numeric Float and decoded valid Char observations. It asks no feasibility or memory
bounds question using an unclosed logical binder. No runtime length cap, environment premise, raw
access right or larger proof budget is introduced. Finite/custom and byte consumers retain their
previous policies, including actual custom comparison bodies and effects.

Dedicated compiler controls exercise 28 roots per host/ARM O0/O2 build: 16 PROVED, 6 REFUTED and
6 UNKNOWN. They include selected membership, arbitrary suffixes, equal-length differing subviews,
IEEE NaNs and signed zero, decoded Unicode, long and empty inputs, original backing retirement,
custom panic effects and missing bodies. Actual helper needle-value mutation refutes every profile
and fails valid native O0/O2 tests on 129-element inputs. Saved full counterexample queries for long
zero-membership and Float self-equality independently recheck SAT; concrete native witnesses remain
separate from arbitrary quantified-array model reconstruction.

The 17 unchanged prior comparison fixture roots now yield 12 PROVED, 2 REFUTED and 3 UNKNOWN per
profile, including both original unrestricted membership and equality functions. The shared
manifest advances its original unrestricted membership control and adds a full-predicate family:
58 cases across 21 families, expecting 24 PROVED, 21 REFUTED and 13 UNKNOWN per configuration.
Merged validation passes 626 Rust tests and 68 Python tests, formatting, cargo lint, release
builds, cargo deny, documentation build and manual hooks. Frozen standalone evidence at
`/tmp/miren-stage148-merged-capabilities-20261010` records 96 PROVED, 84 REFUTED and 52 UNKNOWN,
with unchanged inputs/binaries and no collection errors. Independent final review approves the
source certificates, exact numeric predicates and retained failure/model evidence.


## Stage 149: arbitrary read-only tuple and array slice inputs

A compiler descriptor certifies exact pure tuple and fixed-array primitive element shapes,
Copy/Freeze/no-drop properties and actual nonzero layout stride. Independent logical arrays retain
each expanded primitive field occurrence. Checked indexing reconstructs all fields at the same
index; subviews offset every field together after source, lifetime and bounds validation. Float
storage bits and decoded valid Char observations retain their existing meanings. Owned copies
and caller-backed projected borrows gain no mutation, raw access or physical padding rights.
Shared read-only slice validation is reused by both primitive and composite descriptors.

Runtime length has only the actual valid allocation extent bound. Type shapes retain the existing
16-level, 512-node and 128-element fixed-array limits; zero-length arrays still certify their
original element type. Fully zero-sized whole elements and refined, reference-bearing or
identity-bearing leaves remain unsupported. Selected ordinary core models require concrete bodies;
compiler metadata intrinsics retain their separate execution path. Whole composite membership,
equality and iteration refuse explicitly. Dynamic choice between whole nested aggregate arrays
remains a separate bounded-value completeness gap.

The dedicated 32-root matrix yields 11 PROVED, 5 REFUTED and 16 UNKNOWN per host/ARM O0/O2 build.
It checks field independence, repeated-index correlation, nested arrays, Float bits, Unicode,
views, actual helpers, owned-copy mutation, caller borrows and 129-element inputs. Unsupported
input shapes, oversized type arrays, read-only mutation attempts, retired backing, missing bodies
and deferred consumers retain their recorded categories and reasons. Actual helper field mutation
refutes all four profiles and fails valid native O0/O2 executions. The original iterator aggregate
input remains UNKNOWN at its now-reached composite iterator boundary. Malformed descriptor units
check contexts, sorts, lengths, leaf inventories and same-typed field independence.

The unchanged original aggregate-slice false claim advances from UNKNOWN to REFUTED. The shared
manifest adds checked composite views P/R and deferred iteration U controls: 61 cases across
22 families, expecting 25 PROVED, 23 REFUTED and 13 UNKNOWN per configuration.

Final isolated and merged validation each passes 630 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage149-capabilities-20261010` and
`/tmp/miren-stage149-merged-capabilities-20261010` each records 100 PROVED, 92 REFUTED and
52 UNKNOWN, with unchanged frozen inputs/binaries and no collection errors. Independent source
and focused-evidence review approves the descriptor, source/type/body gates and mutation controls.


## Stage 150: checked pure nested-array choices

The private tuple-choice helper becomes a common pure aggregate-choice helper. It recursively
validates and merges exact fixed-array carriers alongside tuples, primitives and unit. Candidate
kinds, counts, sorts, contexts, widths and signs must match; every candidate occurrence is charged
against the unchanged depth-16 and 512-node limits. The actual checked read still establishes index
bounds. Every descendant follows the same index condition, including Float numeric expressions
and certified raw bits. Raw bits survive only when every candidate carries their certificate.
Existing valid Char values are selected unchanged, and empty arrays remain array carriers.

This closes whole nested-array reads within arbitrary composite slice elements as well as fixed
owned inputs. Owned copies retain mutation isolation. Byte snapshots and views lack a fixed owned
array certificate at this boundary and remain outside the new domain. Identity-bearing values,
references, wrappers and ADTs remain excluded from conditional synthesis. Existing constant,
uniquely proved and singleton retained-handle selection keeps its behavior. Ambiguous writes
continue to refuse; no allocation, reference, raw access, type-domain or effect policy changes.

The dedicated 21-root matrix yields 12 PROVED, 4 REFUTED and 5 UNKNOWN per host/ARM O0/O2 build.
Controls cover nested integer, Bool, Char and Float arrays, mixed tuple shapes, empty arrays,
caller composite inputs and owned-copy isolation. Actual helper inner-position mutation refutes
and fails valid native O0/O2 executions. Same-obligation counterexample query/model evidence and
precise UNKNOWN categories/reasons are retained. The Drop case reaches an earlier actual
core drop-glue layout frontier, not the aggregate selector; metadata units independently refuse
identity synthesis. Existing tuple and finite projection regression controls remain unchanged.

The shared manifest adds pure nested-array P/R and deferred byte-array selection U controls:
64 cases across 23 families, expecting 26 PROVED, 24 REFUTED and 14 UNKNOWN per build.

Final isolated and merged validation each passes 633 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage150-capabilities-20261010` and
`/tmp/miren-stage150-merged-capabilities-20261010` each records 104 PROVED, 96 REFUTED and
56 UNKNOWN with unchanged frozen inputs/binaries and no collection errors. The 192 previously
completed P/R roots retain byte-identical obligation statuses, details and query text across all
four compiler configurations. Independent review approves the source and focused failure evidence.


## Stage 151: shared read-only composite slice cursors

Exact core shared Iter cursors reuse the existing ordinary execution protocol for arbitrary
composite slice inputs. Construction validates its immutable retained source, original element
type, allocation extent and selected concrete body. The common read-only descriptor length helper
serves both primitive and composite typed cursor validation. Every modeled method, including
metadata, clone, count and exhausted operations, validates source lifetime and selected body.
Typed cursor carriers retain target-usize terms and prove front <= back <= source length.
Items remain projected references into the actual caller allocation; the existing checked
composite reader reconstructs their fields. No owned descriptor is promoted to a reference.

The dedicated 24-root matrix yields 13 PROVED, 5 REFUTED and 6 UNKNOWN per host/ARM O0/O2 build.
Forward/reverse skips, metadata, count, clone, by-ref, returned cursors/items, 129-element inputs,
Float bits, Char observations and copied-handle retirement retain their actual semantics.
Actual helper field mutation refutes all four configurations and fails valid native O0/O2 tests.
Mutable and competing roots, retired backing and missing invoked bodies retain conservative
UNKNOWN results. Raw-source controls record the actual profile-dependent sized-pointee or raw
construction frontier on the same obligation. Cursor support supplies no unbounded callback-loop
summary, new alias rights, raw access, environment premise or larger proof budget.

Original aggregate next and nth fixtures now prove without source changes. The shared original
composite iteration-count control advances to PROVED and adds cursor nth P/R and missing invoked
body U controls: 67 cases across 24 families, expecting 28 PROVED, 25 REFUTED and 14 UNKNOWN
per configuration. Original arbitrary-zero claims remain REFUTED.


Final isolated and merged validation each passes 635 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage151-capabilities-20261010` and
`/tmp/miren-stage151-merged-capabilities-20261010` each records 112 PROVED, 100 REFUTED and
56 UNKNOWN with unchanged frozen inputs/binaries and no collection errors. The 200 previously
completed P/R roots retain byte-identical obligation statuses, details and query text across all
four configurations. Independent source and focused-evidence review approves the retained source,
exact type/body gates and cursor protocol.


## Stage 152: pure zero-sized read-only slice elements

Exact pure tuple and fixed-array shapes now admit whole zero-byte elements only with an empty
primitive leaf inventory. Original compiler kinds, Copy/Freeze/no-drop properties, alignment and
all expanded shape budgets remain certified, including original inner types below zero arrays.
A common extent helper preserves isize::MAX divided by stride for nonzero elements and uses the
full target-usize length domain for zero stride. Input and later descriptor validation share it.
Checked observations reconstruct each unique unit/empty-array/tuple value without adding storage
leaves, padding access, raw permissions or identity synthesis.

Existing checked ranges and shared cursor operations retain original source lifetime, selected
body and ordered bounds. Full-length cursors can select index usize::MAX - 1 and reach exhaustion
without wrapping; nth(usize::MAX) exhausts. Unsupported element types still refuse beneath empty
arrays. Mutable/competing roots, raw construction and retired backing remain conservative.
Whole-composite predicates and dynamic size_of_val observations remain separate unsupported APIs.

The dedicated 25-root compiler matrix yields 9 PROVED, 4 REFUTED and 12 UNKNOWN per host/ARM O0/O2
build. Same-obligation models and queries refute both an isize element-count cap and exclusion of
exact usize::MAX. Valid safe native [(); usize::MAX] arrays exercise last-item reads, counts and
exhaustion at O0/O2. Actual helper nth-offset mutation refutes every profile and fails valid native
129-element tests with original assertions unchanged. Exact UNKNOWN categories and actual
profile-dependent raw frontiers remain pinned. Existing scalar/composite zero-size fixtures
advance to PROVED without source changes; six focused and six related tests pass.

The shared manifest adds zero-size cursor P/R and missing invoked body U controls: 70 cases across
25 families, expecting 29 PROVED, 26 REFUTED and 15 UNKNOWN per configuration. Its two baseline
integration tests pass. Independent source and focused-evidence review approves the narrow stage.


Final isolated and merged validation each passes 638 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage152-capabilities-20261010` and
`/tmp/miren-stage152-merged-capabilities-20261010` each records 116 PROVED, 104 REFUTED and
60 UNKNOWN with unchanged frozen inputs/binaries and no collection errors. The 212 previously
completed P/R roots retain byte-identical obligation statuses, details and query text across all
four configurations. Independent review approves the exact zero-byte/no-leaf certificate and
retained source/bounds protocol.


## Stage 153: safe dynamic byte size for read-only composite slices

The exact safe core size_of_val API now observes certified composite slice length through the
common read-only descriptor helper. Original compiler slice element identity, registry metadata,
allocation extent and retained source lifetime remain checked. The selected ordinary core body
must be available before empty or zero-byte success. The API signature is safe, fixed Rust with
its exact reference input and target-usize result. Actual compiler element size includes padding;
nonzero extent certificates establish that the target-usize product cannot wrap, and zero stride
returns zero throughout the full target-usize length domain.

Direct raw size APIs, RawSlice unwrapping, alignment APIs and arbitrary DSTs gain no support.
Existing primitive and finite size observations keep their previous behavior. A user function
with a matching name executes its actual body. No raw access, alias permission, input assumption,
shape budget or comparator policy changes.

The dedicated 22-root compiler matrix yields 7 PROVED, 4 REFUTED and 11 UNKNOWN per host/ARM O0/O2
build. It checks padded tuples, nested arrays, derived views, valid extent, zero-byte MAX lengths,
actual helper entry and same-obligation refutation query/model evidence. Actual helper size+1
mutation refutes all profiles and fails valid native 129-element tests; original native tests
include safe full-MAX zero-sized arrays. Lookalike wrong helper bodies refute. Dead empty/zero-byte
backing, missing bodies, invalid element shapes and raw/alignment sources retain their actual
categories and causes; raw controls stop at their earlier sized-pointee cast frontier. The unchanged
Stage 152 size_of_val source now proves. Four focused and six related tests pass. Independent
source and focused-evidence review approves the narrow extension.

The shared manifest adds composite byte-size P/R and missing invoked body U controls: 73 cases
across 26 families, expecting 30 PROVED, 27 REFUTED and 16 UNKNOWN per configuration.
Its two shared baseline integration tests pass.


Final isolated and merged validation each passes 640 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage153-capabilities-20261010` and
`/tmp/miren-stage153-merged-capabilities-20261010` each records 120 PROVED, 108 REFUTED and
64 UNKNOWN with unchanged frozen inputs/binaries and no collection errors. The 220 previously
completed P/R roots retain byte-identical obligation statuses, details and query text across all
four configurations. Independent review approves the exact safe API, retained body and compiler
stride certificate without new raw permissions.


## Stage 154: safe dynamic alignment for certified read-only slices

The safe core align_of_val function is identified by its exact public function DefId beneath the
actual core module containing the compiler mem_align_of anchor. Unrelated crates, parents and
names are excluded before the exact child check. No nonexistent diagnostic item or user name
supplies identity. The model requires the safe fixed Rust shared-reference signature, original
slice element type, validated read-only primitive/composite descriptor and selected ordinary body.
Source lifetime and valid extent precede the constant result, including empty and zero-byte cases.
It returns actual compiler ABI alignment, checked as a representable nonzero power of two.

Raw APIs, deprecated aliases, unrelated DSTs and finite/owned domains gain no new model. Existing
byte-size observations retain their separate path. No pointer address, alias right, raw memory
permission, input premise or budget changes.

The dedicated 21-root compiler matrix yields 8 PROVED, 3 REFUTED and 10 UNKNOWN per host/ARM O0/O2
build. Primitive Char/Float slices, padded tuples, nested arrays, derived views and aligned empty
array elements pass. Valid native MAX zero-sized arrays retain their element alignment. Actual
helper alignment+1 mutation refutes every profile and fails valid native 129-element tests;
lookalike wrong helper bodies execute and refute. Same-obligation queries/models and actual helper
entry/model attribution are retained. Dead empty/zero-byte backing, unsupported types, competing
or mutable roots, missing bodies and raw/alias calls preserve their exact categories and frontiers.
The original Stage 153 safe-alignment source advances from its earlier body-cast UNKNOWN to
PROVED without a source change. Four focused and six related tests pass. Independent source and
focused-evidence review approves the exact identity and descriptor protocol.

The shared manifest adds dynamic alignment P/R and missing invoked body U controls: 76 cases
across 27 families, expecting 31 PROVED, 28 REFUTED and 17 UNKNOWN per configuration.
Its two shared baseline integration tests pass.


Final isolated and merged validation each passes 642 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage154-capabilities-20261010` and
`/tmp/miren-stage154-merged-capabilities-20261010` each records 124 PROVED, 112 REFUTED and
68 UNKNOWN with unchanged frozen inputs/binaries and no collection errors. The 228 previously
completed P/R roots retain byte-identical obligation statuses, details and query text across all
four configurations. Independent review approves the exact safe API identity and unchanged
source/body/extent protocol without new raw permissions.


## Stage 155: exact local struct read-only slice elements

Composite descriptors now include ordinary local nonzero struct nodes with exact compiler nominal
names and declaration-ordered field identities. Every original monomorphic field type is examined
before normalization, including zero-length array probes. Copy/Freeze/no-drop and original pure
field eligibility remain required, with existing depth/node/array budgets charged before metadata
append. Packed/vector layouts, external ADTs, enums/unions, zero-sized struct nodes and identity
or refined fields remain outside this domain. Private constructors add no input invariant.

A neutral aggregate scalar-validity helper is extracted unchanged from trusted storage. Both
consumers compare exact scalar/scalar-pair validity and physical offsets against actual fields;
the trusted storage domain, normalizer, diagnostics and assumption policy retain their behavior.
New struct admission shares only that concrete compiler layout evidence. Physical temporary fields
are offset-sorted for this check; logical observations retain declaration order and exact named
Adt metadata. Each primitive occurrence has independent storage and all fields observe the same
checked index. Actual compiler stride includes padding and supplies the existing extent bound.

Checked fields, owned copies, caller-backed field borrows, views, shared cursors and safe layout
APIs reuse existing protocols. Whole-composite membership/equality and ambiguous symbolic choices
between struct array elements remain unsupported. No reference, raw, padding-byte or identity
permission follows from the logical descriptor.

The dedicated 36-root matrix yields 10 PROVED, 5 REFUTED and 21 UNKNOWN per host/ARM O0/O2 build.
Named/tuple/generic/nested structs, repeated-field correlation, Float bits, Char, views, returned
fields, owned-copy mutation, cursors and layout observations pass. Independent-field and
constructor-invariant claims refute. Actual helper field mutation refutes every profile and fails
valid native 129-element tests with original assertions unchanged. Same-obligation query/models,
actual helper entry and precise categorized UNKNOWN frontiers are retained. Existing non-Copy
wrapper controls stay UNKNOWN. Four focused and eleven related tests pass, along with metadata
units and warning-free build/lint/fmt. Independent source and focused-evidence review approves the
exact type, layout and source certificates.

The shared manifest adds local struct read P/R and whole membership U controls: 79 cases across
28 families, expecting 32 PROVED, 29 REFUTED and 18 UNKNOWN per configuration. Both baseline
integration tests pass.


Final isolated and merged validation each passes 645 Rust tests and 68 Python tests, formatting,
cargo lint, release builds, cargo deny, documentation build and manual hooks. Frozen evidence at
`/tmp/miren-stage155-capabilities-20261010` and
`/tmp/miren-stage155-merged-capabilities-20261010` each records 128 PROVED, 116 REFUTED and
72 UNKNOWN with current source/input/release hashes verified and no collection errors. All 236
previously completed P/R roots retain byte-identical obligation statuses, details and queries
across four configurations. Independent review approves the original type, field validity and
retained source certificate.

The first merged attempt ran a stale analyzer after copied older source timestamps escaped
Cargo freshness checks; its failures are preserved at
`/tmp/miren-stage155-merged-stale-binary-checks`. A fresh explicit binary build restores the
struct cases and the complete rerun passes. Later copied snapshots use fresh file timestamps and
validation builds analyzer binaries explicitly before compiler integration tests.


## Stage 156: exact nominal zero-sized local struct slices

The local struct certificate now admits zero-byte nodes at every shape level after complete
original field/type probes, unchanged budgets and compiler scalar validity checks. A per-node
consistency gate requires no actual primitive storage leaves for zero layout size. Top-level
eligibility keeps the same local ordinary struct policy without its prior size-only exclusion.
Exact named Adt observations retain zero variant/discriminant, false Option identity and ordered
fields; no struct is replaced by unit. Restricted or unsupported original children remain refused
beneath empty arrays. Source, typed carrier, body and layout protocols retain their behavior.

Existing zero-stride extent and ordered cursor models cover the full target-usize length domain,
including aligned zero-byte structs. Metadata, empty views and exhausted results still validate
live backing. Custom Clone, PartialEq and methods execute actual bodies and retain effects.
Whole membership/equality and untyped ambiguous struct choices remain unsupported. No raw,
alias, padding-byte or conditional identity permission is added.

The dedicated 29-root matrix yields 9 PROVED, 7 REFUTED and 13 UNKNOWN per host/ARM O0/O2 build.
It checks exact nominal values, generic/nested/aligned zero-byte structs, returned fields,
owned-copy behavior, layout, MAX cursors and same-obligation exact-MAX counterexamples. Actual
method and custom trait body entry is asserted; a panicking Clone and false custom comparison
refute. Actual nth-offset mutation refutes every profile and fails valid native 129-element
executions. Native MAX copy/method/aligned-cursor controls pass; finite native count cases pass.
An optional native MAX by-reference count entered the real linear implementation and was stopped;
its unchanged analyzer claim remains checked, without claiming native MAX-count execution.
Durable original/mutated native outputs and the stopped experiment are retained separately.

Three original Stage 155 whole/nested/N=0 zero-struct sources now prove with harness-only
expectation maintenance. Four focused and thirteen related tests pass, as do metadata units and
warning-free build/lint/fmt. Independent source and focused-evidence review approves the nominal
certificate and retained source protocol.

The shared manifest adds nominal zero-struct cursor P/R and missing invoked body U controls:
82 cases across 29 families, expecting 33 PROVED, 30 REFUTED and 19 UNKNOWN per configuration.
Its two baseline integration tests pass, including a valid native MAX named-zero negative witness.

Full isolated validation passes 648 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 601 tracked
files match that validated snapshot byte for byte. Fresh debug/release builds, 12 new/related
compiler integration tests, 68 Python tests and the remaining required checks also pass in main.
Frozen isolated and merged evidence at `/tmp/miren-stage156-capabilities-20261010` and
`/tmp/miren-stage156-merged-capabilities-20261010` each records 132 PROVED, 120 REFUTED and
76 UNKNOWN, with current source/input/release hashes verified and no collection errors. All 244
previously completed P/R roots retain identical obligation statuses, details and query text across
four configurations. Independent review approves exact nominal zero-byte values and unchanged
body, lifetime, original-type and extent certificates.


## Stage 157: compiler-typed owned struct array selection

Actual MIR Copy/Move operands share the ordinary place-read loop with an optional instantiated
Body. At an explicit array Index, the original compiler prefix type supplies exact element type
and inventory length. Earlier constant, primitive/pure aggregate and solver-unique selection,
real bounds and solver errors retain their order. Untyped place/reference projection paths,
borrows, stores and raw operations gain no selection certificate.

The private owned certificate reuses complete original local pure struct shape checks without
normalization or name-based generic inference. Every candidate validates complete nominal fields,
variant/discriminant/Option metadata, arity, scalar sign/width/context, Float optional bit evidence
and valid Char values. Shared candidate node/depth budgets remain bounded. All primitive columns
select with the same index before exact nominal reconstruction, including zero-leaf structs.
No constructor invariant, raw permission, conditional identity or method-effect summary follows.

The dedicated 26-root matrix yields 11 PROVED, 3 REFUTED and 12 UNKNOWN per host/ARM O0/O2 build.
Named, tuple-style, generic and nested structs, composite input rows, Float/Char correlations,
nominal owned zero-byte copies and locally mutated owned values are covered. The actual helper
left-to-right field mutation refutes every profile and fails valid native 129-element inputs;
native originals pass with durable outputs and timeouts. Original borrowed zero-field access
honestly remains UNKNOWN through an untyped projection, alongside raw/ref/Drop/byte-carrier,
ambiguous stores, original restricted N=0 children, resource and missing body boundaries.

Unchanged original Stage 155 ambiguous_nested_struct now REFUTES its false arbitrary-field claim.
Unchanged original pure_array_choices ambiguous_adt now PROVES its owned-copy claim. The unchanged
owned_repeats ambiguous function also proves on host/ARM O0/O2; its compiler harness expectation
is maintained. The original tuple_array_choices structs copy also proves across all four
profiles, with only its expected status and obsolete UNKNOWN assertion updated. Only harness
expectations change. Six focused and thirteen related tests pass, as do metadata corruption units,
build, lint and formatting. Independent source and focused-evidence review approves the scope.

The shared manifest adds typed struct-array selection P/R and missing invoked body U controls:
85 cases across 30 families, expecting 34 PROVED, 31 REFUTED and 20 UNKNOWN per configuration.
Its two baseline integration tests pass.


Full isolated validation passes 651 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 604 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, eight new/related
integration tests, the owned-repeat compatibility test, 68 Python tests and the remaining checks
also pass in main. Frozen isolated and merged surveys each record 136 PROVED, 124 REFUTED and
80 UNKNOWN at `/tmp/miren-stage157-capabilities-20261010` and
`/tmp/miren-stage157-merged-capabilities-20261010`, with current source/input/release hashes
verified.
All 252 earlier completed P/R roots retain identical obligation statuses, details and queries
across four configurations. Independent source review approves the exact owned type certificate.

Two earlier full attempts exposed obsolete expected-UNKNOWN harness entries for unchanged owned
struct copies. Their failures remain at `/tmp/miren-stage157-old-expectation-checks` and
`/tmp/miren-stage157-second-old-expectation-checks`. Actual four-profile probes and native mutation
controls justify expectation-only maintenance; the final complete rerun passes.


## Stage 158: compiler-certified finite byte-array choices

The actual typed Copy/Move array selector now uses a private owned-shape annotation with explicit
ByteArray nodes. It walks original compiler types alongside the complete existing pure certificate,
retaining exact u8 identity even at N=0 and original instantiated struct field types. Incoming
composite shapes and observations retain their representation. Earlier constant/primitive/unique
selection, bounds, source and solver checks retain their order; no generic Bytes selector changes.

ByteArray candidates require exact count, unsigned target-usize constant length, byte data sort
and Context before any Select. Elements candidates require complete unsigned BV8 leaves. Every
candidate byte consumes the unchanged node budget, including compressed Bytes. All byte and
sibling primitive columns share the same index; canonical ConstArray/Store copies retain only the
finite logical bytes. Typed annotation and copied values add no source identity or raw/borrow
permission. The neutral exact byte-metadata predicate is extracted from MaybeUninit unchanged;
its initialization policy, original type gates and diagnostic remain in that separate domain.

The dedicated 21-root matrix yields 10 PROVED, 3 REFUTED and 8 UNKNOWN per host/ARM O0/O2 build.
Local Bytes versus incoming Elements rows, nested structs/tuples with Float/Char siblings, exact
empty u8 versus empty nonbyte arrays, owned writes preserving source and actual helper entries
are covered. Actual byte-position mutation refutes all four profiles and fails valid native
129-element inputs at O0/O2; five native original controls pass with durable logs and timeouts.
Incoming untyped Elements selection was already supported and remains an explicit control.
Distinct local Bytes retained borrows, raw/ref/Drop/restricted original N=0 children, ambiguous
stores, resource and missing-body boundaries retain their honest producer categories.

Original Stage 150 byte_array_choices and Stage 157 byte_choices sources now prove; only harness
expectations change. Six final focused tests, six related MaybeUninit/composite tests, two private
owned-certificate units and the preserved byte-validity unit pass, along with build/lint/fmt.
Independent source and focused-evidence review approves the exact owned type and copy protocol.

The unchanged original shared nested_byte_array_choice source advances from UNKNOWN to PROVED.
Three new typed byte-choice P/R and missing invoked body U controls yield 88 cases across
31 families, expecting 36 PROVED, 32 REFUTED and 20 UNKNOWN per configuration. Both shared
baseline integration tests pass.


Full isolated validation passes 654 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 606 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, ten new/related
integration tests, 68 Python tests and the remaining required checks also pass in main. Frozen
isolated and merged surveys each record 144 PROVED, 128 REFUTED and 80 UNKNOWN at
`/tmp/miren-stage158-capabilities-20261010` and
`/tmp/miren-stage158-merged-capabilities-20261010`, with current source/input/release hashes
verified.
All 260 earlier completed P/R roots retain identical obligation statuses, details and query text
across four configurations. Independent review approves exact byte metadata and owned-copy effects.

The initial full attempt inherited an obsolete parent expected-UNKNOWN entry for the unchanged
struct copy source; its failure remains at `/tmp/miren-stage158-parent-old-expectation-checks`.
Mirroring the independently justified Stage 157 harness maintenance restores the expectation;
no Stage 158 semantics change was needed, and the final complete rerun passes.


## Stage 159: exact ordinary dependency struct values

A shared concrete struct admission predicate serves both incoming composite shape certification
and compiler-typed owned array choices. Local admission retains its prior policy. Newly admitted
external structs require exact ordinary structural flags, allowing only the constructor bit,
and an actual compiler Sized lang-item core-crate anchor. Core, compiler-special and future
unknown flags are refused, as is a missing anchor. No name whitelist or dependency layout shortcut
supplies eligibility.

Original field types and instantiated compiler arguments remain the certificate, before
normalization and even under zero-length arrays. Copy/Freeze/no-drop, scalar validity and physical
offsets, exact nominal metadata, zero-byte inventories and existing type/candidate budgets remain
checked. Field privacy and constructors supply no invariant on arbitrary valid Rust inputs.
Caller-backed lifetime, views, cursors, layout, owned byte normalization and actual method/body
selection reuse their prior protocols. No raw, mutable, alias, ownership or method-effect premise
is added.

A separately compiled no_std dependency rlib is supplied through --extern on host and ARM at
O0/O2. Its 27 retained roots yield 10 PROVED, 5 REFUTED and 12 UNKNOWN per build, covering named,
tuple-style, generic, private, nested, Float/Char and aligned nominal zero-byte values. Actual
accessor, borrowed method, checked arithmetic and const-generic body entries are asserted. The
same non-inline non-generic accessor rebuilt without retained MIR remains MissingCompilerEvidence
UNKNOWN in all four profiles. Unsupported original ref/raw/restricted/core children under N=0,
Drop, packed, mutable/competing roots, whole membership, dead empty backing and shape budgets
retain their precise frontiers.

An actual dependency getter is changed from left to right and its rlib rebuilt for each profile.
The unchanged consumer refutes in all four builds with query/model on the same obligation; valid
129-element native mutation guards fail at O0/O2 while original native tests pass. Complete
commands, source hashes, reports, outputs and timeouts are retained at
`/tmp/miren-stage159-final-evidence`. Two dedicated tests, eleven related tests, six metadata units,
build, lint and formatting pass. Independent source and focused-evidence review approves the
shared original-type and actual-body certificates.

The core-only shared manifest remains 88 cases across 31 families, expecting 36 PROVED,
32 REFUTED and 20 UNKNOWN per configuration. Dependency coverage is recorded by the separate
actual rlib integration rather than synthetic core-only inventory entries.


Full isolated validation passes 657 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 609 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, thirteen new/related
integration tests, 68 Python tests and the remaining required checks also pass in main. Frozen
isolated and merged core-only surveys retain 144 PROVED, 128 REFUTED and 80 UNKNOWN at
`/tmp/miren-stage159-capabilities-20261010` and
`/tmp/miren-stage159-merged-capabilities-20261010`, with current source/input/release hashes
verified.
All 272 earlier completed P/R roots retain identical obligation statuses, details and query text
across four configurations. The separate actual dependency rlib matrix and native mutation ledgers
remain at `/tmp/miren-stage159-final-evidence`. Independent review approves the exact external
struct admission and retained-body certificates; no new conditional assumptions are used.


## Stage 160: compiler-certified owned whole-element array writes

Actual MIR Assign executes its rvalue and existing destination validators before a narrow typed
write hook. Exactly one Index on an original owned array local is admitted; original count must
match materialized Elements and the index must be exact target usize in the active context.
Constant and solver-unique stores retain the existing writer. Reference/Deref destinations,
post-Index fields, call destinations and generic memory projections acquire no new write rule.

A shared original product certificate reuses pure primitive/composite type checks and explicit
byte-array annotations. The replacement and every candidate are flattened with cumulative
512-node and depth-16 budgets, exact scalar/context/nominal metadata and Char validity checks.
Actual bounds must follow from current path conditions. Each position uses one index comparison
for every replacement-versus-old leaf; reconstruction completes before committing. Live allocated
owners reuse existing require_write/read checks and commit to the same slot; unallocated owners
update the same local. Neither path invents source identity or access permission.

The scalar conditional helper is extracted from aggregate choices without changing ITE argument
order. It is shared by product reads and writes, retains Float physical bits only with evidence
from both branches, and refuses invalid conditions even for zero-leaf products. Byte copies,
nominal field order, original type probes beneath N=0 and prior struct admission remain certified.
Metadata units check condition context/sort, leaf inventories and nominal byte reconstruction.

The dedicated 21-root matrix yields 11 PROVED, 4 REFUTED and 6 UNKNOWN per host/ARM O0/O2 build.
Whole primitive, tuple, nested-array, Bytes, ordinary struct and Float/Char replacements,
sequential equal/different indices, untouched siblings, copy independence, allocated owners and
pure zero-byte products are covered. A real by-value noinline helper assignment index is changed
to index XOR 1. Unchanged claims refute in all four profiles, with query/model on the same
obligation and actual helper entry; valid native original tests pass and the rebuilt mutants fail
at O0/O2. Commands, hashes, full outputs and timeouts are retained at
`/tmp/miren-stage160-final-evidence`.

The unchanged nominal zero-struct root remains UNKNOWN at candidate 0: its old zero-sized input
array retains deferred Struct InputValue children, while the replacement is a correctly decoded
nominal constant. Exact flattening refuses that unmaterialized candidate. This is a missing
bounded materialization path, not evidence that the source assertion is false. No Unit-to-Struct
shortcut or source rewrite is added. Retained reference/raw stores, nested field stores and
resource limits keep their actual categorized frontiers.

The unchanged earlier tuple whole-write source proves in all four profiles before its harness
expectation is maintained. Shared tuple_array_symbolic_write also proves without source changes;
three new whole-write P/R/missing actual replacement body U controls yield 91 cases across
32 families, expecting 38 PROVED, 33 REFUTED and 20 UNKNOWN per configuration. The two shared
baseline integration tests pass. Independent source and focused-evidence review checks the
original type certificate, transaction and actual helper mutation.

The unchanged primitive whole-write source in storage_locations also proves on host/ARM O0/O2;
its expected status is maintained only after actual four-profile probes and all three original
storage tests pass. The initial full run found this obsolete expectation and is preserved at
`/tmp/miren-stage160-old-expectation-checks`; no engine or source-claim change is required.


Full isolated validation passes 661 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 611 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, nineteen new/related
integration tests, three additional storage compatibility tests, 68 Python tests and the remaining
required checks also pass in main. Frozen isolated and merged surveys retain 152 PROVED,
132 REFUTED and 80 UNKNOWN at `/tmp/miren-stage160-capabilities-20261010` and
`/tmp/miren-stage160-merged-capabilities-20261010`, with current source/input/release hashes
verified.
All 272 earlier completed P/R roots retain identical obligation statuses, details and query text
across four configurations. Actual by-value helper mutation and native execution ledgers remain
at `/tmp/miren-stage160-final-evidence`. Independent review approves the original-type write
certificate and unchanged-source expectation maintenance; no conditional assumptions are added.


## Stage 161: bounded closed deferred product inputs

A private preparation module serves compiler-typed owned array reads and whole-element writes.
It admits only already certified pure products with no observable primitive data. The actual
original Ty remains available at every descriptor descendant, including the unused element of
N=0 arrays; expanded shape names or normalized input-builder fields do not replace that evidence.
Copy/Freeze/no-drop, original restricted fields, ordinary struct admission, ABI and type budgets
remain the first certificate.

Descriptor preflight checks exact kind, names and ordered fields, counts and original children,
canonical slot modes, recomputed height, seed Boolean context and checked offset arithmetic.
Expanded occurrence cost, including repeated shared descriptor nodes, is charged against the
existing cumulative 512-node/depth-16 budget before allocating or rebuilding. Concrete malformed
aggregates are refused before copying oversized carriers. Exact nominal products are reconstructed
without emitting symbols, replacing structs with Unit or altering generic ValueInput observers.
Existing read/write priority, bounds, live backing and transactional commit remain intact.

General scalar-containing deferred expansion is deliberately separate: current Engine metadata
has no source reservation ledger to certify symbol-offset provenance. Matching seed context and
numerical bounds cannot establish that certificate. The closed subset needs no primitive symbol
ranges and introduces no input assumption, ownership effect or raw permission.

The dedicated 19-root matrix yields 7 PROVED, 4 REFUTED and 8 UNKNOWN per host/ARM O0/O2 build.
Nominal, nested, aligned and const-generic copies/writes, pure zero-byte tuple products, actual
marker/Clone/equality bodies and safe constant-work MAX slice controls are checked. A real marker
method is changed from TAG to TAG+1; unchanged claims refute in all four profiles with the same
obligation query/model and actual method entry. Six original native tests pass at O0/O2 while
valid mutation guards fail. Durable commands, reports, source/binary hashes, full outputs and
timeouts remain at `/tmp/miren-stage161-final-evidence`.

The original Stage 160 nominal_zero source now proves in all four profiles; only its harness
expectation and obsolete UNKNOWN arm change. The original nested alignment claim stays UNKNOWN
at its separate owned align_of_val intrinsic frontier; a distinct nested_copy verifies the same
reconstruction without rewriting that claim. Drop, original restricted/ref/raw/core N=0 children,
retained writes, dead backing and resource controls retain their actual producer frontiers.
Two descriptor metadata units, seventeen related integration tests and four final focused tests
pass, as do build/lint/fmt. Independent source and focused-evidence review approves the closed
reconstruction certificate.

Three shared const-generic owned-zero P/R/missing actual method-result body U controls yield
94 cases across 33 families, expecting 39 PROVED, 34 REFUTED and 21 UNKNOWN per configuration.
The two shared baseline integration tests pass.


Full isolated validation passes 665 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 614 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, seventeen new/related
integration tests, 68 Python tests and the remaining required checks also pass in main. Frozen
isolated and merged surveys retain 156 PROVED, 136 REFUTED and 84 UNKNOWN at
`/tmp/miren-stage161-capabilities-20261010` and
`/tmp/miren-stage161-merged-capabilities-20261010`, with current source/input/release hashes
verified.
All 284 earlier completed P/R roots retain identical obligation statuses, details and query text
across four configurations. The actual marker mutation and native execution ledgers remain at
`/tmp/miren-stage161-final-evidence`. Independent review approves the bounded symbol-free
reconstruction and unchanged-source expectation maintenance; no conditional assumptions are added.


## Stage 162: exact safe sized alignment for certified Rust values

The exact public core::mem::align_of_val identity gains a sized branch before its raw intrinsic
wrapper executes. Its original monomorphic safe shared Rust signature and target-usize result
remain explicit. Original receiver graph checks and live retained projections precede the exact
primitive or pure owned product certificate. A small shared validation helper reuses original
field types, Copy/Freeze/no-drop and ordinary struct admission, bounded closed-zero preparation,
scalar context/sort and Char validity, without introducing a selection or write effect.

The actual selected safe API body must be available before returning compiler ABI alignment,
including nominal zero-byte values and explicit repr alignment. Missing bodies and source errors
propagate. Static views, raw/mutable receiver handles and unsupported product carriers acquire
no new path; unsupported raw alignment is an implementation frontier rather than proof that a
sized raw metadata query is invalid Rust. Existing dynamic slice alignment and safe/raw sized
size-query code remain unchanged. No new raw permission, hardware model or assumption is added.


The dedicated 20-root matrix yields 10 PROVED, 4 REFUTED and 6 UNKNOWN per host/ARM O0/O2 build.
Primitive, padded, explicit-alignment, generic, copied, incoming shared and caller-backed returned
field receivers are covered. Same-name local helpers execute actual bodies. The legacy sized raw
size control stays PROVED, while raw alignment and deprecated aliases retain their unmodeled
intrinsic frontier. Invalid/dead reference construction, trait roots and unsupported wrappers
remain UNKNOWN on their actual producer categories rather than an invented metadata access rule.

A real generic noinline metadata helper is changed to add one to its measured alignment.
Unchanged claims refute in all four builds with actual helper entry and same-obligation query/model.
Six original native tests pass at O0/O2 and valid 129-element mutation guards fail. Complete
commands, source/binary hashes, reports, outputs and timeouts are retained at
`/tmp/miren-stage162-final-evidence`. The unchanged earlier nested alignment source independently
proves in all four profiles before its harness expectation and obsolete UNKNOWN arm are maintained.
No application claim is rewritten. Three existing metadata units, fifteen related integration
tests and four focused new/earlier tests pass, with build/lint/fmt passing as well.

Three shared safe-sized alignment P/R/missing actual invoked body U controls yield 97 cases across
34 families, expecting 40 PROVED, 35 REFUTED and 22 UNKNOWN per configuration.
The two shared baseline integration tests pass. Independent source and evidence review approves
the exact safe API and receiver certificate.


Full isolated validation passes 667 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 616 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, nineteen new/related
integration tests, 68 Python tests and the remaining required checks also pass in main. Frozen
isolated and merged surveys retain 160 PROVED, 140 REFUTED and 88 UNKNOWN at
`/tmp/miren-stage162-capabilities-20261010` and
`/tmp/miren-stage162-merged-capabilities-20261010`, with current source/input/release hashes
verified. All 292 earlier completed P/R roots retain identical obligation statuses, details and
query text across four configurations. The actual generic helper mutation and native execution
ledgers remain at `/tmp/miren-stage162-final-evidence`. Independent review approves the exact
safe API/source/type certificates and unchanged-source expectation maintenance; no conditional
assumptions are added.


## Stage 163: issued input reservations and bounded scalar product preparation

Successful lazy input construction records an immutable original compiler root type, descriptor
Rc, exact Boolean seed and checked reserved interval. The ledger records actual issuance rather
than reconstructing provenance from matching sorts or numerical bounds. Complete original pure
root eligibility precedes bounded descent through declaration-order fields and array occurrences.
A requested descriptor must match its exact Rc, start offset and original child type. Repeated
copies reuse symbols; cached shapes in distinct roots and repeated same-sort leaves remain
independent. The ledger grants no allocation identity, lifetime, reference or write permission.

The former closed-product module becomes shared typed product preparation. Original consumer
type and each product's remaining cumulative 512-node/depth-16 budget precede descriptor metadata
checks and issued
source validation. Only then are existing reserved primitive symbols observed one level at a
time. Scalar context/sort, Float bits, byte metadata and Char checks retain their existing policy.
Closed zero-observable products still reconstruct without symbols. Generic input observers,
root construction policy and the reserved-slot limit are unchanged. Unsupported enum origins,
new Char descriptors, restricted original types and forged/unregistered inputs remain refused.

Three unchanged shared sources are first UNKNOWN on all four profiles at the exact scalar
reservation frontier. Actual input descriptions show three lazy arrays with 193 slots each.
After the new certificate, copied selection proves, independent-root equality refutes and the
missing invoked foreign body remains MissingCompilerEvidence UNKNOWN on its actual call.
Before/after commands, hashes and reports remain at `/tmp/miren-stage163-shared-before` and
`/tmp/miren-stage163-shared-after`. Three new controls yield 100 cases across 35 families,
expecting 41 PROVED, 36 REFUTED and 23 UNKNOWN per configuration.


The dedicated 21-root matrix yields 9 PROVED, 4 REFUTED and 8 UNKNOWN per host/ARM O0/O2 build.
Repeated selection, copies, original root alignment, sequential owned writes and untouched
root/occurrence correlations are checked. False equalities across roots, occurrences or fields
refute, as do unchecked bounds. The original Float/Char source remains UNKNOWN at the existing
input-producer budget; a separate Float-only source validates actual supported lazy observations.
Restricted N=0, enum-origin and retained borrow sources keep their actual separate frontiers.

An actual noinline getter is changed from left to right with the original claim and input domain
unchanged. All four profiles refute with actual helper entry and same-obligation query/model.
Six original native tests pass at O0/O2; valid 64-element mutation guards fail. Complete commands,
source/binary hashes, reports, outputs and timeouts remain at `/tmp/miren-stage163-final-evidence`.
Two new reservation units check root/seed/descriptor/offset identity, copied reuse, foreign and
altered envelopes, overflow and empty-array paths. Existing two product and three candidate units,
twenty-three related compiler tests and two final focused tests pass, as do build/lint/fmt.


Full isolated validation passes 671 Rust tests and 68 Python tests, formatting, cargo lint,
release builds, cargo deny, documentation build and manual hooks. Main's complete 619 tracked
files match the validated snapshot byte for byte. Fresh debug/release builds, nineteen new/related
integration tests, 68 Python tests and the remaining required checks also pass in main. Frozen
isolated and merged surveys retain 164 PROVED, 144 REFUTED and 92 UNKNOWN at
`/tmp/miren-stage163-capabilities-20261010` and
`/tmp/miren-stage163-merged-capabilities-20261010`, with current source/input/release hashes
verified. All 300 earlier completed P/R roots retain identical obligation statuses, details and
query text across four configurations. The actual getter mutation and valid native execution
ledgers remain at `/tmp/miren-stage163-final-evidence`. The two shared baseline tests pass.
Independent review approves the issued namespace, original-type and bounded observation
certificates; no conditional assumptions or generic input-observer changes are added.


## Stage 164: certified Field-path writes in owned array elements

The actual Assign hook admits an owned Array-local Index followed only by compiler Field
projections. Whole original element purity remains mandatory, including siblings and unused N=0
children. Original numbered field identity and monomorphic raw field type resolve a child shape
and checked logical leaf span; neither names nor physical offsets supply the certificate.

The exact child replacement and all complete old candidates share typed product preparation,
issued scalar reservation/closed-zero policy, scalar context/sort, Float bits and Char validity.
Expanded costs retain the existing cumulative 512-node/depth-16 limits. One index condition per
candidate updates the target span; untouched leaves remain exact. Complete nominal reconstruction
precedes commit to the same owned local or live allocation, with existing require_write/read.
Zero-leaf spans still validate replacement, effects, body, type and bounds. Constant and
solver-unique stores retain their old path. Rvalue evaluation and destination validators precede
the hook; retained references, raw/Deref, second Index and call destinations acquire no new rule.


The dedicated 27-root matrix yields 15 PROVED, 4 REFUTED and 8 UNKNOWN per host/ARM O0/O2 build.
Named, tuple, generic, nested-field, pure subtree and byte-subtree writes are covered with
untouched siblings/indices, sequential updates, allocated owners, three actual lazy scalar roots,
Float bits, Char validity and zero-leaf rvalue effects. Direct field observations also prove
through the existing typed reader, without a new reader rule or source rewrite. Actual zero-leaf
callback effects and panics execute; empty field spans do not bypass a body.

The unchanged earlier typed_struct_array_selection ambiguous_store source independently proves
in all four profiles before its harness expectation and obsolete UNKNOWN arm are maintained.
Original second-Index controls stay UNKNOWN. Retained/raw/reference-bearing, restricted N=0,
Drop, missing actual replacement body and existing resource cases retain their actual frontiers.
A real noinline helper assignment is changed from left to right; unchanged claims refute in all
four builds with actual helper entry and same-obligation query/model. Native originals use the
actual two-element owned domain and pass at O0/O2, while valid mutant guards fail. Complete
commands, hashes, reports, outputs and timeouts remain at `/tmp/miren-stage164-final-evidence`.

Shared partial-field P/R sources are first UNKNOWN on all four profiles at the nonunique array
write frontier; a missing actual rvalue body already stops at its separate compiler-evidence
frontier. After implementation, the original claims produce P/R and the missing body stays U.
Before/after commands, hashes and reports remain at `/tmp/miren-stage164-shared-before` and
`/tmp/miren-stage164-shared-after`. Three new controls yield 103 cases across 36 families,
expecting 42 PROVED, 37 REFUTED and 24 UNKNOWN per configuration.

Four product metadata tests cover certified spans, nominal and byte reconstruction, untouched
Float bits, malformed inventories/ranges, foreign conditions and zero-span validation. Nineteen
related compiler tests and four final new/earlier focused tests pass, as do build/lint/fmt.

Final validation passes all 674 Rust tests in the isolated frozen workspace and 68 Python tests.
All 621 tracked main files match that snapshot byte for byte. Fresh main debug/release builds,
22 new/related integration tests, 68 Python tests and all remaining required checks also pass.
Frozen isolated and main surveys retain 168 PROVED, 148 REFUTED and 96 UNKNOWN at
`/tmp/miren-stage164-capabilities-20261010` and
`/tmp/miren-stage164-merged-capabilities-20261010`, with source/input/release hashes verified.
All 308 earlier completed P/R roots retain identical obligation results, details and query text
across four configurations. The two shared baseline tests pass. Actual source mutation and native
execution evidence remains at `/tmp/miren-stage164-final-evidence`; independent review approves
final source and evidence. No assumptions, input caps or resource-budget changes are introduced.


## Stage 165: fixed nested indices in owned array write paths

The next extension follows compiler Field projections and constant fixed-array indices after an
initial symbolic owned-array Index. The complete original product certificate and checked logical
span remain mandatory; a nested array index requires its original element type and count.
Literal local indices must have the exact target usize type and context. Optimized ConstantIndex
metadata is checked against actual array length and offset bounds, including the pinned compiler's
shorter minimum-length encoding. End-relative and dynamic nested indices remain outside this rule.

Replacement and all complete old candidates retain bounded typed preparation, issued scalar input
reservations, zero-product validation and scalar representation checks. Existing rvalue effects,
bounds, destination validators, source liveness and same-owner commit remain required. The extension
reuses the conditional span update; it adds no assumptions, input caps or larger resource budgets.

Four shared fixed-index controls use actual three-array roots with 64 two-word elements per root.
Before implementation all four host/ARM O0/O2 configurations return UNKNOWN. Write-first and false
claims stop at the nonunique write frontier, the read-before-write source stops at the earlier lazy
nested-array reader, and the missing actual replacement body stops at its compiler-evidence
frontier. Commands, source/analyzer hashes and reports are retained at
`/tmp/miren-stage165-shared-expanded-before`. The write-first control independently proves after
implementation, while the false claim refutes and both separate UNKNOWN sources retain their
frontiers. The original read-before-write source is preserved; no reader rule is added here.
Frozen after-evidence at `/tmp/miren-stage165-shared-expanded-after` retains those exact outcomes
across all four compiler profiles, with empty assumptions and verified source/analyzer hashes.
Four shared controls yield 107 cases across 37 families, expecting 43 PROVED, 38 REFUTED and
26 UNKNOWN per configuration. Full required validation remains pending.

The dedicated 25-root matrix yields 13 PROVED, 4 REFUTED and 8 UNKNOWN per host/ARM O0/O2 build.
Fixed inner indices, alternating Field/Index paths, multiple constant levels, complete subtrees,
sequential updates, allocated owners, byte children, Float/Char and zero-leaf effects are covered.
The original lazy read-before-write source retains its earlier reader frontier; a separate
write-first lazy source proves. Dynamic nested indices, retained/raw/restricted values, missing
actual bodies and existing resource limits remain UNKNOWN at their recorded frontiers.

Four unchanged earlier sources prove independently in all four compiler profiles: pure array
symbolic_mutation, owned array deeper_store, field-write second_index and byte-array
ambiguous_store.
Only their harness expectations and obsolete UNKNOWN arms are maintained; source claims stay
unchanged. Initial expectation failures remain in the related logs. Five product metadata tests,
ten new/earlier focused compiler tests and 21 related integration tests pass. Final fmt, lint and
fresh debug build pass. A real noinline assignment helper changes inner index 0 to 1; final
mutation/native evidence is retained separately, with full required validation pending.

Final validation passes all 677 Rust tests in the isolated frozen workspace and 68 Python tests.
All 623 tracked main files match the validated snapshot byte for byte. Fresh main debug/release
builds, nineteen new/related integration tests, 68 Python tests and all remaining required checks
also pass. Frozen isolated and main surveys retain 172 PROVED, 152 REFUTED and 104 UNKNOWN at
`/tmp/miren-stage165-capabilities-20261010` and
`/tmp/miren-stage165-merged-capabilities-20261010`, with source/input/release hashes verified.
All 316 earlier completed P/R roots retain identical obligation results, details and query text
across four configurations. Actual inner-index assignment mutation and valid two-element native
controls remain at `/tmp/miren-stage165-final-evidence`; independent review approves final source
and evidence. No assumptions, input caps or resource-budget changes are introduced.


## Stage 166: certified deferred pure tuple and array reads

The next extension lets actual deferred Input candidates in original pure tuple/fixed-array
products use the existing typed choice preparation. Earlier generic, constant and solver-unique
selection paths retain their priority, with actual bounds and source checks before the typed
route. The deferred marker only chooses a route; complete original type/shape, existing issued
scalar or closed-zero preparation, scalar context and cumulative node/depth validation still
certify every value. Each descriptor is certified before its own reserved symbols are observed;
complete candidate preparation precedes selection.

The original stage165 shared read-before-write source is retained. New tuple/array read-correlation,
independent-root false claim and missing actual field body controls use three 64-element roots.
All four compiler profiles return UNKNOWN before implementation at the earlier lazy read frontier.
Commands, source/analyzer hashes and full reports are retained at
`/tmp/miren-stage166-shared-expanded-before`. Final outcomes and validation are pending.

The dedicated 20-root matrix yields 9 PROVED, 4 REFUTED and 7 UNKNOWN per host/ARM O0/O2 build.
Registered pure tuple/fixed-array reads preserve repeated/copy correlations, independent roots,
Float representation and zero children. The original oversized self-equality source proves
without requiring a deep product observation; a separate over-cap observation uses three actual
lazy roots and reaches the existing 128-element shape resource frontier. Neither source claim
is weakened or relabeled to suggest deeper support.

The unchanged longer stage165 lazy_roots source retains UNKNOWN at a later borrowed-array
comparison/index frontier after its initial reads progress. Its original whole claim and harness
expectation are preserved. The simpler original shared read-before-write source proves in all
four profiles. A real noinline by-value reader changes inner index 0 to 1; unchanged claims refute
across all
four profiles with actual helper entry and same-obligation query/model. Valid originals use the
actual 64-element roots and pass six native tests at O0/O2; mutant guards fail. Complete commands,
source/analyzer/native hashes, reports, outputs and ten-second native timeouts remain at
`/tmp/miren-stage166-final-evidence`. Frozen shared before/after reports retain the original P,
new P/R and missing actual body U outcomes at `/tmp/miren-stage166-shared-expanded-after`.
Six metadata tests and 23 related compiler tests pass. Full required validation remains pending.

Final validation passes all 680 Rust tests in the isolated frozen workspace and 68 Python tests.
All 625 tracked main files match the validated snapshot byte for byte. Fresh main debug/release
builds, nineteen new/related integration tests, 68 Python tests and all remaining required checks
also pass. Frozen isolated and main surveys retain 180 PROVED, 156 REFUTED and 104 UNKNOWN at
`/tmp/miren-stage166-capabilities-20261010` and
`/tmp/miren-stage166-merged-capabilities-20261010`, with source/input/release hashes verified.
All 324 earlier completed P/R roots retain identical obligation results, details and query text
across four configurations. Actual reader mutation and valid 64-element native controls remain
at `/tmp/miren-stage166-final-evidence`; independent review approves final source and evidence.
No assumptions, input caps or resource-budget changes are introduced. The earlier longer borrowed
comparison claim remains UNKNOWN at its recorded frontier.


## Stage 167: one symbolic nested index in owned array writes

The certified destination plan admits one symbolic nested fixed-array Index among existing
Field and constant-index projections after a nonunique owned outer Index. Original parent purity,
raw child types, homogeneous child shapes and checked disjoint logical spans precede the update.
Actual target-usize type, scalar context and inner bounds are required. Two symbolic nested
indices, retained references, raw/Deref and call destinations gain no new rule.

Each target leaf uses the joint outer/inner equality condition. Replacement and every complete
old candidate are prepared and flattened once, then complete reconstruction precedes one commit
to the same live owned local or allocation. Candidate and depth limits remain unchanged; expanded
mask work uses the existing 512-node bound. Zero-leaf targets retain effects, body, bounds, type and
context checks. Single-target conditional helpers and constant/solver-unique outer priority remain
unchanged, with query compatibility checked separately.

The dedicated 24-root matrix yields 12 PROVED, 4 REFUTED and 8 UNKNOWN per host/ARM
O0/O2 build. The unchanged earlier dynamic_inner source independently proves in all four profiles
before its harness expectation and obsolete UNKNOWN arm are maintained. Source claims remain
unchanged. Four new/earlier focused tests and 23 related compiler tests pass. Final build, lint,
fmt and seven product metadata tests pass.

Three shared controls use actual three-root 64-element arrays. Before implementation all four
compiler profiles return UNKNOWN for supported and false claims at the symbolic nested-write
frontier, while the missing actual replacement body retains its compiler-evidence frontier.
Initial after-probes yield P/R/U with empty assumptions. Commands, source/analyzer hashes and
reports remain at `/tmp/miren-stage167-shared-expanded-before` and
`/tmp/miren-stage167-shared-expanded-after`; frozen after-evidence retains those exact outcomes
and verifies current source/analyzer hashes. Three controls yield 113 cases across 39 families,
expecting 46 PROVED, 40 REFUTED and 27 UNKNOWN per configuration.

A real noinline helper assignment changes the selected inner index to inner XOR 1. The unchanged
claim refutes in all four compiler profiles with actual helper entry and same-obligation
query/model.
Valid originals use the actual two-by-two array domain and pass six native tests at O0/O2; mutant
guards fail. Complete commands, hashes, reports, outputs and ten-second native timeouts remain at
`/tmp/miren-stage167-final-evidence`. Full required validation remains pending.

Final validation passes all 683 Rust tests in the isolated frozen workspace and 68 Python tests.
All 627 tracked main files match the validated snapshot byte for byte. Fresh main debug/release
builds, nineteen new/related integration tests, 68 Python tests and all remaining required checks
also pass. Frozen isolated and main surveys retain 184 PROVED, 160 REFUTED and 108 UNKNOWN at
`/tmp/miren-stage167-capabilities-20261010` and
`/tmp/miren-stage167-merged-capabilities-20261010`, with source/input/release hashes verified.
All 336 earlier completed P/R roots retain identical obligation results, details and query text
across four configurations. Actual inner-index mutation and valid two-by-two native controls
remain at `/tmp/miren-stage167-final-evidence`; independent review approves final source and
complete evidence. No assumptions, input caps or resource-budget changes are introduced.


## Stage 168: retained compiler type evidence for owned shared projections

The remaining lazy-array comparison frontier occurs before any PartialEq body entry. An actual
shared borrow calls the untyped place reader, and later retained reference traversal also lacks
the original compiler array type. Making only borrow creation Body-aware is insufficient.

The foundation carries a private compiler type certificate with a retained indexed
projection. Actual shared owned-array MIR and its original prefix type issue the certificate;
it supplies type evidence only. The real owner allocation, projection, capability, lifetime and
frame graph remain authoritative. Current complete source/candidate types, bounds, scalar context
and issued-scalar or closed-zero preparation must be checked on every later observation.
Detached snapshots, allocation-number type maps, mutable/raw/static grants and certificate ids
as address identity are excluded. Projection consumers require an exhaustive audit.

Three shared caller/callee read, false field claim and missing actual getter body controls use
three actual 64-element roots. Before implementation all four compiler profiles return UNKNOWN
at the earlier projected-borrow frontier. Complete commands, hashes and reports remain at
`/tmp/miren-stage168-shared-expanded-before`. Final outcomes and validation remain pending.

Initial probes exposed an older eager-array escape bug: a returned reference to frame-owned
storage could become an owned snapshot. Compiler-correlated return-reference graph validation
now precedes dereference and pure-slice pruning, while owned-value snapshot conventions retain
their separate representation. A distinct three-root custom MIR control exercises the new
certificate path. Neither dangling source is endorsed as a successful proof. Final validation
remains pending.

The new shared controls yield PROVED, REFUTED and missing-actual-body UNKNOWN in every host/ARM
O0/O2 build, with empty assumptions and verified source/analyzer hashes. Reports remain at
`/tmp/miren-stage168-shared-expanded-after`. The unchanged stage165 lazy_roots and stage166
read_then_write whole claims also independently prove in all four configurations before harness
expectation upkeep; their original source and obligations are preserved. Three new shared cases
yield 116 cases across 40 families, expecting 47 PROVED, 41 REFUTED and 28 UNKNOWN per
configuration.

Two further unchanged registered-product and pure-array retained_borrow controls independently
prove in host/ARM O0/O2 before harness-only expectation upkeep. Initial obsolete UNKNOWN assertion
failures and original source hashes remain with the before/after evidence.

The dedicated 29-root matrix yields 13 PROVED, 4 REFUTED and 12 UNKNOWN per compiler
configuration in the focused pass. It exercises exact callee and custom PartialEq body entry,
copied handles, owner updates, caller-backed returns and both frame-escape paths. Static literal
reads use their earlier initializer model; they do not demonstrate a new certificate grant.
An actual shared-to-mutable reborrow reaches the existing writable-storage refusal, while the
original transmute control keeps its earlier frontier. Three new metadata tests and eight
reference-graph tests pass. Seven related suites yield nineteen passing tests; the new fixture
and three maintained old suites yield eight. Final frozen validation remains pending.

The first full workspace run exposed three more obsolete UNKNOWN assertions: unchanged
deferred-zero retained_borrow, typed-byte retained_borrow and nominal_zero claims now prove.
All 24 UNKNOWN roots in those three harnesses were probed in all four configurations; only those
three advance, while the other 21 preserve their outcomes and frontiers. Original fixture sources
remain unchanged. Twelve complete reports, commands and hashes remain at
`/tmp/miren-stage168-full-gap-probes`; the initial full failure log remains at
`/tmp/miren-stage168-checks/tests-initial-obsolete-expectations.log`. Harness-only upkeep precedes
a corrected full-suite rerun. Engine and compiler fixture hashes remain frozen.

Final corrected validation passes all 688 Rust tests in the isolated frozen workspace and
68 Python tests. All 630 tracked main files match that snapshot byte for byte. Fresh main
debug/release builds, twenty-seven new/related integration tests, 68 Python tests and all remaining
required checks pass. Initial obsolete expectation failures remain preserved; the engine and
fixture sources are unchanged by their upkeep. Both frozen surveys retain 188 PROVED, 164 REFUTED
and 112 UNKNOWN at `/tmp/miren-stage168-capabilities-20261010` and
`/tmp/miren-stage168-merged-capabilities-20261010`, with source/input/release hashes verified.
All 344 earlier completed P/R roots retain identical obligations, details and query text across
four configurations. Independent review approves final source, actual getter mutation and valid
64-element native evidence. Eager and typed dangling-reference returns now retain Semantics
UNKNOWN, while supported comparisons advance without source changes. No assumptions, input caps
or resource-budget changes are introduced.


## Stage 169: known outer indices with symbolic nested owned writes

The previous owned writer deliberately keeps compiler-constant and solver-unique outer stores
on their older path. A symbolic inner index can still reach an unsupported projected-write
boundary. The proposed extension reuses the certified indexed product plan after that precise
old-writer refusal, preserving already supported byte writes and their queries. Full original
parent types, current owner, bounds, effects and transaction checks remain required.

Three new shared controls retain actual three-root 64-element arrays and unchanged selected-cell,
untouched-cell and wrong-cell claims. Before/after outcomes and validation remain pending.

Before probes return UNKNOWN for the valid and false claims at the projected-write boundary,
while the missing replacement body retains its compiler-evidence frontier, across all four
configurations. Commands, source/analyzer hashes and original reports remain at
`/tmp/miren-stage169-shared-expanded-before`. No assumptions are introduced.

Initial shared after-probes yield PROVED for selected and untouched-cell claims, REFUTED for the
wrong-cell claim, and missing-actual-body UNKNOWN in every host/ARM O0/O2 build with empty
assumptions. Commands, hashes and reports remain at
`/tmp/miren-stage169-shared-expanded-after`; final immutable capture remains pending. A separate
byte-store control proves before this extension and requires identical completed queries after it.

The dedicated 27-root matrix yields 14 PROVED, 5 REFUTED and 8 UNKNOWN across host/ARM O0/O2.
The unchanged original known_outer claim independently proves in all four configurations before
harness-only expectation upkeep. New and maintained focused compiler tests pass; exact byte-store
query compatibility and final immutable mutation/native evidence remain pending.

Final immutable reports retain the 27-root 14/5/8 matrix across all four builds. A real by-value
helper changes the selected inner index to inner XOR 1; unchanged claims refute in every build
with actual helper entry and the same failing query/model. Valid originals pass seven native
tests at O0/O2; mutant guards exit 101. Complete commands, hashes, reports, outputs and
ten-second native timeouts remain at `/tmp/miren-stage169-final-evidence`. All seven completed
byte-store obligations and query texts remain identical in each profile to the immutable stage168
analyzer on the same final fixture source. No new byte-write support is claimed. Four focused
compiler tests, twenty-one related tests and four metadata controls pass. Full validation pending.


Final frozen validation passes 692 Rust tests and 68 Python tests in the isolated workspace.
All 632 tracked main files match that snapshot byte for byte. Fresh main debug/release builds,
twenty-five new/related integration tests, 68 Python tests and every remaining required check pass.
Both surveys retain 192 PROVED, 168 REFUTED and 116 UNKNOWN, with source/input/release hashes
verified, at `/tmp/miren-stage169-capabilities-20261010` and
`/tmp/miren-stage169-merged-capabilities-20261010`. All 352 earlier completed roots preserve
identical status, obligation details and query text across four profiles. Independent review
approves final source, actual helper mutation and valid native evidence. No assumptions, input
caps or resource-budget changes are introduced.


## Stage 170: owned product fields containing symbolic array writes

A direct owned tuple or certified ordinary struct can contain an array under compiler Field
projections. The writer reuses the original-type product path/span plan and complete
root reconstruction after the older writer reaches its precise unsupported index boundary.
Original root and every field retain pure-type, complete current-source, bounds, input provenance
and cumulative resource checks. The transaction uses the same actual owner; no new reader or
reference capability is planned.

Three new shared controls use actual three-root 64-element struct arrays, preserving selected
and untouched record fields, a root sibling, an untouched row and a false-field claim. Missing
actual replacement bodies retain their independent compiler-evidence requirement. Validation
and immutable before/after outcomes remain pending.

The dedicated 29-root matrix yields 14 PROVED, 5 REFUTED and 10 UNKNOWN in host/ARM O0/O2.
Original selected and lazy read-before-write claims remain unchanged and prove; no distinct
workaround source is needed. Literal byte stores already prove before this extension and all
four completed obligations and query texts remain identical in each compiler profile afterward.

A real by-value helper changes the selected index to index XOR 1. Unchanged caller claims refute
in all four profiles with actual helper entry and the same failing query/model. Valid originals
pass seven native tests at O0/O2; mutant guards exit 101. Eight reports, native outputs, commands,
hashes and ten-second timeouts remain at `/tmp/miren-stage170-final-evidence`. Two dedicated
compiler tests, nineteen related tests and the new root-span/index-context metadata control pass.

Shared controls retain actual three-root 195-slot struct products. Before probes yield UNKNOWN
for valid/false claims at the field-root array-write boundary, with missing actual body UNKNOWN
separately. Frozen after-probes yield P/R/missing-body U in all four configurations with empty
assumptions and verified source/analyzer hashes. Commands and reports remain at
`/tmp/miren-stage170-shared-expanded-before` and
`/tmp/miren-stage170-shared-expanded-after`. Full required validation remains pending.


Final frozen validation passes all 695 Rust tests and 68 Python tests in the isolated workspace.
All 634 tracked main files match that snapshot byte for byte. Fresh main debug/release builds,
twenty-seven new/related integration tests, 68 Python tests and every remaining required check
pass. The initial harness line-wrap formatting failure and exact correction remain preserved;
corrected formatting and its two affected compiler tests pass. Both surveys retain 196 PROVED,
172 REFUTED and 120 UNKNOWN, with source/input/release hashes verified, at
`/tmp/miren-stage170-capabilities-20261010` and
`/tmp/miren-stage170-merged-capabilities-20261010`. All 360 earlier completed roots preserve
identical status, obligation details and query text across four profiles. Independent review
approves final source, actual helper mutation and valid native evidence. No assumptions, input
caps or resource-budget changes are introduced.


## Stage 171: retained shared array projections behind owned fields

A direct owned-array certificate cannot validate the original enclosing tuple or ordinary struct
when a retained projection starts with Field. The proposed extension records the original pure
root type and bounded field path in the private certificate. Every observation must validate the
complete current live root before field materialization and selected array reading. Empty paths
preserve earlier direct-array behavior, with unchanged owner, lifetime and reference checks.

Three shared controls retain actual three-root 64-element arrays within ordinary structs,
selected-field and wrong-root claims, and actual shared getter body entry. Before probes return
UNKNOWN at the projected-borrow boundary in all four profiles, including the missing-body control
which has not yet reached its call. Commands, source/analyzer hashes and original reports remain
at `/tmp/miren-stage171-shared-expanded-before`. Final implementation and validation are pending.


Initial shared after-probes yield PROVED for the selected and repeated-field claims, REFUTED for
the independent-root claim, and missing-actual-getter-body UNKNOWN across host/ARM O0/O2 with
empty assumptions. Complete commands, hashes and reports remain at
`/tmp/miren-stage171-shared-expanded-after`; immutable final recapture and validation are pending.


The final dedicated 32-root matrix yields 19 PROVED, 4 REFUTED and 9 UNKNOWN per profile.
Eight eager/byte/primitive/Char/static paths already succeed before the extension; their original
sources remain unchanged and acquire no new-model attribution. Eight pre-existing entries retain
exact completed query text in every profile: 32 entry/profile comparisons and 80 obligations in
total. Four older direct-array callee/equality/byte/float roots also retain exact queries in all
four configurations: 16 entry/profile comparisons and 40 obligations in total.

The actual shared getter changes field 0 to field 1; unchanged caller claims refute in every build
with actual body entry and the same failing query/model. Originals pass seven valid native tests
at O0/O2; mutant guards exit 101. Complete reports, commands, hashes, outputs and ten-second
timeouts remain at `/tmp/miren-stage171-final-evidence`. Two dedicated compiler tests, two
metadata tests, eight reference-graph tests and seventeen related integration tests pass.
The initial obsolete model-label assertion failure remains preserved. Final shared recapture
retains P/R/missing-body U under the frozen binary and empty assumptions. Full validation pending.


Final frozen validation passes all 698 Rust tests and 68 Python tests in the isolated workspace.
All 636 tracked main files match that snapshot byte for byte. Fresh main debug/release builds,
twenty-nine new/related integration tests, 68 Python tests and every remaining required check
pass. Both surveys retain 200 PROVED, 176 REFUTED and 124 UNKNOWN, with source/input/release hashes
verified, at `/tmp/miren-stage171-capabilities-20261010` and
`/tmp/miren-stage171-merged-capabilities-20261010`. All 368 earlier completed roots preserve
identical status, obligation details and query text across four profiles. Independent review
approves final source, actual getter mutation, valid native evidence and 48 entry/profile
comparisons of old paths. Initial obsolete model-label failures remain preserved. No assumptions,
input caps or resource-budget changes are introduced.


## Stage 173: concrete assignment storage boundary

Assignment evaluation and storage dispatch were interleaved in the statement walker. A concrete
`store_assignment_value` method now owns the existing destination validators and writer selection.
The statement evaluates its rvalue once before calling this method. Validation order, original
writer precedence, exact unsupported-index fallback and same-owner transactions remain unchanged.
All eight function-result stores retain their prior policy during this representation refactor.

The initial frozen Stage 171 comparison passes lint and twelve related compiler tests. Its survey
retains 200 PROVED, 176 REFUTED and 124 UNKNOWN. All 376 completed parent roots retain identical
status, obligation details and query text across host/ARM O0/O2. Independent review checks the
extracted statement body and unchanged call branches. Evidence remains at
`/tmp/miren-stage173-preparent-checks` and
`/tmp/miren-stage173-preparent-existing-query-comparison.json`.
Final required validation is recorded below. This stage is independent of the separate
composite comparison implementation.


Final frozen validation passes all 698 Rust tests and 68 Python tests in the isolated workspace.
All 636 tracked main files match that snapshot byte for byte. Fresh main debug/release builds,
twelve related integration tests, 68 Python tests and every remaining required check pass. Both
surveys retain 200 PROVED, 176 REFUTED and 124 UNKNOWN with source/input/release hashes verified at
`/tmp/miren-stage173-capabilities-20261010` and
`/tmp/miren-stage173-merged-capabilities-20261010`. All 376 completed parent roots retain identical
status, obligation details and query text. All 500 main/isolate selected results, queries, models
and premises match. Independent review approves the exact extraction and unchanged call stores.
No assumptions, input caps or resource-budget changes are introduced. Stage 173 follows Stage 171;
composite comparison Stage 172 remains an independent implementation.


## Stage 174: pre-call indices for direct owned result destinations

A function-result destination was re-evaluated after its callee returned. Actual native execution
of `Call(values[index] = advance(&mut index))` selects the original index. The existing analyzer
instead selected the changed index: it refuted the valid pre-call claim and proved the incorrect
post-call claim in all four profiles. Host O0/O2 execution passes the former and fails the latter.
The unchanged source, commands, queries and binary hashes remain preserved at
`/tmp/miren-stage174-destination-both-directions`.

A private certificate now captures distinct original compiler-usize indices and caller owner
identity before call execution. It validates the complete pure root, declared field types, fixed
indices, original array counts, pre-call bounds and write rights. The same immutable indices feed
the existing generic and typed writers using each returned continuation's current owner memory.
Current liveness, unchanged owner identity, complete root and exact replacement are checked again.
Whole-local result stores retain their original policy; dereference destinations, including
static and raw bases, require a separate pre-call base-location certificate and remain unsupported.
Calls and effects are executed once; a callback cannot retroactively establish destination bounds.

The unchanged timing pair now yields PROVED/REFUTED in all four profiles with empty assumptions.
The final nineteen-root matrix yields eight PROVED, three REFUTED and eight UNKNOWN per profile.
Actual replacement mutation refutes unchanged caller claims; five valid native originals pass
at O0/O2 and mutant guards fail. Two original older call-destination sources advance from UNKNOWN
to PROVED across all four profiles, preserving actual replacement body entry. Initial obsolete
UNKNOWN expectation failures remain saved before harness-only upkeep. New global valid, wrong
and missing-body controls yield P/R/U; original native controls pass and actual advance mutation
fails. All 376 previously completed global roots keep identical status, details and query text.
Evidence remains beneath `/tmp/miren-stage174-destination-both-directions-after`,
`/tmp/miren-stage174-old-call-destination`, `/tmp/miren-stage174-old-known-call-destination`,
`/tmp/miren-stage174-native-final` and `/tmp/miren-stage174-global-initial-after`.
Parent integration, immutable final evidence and full required checks remain pending.


The base-location audit finds the same confirmed false positive without any Index projection:
a callee redirects a reference used in `Call(*pointer = redirect(...))`. Native execution stores
through the original pointer, while the old analyzer re-resolves its changed base. All four
profiles refute the valid claim and prove the wrong one before correction. Until base-location
capture is implemented, any dereference Call destination returns explicit Semantics UNKNOWN
before model or callee execution. Both unchanged claims retain honest UNKNOWN, with native
pass/fail evidence preserved at `/tmp/miren-stage174-deref-destination-evidence`.


Final validation passes all 700 Rust tests and 68 Python tests in the isolated workspace.
The full-test source ledger verifies identical semantic and test bytes after actual Stage 173
parent adoption; only documentation changed. All 639 tracked main files match the final snapshot
byte for byte. Fresh main debug/release builds, fourteen related integration tests, 68 Python
tests and every remaining required check pass. Both frozen surveys yield 204 PROVED, 180 REFUTED
and 128 UNKNOWN at `/tmp/miren-stage174-capabilities-20261010` and
`/tmp/miren-stage174-merged-capabilities-20261010`, with source/input/release hashes verified.
All 376 earlier completed roots retain identical status, obligation details and query text; all
512 main/isolate selected results, queries, models and premises match. Independent source review
approves the nineteen-root matrix, actual replacement mutation, valid native controls and mandatory
dereference refusal. No assumptions, input caps or resource-budget changes are introduced.
This correctness stage follows Stage 173 independently of composite comparison Stage 172.


## Stage 175: captured tracked call-result locations

The dereference timing guard in Stage 174 prevents a confirmed false proof. This extension
captures an actual unprojected tracked mutable reference's allocation and typed destination path
before the callee executes. It requires a complete original pure pointee type and pre-call bounds.
Each returned continuation validates that allocation's current live writable root and exact
replacement together before one commit. Callee pointer redirection cannot change the captured
location, and sibling effects are retained. Shared, raw, static and inherited references gain no
new permission; symbolic writes retain their existing uniqueness and bounds requirements.

The unchanged prior pointer-redirection claims move from UNKNOWN to PROVED/REFUTED in all four
profiles, with empty assumptions. Original sources remain unchanged. The obsolete reason failure
for the older retained-index control is preserved before harness-only upkeep; this control remains
UNKNOWN at its actual pre-call bounds frontier. Evidence remains at
`/tmp/miren-stage175-old-call-destinations` and
`/tmp/miren-stage175-old-call-destinations-initial.log`.

The dedicated twenty-root matrix yields eight PROVED, three REFUTED and nine UNKNOWN per profile.
Actual replacement mutation refutes unchanged claims; valid originals pass native O0/O2 and
mutant guards exit 101 under ten-second timeouts. Complete provisional reports, commands and
source/binary hashes remain at `/tmp/miren-stage175-final-evidence`. Independent review confirms
bounded validation precedes root cloning. Final parent integration and required checks remain
pending; composite comparison Stage 172 proceeds independently.


The global tracked-location triplet yields P/R/missing-body U across all four profiles. The exact
same source returns UNKNOWN for all three under the immutable Stage 174 binary. Actual redirect
replacement mutation from 19 to 20 refutes the unchanged selected-location claim in all builds.
Native custom-MIR originals pass at O0/O2; mutant guards fail with exit 101. Full reports, commands,
query/model equality, empty assumptions and ten-second native timeouts remain at
`/tmp/miren-stage175-global-evidence`. The expanded manifest contains 131 cases in 45 families;
these counts describe the selected controls and do not establish a Rust coverage percentage.


Final validation passes all 703 Rust tests and 68 Python tests in the isolated workspace.
All semantic and test source bytes remain unchanged across actual Stage 174 parent adoption;
only documentation changed. All 642 tracked main files match the final snapshot byte for byte.
Fresh main debug/release builds, sixteen related integration tests, four storage-location unit
tests, 68 Python tests and every remaining required check pass. Both frozen surveys yield
208 PROVED, 184 REFUTED and 132 UNKNOWN at `/tmp/miren-stage175-capabilities-20261010` and
`/tmp/miren-stage175-merged-capabilities-20261010`, with source/input/release hashes verified.
All 384 previously completed roots retain identical status, obligation details and query text;
all 524 main/isolate selected outcomes, queries, models and premises match. One host O0 fold
retains the same thirty-second resource UNKNOWN with a closure-context diagnostic prefix in only
one run; both original reports and the initial exact-detail mismatch remain preserved. Source
review approves original-location capture, current-owner validation, the twenty-root matrix and
actual dedicated/global mutation and native evidence. No assumptions, input caps or resource-
budget changes are introduced. Stage 175 follows Stage 174; composite comparison Stage 172
remains an independent implementation awaiting integration.


## Stage 172: certified full-domain pure composite slice predicates

This independently authored stage integrates after Stage 175. Exact original primitive, unit,
tuple and fixed-array types define recursive numeric comparison. A common logical index observes
all element occurrences; scoped existential membership and length-guarded universal equality keep
arbitrary runtime slice length within the original target extent. Float NaN and signed-zero rules,
Char decoding, complete N=0 children and live source/type/extent checks precede formula creation.
Nominal custom effects and unsupported access paths receive no new summary or permission.

The private semantic encoder matches complete actual pinned core MIR against 113 immutable
reference variants and authenticates compiler identities before normalization. Selected concrete
transitive helpers and closure transport require matching bodies; evaluated SIZE/IS_ZST/ALIGN
constants agree with compiler layout. Target32/64 arithmetic counterexample queries certify exact
caller-guarded cursor addition/subtraction before omitting their unreachable overflow panic edge.
Other missing bodies remain UNKNOWN. Independent source review records the checked boundaries at
`/tmp/miren-stage172-final-source-review.md`.

The frozen thirty-two-root author matrix yields fourteen PROVED, six REFUTED and twelve UNKNOWN
across host/ARM O0/O2. Actual selected needle leaf mutation refutes and fails native O0/O2 guards;
eight valid native originals pass. Full reports, commands, hashes and ten-second timeouts remain
at `/tmp/miren-stage172-final-evidence`. Fifty-six completed older queries retain identical
status, kind, detail and query: forty-eight
scalar/byte/custom fixture queries plus eight separate finite-custom-false queries. Evidence is at
`/tmp/miren-stage172-query-fidelity`. One-byte composite membership and mixed descriptor/finite
equality remain explicit UNKNOWN. Before results for the exact final sources remain preserved.

Two unchanged original composite roots advance from UNKNOWN to PROVED in all four profiles.
Initial obsolete UNKNOWN expectation failure remains at
`/tmp/miren-stage172-old-composite-initial.log`
before harness-only upkeep; sources and actual after reports remain at
`/tmp/miren-stage172-old-composite-after`. The shared triplet yields P/R/missing-body U in the
frozen author binary at `/tmp/miren-stage172-shared-expanded-after`. These author captures
preceded combined parent integration, global mutation evidence and full required validation.


The combined source preserves all Stage 175 assignment and eight call-result stores exactly;
`proof.rs` adds only two module declarations. All 119 disjoint modules/reference assets match the
reviewed author freeze. Integrated metadata tests and eight new/related compiler tests pass.
Independent composition review is recorded at `/tmp/miren-stage172-integrated-source-review.md`.
The final global recapture uses the post-test frozen binary and confirms P/R/missing-body U plus
actual helper mutation across all four profiles at
`/tmp/miren-stage172-integrated-global-final-evidence`. Original native evidence, prior captures
and hashes remain separately recorded. These captures preceded final full validation.


The initial manual hook trimmed ten reference files at physical wrap boundaries. That interrupted
validation run and its original failures remain at `/tmp/miren-stage172-initial-checks`; it is not
counted as a completed suite. The corrected encoder records each terminal whitespace code point
with a reserved marker and rejects marker collisions. All 113 decoded references preserve the
original complete semantic bytes; exactly ten assets change their physical encoding. Four metadata
tests and eight compiler integration tests pass, and hooks leave every asset unchanged. The
canonical correction supersedes the original physical-byte freeze for these eleven paths only.
Evidence remains at `/tmp/miren-stage172-canonical-reference-proof.json` and
`/tmp/miren-stage172-integrated-canonical-core-freeze.json`. The corrected binary recaptures all
eight global after/mutation reports at `/tmp/miren-stage172-integrated-global-canonical-evidence`;
unchanged native evidence retains its original source and execution scope.


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


## Stage 176: readonly direct-tag enum slices


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


## Stage 177: readonly exact Bool niche enum slices


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

## Stage 178: readonly nominal enum payloads


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

## Stage 179: readonly exact Char niche enums


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

## Stage 181: concrete trait-object supertrait upcasts


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


## Stage 180: owned-place initialization and coroutine preservation

This stage integrates after actual Stage 181 commit `38b3b45`. An explicit initialization
ledger follows owned Move operands and actual drop calls through local and tracked storage.
Exact writes repair covered fields without reviving a consumed ancestor. Loads and reference
traversal check initialization before following payloads. Call destinations are captured before
the callee operand and left-to-right arguments. Definite or unresolved overlap between a moved
input and destination returns semantic UNKNOWN under the unresolved compiler contract.

Exact compiler coroutine projections preserve move effects across suspension. Certificates hold
weak references to the original immutable body and cannot survive body replacement or expiry.
Typed observation snapshots scrub inactive consumed fields without modifying live storage.
Exact compiler Pin helper packaging retains validated references while ordinary partially moved
aggregates and escaping frame references remain unsupported. No hardware model is introduced.

Inductive states may omit consumed private temporaries only after compiler liveness and a bounded
scan of the exact future MIR establish no overlapping read before a covering write. RHS reads
precede repairs; storage markers do not repair initialization. Unknown projections refuse this
omission. Arguments, return storage, addressed locals and tracked memory remain strict.

The repaired dedicated matrix has 33 roots with thirteen PROVED, one REFUTED and nineteen UNKNOWN
in all host/ARM O0/O2 profiles. Actual helper mutation refutes the unchanged claim in each profile.
Valid native companions pass at O0/O2; actual helper mutants exit 101 with ten-second timeouts.
Compiler-only invalid MIR is never executed natively. Evidence, source and binary hashes remain
at `/tmp/miren-stage180-repair-final-evidence` and
`/tmp/miren-stage180-repair-core-freeze.json`.

All 72 old async root/profile outcomes remain identical, including 56 completed roots and
24 completed obligation queries. Four existing query-free UNKNOWN diagnostics change only the
missing-field wording at the same Context::waker boundary; original details remain in
`/tmp/miren-stage180-coroutine-fidelity/comparison.json`. All 64 old induction root/profile
outcomes, obligations and premises remain identical, including 28 completed roots and 48 actual
queries, at `/tmp/miren-stage180-induction-fidelity/comparison.json`. Initial implementation,
expectation and probe failures are retained. These focused captures preceded full validation.

The initial integrated full run retained four failed tests across compiler DR16 and inductive
iterator suites. Its source remains at `/tmp/miren-stage180-initial-integrated-source`; original
logs and surveys remain at `/tmp/miren-stage180-checks` and the initial capability directories.
The other 731 Rust tests passed. The expected native-mutant child failure is distinct from these
four Cargo test failures. Initial surveys both yield 236 P, 212 R and 160 U, with all 440 old
completed roots and all 608 main/isolate outcomes, queries, models and premises identical.
These passing selected surveys did not override the broader regression failures.

Actual instantiated `Result::ok` moves the Ok payload before reading the retained tag for drop
dispatch. The repair validates the original enum path, nominal schema and tag without reading
consumed payloads. Ancestor and whole masks remain strict, including niche representations;
arbitrary uninitialized discriminants receive no permission. Exact no-drop MIR Drop short-circuits
without source observation. Compiler-backed scanner controls reject forged recorded field types.

The custom iterator failed in blanket `IntoIterator::into_iter`: its by-value argument legitimately
moves into the return value. A separate terminal adapter preserves consumed argument masks only
for bounded original reference-free, Freeze, noDrop types without addressed storage. It emits no
successor atom or captured terminal state. Returned values and memory stay strict; current-final
postcondition argument reads still refuse consumed storage. The old DR16 proof and real mutants,
Cargo parser test and custom-iterator tests pass in focused repair replay. Reference, addressed and
current-final argument controls remain UNKNOWN. These focused captures preceded corrected full
validation.


The corrected full run restored DR16 and inductive iterator execution, then exposed eight stale
expectations in six storage suites. Its 728 passing tests and eight failures remain at
`/tmp/miren-stage180-repair-checks`. Those helpers dropped types without drop glue; optimized
MIR specifies a complete no-op. Thirty-two unchanged-source runs across host/ARM O0/O2 and their
original ordinary, startup, isolated or trusted modes establish the corrected expectations at
`/tmp/miren-stage180-no-drop-probes`. Actual destructor, lifetime, permission and opaque-effect
controls retain their conservative boundaries. A wrong sibling-value claim now correctly refutes.

The original store-removal claim allowed either enum tag, so it remains a preservation control.
A separate exact written-tag claim proves under the existing recorded startup premises; removing
the actual store refutes the unchanged claim in every profile with the same query and model.
Native originals pass and mutants exit 101 at O0/O2. The original fixture remains an exact byte
prefix of the final source. Evidence remains at `/tmp/miren-stage180-no-drop-new-control`;
the seven-path harness upkeep is frozen at `/tmp/miren-stage180-no-drop-upkeep-freeze.json`.
Independent semantic and effect reviews cover the corrected expectations and meaningful mutation.


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
manifest and runner remain unchanged: 155 cases in 53 families. This dedicated external-domain
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

## Stage210: issued scalar slice metadata

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

Known function tables support two independently typed integer arguments and an integer result.
The compiler's exact A/B/R types, safe nonvariadic Rust signature and full selected Instance
remain required. All targets are authenticated before feasibility; operands are evaluated once
in function/A/B order before branch cloning. Selected calls execute their actual bodies and
retain current returned Memory. Unary table behavior, construction and dispatch limits stay
unchanged. Arbitrary pointer inputs, unsupported signatures and Repeat-produced pointers stay
UNKNOWN. This adds no hardware model, trusted call or input assumption.

The focused checks pass 15 selected tests across ten commands, retaining 41 compiler assets in
four host/ARM O0/O2 profiles. Original helper assertions pass natively; actual helper and order
mutations fail. Ten fresh native controls execute one test each, with four original exits zero
and six mutation exits 101. Genuine retained dependency bodies prove; omitted bodies stay UNKNOWN,
including the literal constant-return helper whose actual body is required.

The proportional parent-release to owner-debug comparison covers 40 groups and 3,396 complete
proof pairs. It preserves 3,065 literal complete objects. There are 328 named changes: 320
status changes and eight omitted-body UNKNOWN results with a later MissingCompilerEvidence
frontier. Every baseline rich queried obligation/model remains an exact prefix, including
partial UNKNOWN queries: 4,980 baseline obligations become 5,228 current obligations. Three
query-free fold timeout differences satisfy the strict existing comparison predicate. The old
arity and selected global helper controls bind index one to the same refuted query/model and
record the actual selected helper body.

The fresh ROOT release executes the same 40 groups on frozen owner input paths and working
directories. It preserves 3,393 literal complete Proof objects and all 5,228 rich queried
obligations/models. Three differences satisfy the existing query-free fold timeout predicate;
every residual Proof field remains exact. Outcomes and numeric CLI exits remain unchanged.
No source-path rewriting, inherited extra-frame exception or UNKNOWN promotion is used.
ROOT debug is built and exercised by workspace tests; no separate debug CLI equality is claimed.

All 22 required ROOT checks pass, including 864 Rust tests across 197 outer Cargo target
summaries and 68 Python tests. Formatting, lint, release builds, dependency policy, examples,
documentation and manual hooks pass. Four fresh surveys cover 239 cases across 81 families,
each with 98 PROVED, 83 REFUTED and 58 UNKNOWN. The 236 parent entries remain intact. The new
Repeat control remains UNKNOWN with an Unclassified diagnostic; its expected category was
corrected without changing production code, assertions or the candidate analyzer.

The failed initial diagnostic check and stale foreign-caller capture remain separate historical
evidence. A fresh full check run validates the category correction; a guarded continuation
adopts 24 completed groups and freshly executes the remaining 16 with the intended caller.
No failed empty-output call is counted as a proof, and no old/new caller equivalence is claimed.

Evidence is under /tmp/miren-two-args-parent215, /tmp/miren-stage216-root-repeat-category,
/tmp/miren-stage216-root-full-checks-repeat-category,
/tmp/miren-stage216-root-repeat-category-survey and
/tmp/miren-stage216-root-release-integration. These are selected Rust capability measurements,
not full Rust parity or firmware coverage.

## Stage217: known integer function-pointer Repeat

The assignment planner accepts MIR Repeat of known function pointers only for the existing safe
integer table families. It authenticates the exact executing Instance, live cached Rc Body and
actual Assign/Rvalue/destination occurrence. Original source/destination types, literal extent,
Copy/Freeze and raw target arguments/signatures remain checked. Shared 512-work/depth-16 preflight
bounds the new route before its compiler queries, target normalization and materialization.
Operand evaluation occurs once, including zero length. A refused assignment publishes no
destination and does not restore a consumed Move. Existing 128-entry and 256-value construction
limits remain; symbolic table dispatch still refuses more than 16 targets. Known count128 has
cost129 within cap256, not a natural construction-budget exhaustion test. Count129 refuses.
Opaque targets, nested Choice and generic pointer-bearing product Repeat remain unsupported.

Selected calls execute their actual bodies with unchanged assertions and current returned Memory.
Four-profile own controls measure five Proved, two Refuted and four Unknown roots. Actual identity
XOR0-to-XOR1 and binary subtraction argument-order mutations produce new Refuted counterexamples
from baseline UNKNOWN, enter the selected helper and retain concrete queried models. They are
not preservation of a nonexistent baseline Refuted query. Six fresh native controls execute one
test each: two originals exit zero and four mutants exit101. Eight guarded genuine dependency
builds retain or omit MIR. Retained selected/constant callers enter their exact external bodies
and prove; omission reaches MissingCompilerEvidence UNKNOWN. Zero construction remains Proved
without executing the target and makes no body-availability claim. The global helper Repeat
control also proves honestly because its repeated first target is not the mutated second helper.

The committed216 release-to-owner comparison contains 60 groups and 3,472 complete selected pairs.
It preserves 3,390 literal FULL objects. Exactly 80 named changes comprise 36 UNKNOWN-to-Proved,
16 UNKNOWN-to-Refuted and 28 UNKNOWN-to-UNKNOWN later/refined frontiers. All 5,228 baseline rich
queried obligations/models remain exact prefixes, including UNKNOWN partial queries; current ALL
is 5,368. Changed proofs contain zero baseline queries. Every previously Refuted proof remains
literal FULL. Two query-free fold timeout differences satisfy the closed root/root-plus-closure
predicate with full residual equality. No third-frame exception, path rewriting or normalization
is accepted. Original stopped captures are preserved; their first nine objects are qualified
without recapture and only the remaining 59 groups are freshly executed.

Fresh ROOT release comparison reuses the exact frozen owner inputs and after reports.
Across 60 groups and 3,472 selected pairs, 3,470 complete Proof objects are literal FULL
and all 5,368 rich queried obligations/models match exactly. The two ARM fold timeout
contexts satisfy the same closed predicate with full residual equality. No owner baseline
is rerun, no paths are rewritten and no changed outcome is accepted in this comparison.

All 22 required ROOT checks pass: formatting, lint, workspace tests, Python tooling, release
builds, dependency policy, documentation, three examples including ARM release builds,
manual hooks and the four-profile capability survey. The outer workspace Cargo summaries
contain 868 passing Rust tests; the tooling suite passes 68 tests. A nested one-test native
summary in guarded_arithmetic is excluded from the outer total. Original and helper-mutated
Repeat cases, compiler controls and genuine dependency-body controls are also validated.

The fresh survey covers the unchanged 239-case, 81-family inventory with
99 Proved, 83 Refuted and 57 Unknown in each host/ARM O0/O2 profile.
Only the measured existing global Repeat expectation changes to Proved; the other 238 entries
stay exact. The existing two-argument foreign harness now requires the retained Repeat constant
body or the omitted body's exact Missing frontier. Its original caller assertions and separate
literal-constant controls remain unchanged. Counts are selected cases, not a Rust parity percentage.

Evidence is under /tmp/miren-known-repeat-parent216, /tmp/miren-stage217-root-full-checks and
/tmp/miren-stage217-root-release-comparison. Provisional parallel Float and integer-driver
refactors are not
part of this stage. Their later actual-parent reassociation and validation remain separate.

## Stage222: unary Bool and Char function tables

Known nongeneric safe Rust unary Bool-to-Bool and Char-to-Char tables preserve original compiler
signatures and execute actual available helper bodies. Callable and argument evaluation occur once
before branch dispatch. Exact result context, Unicode scalar validity and current returned Memory
remain required. Caller grammar and all-target body scans use separate 512-work/depth-16 bounds;
this is not a total whole-engine admission budget. Integer unary/binary and Repeat support is
unchanged. Float tables, references, mixed signatures and opaque target grants are excluded.

The original 239 capability cases and source prefix are unchanged; six new controls append P/R/U
for each primitive domain. All four owner profiles measure 245 cases across 83 families:
101 PROVED, 85 REFUTED and 59 UNKNOWN. The original dedicated Bool/Char assertions refute through
actual second-helper counterexamples; only their harness expectations change.

Six scoped commands pass with 19 actual tests. The separately sealed dataset has 48 groups and
1,656 Proof pairs: 1,570 literal FULL, 84 exact named changes and two query-free Resource contexts.
All 2,812 baseline queried obligations/models are exact prefixes of 2,848 current obligations,
including UNKNOWN partials. One extra wrapping_add frame belongs only to a fresh hash-bound host-O0
pair; the generic predicate stays strict. Its failed writer, 26 preserved groups and adopted pair
remain distinct from 21 fresh tail groups. Post-call guards precede numeric call-record persistence;
all recorded guards pass, and complete Proof comparison never injects or rewrites fields.

Eight genuine dependency archives compile with numeric exit0. Retained bodies prove and omitted
bodies reach MissingCompilerEvidence. Eight native runs each execute one test under timeout10:
originals pass at O0/O2; Bool/Char helper and table-order mutations fail unchanged claims.

Evidence is under /tmp/miren-primitive-tables-provisional and the independent source/data review
/tmp/miren-primitive-final-source-data-independent-review.md. Those measurements retain their
provisional Repeat/Float/driver association. /tmp/miren-primitive-parent221 records the separate
source-only composition onto committed Stage221, preserving helper tools and transport controls.
That owner checkpoint makes no current-parent analyzer or ROOT full-check claim.
The completed ROOT evidence is recorded separately below.

### Completed ROOT validation on committed Stage221

All 24 required commands pass. Actual logs contain 874 workspace Rust tests and
9 example Rust tests (883 outer Rust tests in total), plus 91 Python tests.
Four fresh ROOT surveys each measure 245 cases across 83 families:
101 PROVED, 85 REFUTED and 59 UNKNOWN.
The exact 947-source composition preserves both helper files, Float/driver behavior and transport
controls from its committed Stage221 parent. Documentation closure changes only four prose files.

Fresh ROOT release comparison covers 48 groups and 1,656 whole Proof objects, with
1,652 literal FULL and
4 precise query-free Resource contexts.
All 2,848 rich queried obligations/models match, including UNKNOWN partials. These are actual
ROOT release captures on frozen owner inputs; no separate ROOT debug CLI capture is claimed.
Exact resource-context reviews distinguish the owner's 30-second execution-budget trigger from
the ROOT symbolic step-limit trigger where observed. Both remain UNKNOWN with no query or model.
Recorded call-chain differences are reviewed with the precise reason fields and all other fields.
Each classification binds its fresh raw pair; no inherited or general resource waiver applies.
The eight owner dependency builds/native runs retain their original guarded association; ROOT
release comparison does not describe those rustc controls as freshly rerun native tests.

Owner source/data was independently reviewed before actual-parent composition. This stage's
source/index readiness combines that qualified review with explicit parent byte/prefix association;
it does not claim that the feature author independently reviewed their own implementation.

ROOT evidence: /tmp/miren-stage222-root-full-checks, /tmp/miren-stage222-root-survey and
/tmp/miren-stage222-root-release-comparison. Final closure/index records preserve the pre-prose
947-source capture freeze and separately authenticate the resulting source and staged bytes.

## Stage223: unary Float function tables

Known nongeneric safe Rust `fn(f32) -> f32` and `fn(f64) -> f64` tables preserve exact
compiler signatures and execute actual available selected bodies. Callable and argument
evaluation occur once before dispatch. Arguments and returns require the original width,
term context and a proven numeric/raw decoding relation under actual path conditions.
Shared dispatch now uses domain-neutral names; integer and Bool/Char behavior is retained.

Identity and negation preserve actual copied raw bits, including NaN payloads and signed zero.
Arithmetic NaNs retain existing payload/sign nondeterminism. Scalar decoding equality does
not authenticate an arbitrarily substituted NaN payload, issue mutable Float pair authority,
or admit Float Repeat, mixed widths, two arguments or opaque function bodies.

Eight cases append to the unchanged 245-case inventory and literal guest prefix.
All four owner profiles measure 253 cases across 85 families:
103 PROVED, 87 REFUTED and 63 UNKNOWN. The existing `float_unknown` assertion now refutes
through its actual identity helper: floating-point NaN is unequal to itself. Exact host
counterexample encodings are 0x7f800100; ARM captures use 0x7f800010. These are signaling
NaNs, not positive infinity. Both encodings fail the unchanged claim in native host tests.
Executing ARM model bits on the host does not establish native ARM execution.

The separately reviewed owner dataset contains 76 groups and 1,868 Proof pairs:
1,771 literal FULL, 96 exact named changes and one closed query-free Resource context.
All 3,164 baseline queried obligations/models are exact prefixes of 3,196 current ones,
including UNKNOWN partials. Named changes include supported outcomes and later unsupported
frontiers; a changed UNKNOWN frontier is not a successful proof. Eight fresh dependency
archives preserve retained-body and omitted-body controls. Eight native runs include two
passing originals and six failing helper mutations with unchanged assertions.
Four additional host runs reject the exact signaling-NaN counterexample patterns at O0/O2.
Actual Return controls cover 32 faults and eight restoration observations across four profiles.

Owner source/control and data reviews precede ROOT adoption. All 24 required ROOT commands
pass: formatting, lint, workspace/Python tests, release builds, dependency policy, documentation,
three examples including ARM releases, manual hooks and the capability survey.
Actual logs contain 878 workspace and 9 example Rust tests, totaling 887 outer Rust tests,
plus 91 Python tests. One nested native ticket test is excluded from the outer total.
Four fresh ROOT surveys each measure 253 cases across 85 families: 103 P, 87 R and 63 U.

Fresh ROOT release captures cover 76 groups and 1,868 whole Proof objects:
1867 literal FULL and 1 closed query-free Resource contexts.
All 3,196 rich queried obligations/models match, including UNKNOWN partials. No ROOT debug CLI
capture or replay of the owner's compiler/native controls is claimed. The unchanged generic
resource predicate remains limited to the recorded unbounded scalar fold; no broad waiver applies.

The 949-source adoption preserves 940 committed parent paths. Final documentation closure updates
five prose files, yielding 13 owned paths and 936 unchanged parent paths. Pre-prose captures keep
their immutable original association; final source/index records authenticate the prose delta.
Owner independent implementation/data review remains separate from ROOT consistency validation.

Evidence: /tmp/miren-float-tables-parent222, /tmp/miren-stage223-root-full-checks,
/tmp/miren-stage223-root-survey and /tmp/miren-stage223-root-release-comparison-ready.

## Stage224: unary Bool and Char function-pointer Repeat arrays

Known Repeat arrays now admit nongeneric safe Rust `fn(bool) -> bool` and `fn(char) -> char`
values with their exact original unary signatures. Array construction and dispatch retain the
existing bounds. The constructor evaluates its operand once, including for a zero count;
Move consumption is preserved. Calls execute actual available selected bodies and validate
returned values and Memory. Integer unary/binary Repeat admission remains unchanged.

Opaque, generic, wrong-signature and missing-body cases remain UNKNOWN. Float Repeat is still
unsupported. Six P/R/U cases append to the unchanged 253-case manifest and literal guest prefix.
All four fresh ROOT host/ARM O0/O2 surveys measure 259 cases across 87 families:
105 PROVED, 89 REFUTED and 65 UNKNOWN. These selected capabilities do not measure Rust parity.

The reviewed owner comparison contains 100 groups and 2,980 whole Proof pairs:
2,891 literal FULL, 88 exact named changes and one closed query-free Resource context.
All 5,140 baseline rich queried obligations/models are exact prefixes of 5,232 current ones,
including partial results in UNKNOWN cases. Named UNKNOWN changes do not establish a proof.
Sixty-four previously reviewed Repeat changes reproduce identical before/after Proof hashes and
refuted queries/models in fresh actual223 captures. The 24 expanded survey changes are also
bound to fresh current captures. Six native runs comprise two passing originals
and four failing actual helper mutations with unchanged assertions. Unicode boundaries and both
boolean states are covered by the native controls.

All 24 required ROOT commands pass, including formatting, lint, tests, release builds, dependency
policy, documentation, three examples with ARM releases, manual hooks and the capability survey.
Actual logs contain 881 workspace and nine example Rust tests: 890 outer Rust tests, plus
91 Python tests. One nested native ticket test is excluded from the outer total.

Fresh ROOT release captures cover 100 groups and 2,980 whole Proof objects:
2,979 literal FULL and one closed query-free Resource context. All 5,232 rich queried
obligations/models match, including UNKNOWN partials. Owner AFTER references are reused;
no baseline, native or archive replay is claimed. The existing generic Resource predicate remains
limited to the recorded unbounded scalar fold.

The 951-source adoption preserves 944 parent paths. Five final prose updates yield 11 owned
paths and 940 unchanged parent paths. Pre-prose captures keep their immutable association;
final source/index records authenticate the prose delta. Independent owner implementation/data
review remains separate from ROOT consistency validation.

Evidence: /tmp/miren-primitive-repeat-parent223/compatibility-completed,
/tmp/miren-stage224-root-full-checks, /tmp/miren-stage224-root-survey and
/tmp/miren-stage224-root-release-comparison-ready.
