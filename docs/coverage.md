# Coverage and evidence

Coverage means the Rust/MIR behavior the interpreter can analyze and the selected roots tested
against it. These tables do not imply that the interpreter or its explicit library models have
completed a soundness audit. Every result is tied to its compiler, target, flags and root domain.

## Inputs and values

The interpreter consumes rustc's typed MIR enums and compiler types/definitions directly.
Debug MIR strings are report details, not proof input. Language items identify compiler hooks;
broad Rust support also requires MIR operations, memory/ownership semantics, call resolution
and intrinsics. Complete language support still cannot guarantee a complete proof for every
program: resource limits and undecided queries remain separate sources of UNKNOWN.

| Feature | Current support | Boundary |
| --- | --- | --- |
| Integers and bool | Symbolic target-width values, signed comparisons, exact bit-vector operations and population counts | Raw memory access remains unsupported; Unicode char and integer pattern domains are modeled |
| Floating point | f32/f64 arithmetic, remainder, casts and IEEE bits | Wider formats; NaN bits |
| Bytes | Shared byte slices and fixed arrays; symbolic contents and valid-reference length bounds | Disjoint mutable byte-slice roots support guarded writes; general aliases remain unsupported |
| Primitive slices | Arbitrary input, checked reads/ranges | One shared root; no raw/write rights |
| Tuples | Nested values, shared references, field projections and numeric contract fields such as `value.1.0` | Destructured argument names with projected debug bindings are not contract bindings |
| Structs | Nested local/dependency structs, concrete generic fields and supported shared-reference fields | Unions, reference fields in mutable root pointees and unresolved generics remain unsupported |
| Fixed non-byte arrays | At most 256 input elements; large eligible subtrees use bounded lazy descriptors; scalar constants up to 256; composite constants and generated owned repeats up to 128 | Larger arrays fail as UNKNOWN |
| Array indexing | Symbolic bounded scalar and compatible fieldless enum input choices, start/end pattern offsets and uniquely determined composite indices | Ambiguous payload, mixed enum, tuple and struct choices remain UNKNOWN |
| Fixed-array equality | Primitive numeric equality and actual custom/nested comparisons; ordered short-circuit effects | At most 128 elements per array; general slice equality and inlined pointer-based comparisons remain gaps |
| Enums | Local/dependency inputs with symbolic tags/payloads; constructed variants and core Option/Result/ControlFlow | At most 256 fieldless or 64 payload input variants, all payloads modeled; enum/struct slices remain unsupported |
| Mutable storage | Disjoint mutable root references, projected writes, tracked aggregate/capture references and incoming-storage returns | Reference fields in root pointees, general aliasing and partial initialization remain UNKNOWN |
| Typed static stores | Certified UnsafeCell payload places accept supported typed moves, known callbacks and fresh constructed futures; stored references retain escape evidence | Shared reads remain opaque; no last-write, initialization-protocol or exclusivity facts; arbitrary writes, general unions, resumed futures and static future polling remain UNKNOWN |
| Interior mutation | Scalar Cell aliases/calls; distinct owned integer atomic allocations retain new/load/store/add/sub/swap/CAS history; fences check orderings | Root/static atomics and local atomics after trusted publication remain arbitrary per access; thin pointer loads/CAS support observed address relations; pointer histories, thread execution, RefCell and general pointer destinations remain gaps |
| Shared references | Read-only snapshots of supported values, including nested slice fields | Snapshot writes and general aliases remain unsupported; certified static stores have a separate model |
| Constants | Compiler-evaluated structs/tuples, active enum fields, bounded arrays/slices and immutable promoted/static references | Unions/MaybeUninit, interior mutable storage and raw pointers remain UNKNOWN |

Eager root input construction has at most 16 recursive levels and 512 values across all arguments.
References, aggregate containers and their children consume the budget. Large reference-free Freeze
struct/tuple/array subtrees with ordinary scalar leaves can instead use lazy descriptors. Repeated
types share descriptors while retaining independent values. A bounded eager-size estimate selects
compact eligible subtrees before other fields consume the budget. Cached descriptor heights must
fit each occurrence's nesting depth. The descriptor budget
shares the same 512-node total and 16-level limit, counting each descriptor/field edge once and each
lazy occurrence once. Accepted descriptors are shared across eager enum variants and separate
arguments; unaccepted candidates are discarded. Arrays retain their 256-element limit and a root
reserves at most 262,144 symbol slots. One level is materialized on access or mutation, leaving
nested aggregates lazy. Unsupported leaves are checked even when unused. Enums, chars, NonZero and
compiler patterns retain eager validity constraints, with lazy eligible children. Snapshots and
by-value copies retain initial values after writes. Induction does not yet accept lazy state. A
symbolic byte array or slice is one modeled value rather than one value per byte. Recursive
reference shapes and budget exhaustion return UNKNOWN before execution. Zero-length arrays do not
require modeling an element value. Struct fields remain arbitrary inputs; privacy and constructors
imply no hidden invariant. Enum selectors are constrained to the actual compiler discriminants,
including explicit signed values. A downcast must prove the active tag before reading its payload.
Reports expose `value.discriminant` and `value.variantN.field`; inactive payload bindings have no
runtime meaning. Input-construction failures name the specific field, variant or array element.

Ordinary membership can read lazily represented fixed arrays, including nested scalar arrays and
custom element records. Custom equality still executes its actual body; changing that body or an
index guard refutes the original proof. Host/ARM cases and native execution check these
interactions.
Owned repeats and iteration validate deferred fields within the 256-value limit; small no-drop
records can remain deferred, while oversized values and identity-bearing storage remain UNKNOWN.

Compiler-typed `u8` MIR repeats use a constant SMT array, independent of their byte count, with
target layout validation, bounds checks and byte updates. Host/ARM debug and optimized fixtures
check 4,096-byte repeats, symbolic guarded indices, updates and value/bounds mutations. Reference
snapshots cannot be mistaken for bytes: compiler element types select this representation.
Expanded nonbyte repeats retain their 128-element and 256-owned-value limits. Explicit byte
aggregates, evaluated constant tables and chunk operations retain their separate budgets.

Constants use rustc_const_eval to read compiler layouts, discriminants and initialized scalars.
The decoder inspects only the active variant; it does not invent values for inactive or
uninitialized fields. Immutable references require a pointee without interior mutation, and the
compiler's inspection context rejects mutable global reads. Constant decoding has eight recursive
levels and 256 values, including containers/references and each element. Evaluated arrays/slices
have at most 128 elements. Exhaustion is UNKNOWN.

## Execution and calls

Shared byte slice pointer aggregates retain their tracked source and metadata. The address
descriptor records the compiler pointee type before pointer casts erase it. Reads use live backing
storage and exact target-endian integer encodings and struct field offsets, with at most 128 bytes
and 16 levels. Every byte must belong to initialized supported fields; padding is rejected. Slice
bounds, allocation liveness, embedded reference graphs and frame escapes remain checked.
Host/ARM debug and optimized tests cover byte reads/copies, partial offsets, live updates, wrong
endianness and field/value mutations, with native layout checks. Numeric origins, padded storage,
mutable slices, raw subobjects, invalid bounds, dead storage and escaping locals remain UNKNOWN.
Float/enum/union byte encoding, larger views, arbitrary pointer loads/writes and induction over
these retained byte slices remain unsupported.

The compiler-identified `mem::zeroed` operation checks the actual zero-validity guard before
reconstructing initialized zero-bit values. Supported payloads are bool, char, primitive integers,
f32/f64, tuples, structs, compact compiler-sized byte arrays and at most 128 expanded array
elements.
Fieldless enums need a bounded direct-tag compiler layout and an actual zero discriminant; zero
does not imply the first declared variant. Reconstruction uses at most 16 levels and 256 values.
Invalid references, nonzero integers, patterns and enum tags refute the compiler panic guard.
Unions/MaybeUninit, pointer payloads, niche/payload enums and restricted integer reconstruction
remain UNKNOWN. Padding is not exposed as initialized readable bytes. Host/ARM debug and optimized
tests include value/type/tag mutations and independent native checks of valid zeroed values.

Shared Freeze snapshot reborrows retain the snapshot's projected value, including immutable static
and dependency static aggregates. They do not create a temporary frame-owned allocation. The
compiler shared-reference type and initial dereference identify this domain; tracked references
retain their original allocation and liveness rules. Host/ARM debug and optimized tests cover
whole/projected static returns, input projections and local mutation. Initializer/projection
mutations refute; dead/nested references, frame-owned escaping pointers and snapshot raw addresses
remain UNKNOWN. Snapshots still supply no allocation identity or mutable access.

Compiler-identified `size_of_val` accepts sized target layouts and modeled slice length metadata,
including nonbyte element strides. Trait-object and arbitrary raw unsized metadata remain UNKNOWN.
The compiler zero-initialization validity guard uses its actual validity query and records a
panic-safety obligation; passing the guard does not initialize storage or authorize payload reads.
Host/ARM debug and optimized cases cover valid and invalid layouts, subsequent panics and a
same-name function that must execute its own body.

Equal-sized initialized byte arrays can transmute to primitive integers or f32/f64 in the target's
native endian order. Float decoding preserves signed zero and NaN payload/sign bits. Boolean,
character, restricted integer and reference targets remain UNKNOWN. Byte-order and target-type
mutations check both the successful and unsupported boundaries; native execution independently
checks the supported bit encodings.

| Feature | Current support | Boundary |
| --- | --- | --- |
| Branches | Path-sensitive states; discard a branch only after an exact constant UNSAT decision or an unsat solver response | Ordinary mode does not merge states; induction forms per-block relations |
| Loops | Complete finite unrolling; opt-in Spacer induction over cyclic root MIR with integer/Boolean/tuple and fixed byte-array state | Induction includes available concrete callee MIR and checked contracts; typed stable references are supported; integer ranges, tagged enums and typed custom iterators are supported; byte-slice/scalar-array iterators and indexed references are supported; slice views, arbitrary non-byte slices, changing allocations, recursion and coroutines remain gaps; incomplete or undecided proofs are UNKNOWN |
| Generics and static traits | Substitute/normalize concrete arguments and resolve implementations | Unresolved generic roots, dynamic dispatch and unsupported shims are UNKNOWN |
| Dependencies | Cargo retains ordinary direct/transitive bodies at MIR level zero and executes concrete instances | Prebuilt sysroot/foreign bodies can remain missing; retained unsupported behavior is UNKNOWN |
| Closures and function items | Tracked captures, owned FnMut state and supported generic Fn/FnMut/FnOnce calls | Unsupported call shapes remain UNKNOWN |
| Known function pointers | Function-item coercions retain concrete instance/signature; selected targets, returns, local aggregates and Fn/FnMut/FnOnce adapters execute actual MIR with checked contracts/effects | At most 512 targets per root; arbitrary input calls, closure coercions, reification shims, numeric/signature-changing casts, missing bodies, arbitrary opaque static writes and induction remain UNKNOWN |
| Array map | Actual callback bodies in order, retaining capture state and reference-valued elements | At most 16 elements; callback destructors remain UNKNOWN |
| Array from_fn | Actual callbacks in ascending index order, retaining capture state and effects | At most 128 owned elements and 256 values; drops and identity-bearing results remain UNKNOWN |
| Owned array iteration | Compiler ArrayIntoIter, ordered cursors, count/last, predicates and fold/rfold callbacks | At most 128 owned elements and 256 values; owned Cell/atomic identities, user destructors, clone and views remain UNKNOWN |
| Iterator fold/sum | Function items, closures and known safe Rust pointer callbacks execute actual fold/rfold bodies, preserving accumulator, capture state and effects; sum uses ordinary MIR | Unfinished folds, callback drops and unsupported element/call shapes remain UNKNOWN |
| Evaluated closure constants | Typed noncapturing, zero-field, zero-sized closure values | Captured constants, including zero-sized captures, remain UNKNOWN |
| Error formatting setup | Shared concrete core Debug coercions retain opaque reference identity; Result unwrap/expect variants execute branch MIR and recognize the pinned failure helper as a panic boundary | Calling formatters, mutable/other trait coercions, unknown trait-object inputs, vtable/address operations and induction remain UNKNOWN |
| Integer operations | Arithmetic, overflow flags, min/max, saturating add/subtract, zero counts, byte/bit reversal, comparisons, casts, bit operations and shifts | Optional overflow checks depend on build settings; unsafe nonzero count intrinsics remain unsupported |
| Float operations | Numeric IEEE operations, exact input/from_bits encodings, moves, negation, abs, clamp and to_bits | Arithmetic NaN encodings allow every payload/sign, including signaling NaNs; counterexamples may not replay |
| Drop | Concrete synchronous rustc drop glue executes user destructors and ordered aggregate field drops | Pointer-based array/slice glue, unsupported coroutine drops, unwinding and induction drops remain UNKNOWN |
| MIR assume | Prove its predicate as a validity obligation | Never turn it into an unchecked assumption |

The default execution budget is 8,192 steps per root, including callees, iterator model steps and
infeasible
queued branches. The default call depth is 16 active frames; recursion can finish within the same
limits.
By default, queries have at most 200,000 bytes, a five-second solver timeout and a six-second host
deadline per
default solver request. Exceeding a limit returns UNKNOWN. The default root budget is 30 seconds.
Root-local solver sessions retain common assertions with push/pop and reset incompatible declaration
namespaces. Exact-query caching, Boolean/bit-vector folding, exact complementary integer guards
and a full-Instance MIR cache reduce repeated work. Floating-point ordering keeps its NaN behavior.
None reuses function proofs or unchecked summaries; full standalone queries
remain in reports.

Mixed floating-point paths can discharge an integer/Boolean safety check with a stronger
non-floating query. Only UNSAT is accepted; SAT/UNKNOWN use the original full query, including all
floating constraints, and counterexample models come from that full query. Host/ARM and native
cases cover guarded array accesses, integer facts that require a float constraint, actual linked
counterexamples, remainder operations and an off-by-one mutation. Feasibility checks keep the full
path, and their failing queries now appear in UNKNOWN reports. No alternate floating-point tactic
or repeated UNKNOWN retry is enabled.

Explicit core models implement byte lengths/ranges/copies, shared slice-to-array conversion,
lossless integer conversion, endian decoding, fixed-array map and opaque formatting arguments from
static strings, plus compiler-identified float absolute value and min/max. They check their
applicable bounds/length conditions and are recorded per root. They are trusted translation code,
not proofs of the modeled library bodies. Dynamic formatting, arbitrary pointer operations and some
constant shapes remain unsupported.

Primitive slice membership identifies core's inherent slice method or its exact SliceContains
trait implementation and checks the instantiated signature and primitive element type. The model
computes membership over fixed scalar elements or byte storage with a proven length at most 128.
Shared byte-pattern Subslice projections use checked region bounds and shifted array storage.
Byte array selects are guarded by the actual length, including empty and shifted views; longer or
unbounded byte slices remain UNKNOWN. Floating equality preserves NaN non-reflexivity and equality
of signed zeros. Fixed custom element membership calls resolved PartialEq MIR in slice order,
preserving comparison panics, interior effects and short-circuiting. Host/ARM tests include
positive, negative, unknown and source-mutated cases, plus native replay. Inlining that erases the
supported call boundary remains a limitation, including inlined custom comparisons that expose
unsupported interior-storage or panic-formatting internals. Mutable Subslice addresses remain
unsupported.

Fixed-array equality and inequality recognize core's PartialEq implementations and its exact
SpecArrayEq trait, with shared-reference array signatures and matching fixed lengths. Primitive
elements use numeric equality, including char, NaN non-reflexivity and signed-zero equality.
Custom and nested elements call actual resolved `ne` MIR, matching the pinned core slice comparator;
the model preserves receiver order, call checks, panics, interior effects and early termination.
Arrays with no elements call no comparison body. Comparisons have at most 128 elements per array;
unsupported callees and exhausted execution/solver budgets remain UNKNOWN. Host/ARM debug and
optimized cases cover guarded comparisons, byte arrays at the limit, nested and derived records,
cross-type comparisons, overridden inequality, reachable and skipped panics, counterfeit method
names and the budget boundary. Three failing mutations are refuted and replayed natively.
Ordinary float remainder inside an element comparison uses the same numeric model as direct MIR.
This comparison model currently applies to ordinary execution.

## Contracts and root selection

`requires` predicates constrain selected root inputs and must be proved at every reachable call.
`ensures` predicates are checked at actual returns, with parameter names bound to entry values.
Supported predicates include comparisons, boolean operations, named/numeric fields, array/slice
lengths, constant non-byte array indices, integer/float casts and exhaustive unguarded Option
matches. Symbolic Option arms must be boolean; float literals are checked for type and range.
Arithmetic, dynamic indexing, arbitrary predicate calls and Result contract matches remain gaps.

Cargo can select exact or crate-qualified roots. Unselected callees can still be interpreted
with particular symbolic arguments; that does not independently verify their full input domains.
Schema version 8 separates root outcome counts, unselected bodies, interpreted instance counts
and grouped unknown reasons. An empty inventory or zero selected roots establishes no safety.

## Concrete evidence

| Case | Positive evidence | Negative or incomplete evidence |
| --- | --- | --- |
| Guarded scalar/slice operations | Universal symbolic proofs; exhaustive replay of all u8 addition pairs | Off-by-one, overflow, division, stale-guard and call-bound failures |
| CAN frames | Six unchanged methods and two payload-preservation harnesses on host/ARM | Invalid lengths/IDs, relaxed FD rules and broken byte copies are refuted |
| Bus validator | Two symbolic three-device families through 44-block nested-loop MIR on host/ARM | Five invalid families are refuted/replayed; arbitrary input slices remain UNKNOWN |
| DR16 parser | Unchanged 42-block body, exact length and decoded bounds on host/ARM without entry assumptions | Bad index and channel mask are refuted; 4,608 sample frames use independent formulas |
| Generic/dependency calls | Concrete bodies/static traits; non-inline transitive dependencies on host/ARM, with configuration and encoded flags preserved | Dependency precondition violations and overflow refute; opt-out calls and unsupported retained operations stay UNKNOWN |
| Callbacks and aggregate borrows | Struct/tuple/Option references, returned captures, owned FnMut state, Zip/Flatten and ordered callback effects on host/ARM | Wrong field/state assertions and swapped-field mutations refute; unresolved root aliases remain UNKNOWN |
| Generated arrays | Synthetic ticket/parcel/label cases, function items, zero length, 18/128-element arrays and exact value-budget boundary on host/ARM | Bad callback assertions, overflows, call bounds and label mutations refute; drops, storage identities and larger shapes remain UNKNOWN |
| Iterator audit regressions | Mixed forward/reverse skips, usize::MAX exhaustion, zero-sized elements, skipped byte storage and shared Cell aliases on host/ARM; 1,792 native cases | Wrong alias, false reset-state claims and exhaustion mutations refute; unsupported views remain UNKNOWN |
| Aggregate inputs | Nested/generic structs, tuples, shared byte fields and fixed struct arrays on host/ARM | An off-by-one nested call guard is refuted; mutable/recursive/oversized shapes are UNKNOWN |
| Floats | Host/ARM numeric, storage and remainder controls | NaN bits may overapproximate targets |
| Symbolic enums | Signed tags, Option/Result payloads, foreign nested inputs and entry snapshots on host/ARM | Variant/payload/off-by-one call mutations are refuted; unsupported payloads stay UNKNOWN |
| Array patterns | Fixed float arrays and guarded byte slices with start/end projections on host/ARM | An unequal-endpoint assertion is refuted; float slices remain UNKNOWN |
| Aggregate constants | Option::as_ref, niche layouts, signed enum tags, nested fields and immutable storage on host/ARM | Wrong payloads/guards and a mutated constant index refute; unions, mutable storage, unsupported transmutes and oversized shapes remain UNKNOWN |
| Cargo selection | Selected roots can prove beside unsupported workspace code | Ambiguous names select all matches; unknown/refuted/missing roots fail |

Mutation regressions change source guards, indices, masks and copies to ensure the corresponding
proof tests reject them. Separate runtime tests cover confirmed failures and formulas. These
checks provide practical evidence, not a formal verification of the translator or whole firmware.

Mutable-storage tests cover host/ARM writes through callees, branch isolation, byte-slice updates,
entry/final-state postconditions and rejected aliases/returns. A vendored PID excerpt preserves
its original bodies: reset proves with a final-state assertion, a configured update with concrete
inputs proves, invalid limits refute, and a reset-write mutation refutes. Universal symbolic PID
update exploration remains expensive; the root execution budget bounds that work.

Interior-mutation tests prove shared Cell writes through aliases, branches and array-map callbacks.
Atomic tests prove wrapping counters and guarded orderings, refute invalid orderings/unchecked
increments/history assumptions, and keep RefCell conflicts unknown on host/ARM. The fleet's
unchanged validate::Site::fail and total also prove through ordinary ARM Cargo verification.

External sidecars check unchanged body/caller contracts without a source dependency. Host/ARM
tests cover formatter-boundary preconditions, arbitrary Result failures, tracked effects and
strict rejection of conditional proofs. Additional tests cover unavailable dependency bodies
through Cargo, generic instance selection, invalid/stale configuration, inconsistent assumptions
and unsupported reference returns. Trusted summaries remain explicit assumptions, excluded from
ordinary proof counts; they expand caller analysis without establishing the skipped body's safety.
An external checked postcondition also proves final_state.integral == 0.0 for the unchanged fleet
controller::Pid::reset through ARM Cargo verification, without adding a firmware dependency.

## Population counts and floating-point clamp

The compiler-identified ctpop intrinsic counts individual bits exactly and returns u32, including
for signed operands and target-width usize/isize. The model does not recognize user methods by
name. Host/ARM tests prove width bounds, masked counts and byte count/complement relationships;
wrong bounds and a tightened mask bound refute. Unsupported pointer inputs remain UNKNOWN.

Primitive core f32/f64 clamp checks min <= max before producing a value. Reversed bounds and NaN
bounds refute; a NaN input remains NaN and equality preserves the input's signed zero. Tests cover
symbolic ordered bounds, infinities, signed-zero observations and a reversed-guard mutation.
Float storage observations preserve selected input/clamp bits. These models follow the pinned
compiler's core
intrinsic declaration and primitive clamp implementation; they do not trust application summaries.

## Owned aggregate repeats

Small repeated tuples, structs, enum values and nested arrays preserve their contents and variant
tags. Each copy owns its data: changing a field or byte in one copy does not change another copy.
Generated repeats have at most 128 elements and a 256-value retained clone budget. Operand
validation
counts aggregate containers and their children. Non-byte root arrays allow 256 elements with eager
values or bounded lazy
descriptors; evaluated scalar constants permit 256 elements and composite constants 128. Byte arrays
as inputs retain their 128-byte limit.
Tracked references, Cell/atomic identities and mutable views are excluded from repeat cloning.

Host/ARM tests prove six-by-six float matrix initialization, tuple/struct/enum copies, 18-element
scalar/enum arrays, 128-element generated arrays and byte writes inside nested tuples. An incorrect
copy assertion and a mutation that writes the wrong matrix row refute. Ambiguous composite indices,
excessive shapes and operations on repeated interior mutable storage remain UNKNOWN. Root input
budgets and general aliasing limits are unchanged.

## Shared slice iteration

Shared slice iterator identity comes from the compiler's SliceIter diagnostic item. The model
tracks a source and front/back cursors, advances typed iterator storage and yields original
references where allocation identity is available. Byte snapshots yield their exact symbolic
contents. Forward/reverse next, symbolic nth/nth_back, length/count/size_hint and independent
cloned cursors are modeled. Counts and skips use the cursor directly, without unrolling discarded
items. Generic enumerate/copied/rev adapters execute actual core MIR.

all/any execute concrete callback bodies in element order and preserve memory effects, including
Cell updates. A deciding callback stops traversal immediately and leaves the remaining cursor
intact. Iteration consumes the existing step/time budget; unfinished paths remain UNKNOWN.
Mutable iteration uses the same tracked storage machinery; iterator slice views remain unsupported.

Host/ARM compiler tests cover integers, floats, units, tuples, bounded symbolic byte slices,
clones, mixed-direction traversal, huge skip counts, short-circuiting and shared Cell
identities. Wrong element assertions and reachable callback panics refute. Order/short-circuit
mutations refute, and 4,096 host cases agree with direct array formulas. Unbounded iterator
loops and unsupported views remain UNKNOWN. Compiler-layout-derived singleton tags let optimized
residual enums finish without inventing initialized payloads; ordinary unavailable storage reads
still fail.

## Mutable slice iteration

Mutable iterators retain a writable source reference and yield projections into that allocation.
Forward/reverse traversal and skips share the cursor machinery with immutable iterators. Local
byte-array views are attached to typed storage; subsequent byte copies update that same storage.
Mutable enumerate and IntoIterator adapters preserve the source reference, with checked counter
increments under the active overflow configuration. Unwrapping a known Some mutable payload
preserves its tracked reference. These explicit models are recorded separately from body calls.

Host/ARM tests prove disjoint element writes, final-array postconditions, tuple updates, bounded
byte-slice clearing, byte-prefix writes followed by copies, mutable predicate short-circuiting
and six-by-six diagonal matrix initialization. A wrong-column mutation and incorrect alias or
overflow assertions refute. Two sets of 4,096 host cases compare reads and writes with direct
formulas. Incoming-storage iterator returns and tracked references inside aggregates/captures are
supported. Ambiguous composite writes, general raw pointers and unresolved root aliases remain
UNKNOWN.

Borrowed fixed-array/slice IntoIterator factories also use these cursor models; owned arrays have
a compiler-identified model over the same cursor representation. Compiler-identified primitive
finiteness is exact IEEE NaN/infinity
classification. Host/ARM tests compare f64 classification with abs < infinity and refute an
unconstrained finiteness assertion. This avoids spending MIR steps on the helper implementation
inside each callback while preserving the predicate's meaning.

Owned arrays can move tracked shared/mutable references and aggregates containing them. Cursor
steps preserve allocation/projection identity instead of snapshotting pointee values. Shared Cell
aliases observe writes through earlier yielded references; mutable elements update caller storage.
Reference liveness and frame-escape checks still apply. Owned Cell/atomic elements, element
Clone/views/destructors and symbolic skips between different reference identities stay UNKNOWN.
Repeating identity-bearing values remains unsupported.

Owned array cursors preserve value order, forward/reverse skips, count/last, checked predicate
callbacks and fold/rfold. Callback bodies execute rather than supplying assumed results. Shared
slice folds and ordinary sum bodies use the same callback execution. Consuming count/last/fold
through a mutable iterator reference updates that original cursor; by_ref and IntoIterator
passthrough preserve its reference. Owned iterator clone stays unknown because element Clone
implementations may execute user code.

Harmless owned iterator drop glue is recognized only when elements need no drop and every
drop-requiring field of a wrapper is itself harmless. Other ordinary drops execute rustc's concrete
glue, including a wrapper's actual user destructor. Unsupported glue remains UNKNOWN. Evaluated
noncapturing closures require compiler-confirmed empty upvars, zero fields
and zero-sized layout. Captured constant environments are not fabricated, even when zero-sized.

## Aggregate references and callback state

Tracked references retain allocation IDs and field/index projections inside tuples, structs,
enums and closures. Returned values can refer to caller storage; the reference graph rejects
callee-local or dead allocations escaping directly or through caller storage. Core Zip/Flatten
adapters can execute actual MIR over supported mutable iterators without assumed summaries.
One tracked environment per modeled callback invocation preserves owned FnMut fields and writes
through captures. Array map retains reference-valued input elements. Completed temporary callback
environments are retired; unsupported destructors do not become harmless by entering a model.

The synthetic aggregate fixture checks 19 roots on host/ARM: 14 prove, three refute and two remain
unknown. Native execution checks 700 bounded calls plus stateful callback examples and negative
panic catches. Swapping the mutable struct fields refutes the unchanged assertion. Three memory
regressions reject dead references and a callee borrow hidden in caller storage, while preserving
nested incoming references. These checks do not cover every alias/lifetime rule.

## Floating-point storage

Inputs, evaluated constants and from_bits preserve every IEEE encoding, including quiet/signaling
NaN signs and payloads. Moves, selected array elements, negation, abs and clamp retain the selected
encoding. to_bits and same-width integer/float transmutes expose it. Numeric arithmetic still uses
IEEE nearest-even operations; its stored result is constrained to that numeric value. NaN results
conservatively allow all payloads/signs, including signaling encodings. Repeated reads of one
stored result use the same bits, while a bit-level NaN counterexample may not replay on the target.

The storage fixture checks 17 roots on host/ARM: 13 prove and four refute.
A changed sign mask refutes. Native checks include signed zero, subnormals, infinities and both
kinds of NaN for f32/f64, plus 1,024 integer-cast/arithmetic inputs. Checked sidecars force actual
core to_bits/from_bits bodies through typed transmutes and retain the same outcomes without
library summaries. Ordinary remainder is supported; wider floating-point formats remain unsupported.

Compiler-identified binary32/binary64 floor, ceil, trunc, round, round_ties_even, sqrt and fused
multiply-add intrinsics now have typed IEEE models. Directional rounding uses RTN, RTP and RTZ;
round uses nearest ties away from zero, while round_ties_even, sqrt and mul_add use RNE. Returned
numeric results retain stable storage encodings with the existing conservative NaN payload rules.
This applies to the pinned compiler's experimental no_std core_float_math wrappers. It does not
replace user functions with matching names or summarize a dependency's math implementation.

The intrinsic fixture checks 14 roots on host/ARM: nine prove and five refute.
Cases cover positive/negative rounding ties, signed zeros, infinities, NaNs, subnormals,
invalid square roots and a fused result differing from separate multiply/add. Native tests replay
the positive cases and all five failing mutations. Floating-point induction remains unsupported;
adding ordinary intrinsic models does not extend the loop-state encoding.

## Larger evaluated tables and numeric-only float exploration

Evaluated constants allow 256 scalar or 128 composite array elements, a 2,048-visit total and
sixteen-level depth budget. Symbolic compatible scalar selection needs a bounds proof, while constant
indices select directly. Composite indices still require uniqueness. Host/ARM tests retain unknown results
for oversized, ambiguous, uninitialized and interior-mutable cases.

Deferred float encoding relations avoid translating unused storage observations into numeric-only
queries. Exact symbol dependency closure includes the required relations for computed, returned,
transformed and selected bit roundtrips. Wrong roundtrip assertions refute; native IEEE cases and
copy-correlation regressions check the retained encodings. Arithmetic NaN payload overapproximation
remains unchanged.

Opaque static string transport now supports guarded Option expect and nested shared arguments.
Unguarded expect calls refute; changed guards also refute. String length/content operations and
mutable string-reference storage remain UNKNOWN.

Fixed-array selection supports same-type fieldless enum input choices with identical complete
variant metadata and discriminant representation. Signed sparse tags retain their exact bits.
Actual compiler array bounds are still checked; payloads and mixed inventories do not merge.
Host/ARM O0/O2 tests cover selected return values, casts and matches, wrong claims, unguarded
out-of-bounds indexing and UNKNOWN payload/mixed choices. Changing the actual selected index
refutes the proof and fails native execution.

NonZero getters validate compiler identity before applying the scalar model. Actual free and trait
get lookalikes retain their return values and panics, including a dependency getter without MIR
remaining UNKNOWN. Host/ARM O0/O2 regressions cover unsigned, signed and pointer-width core getters,
wrong claims and actual-body mutations that fail native execution. Recognition does not add a
NonZero constructor or new assumptions in that getter model.

Actual core NonZero constructor bodies now execute their primitive integer to `Option<NonZero<T>>`
transmute when compiler types, scalar validity ranges, sizes, alignments and the exact zero-only
niche agree. The semantic discriminant and payload retain the original input expression, so None
remains reachable at zero and Some access requires a proven variant check. Host/ARM O0/O2 cases
cover all primitive integer families, zero, negative values and unwrap failures. Different integer
types, wrappers, pointer/bool niches and an unchecked Some projection remain UNKNOWN. A mutated
None-branch claim refutes and fails native execution. Missing constructor bodies remain UNKNOWN.

Reverse NonZero-to-primitive transmutes reuse the exact compiler inner-type/scalar certificate and
retain original bits only when source validity is proved. Compiler-identified core ctlz_nonzero
uses the established leading-zero expression only when zero is proved infeasible. MIR
ShlUnchecked checks the original shift count against the left width before any cast or masking;
zero counts and values are valid, while unproved/out-of-range counts remain UNKNOWN. Actual
checked_pow now proves the guarded-power fixture. Unchecked power still reaches missing core
overflow-panic MIR and stays UNKNOWN. Host/ARM O0/O2 cases cover every primitive integer family,
negative values, exact bit counts, bounds, invalid source/projection controls and lookalike bodies.
Reverse-transmute and power-claim mutations refute and fail native execution. No fleet gain has
been demonstrated for this extension.

Repeated eligible enum input shapes can share bounded descriptors rather than eagerly expanding
every array occurrence. Compiler variant identity, field names, exact signed tags and Option
metadata are retained. Selector mapping covers every actual variant and prevents invalid tags;
individual variant payloads and array occurrences have independent symbol slots. Direct large enum
roots use an already reserved variant wrapper slot for the selector, separate from the Boolean
context seed. Existing budgets and unsupported payload boundaries remain unchanged.

## Mutable byte regions and valid bounded roots

Fixed byte-view updates permit larger destination allocations when the generated update contains
at most 128 array stores. A symbolic length retains the conservative full-capacity update bound.
Exact same-term modular add/sub cancellation preserves fixed lengths with symbolic offsets;
Rust overflow, region bounds and equal copy lengths remain checked. Truly variable lengths retain
the conservative store bound. The separate typed-encoding and chunk-model budgets are unchanged.
Host/ARM O0/O2 controls
cover 136-, 256- and 4,096-byte backing storage, nested views, guarded offsets, empty end ranges,
exact-budget copies, preserved neighbors, refuted value/bounds failures and unsupported oversized,
symbolic-length or retired-storage writes. A copy-source mutation fails native execution and proof.

Local mutable byte arrays retain allocation identities through helpers, returned borrows and
closure captures. Prefixes and finite `as_chunks_mut` views share the original allocation; chunk
and remainder writes preserve disjoint regions. The exact core model checks nonzero chunk width
and a fixed length within 128 bytes. Symbolic chunk lengths, larger views and unresolved root
aliasing remain UNKNOWN. Literal byte indices in contracts require a fixed modeled length.

Function-item callbacks resolve concrete trait implementations before requesting their MIR.
Missing-body diagnostics distinguish foreign declarations from omitted prebuilt core bodies.
The existing Cargo `-Zbuild-std=core` path captures rebuilt core MIR, but unsupported operations
inside those bodies still remain UNKNOWN. Primitive integer endian encoding and decoding use
exact compiler identities, signatures and byte order.

Root arrays allow 256 non-byte elements with eager values or bounded lazy descriptors, and enums
allow 256 fieldless or 64 payload variants. Integer compiler patterns and Unicode char validity
constrain the input domain.
The exact core NonZero getter reads the modeled scalar; other struct invariants are not inferred.
Exhausted budgets and unresolved input types remain UNKNOWN.

Original host/ARM cases check mutable region writes, returned views, caller bounds, callback
dispatch, endian boundaries and valid scalar domains. Native tests and failing mutations check
these effects independently. Byte-source sharing bounds expression growth without increasing
the query-size cap, and standalone SMT scripts remain available in reports.

Guarded unchecked integer MIR arithmetic generates validity obligations before continuing.
Compiler runtime-check operands follow the analyzed session's UB/overflow flags, and the actual
cold-path marker has no runtime effects. Original integer-boundary and host/ARM flag regressions
check these paths. Unsupported pointer continuations remain UNKNOWN.

Scalar static-value optimization hints produce independent Boolean choices, so both branches
must be safe. Unused contract name maps do not block dependency execution; declared predicates
and argument aliases still validate. Integer power currently progresses to a niche-layout
transmute, which remains unsupported.


## Unbounded loop induction

The opt-in induction fixtures prove endless wrapping counters, tuple state, a register parser with
persistent byte history and a loop with an exit on host and ARM no_std. A host binary main proves
without running it. These are actual typed MIR translations, following the earlier handwritten Horn
spike. The packet is an arbitrary fixed root input; renewing hardware reads requires call models.
Changed masks, cursors and a failure after 12,000 iterations never pass. Native tests replay the
mutated panics. Entry requires restrict the initial domain, callee requires are checked at call
sites, and root/callee ensures are checked at actual returns. Inconsistent entry domains and
unsupported predicates remain UNKNOWN.

Host/ARM call tests cover concrete generic instances, retained dependency bodies, an entry
delegating to an endless helper, callee loops, restored caller state and original/final
owned-byte snapshots. Changed wraps, violated call domains, false postconditions, recursion and
unsupported inputs never pass. Existing 256- and 1,024-iteration scalar loops prove inductively.
Typed memory tests cover persistent structs, static field aliases, shared array roots, mutable
byte-array roots and callee writes. Separate contract snapshots retain entry values. Off-by-one
writes, bad wraps and false snapshot contracts never pass; changing aliases and interior mutation
remain UNKNOWN. Integer range loops, tagged enum state and a custom iterator's actual body also
prove on host/ARM.
Tests cover signed endpoints, maximum endpoints, early breaks and borrowed-array writes. Mutated
ends, false custom-iterator claims and a late range panic never pass. Slice tests prove
shared/mutable
byte iteration, retained references, mixed forward/backward steps, skips, cursor cloning, borrowed
count exhaustion, fixed integer/Boolean arrays and indexed helper snapshots. Mutated assertions,
writes and bounds never pass. Native cases and small complete unrollings cross-check the encoding.
Slice views, arbitrary non-byte slices and adapters still remain unsupported. A supported
12,000-element range can exhaust invariant inference; it is not guaranteed faster than unrolling. A
relational decrement/count query remains UNKNOWN after a Z3
crash. A preprocessing experiment that claimed a native-replayed late panic was safe was
rejected and is not enabled.

Typed Horn tests check relation arity/sorts/context, exact printer budgets and a transition
mutation. Solver tests distinguish SAT inductive models from SAT counterexamples and check
resets between Horn and ordinary queries. Raw reports store inductive models separately in
invariants. Horn UNSAT and timeouts remain UNKNOWN pending Rust counterexample replay. See [loop
execution and limits](proofs.md#loops-and-limits) for the supported operations and budgets.

Both CLIs configure steps, call depth, query bytes, root seconds and solver milliseconds.
Reports retain the selected analysis_limits; old reports do not invent historical settings.
Host/ARM tests cover low-budget UNKNOWN results, completed bounded work at larger limits,
late failures and a mutated deep callee. Horn queries carry the selected timeout and byte cap;
a stalled persistent session is killed under its configured deadline. Input and model shape
limits remain independent. See [analysis budgets](usage.md#analysis-budgets).

Ordinary slice equality and array/slice comparisons now model the exact core PartialEq boundary.
Length mismatches return without comparing elements. Equal-length paths need a proven bound of
128; primitive comparisons guard each byte select by the real length, and fixed custom elements
execute ordered resolved `ne` calls. Empty comparisons, unequal unbounded lengths, numeric edge
cases, prefix views and custom effects have host/ARM debug and optimized tests. Mutations refute
and panic during native replay. Arbitrary unbounded equality, general range indexing and induction
comparison translation remain gaps. Increasing execution budgets does not remove model shape caps.

Constructed async futures execute optimized poll MIR with compiler-provided saved-local layouts.
Variant fields that share a saved local use one logical slot. Captures, mutable writes, nested
futures, suspension/resumption and completion-state checks have host/ARM debug and optimized tests.
Available cancellation drop glue is interpreted, including destructor effects and panics. Saved
locals are explicitly uninitialized until assigned; unsupported reads never become symbolic data.
The state model allows at most 64 variants and 512 capture/saved-local slots.

Core Context is an opaque valid argument; its waker/extension fields cannot be observed. The exact
compiler Context/NonNull reference adapter and core Pin<&mut T> mutable dereference preserve tracked
storage. Compiler-identified noop-waker/context constructors let a standalone binary fixture prove
from main through two polls; a bad resumed index refutes and panics natively. Construction-only
proofs cover the async factory, not deferred execution. Unbounded polling, arbitrary coroutine root
states, waker operations and executor internals remain incomplete.

Explicit `--async-entry` selectors construct fresh concrete factory returns from supported inputs
and poll each feasible Pending state until Ready. Shared execution limits prevent forever-Pending
paths from proving. Executor input handles, startup history, coroutine induction, cancellation,
returned-output drops and native replay are not supplied by this entry mode. Initialization roots
remain separately selectable and report their own result.

Integer-derived thin pointer handles support address casts, address exposure, equality and null
checks. Numeric constants without allocation provenance preserve their exact target-width address.
Copied handles and aggregate storage retain that address. Core pointer-atomic construction checks
normalized, single-field core wrappers with zero field offset and pointer-sized representation;
operations on pointer-atomic memory remain unsupported. Constructor bodies still execute and their
panics remain checked. This is address-value translation only: arbitrary pointer inputs,
reference-derived pointers, allocation provenance, metadata, arithmetic and dereferences remain
UNKNOWN. Host/ARM debug and optimized fixtures include positive, negative, unknown and mutated
cases, with native replay of address operations and failing claims.

Lifetime-only mutable-reference casts keep their tracked allocation and projection when the erased
MIR reference types match. Typed writes and frame-escape checks still apply; no static allocation
or general lifetime guarantee is introduced. Explicit trusted returns_alias clauses can preserve
one named mutable-reference argument with the same pointee type and the claimed memory effects.
Assumptions are visible on successful, refuted and unknown roots. Host/ARM synthetic MIR fixtures
check scoped writes, rejected casts, dead storage and escaping borrows, with native mutation replay.
General access to interior-mutable byte storage through raw pointers remains unsupported.

Opaque views now support recovering compiler-known typed static storage from UnsafeCell byte
carriers. Whole static provenance, initializer transmute origins, transparent UnsafeCell layouts,
size, alignment and field offsets are checked. Pointer casts and shared reference restoration keep
the storage identity; unrelated same-size types remain UNKNOWN. Initializer bytes are not runtime
state. Supported integer atomic fields use their existing conservative model; general payload
reads/writes, MaybeUninit reads and induction over this storage remain gaps. Shared fixed arrays
support slice coercions and ordered element references for at most 128 elements, with compiler
strides and distinct storage descriptors. Slice iterator `find_map` executes actual callback MIR,
including side effects and short circuiting. Mutable opaque element storage and ambiguous symbolic
composite indices remain UNKNOWN. Address checks use symbolic non-null aligned bases without
enabling arbitrary memory access.

Static storage-origin reconstruction checks initializer MIR availability before querying rustc.
The pinned compiler omits dependency static initializer MIR even with retained function bodies.
Retained builds emit artifact-bound origin metadata from a compiler pass that checks construction
and emits its own metadata artifact. A bounded typed construction graph supports declared origins
and narrow `u32` return transmutes, including core atomic construction. Newly constructed outer
aggregates keep their declared type; direct constructor returns retain their primitive origin.
Compiler types and layouts are checked without parsing serialized type names. Missing, stale,
corrupt or unsupported evidence remains UNKNOWN. Host/ARM debug and optimized tests cover ordinary
atomic interference, conditional startup values, source/evidence mutations and same-pass artifact
emission. Supported immutable constant reads and local origin reconstruction remain available.

Tracked thin raw addresses support MIR `Offset` within the exact compiler-sized reference extent.
Array-to-element casts retain their array extent; signed scaling and cursor bounds are checked,
including one-past formation and reverse offsets. Host/ARM debug and optimized fixtures check
address relationships, later panics, validity refutations and stride/bounds mutations. Native tests
cross-check valid address relationships and the wrong-stride assertion. Numeric offsets, zero-sized
strides, wrapping arithmetic, untracked reference snapshots, raw dereferences and frame escapes
remain UNKNOWN. Offset validity refutations do not claim an observed runtime panic.

Certified initialized static `Copy + Freeze` enum places support discriminant-only reads. In ordinary
analysis each read is a fresh logical tag constrained to compiler-declared variants, including signed
sparse tags and pointer-bearing option tags. One saved observation stays consistent; separate storage
reads need not agree. Ordinary typed stores preserve legal tag shape without retaining a variant.
The explicit startup domain can retain checked initializer tags and supported scalar enum stores.
Tag-dependent counterexamples report the abstraction and remain runtime unconfirmed. Host/ARM debug and optimized fixtures check legal domains, separate
reads, payload-read barriers, invalidated epochs, unrelated casts, noncopy tags and static
destructors.
A declared-variant mutation fails symbolic checking and native replay. Uninitialized single-variant
static tags are UNKNOWN, with validation before the constant-tag shortcut. Rustc-elided owned locals
can still use their compiler-known constant tag without performing a storage read.

Compiler-identified fence/compiler_fence wrappers validate non-Relaxed Ordering arguments before
executing actual MIR. Their intrinsic boundaries validate constant ordering enums and preserve
tracked local storage. Both compiler and hardware fences add no synchronization facts: atomic
accesses still allow arbitrary per-access values. Host/ARM debug and optimized tests check all valid
orderings, symbolic guarded and invalid orderings, native panic replay, mutations and unsupported
payloads. Invalid direct intrinsic orderings remain UNKNOWN. This does not establish whole-function
atomicity, publication safety or full weak-memory correctness.

Dense Boolean/integer atomic prefixes in certified static storage can form an integer atomic
view. Compiler offsets and strides must cover every accessed byte without padding or cutting a
leaf, and the allocation must satisfy alignment at the projected offset. Opaque fields and padding
outside that footprint can be ignored. Reading padding, uninitialized storage, pointers or
ordinary payload fields, and destructors, remain UNKNOWN. Shared atomic reborrows retain their
opaque
marker. Host/ARM debug and optimized tests cover nonzero offsets, Boolean arrays, arbitrary values,
rejected regions, native scoped replay and layout/offset mutations. This adds no synchronization or
atomic-history facts and does not verify overlapping concurrent accesses.

Integer strong and weak compare_exchange model their old value and success/failure relationship,
with symbolic ordering checks. Weak CAS allows spurious failure. All 15 valid success/failure
ordering pairs in the pinned core are accepted; Release and AcqRel failure orderings refute. The
model adds no atomic history or synchronization facts. Pointer CAS remains UNKNOWN. Host/ARM tests
include positive, refuted and unknown cases, mutations and native replay.

Certified shared static MaybeUninit containers support as_ptr with size/alignment checks. The raw
payload address keeps the container's initialization barrier; it does not authorize reading T.
General union/payload reads remain unsupported. Certified UnsafeCell places support typed stores
and whole payload initialization moves while keeping read facts opaque. Tracked local static
reference slots support shared captures and mutable slot replacement. Actual mutable static
payload borrows remain UNKNOWN. Concrete zero-argument closure/function-item calls now accept the
empty Rust-call tuple's unit representation, with actual callback MIR execution.

Typed static store fixtures cover owned values, known callbacks, fresh constructed futures,
MaybeUninit/UnsafeCell address chains and provenance-backed thin NonNull round trips. Writes do not
supply shared-read or atomic-history facts. Stored references retain conservative frame-escape
evidence, including through unknown trusted memory effects. Each store has depth 16 and 512-value
limits; a root retains at most 512 reference entries. Resumed future stores, payload polling,
general unions, arbitrary destinations and unsupported shapes remain UNKNOWN. Host/ARM debug and
optimized tests include negative/unknown cases, a constructor-guard mutation and native replay.

Error-formatting fixtures cover guarded Result unwrap/expect and error-return counterparts, feasible
panic paths, shared Debug reborrows/aggregates/returns and a formatter counter that stays unchanged
when only a reference is constructed. General formatting stays UNKNOWN. Same-named user traits and
helpers cannot acquire core models; reference erasure retains dead/frame escape checks. Tests cover
host/ARM debug and optimized builds, constructor-guard mutations, native replay and induction
rejection. A panic-helper counterexample remains a translated obligation rather than an automatic
replay-confirmed failure; arbitrary atomic states can make otherwise unobserved error paths
feasible.

Static no-destructor drop fixtures check retirement before tag reads, old reference and atomic use,
and a second drop. Exact typed stores restore initialization; partial parent stores and writes in
another branch cannot restore it. Removing a required store changes the proof to UNKNOWN on host
and ARM in both optimization modes. Supported native cases restore storage before observing it.
Static destructors, zero-sized retirements and static payload moves remain unsupported. General
partial initialization and exact mutable-static payload histories are still separate work.


Compiler-identified thin pointer atomic loads validate their exact inherent signature and permit
Relaxed, Acquire and SeqCst ordering. Release and AcqRel orderings produce panic obligations.
Initialized certified static receivers and exact compiler-shaped tracked wrappers support these
loads, including static fields at nonzero offsets. Ordinary loads return arbitrary target-width
address bits. A saved observation stays consistent, but separate reads and initializer-specific
claims can refute under the reported abstraction. Explicit startup mode retains initialized null or
numeric address bits at certified static locations until history is invalidated. Provenance-bearing
initializers remain UNKNOWN; loaded addresses grant no pointee access. Raw intrinsic loads,
loaded-pointer dereferences, volatile loads and general raw atomic destinations remain unsupported.

Host/ARM debug and optimized fixtures cover legal comparisons, guarded ordering, uninitialized
receivers, numeric intrinsic destinations, conservative local and shared reads, and startup
boundaries. Native cases check valid operations and ordering panics. Admitting Release into a
permitted-order guard fails both symbolic analysis and native execution. Integer and pointer
static atomic storage share compiler type, extent, epoch and initialization validation; pointer
constructors and tracked receivers share the same compiler wrapper-layout checks.


Thin pointer/NonNull representation changes check the exact compiler wrapper, pointee and scalar
layout, then prove a nonzero address obligation. Address round trips preserve observed bits and
existing tracked references. Numeric nonnull handles do not acquire pointee alignment or memory
permissions; dereferencing them remains UNKNOWN. The pinned compiler's nonnull pointer-field
pattern is recognized explicitly. Typed static stores verify that pattern, and supported integer
range/or predicates, against the current path before accepting their values.

Host/ARM debug and optimized fixtures cover checked nullable conversions, address-one handles,
loaded observations, caller storage, forward/reverse representation changes and typed publication.
Zero-address conversions refute validity. Removing a nonzero guard fails the proof, and corrupting
an address round trip refutes and panics in native tests. Supported native cases publish both null
options and nonnull handles; ordinary shared payload reads still remain UNKNOWN.

Thin raw-pointer root inputs carry arbitrary target-width address bits, including nested struct
fields. Compiler nonnull pointer patterns constrain those bits to be nonzero. These inputs provide
no pointee storage, provenance, alignment or executor initialization history. Fat pointer inputs
remain UNKNOWN. Guard mutations refute and fail native checks; nonnull roots, nested fields and
unsupported dereferences are checked on host and ARM in debug and optimized configurations.

Thin pointer compare-exchange validates the same compiler-typed initialized storage as pointer
loads. Strong CAS succeeds exactly when the observed old address matches the expected address;
weak CAS also permits spurious failure. Both Result variants carry that same arbitrary observed
address, without pointee provenance or retained update history. Failure Release and AcqRel produce
panic obligations. A possible pointer publication invalidates startup and existing owned atomic
histories.
Address/order guard mutations fail symbolic and native tests; matching observed bits do not
permit dereferencing a returned pointer. Numeric intrinsic destinations remain unsupported.

## Incoming shared storage and platform calls

Shared non-Freeze root references, including nested struct, tuple, array and enum fields, retain
incoming read-only storage identity. Potentially aliased multiple interior/mutable root graphs
remain UNKNOWN. Static stores validate Freeze snapshots against the exact compiler pointee shape;
non-Freeze snapshots remain unsupported. Tracked stores retain lifetime and escape evidence without
inventing static payload initialization or startup history. Guard, type, field, lifetime, alias
and unknown-effect mutations are exercised on host and ARM with debug and optimized MIR.

Metadata-only dependency retention preserves the actual compiler exported-symbol index. Foreign
Rust ABI declarations can resolve to a unique, strong, explicitly exported, non-generic Rust body
with a matching normalized signature. Native-library, dynamic, weak, ambiguous, missing and
unsupported exports remain UNKNOWN. Declaration contracts are not a proof; callee contracts and
retained bodies execute normally. Temporary copies of an existing third-party implementation test
positive, panic/assertion mutation and UNKNOWN paths while the analyzed fixtures forbid unsafe code.

Exact Cortex-M PRIMASK reads/writes and interrupt mask instructions support only validated compiler
assembly templates, u32 register operands, options and fallthrough shapes on supported ARM targets.
PRIMASK reads remain arbitrary, including reserved upper bits. Repeated reads need not agree;
counterexamples depending on that abstraction are labeled. Mask writes establish no exclusion or
startup history and invalidate published atomic history. Other assembly remains UNKNOWN. This does
not establish scheduling, interrupt handler behavior or MMIO access conditions. Exact `sev`, `wfe`
and `wfi` templates stay UNKNOWN with a diagnostic naming the unmodeled hardware event/wait
instruction, including bare instructions with no PRIMASK-specific assembly options. Assembly
recognition errors propagate to the selected root's `function` and `source`; the recorded
`call_chain` retains
the deepest failing dependency call. The diagnostic does not claim that assembly ran at the root.

Compiler-typed inhabited zero-sized structs, tuples and arrays share bounded input descriptions.
They emit no scalar symbols and consume one ordinary input slot per completed argument shape.
The 16-level depth, 256-element array and 2048-node descriptor limits remain explicit. Unions,
uninhabited types and unsupported reference shapes do not become valid from size alone.

Checked dependency construction can certify MaybeUninit's uninitialized unit field and exact
core UnsafeCell/SyncUnsafeCell forwarding. The narrow bool-to-u8 construction encoding preserves
portable atomic container origins. A certificate does not establish initialized payload bytes;
shared payload reads remain UNKNOWN even after supported stores. Compiler fixtures cover stores,
guard mutations, spoofed unions, initialized alternatives and stale certificate rejection.

Whole compiler-backed mutable Rust bool statics admit fresh arbitrary valid values on each read.
Their declared initializer and preceding writes establish no runtime history. Supported typed
writes discard shared history. The model requires exact bool storage at offset zero and rejects
numeric addresses, immutable storage and readonly writes. Counterexamples relying on arbitrary
state or unstable reads carry an abstraction reason; they do not establish a boot-time panic.

Certified bool payloads inside core UnsafeCell, including `Cell<bool>`, use the same arbitrary-read
model. A bounded compiler struct/tuple field path must match the exact declared storage type and
byte offset. Unions and MaybeUninit paths remain unsupported; reads grant no initialization,
startup, exclusion or stable shared-state evidence in ordinary analysis.

Under the explicit `--startup` domain, those same certified boolean locations use checked compiler
initializer bytes and branch-local writes. A shared static footprint map prevents boolean and
integer atomic histories from describing overlapping bytes independently. Nonboolean stores and
opaque calls invalidate known and unseen histories; subsequent writes do not restore precision.
Host/ARM O0/O2 compiler cases cover conditional first use, repeated use, independent allocations
and fields, branch-local updates, mixed disjoint atomic history and unsupported pointer/storage
cases. Initializer mutations refute the conditional proof; separate native runs confirm first use,
repeated use and the mutation. Default outcomes and async startup rejection remain unchanged.

Concrete trait-object unsizing preserves a compiler Unsize certificate and exact vtable slot.
Actual method bodies execute with retained storage, mutations and lifetimes. Arbitrary dyn roots
remain UNKNOWN; the analyzer does not infer a closed set of implementations from the workspace.

Compiler-layout raw field and array-element pointers retain their containing allocation and child
extent. The exact `each_mut` reference-array conversion checks initialized typed live projections
and disjoint mutable elements, but nonempty grants remain UNKNOWN without temporal permission
certification. Numeric origins, unions, incompatible anchors, forged permissions and unsupported
symbolic reference-array selection also remain UNKNOWN.

Compiler-identified volatile scalar loads check exact typed, initialized, live whole allocation
backing and a matching registered address. Those spatial facts do not certify temporal access
permission: tracked loads remain UNKNOWN before exposing retained values. Numeric MMIO, static
payloads, projections, cursor offsets, punned or invalidated storage also remain UNKNOWN. The
explicit hardware model has its separate conditional peripheral-access boundary and cannot
silently authorize tracked Rust RAM.

Arbitrary valid function-pointer input fields use bounded typed opaque witnesses. These witnesses
retain the full compiler signature, including safety, ABI and bound regions, without a numeric
address, concrete target or callback effects. Unused fields, lazy input arrays and exact typed
stores are supported. Invocation, address casts, identity comparisons, contract comparisons and
native replay remain UNKNOWN. Host/ARM tests cover ordinary and unsafe signatures, Waker tables,
reached panics, changed guards and forged signature mutations.

Owned non-byte arrays use immutable shared host payloads with copy-on-write updates. Sharing the
host representation creates no Rust alias: each retained value and branch detaches changed paths.
Constant storage reuse requires exact compiler types and lossless decoded value keys; every field
is still read and validated before reuse. Limits count all 2,048 CTFE visits, not only unique keys.
Owned repeats validate their operand within 256 values, then charge bounded shared clone handles.
Nested array copies and writes, large tables, signed-zero/NaN bits, unsupported payloads and budget
boundaries have compiler and mutation tests.

Exact core `Range<usize>` mutable byte slicing checks start <= end <= current length as a panic
obligation and returns a writable projection into the original allocation. Nested and empty ranges
retain their correct offsets and lengths. Invalid bounds refute; non-byte, readonly, arbitrary raw
and dead backing remain UNKNOWN. Host/ARM and native mutations check bounds, updates and model
identity, including similarly named user implementations that execute their actual bodies.

Compiler inventories record direct coroutine return types independently of proof outcomes.
The fleet exporter counts future factories separately and identifies their compact root rows.
These proofs construct futures without polling them. Explicit async-entry results remain separate;
missing metadata in legacy inventories is unclassified rather than inferred from function names.

Scalar constant tables contain at most 256 bool, integer or f32/f64 elements, including nested
`Table<1>`-shaped arrays. Every element passes exact typed initialized decoding and retains raw
float bits. Composite arrays keep the 128-element cap; total visits remain 2,048 and depth sixteen.
Host/ARM and native tests check bounded lookup, bad indices, data and guard mutations, NaN payloads,
signed zero, uninitialized storage, composite limits and 257-element scalar rejection.

Origin schema 2 certifies unevaluated aggregate constant items and associated constants only
through available monomorphized compiler MIR with exact operand and return types. Construction
DAG edges bind every referenced definition; missing edges, obsolete schemas and unsupported
operations remain UNKNOWN. Local and foreign declarations without bodies are rejected before
compiler CTFE MIR queries. This certifies construction provenance, not runtime values, verified
callee behavior, initialization history or synchronization.

Closed constructor dataflow checks actual aggregate arguments, initialized locals and exact
monomorphized input/output types before reusing a construction node. Straight-line calls, moves,
fields, aggregates and repeats retain bounded origin evidence; joins, cycles, dynamic calls,
references and unions remain unsupported. Whole U32 carriers keep their origin kind. Composition
admits only the compiler's exact `Atomic<u32>` with matching layout, and a separate exact
`Atomic<usize>::new` rule checks initialized usize input and its typed scalar conversion. Folded
constants admit only compiler `Option::None` and inhabited fieldless zero-sized structs. These rules
supply neither selected runtime state nor synchronization, initialization history or device models.

Core `__iterator_get_unchecked` retains actual iterator backing, cursor bounds and element type.
Mutable access requires writable storage and distinct issued absolute indices, with at most 256
issued indices per retained iterator. Ordinary element access after mutable unchecked issuance
remains UNKNOWN; metadata queries retain their existing behavior. Bare snapshots, dead backing,
unknown or duplicate indices and unsupported induction histories remain UNKNOWN. Host/ARM tests
and safe native mutations exercise float zip adapters, shared reads and cursor offsets. Synthetic
invalid custom MIR cases are checked only by the analyzer, without native undefined behavior.

Integer and pointer CAS share the same ordering checks and strong/weak success condition. Strong
success compares observed old value with expected value; each weak operation additionally has its
own unconstrained spurious-failure choice. Shared code does not merge pointer address provenance,
owned integer history or startup assumptions. Regression cases distinguish independent weak choices
from repeated strong zero-value writes on host/ARM at both compiler optimization levels.


## Application entry traversal evidence

Proof reports record symbolic body entry only after validating call arguments and finding a
satisfiable start-block path. Compiler coroutine identity distinguishes application poll bodies
from future constructors; inventory and analyzed-body lists do not establish entry. The 512-record
budget reports truncation explicitly. Host/ARM O0/O2 cases preserve positive, negative and unknown
poll outcomes, exclude constructors and rejected roots, and deserialize older reports conservatively.
Reaching a body is separate from completing a proof or confirming a native execution.

Explicit startup mode can additionally inspect an exactly certified Copy/Freeze static enum's
initializer tag. Rustc decodes the typed layout, including niche `Option<NonNull>` and signed sparse
tags, from a read-only host snapshot capped at 1 MiB. The copy supplies no runtime freeze property
or pointer/payload access. Writes and opaque calls invalidate precision; wrong origins, uninitialized
places and unsupported payload reads stay UNKNOWN. Compiler initializer mutations and independent
native runs distinguish fresh None from occupied Some. Ordinary-root tag observations stay opaque.

Explicit startup analysis retains tags after exact certified Copy/Freeze enum stores whose variants
contain only bool, integer or float fields. Stores preserve disjoint initializer facts and
branch-local tag choices; they do not enable payload reads. Pointer-bearing enums, publication,
opaque calls and interrupt-mask writes retain conservative invalidation. Ordinary reads remain
arbitrary legal tags, and later writes cannot restore invalidated startup history.

Certified whole mutable primitive integer statics and exact integer payloads within core UnsafeCell
struct/tuple paths support direct reads. Ordinary reads admit fresh arbitrary valid target-width
bits; startup reads use checked initialized scalars and exact typed writes. Unions, arrays,
MaybeUninit, numeric origins and mismatched declared types remain UNKNOWN. Conditional integer
writes preserve disjoint boolean, enum and atomic history; opaque effects still invalidate it.

The separate `--startup-isolated` domain conditionally retains actual typed static writes and
local/static pointer atomic history beyond publication. Its recorded premise excludes external Rust
storage mutations throughout the selected entry. Partial overwritten ranges cannot resurrect
initializers, and symbolic pointer-origin merges retain address bits without pointee rights.
Opaque calls and frame-escape checks remain conservative. Hardware and scheduler validity are not
supplied by this premise.

Core slice Iter/IterMut for_each uses tracked backing and executes concrete function-item, closure
or known safe Rust function-pointer callbacks in order. Fold/rfold and predicates share the same
callback resolver. Known pointer values require exact registered signatures and retained Rust bodies;
arbitrary inputs, callback references, unsafe/non-Rust signatures and unavailable bodies stay UNKNOWN.
Callback effects and branch conditions persist, borrowed cursors advance, and closure storage retires
after exhaustion. Panicking callbacks refute the root; incomplete callbacks and unsupported storage
remain UNKNOWN. This supports finite controller-array reset traversal without interpreting physical
NonNull fields or assuming reset contracts.

Typed solver queries that exceed their configured byte budget retry the same Boolean conditions
with query-wide local DAG sharing. Ordinary queries retain their previous text and incremental
prefixes. The fallback preserves all conditions, models and floating-point probes; budgets stay
unchanged, and oversized results remain UNKNOWN. Compiler CRC16 fixtures cover host/ARM O0/O2
PROVED, REFUTED and UNKNOWN outcomes and a natively failing table-index mutation.

Constant homogeneous integer array choices share an SMT table across index expressions. Exact
width, signedness, context and index-key capacity checks preserve all element values and the prior
unmatched-index default. Compiler bounds and storage checks stay active. Host/ARM O0/O2 fixtures
cover guarded lookup and a 21-byte symbolic CRC payload, with failing native array-value mutations.
Other scalar and pointer choices retain their previous domain.

SMT read-over-write simplification walks store chains iteratively. It skips a store only for
same-sort literal bit-vector keys proven unequal by their exact values. Exact key identity retains
the newest matching payload; constant-array bases retain their default. A symbolic key remains a
barrier, including stores with conditional payloads. Context and key-sort checks run before folding;
no solver answer, pointer origin, bounds obligation or storage-lifetime check is bypassed.

One eligible incoming shared `Freeze` reference can retain live caller-owned storage through
projected, returned and reborrowed views, including byte-array iterator backing. Eligibility checks
all root arguments and reachable compiler field types; competing or nested references, raw pointers
and interior mutation do not acquire this new identity. Existing snapshot domains remain available.
Root-local `StorageDead` preserves caller storage, while actual dead local/callee backing and opaque
invalidation stay UNKNOWN. Shared writes remain unsupported. Host/ARM O0/O2 and failing native
iterator mutations cover the model without application assumptions.

Stage 125 adds retained checked ranges for finite integer/tuple arrays and concrete ordered
`find` predicates. Its compiler controls cover host and ARM at O0/O2: safe prefixes, offset
ranges, empty iterators, first-match/late effects and valid nested borrows prove; unguarded
bounds, counter overflow and wrong update/order claims refute; dead/exhausted storage, opaque
callbacks, unsupported aliases/payloads/whole views and forged mutable exposure remain unknown.
The callback increment mutation refutes in the solver and fails native execution. No assumptions
or trusted calls are introduced.

The motivating source root is `bench::Sniff::saw` at dm-mc02-bringup/src/bench.rs:279, called by
`Bench::receive` at line 476. Its selected root domain includes arbitrary `self.len`; a length
above the 16-element backing can produce a real bounds counterexample. Such a root refutation
would not establish reachability from the application's constructor/feed invariants. Fleet outcomes
require separate replay and publication.

Actual Sniff::saw replay now refutes at len=24 versus capacity16. Independent solver and native
O0/O2 source controls confirm that bounds panic; constructor-shaped len<=16 controls pass.
The source initialization/update invariant excludes this witness, without a whole-program
reachability proof. The normalized forged-MIR permission audit now remains UNKNOWN while
valid shared reads and mutable reborrows prove. All 546 workspace Rust and 48 Python tests pass.

Stage 127 adds a public, validated external hardware model API with a separate opt-in conditional
backend. Exact STM32H723VG/STM32F407IG 32-bit policies admit bounded forward byte-address transport
and exact write-only u32 registers, including compiler-certified transparent u32 values. Core
pointer add checks its original unsigned count before conversion; subtraction, wrapping and
negative transports remain unsupported. Actual callbacks execute, and hardware stores invalidate
published/startup histories. Unmapped/readback/type/device/context/liveness failures remain UNKNOWN.

New compiler controls prove conditional writes, refute callback mutations and reject unsupported
accesses on ARM O0/O2. Host-width mismatch is UNKNOWN; native execution checks only actual Rust
callbacks, never MMIO. All nine hardware-profile paths execute BSRR writes and reach unsupported
PUPDR reads in the actual fleet replay. No strict proof gain or firmware boot guarantee follows.

Stage 128 extends the public API with opt-in hardware schema 2 and exact independent u32 reads.
The same initialized full-range scalar certificate supports transparent register wrappers;
actual read-modify-write callbacks execute. Read/write permissions are independent, and every
read is a fresh abstraction with device correlations explicitly unverified. Reads conservatively
invalidate publication/startup histories; tracked RAM reads keep their original behavior. Native
replay refuses configured or recorded hardware models. Schema-1 serialization stays unchanged.

The nine hardware-profile fleet paths pass BSRR and PUPDR read, then reach an unsupported Rust
fieldless enum-to-u8 transmute inside the actual setter callback. They remain UNKNOWN; no fixed
register values, readback, hardware-ready assumptions or new completed main proof are introduced.

Stage 129 supports strict fieldless enum-to-integer Transmute with an explicit integer repr and
exact matching target primitive. The compiler must certify a non-Drop initialized direct scalar
layout, equal size/alignment, zero tag offset and exact tag width/signedness. Every represented
variant and symbolic inventory entry is checked against compiler metadata. Symbolic tags require
proven membership in the exact legal set, including holes and signed discriminants; conversion
preserves the original bits and adds no validity assumption. C/default repr, payloads, layouts
without an initialized direct tag, reverse reconstruction and mismatched primitives remain UNKNOWN. Actual PAC
`to_bits` methods execute their Rust bodies rather than receiving a device-specific summary.

The twelve-main schema-2 replay clears that conversion gap for all nine affected application bodies.
Their next UNKNOWN is a tracked-storage reference diagnostic in the application future, under audit.
The other three retain earlier RTT refutations. This traversal progress adds no completed main proof
and supplies no executor or native boot guarantee.

Stage 130 adds an explicit trusted storage effect API for a call that promises not to mutate,
publish or retire pre-existing ordinary tracked storage. Pure owned compiler/value input
certification precedes snapshots, and static/startup plus atomic precision remains invalidated.
Existing dead allocations are never revived. The exact used selector/effect/reason premise is
recorded separately; strict defaults and legacy omitted-modifies boundaries are unchanged.
This addresses conservative future-frame invalidation only under the stronger recorded premise,
without establishing a general private-storage or alias-reachability theorem.

Final STM32 frame-profile replay clears lost future storage for all nine affected bodies. With
separate alternate-function GPIO permissions, eight H7 bodies reach an unsupported RCC pointer
constant and the F4 body reaches retired USB static storage. All remain UNKNOWN; the other three
keep earlier RTT refutations. The new boundaries require further storage/device modeling.

Independent source audit identifies the H7 pointer as ordinary Rust
`embassy_stm32::_generated::REFCOUNTS: [u8; 3]`, taken with `addr_of_mut!`; the raw constant decoder
currently handles numeric bits and misses allocation-backed static provenance. The F4 object is
`rm_c::UsbPort::open::EP_OUT: StaticCell<[u8; 256]>`, whose view is retired by the opaque static
effects. Neither diagnostic establishes a firmware lifetime failure. Static identity alone would
not prove zero refcounts or an unused USB cell; those need separate state/effect evidence.


Stage 131 separates exact Rust static address identity from a conditional preservation of existing
static access validity. The new external storage effect retains already-live allocation/type and
borrow/access rights, while invalidating value history and atomic precision. Whole compiler-named
Rust static raw pointers retain exact declared types; bounded initialized mutable byte-array
leaves admit arbitrary values. Neither initializer zeroes nor an unused USB cell is inferred.

The stage-131 complete all-main replay remains three REFUTED and nine UNKNOWN. Eight H7 paths
now stop at mutable static array-to-slice coercion; F4 reaches the portable-atomic bool-to-byte
wrapper cast. These are Rust representation gaps, not MMIO access failures or observed boot bugs.
All 36 strict obligation arrays match stage 130. The ordinary-frame profile still invalidates
static views: eight H7 diagnostics now report that invalidation after raw identity is decoded,
while all outcomes remain unchanged. Local evidence:
`/tmp/miren-stage131-main-static-validity-20261010`.


Stage 132 addresses the newly exposed Rust representations: bounded mutable static byte-array
slices and an exact portable-atomic wrapper conversion. The existing static-validity profile is
reused; no initializer values or hardware progress assumptions are added.


The complete stage-132 replay reaches the conditional supported-outcome milestone: all twelve
application async mains are REFUTED under the captured root domain. Three RTT lifecycle results
remain unchanged; eight H7 paths expose REFCOUNTS[1] == 255 overflowing checked u8 addition, and
F4 reaches the real already-full StaticCell panic. These are abstract shared-state witnesses,
with startup/native/boot reachability unverified. The F4 saved byte witness is 255; independent
solver replay also admits valid already-used byte 1 and excludes unused byte 0. No unused-cell or
zero-refcount premise is added, and the success-path MaybeUninit write remains unsupported.

Strict remains four REFUTED/eight UNKNOWN, and all fresh application future bodies are entered.
Final captures are `/tmp/miren-stage132-main-{strict,legacy,static-validity}-verified-20261010`.
Paired export validation checks exact configured premises and captured source/artifact identities.
This milestone supplies supported outcomes for the chosen abstract domain; startup and firmware
boot reachability remain unverified.

A separate permission correction rejects writes recovered from shared Freeze-payload
`MaybeUninit::as_ptr` views. Valid original raw capabilities and exact `UnsafeCell::raw_get` keep
address-only access, without assuming initialized payload references. Embassy's actual
`UninitCell::as_mut_ptr` forms such a reference before payload initialization and remains UNKNOWN.
Registration and runtime therefore each have twelve UNKNOWN results in the final capture.
The [core raw_get documentation](https://doc.rust-lang.org/core/cell/struct.UnsafeCell.html#method.raw_get)
recommends raw access for gradual initialization; the
[Rust validity reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html#undefined.validity.reference-box)
leaves the exact reference-pointee requirement unsettled. This boundary does not establish an
Embassy application bug or authorize replacing its actual reference-forming MIR with raw_get.

The fresh strict fleet survey records 32 units and 2336 roots: 1107 PROVED, 237 REFUTED and
992 UNKNOWN, with no collection errors or assumptions. Compared with pass 19, three UNKNOWN
become REFUTED; 13 PROVED and 24 REFUTED become UNKNOWN at that validity boundary. New refutations
also use arbitrary static-state witnesses, with boot reachability unverified. Final evidence:
`/tmp/miren-fleet-pass20-final-20261010`. All 570 Rust and 57 Python tests pass.


Stage 134 adds checked snapshot projections for retained finite integer/tuple slices. Bounds are
proved before absolute index arithmetic; lengths must be uniquely determined and at most 128.
References keep the original allocation, projection chain and permissions, so nested indexed
writes affect the backing storage. Dead parents, including empty views, remain unavailable.
Whole-slice assignment, arbitrary incoming non-byte slices, ambiguous writes, unsupported element
shapes and variable-length snapshots remain UNKNOWN.

The independent Rust capability suite advances `retained_prefix_index` from UNKNOWN to PROVED
across host/ARM O0/O2. Its current 23 cases yield 44 PROVED, 36 REFUTED and 12 UNKNOWN over the
four configurations, with strict premises. No device or startup hypotheses are used.

Stage 136 hardens tracked raw-access boundaries. Volatile scalar reads, byte views/references
from raw pointers and nonempty raw-pointer-to-reference array conversions now require a temporal
permission certificate and return Semantics UNKNOWN without one. Earlier spatial/type/liveness
checks remain active. This supersedes earlier claims that those checks alone support the reads
and `array::each_mut` reference grants. Ordinary tracked reference/slice operations and raw
address formation, offsets and comparisons retain their separate support. Const raw byte-slice
metadata formation and length queries preserve the raw descriptor and grant no access rights.

The expanded core-only capability matrix has 26 cases and 13 families, expecting 48 PROVED,
40 REFUTED and 16 UNKNOWN outcomes across host/ARM O0/O2. New cases exercise metadata P/R and
a safe core reference grant U; its larger denominator is not a percentage gain.

Stage 137 selects correlated immutable tuple values from bounded fixed arrays and checked
finite-slice snapshots at symbolic indices. Bool, primitive integer/float and unit leaves have
exact matching shapes, widths, sorts and symbolic contexts; one index predicate selects every
field. Known float raw bits survive selection, including payload NaNs and signed zero. Candidate
trees are limited to depth 16 and 512 nodes. Existing incoming shared-reference snapshots supply
values without restoring identity or reference rights. Retained handles, ADTs and Drop-bearing
values remain excluded; symbolic composite writes still require a unique location. The expanded
29-case/14-family baseline expects 52 PROVED, 44 REFUTED and 20 UNKNOWN outcomes across four builds.


Stage 138 retains initialization state for compiler-identified `MaybeUninit` containers holding
primitive bool/integer/float or pure tuple values. Actual core constructors and `assume_init`
bodies execute; exact type, layout and `ManuallyDrop` field certificates control representation.
Initialized extraction preserves the value and floating-point raw bits. Uninitialized nonempty
payloads return Semantics UNKNOWN. Unit-only zero-byte tuples can extract their unique value;
unrelated zero-sized ADTs remain unsupported. Whole assignments and copies preserve state without
new assumptions. Raw writes, `zeroed`, reference-forming methods, pointer/reference payloads and
arbitrary unions remain UNKNOWN. This does not establish general allocation initialization or
raw-access permissions. The 32-case/15-family capability baseline expects 56 PROVED, 48 REFUTED
and 24 UNKNOWN outcomes across host/ARM O0/O2.


Stage 139 extends the owned `MaybeUninit` certificate to bounded arrays of supported pure values.
Exact compiler counts, element types and layouts control construction and extraction. Element
vectors must match the count and every typed child; byte arrays additionally need exact unsigned
usize length metadata and the correct data sort and symbolic context. Counts are at most 128,
and expanded trees retain depth-16 and 256-node limits. No input domain or resource budget expands.
Initialized extraction preserves the array, including available float bits. Uninitialized arrays
remain UNKNOWN unless their exact closed type has a unique zero-byte value: a supported empty
array or an array of unit-only values. Unsupported element types remain unsupported even at
length zero. Partial initialization, wrapper repetition, `array_assume_init`, raw/static access
and reference-forming methods remain separate frontiers. The baseline now contains 35 cases in
15 families, expecting 60 PROVED, 52 REFUTED and 28 UNKNOWN outcomes across host/ARM O0/O2.

Stage 140 checks Unicode scalar validity at character formation and typed value boundaries.
Actual core checked conversions execute and prove their integer-to-character conversion from
existing path conditions. Invalid or unconstrained encodings return Semantics UNKNOWN; validity
is never inserted as a premise. Refined scalar targets additionally prove their original compiler
pattern, preserving previously supported valid conversions. Initialized static character reads
use a domain encoding that covers every Unicode scalar without restoring the initializer or
write history. Cached, stored and startup values require proof of validity instead. Uninitialized
and uncertified raw access retain their separate UNKNOWN boundaries. The expanded baseline has
38 cases across 16 families: 64 PROVED, 56 REFUTED and 32 UNKNOWN across host/ARM O0/O2.

Stage 141 admits exact character leaves in owned `MaybeUninit` payloads. Construction, extraction
and recursive typed carrier validation prove Unicode validity using the current path conditions.
Whole copies, helpers, tuples and bounded arrays retain exact initialized values. Uninitialized
nonempty character payloads remain Semantics UNKNOWN, while an eligible empty character array
has its unique empty value. The original type/layout, initialization and resource certificates
remain required; raw pattern types and reference-forming operations remain unsupported. The
41-case/16-family baseline expects 68 PROVED, 60 REFUTED and 36 UNKNOWN across four builds.

Stage 142 models ordinary binary32/binary64 remainder with exact same-format operands.
[Rust remainder](https://doc.rust-lang.org/std/ops/trait.Rem.html) uses a truncating quotient;
[SMT remainder](https://smt-lib.org/theories-FloatingPoint.shtml) uses a nearest-even quotient.
The translation computes the IEEE remainder and, when its nonzero sign opposes the dividend,
adds the dividend-signed divisor magnitude. This correction is an independently reviewed
derivation. The truncating residual is exactly representable: when the dividend is smaller,
it is the dividend; otherwise it is an integer multiple of the divisor's binary lattice unit,
with fewer than one significand's worth of bits. The correction addition therefore rounds exactly,
including subnormals, and cannot overflow. Strict ordered sign comparisons preserve signed zero
and leave exceptional NaN results unchanged. Arithmetic storage keeps the existing conservative
NaN encoding policy; no raw-bit certificate is fabricated.

Compiler controls exercise actual remainder and compound assignment bodies, both divisor signs,
nearest ties, signed zero, subnormal and extreme values, infinities, zero divisors and NaNs.
Numeric equality guards retain their full input domain. Equality against a finite nonzero constant
may use exact encoding equality when both actual terms are same-format bit-to-float conversions;
zero and NaN comparisons retain numeric semantics. Independent SMT checks validate this rewrite.
Missing external bodies, wider formats and unfinished solver queries remain UNKNOWN. The baseline
has 44 cases in 17 families, expecting 72 PROVED, 64 REFUTED and 40 UNKNOWN across four builds.


Stage 143 extends ordinary execution with arbitrary read-only primitive slice inputs. Admission
requires an exact compiler primitive element type and the existing single immutable incoming-root
certificate. A symbolic target-usize length is bounded by the actual nonzero element byte extent,
not by a finite element-count budget. Typed array observations retain repeated-index correlation;
Boolean values use logical elements, integers preserve their width/sign and floats preserve input
storage bits. Character observations use the valid Unicode domain encoding from stage 140. Its
underlying seed is not physical character storage and cannot authorize byte reinterpretation.

The descriptor grants no allocation or raw/mutation rights. Checked indexing and subviews must
retain their original reference source, prove bounds before offset arithmetic and validate the
parent lifetime before metadata or empty paths. Original pattern, aggregate, reference-bearing,
zero-sized and mutable input domains retain UNKNOWN boundaries. Unrestricted equality, iteration
and induction require their own supported consumers. The existing finite retained integer/tuple
projection budgets remain separate from this arbitrary input domain.


Stage 144 adds compiler-identified shared scalar-slice iterator cursors and metadata. Arbitrary
lengths stay admitted; nth, reverse traversal, count, clone and exhaustion operate on checked
target-usize front/back positions and the original readonly source. Missing selected bodies remain
UNKNOWN. Every new result validates retained backing, including metadata and empty cursors.
Floating input bits and decoded character values preserve stage-143 correlations. Full loops
still require complete execution or a supported invariant; an unrestricted wrapping fold reaches
the default execution time budget. The 49-case/18-family baseline expects 80 PROVED, 72 REFUTED
and 44 UNKNOWN outcomes across host/ARM O0/O2.

Stage 145 supports primitive slice membership and equality when actual path conditions prove
the comparison work fits within 128 elements. This bounds execution work without restricting
the incoming slice domain. Equality can resolve mismatching lengths without scanning. Original
backing must remain valid even for empty views or unequal lengths, and selected concrete core
bodies must be available. Floating comparisons retain numeric NaN and signed-zero semantics;
character comparisons use decoded Unicode values. Unbounded scans remain UNKNOWN. Combined with
stage 144, the 52-case/19-family baseline expects 84 PROVED, 76 REFUTED and 48 UNKNOWN outcomes
across host/ARM O0/O2.

Stage 146 certifies supported synchronous closure captures using their exact compiler definition,
resolved closure kind and original capture types. Primitive slice and pure initialization-wrapper
captures retain their separate validity rules. Returned closures preserve caller-owned references;
captured frame-owned borrows refuse before the return path can turn them into owned snapshots.
Aggregate capture carriers validate their compiler field and variant metadata. Calls through
`FnOnce` execute the selected compiler-generated shim and actual closure body, preserving receiver
borrow conversion and drop execution. This does not supply an async closure state model, new raw
rights, mutable slice roots or unbounded loop summaries. The 55-case/20-family shared baseline
expects 88 PROVED, 80 REFUTED and 52 UNKNOWN outcomes across host/ARM O0/O2.

Stage 147 adds explicitly scoped SMT predicates with lexical free symbols and safe shared printing.
Its representation foundation changes no Rust consumer or input domain. Stage 148 uses it for
full-length read-only primitive scalar membership and equality, retaining original source, type,
lifetime and body-availability checks. Guarded logical observations preserve decoded Char and
numeric Float equality; they create no raw-access rights. Equal-length differing views and long
inputs have P/R controls, and missing bodies and retired sources retain their conservative causes.
The unchanged unrestricted scalar membership and equality functions now prove in all four compiler
profiles. Byte and finite/custom policies remain distinct. The 58-case/21-family shared baseline
expects 96 PROVED, 84 REFUTED and 52 UNKNOWN outcomes across host/ARM O0/O2.


Stage 149 admits arbitrary-length read-only slices of exact pure tuple and fixed-array primitive
elements. Compiler shape and layout certificates retain independent logical arrays for repeated
field occurrences. Checked common-index reads reconstruct exact nested values; range views apply
the same checked offset to every field. Float observations retain storage bits, Char observations
decode valid scalars, and owned copies and caller-backed borrows retain their existing rights.
The actual nonzero compiler element stride bounds allocation extent without capping slice length.
Expanded types retain depth-16, 512-node and 128-element fixed-array shape budgets. Unsupported
leaves are certified even beneath zero-length arrays; fully zero-sized whole elements refuse.

The 32-root compiler matrix yields 11 PROVED, 5 REFUTED and 16 UNKNOWN per host/ARM O0/O2 build.
Actual selected-field mutation refutes and fails valid native executions on 129-element inputs.
Mutable and competing roots, invalid lifetime and mutation attempts, missing bodies, refined and
identity-bearing leaves, oversized type arrays and deferred whole-composite consumers retain their
specific UNKNOWN causes. Whole nested-array dynamic selection remains a separate finite-value gap.
The original aggregate-slice false assertion now refutes without a source rewrite. The shared
61-case/22-family baseline expects 100 PROVED, 92 REFUTED and 52 UNKNOWN across four builds.


Stage 150 extends bounded pure value selection from tuples to nested fixed arrays. Every candidate
is validated before constructing conditions, with exact carrier kind, arity/count, leaf width/sign,
sort and term context. All fields share the same index condition. Float numeric expressions and
available storage bits follow that condition; raw bits survive only when every candidate retains
a certificate. Existing valid Char values are selected without repair or added premises. Empty
inner arrays retain their array carrier. Constant, uniquely proved and singleton handle selection
keeps its prior behavior; new reads do not grant writes or create conditional reference identities.

The 21-root matrix yields 12 PROVED, 4 REFUTED and 5 UNKNOWN per host/ARM O0/O2 build. It includes
whole inner-array choices from arbitrary-length composite slices, owned-copy mutation isolation,
Float bits, Unicode, mixed tuples/arrays, bounds and actual helper mutation with valid native
failure. Byte snapshots and ambiguous references/ADTs retain their actual selection frontiers;
symbolic writes retain their Semantics refusal. The Drop control reaches an earlier actual
`core::ptr::drop_glue` layout gap, recorded separately from conditional-selection eligibility.
The shared 64-case/23-family baseline expects 104 PROVED, 96 REFUTED and 56 UNKNOWN across builds.


Stage 151 extends exact core shared slice cursors to the supported arbitrary-length composite
input domain. Construction retains the original immutable reference and validates its exact
compiler element type and selected body. Every modeled cursor API validates source availability;
metadata, clones and exhaustion require the same body and lifetime checks as element reads.
The typed Iter carrier proves target-usize front/back metadata, ordered positions and back within
actual source length. Items retain source Index projections and reconstruct tuple/array fields
through checked reads; no owned descriptor becomes a reference or gains mutation/raw rights.

The 24-root compiler matrix yields 13 PROVED, 5 REFUTED and 6 UNKNOWN per host/ARM O0/O2 build,
including forward/reverse skips, metadata, count, clone/by-ref, returns, long inputs, Float bits,
Char observations, copied handles and retired backing. Actual nth-helper field mutation refutes
and fails valid native O0/O2 tests. Raw-source controls stop at their actual sized-pointee or raw
construction frontier according to compiler profile. Mutable/competing roots, unavailable bodies
and retired source metadata remain UNKNOWN. Existing aggregate next/nth controls prove with their
original sources unchanged. The shared 67-case/24-family baseline expects 112 PROVED, 100 REFUTED
and 56 UNKNOWN across the four configurations. Unrestricted callback loops still require complete
execution or a separate supported invariant; cursor support supplies no loop summary.


Stage 152 admits exact pure zero-sized tuple/array elements in the same read-only composite slice
representation. Their empty primitive inventory supplies only each unique typed value. The original
inner type is still certified beneath empty arrays, and source lifetime, selected bodies and checked
index/view/cursor bounds remain required. Zero stride permits every target-usize length; nonzero
strides retain their original allocation extent. No physical storage, alias or raw rights follow.

The 25-root host/ARM O0/O2 matrix yields 9 PROVED, 4 REFUTED and 12 UNKNOWN per build. Exact MAX and
above-isize counterexamples establish that the large length domain is admitted. Safe native
[(); usize::MAX] arrays check last-item reads and exhausted cursors; actual helper nth-offset
mutation refutes and fails native 129-element tests. Two original zero-size input fixtures now
prove without source changes. Unsupported original leaves, mutable/competing roots, raw sources,
missing bodies and dead backing retain their actual UNKNOWN frontiers. Whole-composite comparison
and size_of_val remain separate boundaries. The shared 70-case/25-family baseline expects
116 PROVED, 104 REFUTED and 60 UNKNOWN across all four configurations.


Stage 153 supports the exact safe core size_of_val API for certified read-only composite slices.
Its selected ordinary body, exact original element type, source lifetime and extent are checked
before computing length times actual compiler stride, including tuple padding. Extent validation
prevents product overflow for nonzero stride; pure zero-byte elements return zero even at MAX
length. No raw descriptor is unwrapped or granted reference validity.

The 22-root host/ARM O0/O2 matrix yields 7 PROVED, 4 REFUTED and 11 UNKNOWN per build. Padded stride,
nested arrays, views, MAX zero-size arrays and actual helper calls pass. Actual size+1 helper
mutation refutes and fails native 129-element tests; unrelated lookalike bodies also refute.
The unchanged earlier size query now proves. Dead backing, missing bodies and unsupported types
retain their actual UNKNOWNs. Raw size and safe alignment controls reach their earlier sized-pointee
cast frontier; this stage supplies no raw or alignment model. The shared 73-case/26-family
baseline expects 120 PROVED, 108 REFUTED and 64 UNKNOWN across the four configurations.


Stage 154 models the exact safe core align_of_val function for certified read-only primitive and
composite slices. Compiler module identity supplies the exact public function; its actual safe
signature and retained body are required. Source lifetime, original element type and descriptor
extent remain checked before returning compiler ABI alignment for empty or zero-byte storage.
Alignment supplies no raw permissions or physical address theorem.

The 21-root host/ARM O0/O2 matrix yields 8 PROVED, 3 REFUTED and 10 UNKNOWN per build, covering
primitive Char/Float, padded tuples, views, nested arrays and aligned zero-sized arrays at MAX
length. Actual helper alignment+1 mutation refutes and fails native 129-element tests. Lookalike
wrong bodies refute; missing bodies, dead backing, unsupported roots, raw calls and deprecated
aliases retain recorded UNKNOWNs. The unchanged prior safe alignment fixture now proves. The
shared 76-case/27-family baseline expects 124 PROVED, 112 REFUTED and 68 UNKNOWN across builds.


Stage 155 supports arbitrary read-only slices of exact local ordinary nonzero structs whose
original pure fields and compiler scalar layout validity are certified recursively. Logical fields
retain exact nominal/declaration identities and independent per-occurrence primitive arrays at the
same index. Physical offset checks share an unchanged neutral helper with trusted storage, without
sharing its assumption or normalization domain. Actual stride includes padding. Constructor-only
policies impose no restrictions on arbitrary valid Rust input values.

The 36-root host/ARM O0/O2 matrix yields 10 PROVED, 5 REFUTED and 21 UNKNOWN per build. Fields,
generics, nested structs, Float/Char, views, cursors, owned-copy mutation and layout pass. False
field relations and constructor invariants refute; actual field-helper mutation refutes and fails
native 129-element tests. Packed layouts, external ADTs, zero-size struct nodes, restricted or
identity-bearing fields, raw access and retired sources retain their actual UNKNOWNs. Whole
membership/equality and ambiguous nested array-of-struct choices remain separate boundaries.
The shared 79-case/28-family baseline expects 128 PROVED, 116 REFUTED and 72 UNKNOWN across builds.


Stage 156 extends exact local struct slice shapes to zero-byte nodes after the same original
field/N=0 and scalar-layout certificates. Zero size requires no actual primitive storage leaves.
Nominal Adt names, tags and ordered fields are retained; unit replacement supplies no success.
The existing full-usize zero-stride domain, source lifetime, selected body and ordered cursor
checks apply equally to aligned zero-sized local structs.

The 29-root host/ARM O0/O2 matrix yields 9 PROVED, 7 REFUTED and 13 UNKNOWN per build. MAX witnesses,
nominal copies, returned fields, methods and actual custom Clone/PartialEq bodies are checked.
A real cursor-offset mutation refutes and fails native 129-element tests. Native MAX copies,
methods and aligned cursors pass; native count is checked on finite inputs. The optional linear
MAX by-reference native count was stopped and is not claimed as completed. Three unchanged prior
zero-struct sources now prove. Unsupported original children, missing bodies, dead backing,
whole comparisons and ambiguous struct choices retain their actual UNKNOWNs. The shared
82-case/29-family baseline expects 132 PROVED, 120 REFUTED and 76 UNKNOWN across builds.

Compiler-typed finite local struct array copies support checked symbolic indices on actual MIR
Copy/Move reads. The original array-prefix type certifies every complete candidate before a
shared-index merge; nominal fields, Float storage bits and valid Char values retain their meaning.
Constant, singleton and solver-unique identity-bearing selection retain their existing paths.
Untyped retained reference projections and ambiguous stores remain unsupported; owned copies add
no raw, alias, custom-method purity or constructor-invariant assumptions.

The compiler-typed owned array choice also accepts exact fixed u8-array descendants. An original
u8 type annotation survives zero length; byte carriers must match constant count and exact
context/sorts before observation. Bytes and Elements are normalized to bounded byte values, with
all candidate byte nodes charged. Canonical copied byte arrays retain shared-index correlation
and local write independence without granting source, raw or retained-reference permissions.


Stage 159 applies the existing pure-field certificates to ordinary dependency structs, including
private, generic, nested, zero-byte and owned byte-containing values. Actual compiler crate and
structural flags keep core and compiler-special wrappers outside this admission. Original field
probes, layout validity, budgets, backing lifetime and actual selected bodies retain their checks.

A real separate dependency rlib matrix yields 10 PROVED, 5 REFUTED and 12 UNKNOWN per host/ARM
O0/O2 build. Rebuilding the same accessor without retained MIR yields MissingCompilerEvidence
UNKNOWN in each profile. Rebuilding an actual dependency getter mutation refutes every profile
and fails native 129-element execution; original native tests pass. Constructor invariants,
method arithmetic and const-generic claims are checked through actual bodies. The shared core-only
88-case/31-family baseline remains unchanged; these dependency controls have their own integration.


Stage 160 supports compiler-typed whole-element symbolic writes to direct owned finite arrays.
Original pure type and scalar layout checks certify all candidates and the replacement, with
unchanged depth/node limits. One index condition selects every leaf of each updated element;
Float bits require both-branch evidence and Char values remain validated. Existing live allocated
owners commit once to the same allocation. Constant and solver-unique writes retain their paths.
Nested projected stores, reference/raw destinations and deferred lazy nominal inputs stay outside
this new writer.

The 21-root host/ARM O0/O2 matrix yields 11 PROVED, 4 REFUTED and 6 UNKNOWN per build. Primitive,
tuple, nested array, byte, struct, Float/Char, sequential and allocated-owner writes are checked.
An actual by-value helper destination-index mutation refutes all four profiles and fails valid
native O0/O2 execution; original native tests pass. The unchanged nominal zero-struct source
remains UNKNOWN because its old candidate is a deferred lazy input, while its replacement retains
nominal identity. The unchanged tuple whole-write source now proves. The shared 91-case/32-family
baseline expects 152 PROVED, 132 REFUTED and 80 UNKNOWN across four configurations.


Stage 161 reconstructs closed zero-observable-leaf deferred owned input products under the exact
original compiler type certificate. Complete descriptor shape, fields, N=0 children, slot/height
arithmetic, seed context and expanded costs are checked before rebuilding nominal values. The
private typed reader and writer share this preparation; generic input observation is unchanged.
No primitive symbols, alias rights, lifetime facts or assumptions are created.

The 19-root host/ARM O0/O2 matrix yields 7 PROVED, 4 REFUTED and 8 UNKNOWN per build. Nominal,
nested, aligned and const-generic copy/write routes, actual marker/Clone/equality bodies and
read-only MAX metadata are checked. Actual marker mutation refutes and fails valid native
O0/O2 execution. The unchanged nominal-zero source now proves; an unchanged nested owned
alignment claim retains its separate intrinsic UNKNOWN. Ordinary scalar-containing deferred
products require an engine-issued source reservation certificate before broader expansion.
The shared 94-case/33-family baseline expects 156 PROVED, 136 REFUTED and 84 UNKNOWN across builds.


Stage 162 adds exact safe sized `core::mem::align_of_val` for primitive and certified pure product
receivers. The actual compiler-resolved public core API, safe shared Rust signature, original
receiver graph and live projection, original type/product metadata and selected body are checked
before returning target ABI alignment. Closed nominal zero-byte inputs retain their exact type
and explicit alignment. Static/raw/mutable handles and unsupported original products remain
conservative; no payload dereference permission follows from layout metadata. Dynamic slice
alignment and existing safe/raw sized size queries retain their separate behavior.

The dedicated 20-root host/ARM O0/O2 matrix yields 10 PROVED, 4 REFUTED and 6 UNKNOWN per build.
Primitive, padded, aligned, generic, copied, incoming shared and caller-backed returned-field
receivers are checked. The original deferred_zero_products nested source now proves across all
four profiles; only its harness expectation changes. Real generic helper result+1 mutations
refute, and valid native original tests pass while mutation guards fail at O0/O2. Raw alignment,
invalid/dead reference formation, opaque traits and unsupported wrappers retain their actual
frontiers. The shared 97-case/34-family baseline expects 160 PROVED, 140 REFUTED and 88 UNKNOWN
across four configurations; no fleet coverage claim follows from that inventory.


Stage 163 adds an Engine-owned ledger of actual lazy input reservations and a shared typed
product preparation module. Root seed, immutable descriptor identity, exact descendant offset
and raw original compiler type certify already reserved symbols before bounded scalar expansion.
The original complete pure root certificate and cumulative 512-node/depth-16 consumer budget
remain separate gates. Copies preserve their symbol correlations; different roots and offsets
stay independent. Closed zero products remain symbol-free, and no generic input observer,
source lifetime, write authority, raw access or input-domain budget is broadened.

The dedicated 21-root host/ARM O0/O2 matrix yields 9 PROVED, 4 REFUTED and 8 UNKNOWN per build.
Actual three-array roots trigger lazy input construction while each requested product stays
bounded. Copy/read/write/alignment correlations, distinct root/field/occurrence refutations and
actual getter mutation are checked. A Float-only lazy product is supported; the original
Float/Char source retains its earlier input-producer budget frontier. The shared 100-case/
35-family baseline expects 164 PROVED, 144 REFUTED and 92 UNKNOWN across four configurations.


Stage 164 supports symbolic Field-path writes within owned array elements certified by original
compiler types. Numbered fields resolve an exact original child type and logical leaf span;
the existing typed product preparation validates the replacement and all complete candidates.
One index condition updates only the affected leaves, preserving untouched values and complete
nominal metadata before committing to the same owned local or live ordinary allocation. Existing
bounds, rvalue effects, destination validators, constant/unique store priority and candidate budgets
remain in force. Retained/raw references, second indexing and call destinations gain no new rule.

The dedicated 27-root host/ARM O0/O2 matrix yields 15 PROVED, 4 REFUTED and 8 UNKNOWN per build.
Named, tuple, generic, nested-field and subtree writes, untouched siblings/indices, sequential
updates, allocated owners, lazy scalar roots, Float/Char and zero-leaf rvalue effects are checked.
Existing typed readers also support direct field observations without a reader change. The
unchanged earlier ambiguous_store source proves in all four profiles before harness maintenance.
Second Index and retained/raw/identity/restricted/resource cases keep their separate frontiers.
A real helper assignment changes left to right; unchanged claims refute and valid original
2-element native inputs pass while mutants fail at O0/O2. The shared 103-case/36-family baseline
expects 168 PROVED, 148 REFUTED and 96 UNKNOWN across four configurations.


Stage 165 extends the certified owned-array destination path with constant nested fixed-array
indices between original Field projections. Actual target-usize literal locals and optimized
ConstantIndex metadata retain original element types, actual bounds and checked logical spans.
The complete original product and all candidate values remain validated before one same-owner
commit. Dynamic nested indices and end-relative projections have no new rule. The shared controls
use actual three-root 64-element arrays. A distinct write-first claim proves, its false claim
refutes, a missing actual replacement body remains UNKNOWN, and the unchanged read-before-write
source remains UNKNOWN at the earlier lazy pure-array reader. No reader rule is introduced.
Before/after evidence is retained; final frozen outcomes and required validation remain pending.

The dedicated 25-root host/ARM O0/O2 matrix yields 13 PROVED, 4 REFUTED and 8 UNKNOWN per build.
Four earlier unchanged constant-index sources now prove across all four profiles before harness
maintenance. The shared 107-case/37-family baseline expects 172 PROVED, 152 REFUTED and 104 UNKNOWN
across four configurations. Required full validation remains pending.


Stage 166 routes deferred pure tuple/fixed-array candidates through the existing typed owned
selection certificate after generic, constant and solver-unique paths. A bounded borrowed search
is only an eligibility hint. Complete original types, existing issued scalar or closed-zero
preparation, scalar representations and cumulative candidate limits remain mandatory before
selection and full product reconstruction. No generic input observer or reference access changes.
The original shared read-before-write source and new repeat-read/root-independence controls are
retained, with final frozen outcomes and required validation pending.

The dedicated 20-root host/ARM O0/O2 matrix yields 9 PROVED, 4 REFUTED and 7 UNKNOWN per build.
The original shared read-before-write source proves, while the longer dedicated source retains
its later borrowed-array comparison frontier. A distinct over-cap observation retains the actual
shape resource limit. The shared 110-case/38-family baseline expects 180 PROVED, 156 REFUTED and
104 UNKNOWN across all four configurations; final frozen validation remains pending.


Stage 167 supports one symbolic nested fixed-array index within the existing owned outer-index
write path. Exact original parent and child types certify homogeneous disjoint logical spans;
joint outer/inner equality masks update only selected leaves. Replacement and complete old values
are flattened once before full reconstruction and same-owner commit. Existing source, bounds,
scalar validity, rvalue effects, candidate/depth limits and single-target behavior remain required.
Two symbolic nested indices and reference/raw/call destinations stay outside this extension.

The dedicated 24-root host/ARM O0/O2 matrix yields 12 PROVED, 4 REFUTED and 8 UNKNOWN
per build. The original earlier dynamic_inner source proves in all four profiles before harness
maintenance. The shared 113-case/39-family baseline expects 184 PROVED, 160 REFUTED and 108 UNKNOWN
across all configurations. Real inner-index XOR 1 mutation refutes unchanged claims in all four
profiles and fails valid two-by-two native controls. Full required validation remains pending.


Stage 168 retains original compiler array evidence with shared owned indexed projections. Actual
MIR issues a bounded type certificate; later reads keep the real owner and revalidate complete
current backing, bounds, scalar context and registered input or closed-zero preparation. New
projection writes, raw address identity and induction remain unsupported. Exact callee and
PartialEq bodies execute normally; type certificates do not summarize comparisons or add rights.

The unchanged earlier long lazy-array read/write and comparison claims independently prove in
all four compiler configurations before their harness expectations are updated. Three new shared
controls yield PROVED, REFUTED and missing-actual-body UNKNOWN in host/ARM O0/O2, with no
assumptions. Frozen before/after commands, hashes and reports remain at
`/tmp/miren-stage168-shared-expanded-before` and
`/tmp/miren-stage168-shared-expanded-after`. Final full validation remains pending.

A custom MIR test exposed an older eager-array return boundary that converted a frame-owned
reference into an owned snapshot. Compiler-correlated returned-reference graph validation now
precedes that conversion; owned-value representation remains separate. Dedicated eager and issued
projection escape controls retain their original claims and require UNKNOWN.


Stage 169 admits a constant or condition-entailed owned outer array index followed by one symbolic
nested index after the older writer reaches its precise unsupported boundary. Original Rvalue
effects and destination checks occur once. Successful byte stores keep their existing path;
unsupported body, permission, solver and resource failures never trigger a successful fallback.
Full original parent and candidate types, bounds, context and complete transaction checks retain
the existing budgets and same owner. Typed references, raw paths and call destinations acquire
no writer. Frozen host/ARM O0/O2 surveys and all required validation pass.
