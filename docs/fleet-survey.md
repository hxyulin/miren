# Fleet workspace survey

## Current repeatable measurement

The thirteenth 2026-10-09 pass collected all 2,336 roots from all 32 ARM library/binary units in
fleet-2027: 1,115 PROVED, 256 REFUTED and 965 UNKNOWN, with no assumptions. All units completed
collection. Counts describe selected root domains, not line coverage or whole-firmware safety.

The source-function heuristic identifies 1,019 declarations: 520 PROVED, 232 REFUTED and
267 UNKNOWN. Refutations concern arbitrary supported root state and remain runtime unconfirmed.

The [current JSON summary](/data/fleet-survey-current.json) records every root, first blocker,
compilation unit and input-integrity evidence. The deterministic exporter recreates this compact
publication from complete raw collections; inventories, solver reports and logs remain local.

- Firmware revision: `26377371e38ed3234f972bcdf6b2f9f4d26a7f02`;
  all 243 source-input fingerprints stayed equal. The existing untracked `rust-project.json`
  remains.
- Full-survey analyzer: `2d183c7`, JSON schema 9; clean working tree, frozen binaries.
- Compiler: nightly-2026-09-22; Z3 4.15.4.
- Target: `thumbv7em-none-eabihf`; dev profile, Cargo default features and locked dependencies.
- Panic abort, enabled overflow checks and root/dependency MIR optimization zero in all 32 units.
- Limits: 8,192 steps, call depth 16, 200,000 query bytes, 30 seconds per root and 5 seconds per
  solver request; four verification workers and sequential Cargo inventories.
- No project proof configuration, startup assumptions, trusted contracts, induction
  or native replay.

Compared with the twelfth pass, referee::ui_number moves UNKNOWN to PROVED without assumptions.
Bounded constant integer choices share exact SMT tables under the existing query-byte limit.
The actual helper completes both CRC8 and CRC16 bodies; ui_delete_all remains PROVED. All previous
1,114 proofs and 256 refutations retain their outcomes. There are no added/removed roots,
incompatible analysis configurations or resource-limit outcome regressions.

Compiler return-type metadata now separates direct future construction from function bodies:

| Root scope | Roots | PROVED | REFUTED | UNKNOWN |
| --- | ---: | ---: | ---: | ---: |
| Function body | 2,232 | 1,065 | 256 | 911 |
| Direct coroutine factory | 104 | 50 | 0 | 54 |

All roots have compiler-backed scope metadata. Among source-heuristic roots, 505 proofs concern
function bodies and fifteen concern future construction. A function-body label can still describe
a generated wrapper; it does not imply execution of a wrapped task. Explicit task polling remains
separate from this function-only collection.

Nineteen source and 455 generated UNKNOWN diagnostics changed only compiler display. Three source
UNKNOWN grouping changes concern solver/step/time budgets without changing outcomes. Raw diagnostics
stay separate from display normalization and proof outcomes.

The constructor checkers share body availability, monomorphized MIR loading, resource caps,
constant return binding and certificate finalization. Their distinct argument/origin policies and
context caches remain explicit. Integer and pointer CAS share ordering and success calculations;
each weak operation retains a fresh possible spurious failure. Integer history and pointer
publication effects remain separate. Fixed byte-view writes now budget generated stores rather than
total allocation capacity. The 128-write ceiling and separate typed-encoding/chunk limits remain.

Numeric MMIO, arbitrary dynamic controller inputs, mutable references and alias constraints,
solver/resource limits, larger byte views and iterator source provenance remain current gaps.
Source, dependency artifacts, origin sidecars and generated build inputs stayed unchanged at all
four recorded checkpoints for every unit. These checks establish input integrity during collection,
not hermetic capture of arbitrary custom build environment variables.

## Progress through Embassy main

The separate [all-main evidence](/data/fleet-embassy-main-current.json) covers every one of the
12 binary mains in three scopes. Its refreshed analyzer is `03e66a2`; the full fleet measurement
above remains frozen at `2d183c7`. Both use the same captured fleet artifacts and default limits.
Factory construction alone does not
execute the async body; `--async-entry` constructs a fresh future and follows its reached polls.

The fresh-future entry milestone is reached in strict Rust: **all twelve application async mains
enter their own coroutine poll bodies**, with no additional assumptions. The compact evidence
retains the exact poll instance, source and factory-rooted call chain. Records are emitted only
after argument validation and a satisfiable start-block path; constructor analysis does not count.
All traces fit the bounded 512-entry budget without truncation. This establishes symbolic entry
from the selected fresh future, independently of subsequent panic or unsupported hardware paths.

| Scope | Strict Rust run | Explicit reset-cause hypothesis |
| --- | --- | --- |
| Async main bodies | 4 REFUTED, 8 UNKNOWN | 12 REFUTED |
| Task registration | 12 PROVED | 12 PROVED |
| Runtime entry | 12 REFUTED | 12 REFUTED |

The conditional first milestone is reached: every expected async main body has a supported outcome
under the recorded policy. The strict milestone remains unreached. Exactly eight DM robot mains
use one trusted `dm_mc02::reset_cause` call each. The
[recorded hypothesis](/data/fleet-main-reset-hypothesis.json) assumes a panic-free, terminating
reset-status boundary returning a valid Rust value, with no caller argument storage modifications.
It does not verify the MMIO access, register values or hardware side effects. The remaining four
mains and all registration/runtime roots use no trusted calls. Policy bytes and per-unit normalized
configurations are fingerprinted and retained in the compact evidence.

Nine bodies refute at `embassy_stm32::Peripherals::take_with_cs` when its singleton flag is true.
The DM bring-up and two sentry bodies refute at the RTT repeated-initialization check. Boolean reads
admit arbitrary valid state, including inside certified core cells; initializer values, writes and
critical sections establish no startup or stable-state history. Counterexamples carry the explicit
abstraction reason and are not confirmed boot-time failures.

The [initialization audit](/data/fleet-initialization-audit-current.json) checks actual source
sites and compiler counterexamples. It finds one board-init call per main, plus a distinct RTT
initialization in three mains. The counterexamples require flags to be true despite their declared
false initializers. These are not confirmed firmware defects: the runtime reset data/BSS path and
its hardware prerequisites are outside the selected Rust root domain. Safe local lifecycle tests
prove fresh initialization and refute a second call, with native mutation checks.

The conditional supported-outcome milestone establishes a failure path in each selected body
domain. Neither milestone establishes complete traversal or safety of every main path, executor
startup, scheduling, waking,
interrupt handling, cancellation, returned-output drops or persistent-loop induction. The eight
strict UNKNOWN bodies still require a Rust-supported reset boundary or a separately specified
conditional hardware model to progress past numeric MMIO.

## Why the main counterexamples appear

The audited failures are state-domain counterexamples, not confirmed fresh-boot failures. The
checker starts at the selected Rust root and admits arbitrary shared state. Z3 does not assume
that initialization has already happened; it chooses already-used resources because the analyzer
has not established reset initialization, exclusive first use or stable shared-state history.

| Selected roots | First stop | Interpretation |
| --- | --- | --- |
| Eight strict DM robot async mains | `reset_cause → Rcc::rsr → ptr::add` | UNKNOWN at numeric MMIO, before reading RCC_RSR |
| DM bring-up and both sentry async mains | RTT repeated-init guard | REFUTED with `INITIALIZED=true` |
| RM-C bring-up async main | Peripheral singleton guard | REFUTED with taken flag true |
| Eight reset-profile DM robot async mains | Peripheral singleton guard | Conditional REFUTED with taken flag true |
| All twelve runtime wrappers | Main-task pool claim followed by unwrap | REFUTED with an occupied task pool |

The MMIO address is RCC at `0x58024400`, then offset `0xd0` for RCC_RSR. Numeric device addresses
supply no Rust allocation provenance. The reset-only profile assumes a terminating panic-free
`dm_mc02::reset_cause` returning a valid ResetCause, with no Rust argument-storage modifications.
It neither grants fresh startup nor assumes that the singleton, RTT or task pool is available.
Its arbitrary reset discriminant does not cause the following singleton panic.

The actual singleton macro declares its flag false, panics when true and then sets true. RTT
uses the same lifecycle in a critical-section `Mutex<Cell<bool>>`. Source inspection found one board
initialization per main and separate RTT initialization in three mains. The existing safe lifecycle
fixture proves fresh single initialization and refutes a repeated call, including native mutations.
Neither lexical call counts nor declared initializers prove that the captured shared state is fresh.

Runtime entry fails earlier than task spawning: `embassy-executor-macros` main expansion unwraps
`__embassy_main(spawner)` before calling `spawner.spawn(main_task)`. Task allocation calls
`State::spawn`; failed pool claim returns `SpawnError::Busy`, and unwrap panics. The model's old CAS
word is `v1`; `v0` is an abstract compiler-backed static address, not a task flag.

The original runtime witness uses `0xffffffff`, which exceeds values produced by safe AtomicBool
operations. Pinned core represents AtomicBool through byte storage, so compiler layout validity
alone does not establish its safe-library boolean encoding invariant. Silently imposing that
invariant would require additional history or effect evidence. The broad word is unnecessary:
adding `v1=0x101` to each captured runtime panic query still yields SAT for all twelve wrappers.
This word represents spawned/run-queued true with both padding flags false, and is produced by a
prior successful claim. A registration-wrapper proof establishes panic freedom even when allocation
returns an error; it does not establish successful allocation. The
[audit manifest](/data/fleet-main-failure-audit-current.json) records source, original/constrained
query, model and capture hashes; queries and models remain local.
This check validates an arbitrary-history busy candidate, not native boot reachability.

Under a correctly initialized, exclusive first-use premise, these repeated-init/busy candidates
would be spurious for fresh boot. That premise remains unverified. Existing REFUTED outcomes are
therefore retained and explicitly scoped; they do not prove traversal or safety after the first
counterexample. The next semantic step requires recorded startup and exclusion evidence before
initial values or writes can constrain subsequent shared reads. Strict hardware boundaries remain
UNKNOWN without a Rust-supported access model.

Separate diagnostic replays at `80030b0` use the user-selected `--startup-isolated` premise: fresh
Rust statics and no external task, thread or interrupt mutation of tracked Rust storage throughout
the entry, including after publication. Actual typed stores and pointer atomics pass the queue
guard. Checked weak-CAS returns continue while unfinished retries retain UNKNOWN. All twelve runtime
wrappers enter the actual `__pender` body and stop at its bare `SEV` assembly before the first poll.
No hardware instruction is skipped or MMIO validity assumed. These conditional diagnostics do not
change the ordinary full-survey or published fresh-future main outcomes.

## Earlier repeatable measurements

The eleventh 2026-10-09 pass at analyzer `d45d34f` collected 2,336 roots: 1,113 PROVED,
256 REFUTED and 967 UNKNOWN. Its source-function heuristic was 518/232/269. Fixed short byte writes
pass the 136-byte referee buffer limit; private encode reaches the audited oversized-payload
refutation, excluded by its intended 127-byte domain. Both UI helpers reach CRC16 query limits.

The tenth 2026-10-09 pass at analyzer `2169311` collected 2,336 roots: 1,113 PROVED,
255 REFUTED and 968 UNKNOWN. Its source-function heuristic was 518/231/270. Ordered for_each clears
two controller traversal blockers and reaches audited Chassis/Arm refutations under arbitrary root
state. Constructor/history invariants exclude those witnesses; application reachability remains
unverified.

The ninth 2026-10-09 pass at analyzer `80030b0` collected 2,336 roots: 1,113 PROVED,
253 REFUTED and 970 UNKNOWN. All outcomes matched the eighth pass. Its source-function heuristic
was 518/229/272. The tenth pass adds the two audited iterator refutations above.

The eighth 2026-10-09 pass at analyzer `a65192d` collected 2,336 roots: 1,113 PROVED,
253 REFUTED and 970 UNKNOWN. Its source subset had 518 proofs, 229 refutations and 272 unknowns.
All outcomes matched pass seven. Shared constructor validation and integer/pointer CAS calculations
were refactored without granting new semantics. Nineteen source and 455 generated UNKNOWN
diagnostics changed only compiler display.

The seventh 2026-10-09 pass at analyzer `c908598` collected 2,336 roots: 1,113 PROVED,
253 REFUTED and 970 UNKNOWN. Its source subset had 518 proofs, 229 refutations and 272 unknowns.
Dr16::parse gained a body proof. Sentry Can1Bus::receive refuted for arbitrary ESC ID 65024,
overflowing checked 512 + esc_id; its constructor uses IDs 2, 1, 4 and 3, so firmware reachability
and native confirmation remained unverified. Seventeen DMA helpers cleared missing STATE origins
and reached numeric MMIO; three encoding helpers reached byte-view limits and two iterator callers
reached retained-source liveness. No future factory gained a proof. A missing local trait-constant
body query was guarded after its incomplete capture was preserved separately. Main outcomes stayed
unchanged under the exact eight-call reset-only hypothesis.

The sixth 2026-10-09 pass at analyzer `901304a` collected 2,336 roots: 1,112 PROVED,
252 REFUTED and 972 UNKNOWN. Its source subset had 517 proofs, 228 refutations and 274 unknowns.
Five ordinary helpers, eleven async future factories and twelve generated wrappers gained proofs.
The private referee interaction helper refuted for arbitrary 20-byte content in a 21-byte buffer
with a six-byte header; its two current callers provide two or fifteen bytes. Firmware reachability
and native confirmation were not established. Twenty-nine source roots reached different blocker
keys and nineteen changed only compiler display. Strict/reset main outcomes remained unchanged.

The fifth 2026-10-09 pass at analyzer `fe25949` collected 2,336 roots: 1,084 PROVED,
251 REFUTED and 1,001 UNKNOWN. Its source subset had 501 proofs, 227 refutations and 291 unknowns.
Nine axis/loader/wheel constructors gained proofs. Twenty source roots cleared enum or volatile
barriers but remained UNKNOWN. Main captures retained four strict refutations, eight strict
unknowns and twelve conditional refutations under the recorded reset-only profile.

The fourth 2026-10-09 pass at analyzer `d94334c` collected 2,336 roots: 1,075 PROVED,
251 REFUTED and 1,010 UNKNOWN. Its source subset had 492 proofs, 227 refutations and 300 unknowns.
All twelve generated registration wrappers gained proofs, and `rm_c::init` refuted under arbitrary
singleton state. Separate main captures at `7257e00` included certified core boolean cells and
reached the conditional milestone under the same eight reset-cause assumptions.

The third 2026-10-09 pass at analyzer `efe9d66` collected 2,336 roots: 1,063 PROVED,
250 REFUTED and 1,023 UNKNOWN. Its source subset had 492 proofs, 226 refutations and 301 unknowns.
Two encoding helpers gained proofs through retained typed byte slices. Its two async-body probes
remained UNKNOWN at critical-section foreign calls and reset-cause MMIO respectively.

The second 2026-10-09 pass at analyzer `90170db` collected the same 2,336 roots: 1,061 PROVED,
250 REFUTED and 1,025 UNKNOWN. Its source subset had 490 proofs, 226 refutations and 303 unknowns.
Five previous unknown source functions proved through compact byte repeats and exact byte-to-float
casts; all earlier proofs and refutations retained their outcomes. Another 20 source functions
cleared their first blocker but stayed UNKNOWN: ten UART/DMA helpers, five encoding helpers,
two board initializers, two USB constructors and referee encoding. The compact comparison retained
source diagnostic transitions and counted generated transitions without publishing their large
texts; all four artifact checkpoint maps stayed unchanged.

The first 2026-10-09 pass at analyzer `5a2fe83` collected the same 2,336 roots: 1,056 PROVED,
250 REFUTED and 1,030 UNKNOWN. Its source subset had 485 proofs, 226 refutations and 308 unknowns.
Checked dependency-origin metadata resolved 57 previous unknown source functions: 28 proved and
29 refuted. All 1,028 earlier proofs and 221 refutations retained their outcomes. Constructor
origin records establish provenance, not runtime atomic values or verified callee contracts.
Tracked pointer offsets passed host/ARM mutation tests but added no fleet proofs because all
45 offset blockers used numeric MMIO addresses. That scan stored three artifact checkpoint maps
and enforced a pre-verification comparison; the second pass stores all four maps explicitly.

The complete 2026-10-08 baseline had 1,028 proofs, 221 refutations and 1,087 unknown roots.
It followed a partial pre-guard run in which 13 units crashed on unavailable dependency CTFE MIR.
The guard recovered collection without inventing origin evidence, adding 556 proofs and
171 refutations to that partial baseline.

## Historical 2026-10-06 survey

On 2026-10-06, miren checked the unchanged fleet-2027 shared libraries, DM-MC02 board/robot
workspace and RM-C board workspace for `thumbv7em-none-eabihf`. After adding floating point,
symbolic enum inputs, dependency-defined inputs, array patterns, dependency MIR retention and
aggregate constants, it proves 293 of 976 function roots, up from 25 in the original baseline.
It cannot yet prove entire mutable control loops or firmware applications.

## Coverage change

All four scans use the same 32 ARM compilation units, firmware, pinned compiler, root profiles
and source-span classification. The first expansion adds input/operation support. Dependency
retention then rebuilds Cargo dependencies with ordinary bodies encoded at MIR optimization level
zero. Their metadata paths and retention flags differ; root MIR optimization remains level zero.
The constant expansion reuses the dependency-retaining inventory and compiler arguments.

| Function declarations | Original (`07f1412`) | Input expansion (`af829e4`) | Dependency retention (`0dc7551`) | Constants (`55d9dd3`) |
| --- | ---: | ---: | ---: | ---: |
| PROVED | 25 | 149 | 196 | 293 |
| REFUTED | 25 | 46 | 71 | 74 |
| UNKNOWN | 926 | 781 | 709 | 609 |
| Total | 976 | 976 | 976 | 976 |
| Proved fraction | 2.6% | 15.3% | 20.1% | 30.0% |

Dependency retention turns 47 previous unknowns into proofs and 25 into refutations. All 149
previously proved and all 46 previously refuted function roots retain their outcomes. Aggregate
constants then add 97 proofs and three refutations, preserving all 196 proved and 71 refuted
outcomes. Across the expansions, 268 original unknowns now prove and 49 now refute.

These are root-domain proofs, not line coverage or the fraction of firmware safety established.
The original and intermediate measurements remain available:

- [Original baseline data](https://hxyulin.github.io/miren/data/fleet-survey.json).
- [Input expansion data](https://hxyulin.github.io/miren/data/fleet-survey-expanded.json).
- [Retained MIR data](https://hxyulin.github.io/miren/data/fleet-survey-dependency-mir.json).
- [Aggregate constant data](https://hxyulin.github.io/miren/data/fleet-survey-constants.json).

The new data records per-unit counts, outcome transitions and the first reported unknown reasons.

## Scope and configuration

- Firmware revision: `b81a247a3295b13553087f5e328f201944a1eb61`.
- Analyzer implementation: `55d9dd3`, JSON schema 7; previous `0dc7551`, `af829e4`,
  original `07f1412`.
- Compiler: nightly-2026-09-22, rustc commit `1303417c416e1595173d9689e7394c31e136ae95`.
- Target: `thumbv7em-none-eabihf`, panic strategy abort, overflow checks enabled.
- Profiles: shared workspace dev; board workspaces dev with their configured optimization level 1.
- Cargo defaults and locked dependencies; shared workspace excludes the host-only xtask.
- Cargo dependencies rebuilt with always-encode-mir enabled and MIR optimization level zero.
- Prebuilt sysroot libraries are not rebuilt; dependency roots are not independently inventoried.
- No firmware annotations, new dependencies, source changes or unchecked contract assumptions.

These are development-profile analysis results under the checker's pinned compiler, not proofs
of the stable compiler's release binaries. Inventory ran from each workspace root with the target
explicitly supplied. Firmware-directory runner/linker/CPU flags were not selected; those flags
and release overflow settings require separate measurements. MIR optimization remains at the
checker's level 0.

## All inventoried roots

| Workspace scope | ARM compilation units | MIR roots | PROVED | REFUTED | UNKNOWN |
| --- | ---: | ---: | ---: | ---: | ---: |
| Shared libraries | 7 | 1,087 | 522 | 47 | 518 |
| DM-MC02 board, bring-up and ten robot firmwares | 23 | 1,192 | 291 | 27 | 874 |
| RM-C board and bring-up | 2 | 57 | 2 | 0 | 55 |
| Total | 32 | 2,336 | 815 | 74 | 1,447 |

These are independently checked roots, including closures, derives and macro-generated methods.
Host build scripts and third-party dependency roots are excluded. Shared path dependencies are
inventoried in their own workspace rather than counted again for each board. Their independently
selected root results therefore use the shared workspace's default features; board-specific
dependency features can differ. An available dependency body is still executed with actual
arguments when a board root reaches it.

The raw success rate is 34.9%, but that overstates useful application coverage. For example,
zerocopy generates many empty marker methods that prove trivially.

## Function declarations without closures or derives

To expose that skew, this table counts roots whose reported source line contains a function
declaration, excluding names containing `{closure#`. This is a source-span filter, not a full
AST classification. It includes handwritten trait methods and instantiated methods emitted from
local function-declaring macros. Separate compilation units remain separate roots.

| Scope | Function roots | PROVED | REFUTED | UNKNOWN |
| --- | ---: | ---: | ---: | ---: |
| Shared libraries | 436 | 108 | 47 | 281 |
| DM-MC02 workspace | 523 | 185 | 27 | 311 |
| RM-C workspace | 17 | 0 | 0 | 17 |
| Total | 976 | 293 | 74 | 609 |

The current success rate for this subset is 30.0%. It is a count of function roots under arbitrary
supported inputs, not line coverage, runtime branch coverage or a fraction of firmware safety.

| Shared crate | Function roots | PROVED | REFUTED | UNKNOWN |
| --- | ---: | ---: | ---: | ---: |
| attitude | 19 | 5 | 0 | 14 |
| can-frame | 9 | 6 | 2 | 1 |
| controller | 20 | 5 | 0 | 15 |
| devices | 216 | 60 | 44 | 112 |
| link | 11 | 4 | 1 | 6 |
| subsystems | 156 | 28 | 0 | 128 |
| validate | 5 | 0 | 0 | 5 |

## Useful positive results

The actual `devices::dr16::Raw::parse` proves with 43 obligations, seven interpreted bodies and
no declared entry assumptions. Every valid byte slice is in its domain. This establishes panic
freedom; the original function has no annotations asking for decoded-value postconditions.
The separate [vendored fixture](examples.md#dr16-parsing) adds and verifies those postconditions.

Other passes include both CAN constructors and ID getters, `dr16::Switch::from_wire`,
`link::EngineerMode::from_wire`, `link::Flags::from_bits`, the link bit helper, several integer-only
motor constructors and small state/default helpers. The expanded scan adds PID/filter
constructors, IMU temperature conversion, RPM/radian conversions, motor feedback state readers,
attitude getters and subsystem validation/state helpers.

Board and robot passes now include the four gimbal boards' `shooter::update` functions, the
engineer lower board's `chassis::mecanum`, hardware velocity readers, gimbal deadbands and several
leg/mode readers. The shooter policy accepts arbitrary supported `Option` target/remote values,
checks the remote switch, maps two RPM values and returns spin or stop. The result establishes
panic freedom; the unannotated function has no policy postcondition to verify. These passes
require floating point, enum payloads and types defined in shared dependency crates. They do not
prove the mutable PID updates that consume the returned commands. Existing `Gripper::new`, its
handwritten default implementation and `Text::is_empty` passes remain.

Retained dependency bodies add 47 function passes, all in board/robot workspace units. These include
`arm::pid`, `head::cascade` and `head::pid` on the engineer upper board, chassis/gimbal/shooter PID
configuration helpers across the robots, CAN bus constructors and `wired`/supercap readers,
`UserIo::open` and flash instruction construction. They execute actual shared constructor bodies; no
helper annotation or previous independent proof is used as a trusted call summary. The PID
configuration helpers construct controllers; they do not execute mutable controller updates.

Aggregate constants add 24 shared and 73 board/robot proofs. New shared passes include 20 motor
feedback accessors, `link::from_raw` and three balance-state `done` helpers. Board passes include
engineer upper `arm::command` and `Head::new`, gimbal/shooter controller constructors, shooter
target selection, CAN bus readers and hardware joint/wheel helpers. They execute actual retained
bodies with decoded constant fields; the engine does not infer a library summary.

A fresh Cargo verification of hero chassis `gimbal::controllers` and `shooter::target` also proves
both selected roots on ARM, interpreting eight distinct instances across their reports. This
checks the ordinary Cargo path as well as the survey's direct-driver replay.

The constructed CAN payload and bus-configuration fixture proofs remain stronger targeted
examples than whole-crate scanning: a caller supplies useful relationships that an arbitrary
independent struct input does not have.

## What refutations mean here

The 74 refuted roots are failures over their unconstrained root domains, not 74 confirmed
firmware defects. They identify assumptions worth expressing and checking at callers:

- CAN and referee data accessors, console `Line::as_str` and `Text::as_bytes` need stored lengths
  within buffer capacity. Private fields currently acquire arbitrary symbolic values; the
  checker does not infer constructor-preserved type invariants.
- Several motor constructors intentionally panic on invalid IDs. Their useful guarantee is
  conditional on accepted ID bounds or a caller that constructs a valid configuration.
- `motor::received_tick` requires a nonzero `period_us`, as its existing documentation states.
  A root over arbitrary u32 values includes zero and refutes division safety.
- `dji_uses` and referee `frame_len` have arithmetic obligations that require input bounds.
- Three chassis `count` helpers can overflow before their final clamp for arbitrary i32 values.
  Proving their actual callers requires the state/count bounds maintained by the control loop.

Dependency retention exposes 25 additional refutations: seven shared roots and eighteen
board/robot roots. Most board cases reach motor-ID arithmetic through CAN bus `uses` methods with
arbitrary stored IDs. Shared decoder cases reach byte-prefix bounds with arbitrary frame lengths.
These are additional caller/type-invariant assumptions to check, not confirmed runtime failures.

Constants expose three additional bounds refutations in engineer lower `hardware::joint`,
engineer upper `hardware::joint` and `hardware::joint_current_a`. Their root domains include
arbitrary array indices; useful caller guarantees need explicit accepted-index bounds.

Solver assignments concern translated obligations. Runtime replay or caller analysis is needed
before treating one as a reachable defect. The survey did not modify firmware or add replay tests.

## Remaining blockers

For each unknown function root, the following table classifies its first unknown obligation in
report order. This gives mutually exclusive counts, rather than adding every gap reported for a
root. It is not an exhaustive list of a function's needs.

| First reported blocker | Original roots | Input expansion | Dependency retention | Constants |
| --- | ---: | ---: | ---: | ---: |
| Mutable inputs | 263 | 300 | 300 | 300 |
| Floating-point inputs | 159 | 0 | 0 | 0 |
| Other input shapes | 378 | 25 | 25 | 25 |
| Input shape limits | 4 | 44 | 44 | 44 |
| Missing dependency MIR | 34 | 237 | 16 | 17 |
| Constants | 61 | 108 | 194 | 69 |
| Other MIR/library/solver behavior | 26 | 66 | 129 | 147 |
| Execution limits | 1 | 1 | 1 | 7 |
| Total UNKNOWN | 926 | 781 | 709 | 609 |

Counts can rise when an earlier blocker disappears. There are no previous proved/refuted roots
that regressed to unknown. The main remaining work is:

- **Mutable state:** inputs such as `&mut Pid`, balance components, operator state and hardware
  buses need writes and alias relationships to be modeled. A useful first step is owned state or
  a single nonescaping mutable receiver with explicit alias limits. Treating it as a read-only
  snapshot would not prove the real update.
- **Remaining missing bodies:** eleven roots first stop at prebuilt core's `option::unwrap_failed`,
  five at the platform critical-section foreign acquire function, and one at `core::convert::From`.
  Cargo retention cannot supply foreign implementations or bodies omitted from prebuilt sysroot
  metadata. A missing body remains unknown, even when its name suggests a panic helper.
- **Constants and mutable storage:** the 54 `Option::as_ref` first blockers are resolved. Of 69
  remaining constant first blockers, 51 reject references to interior mutable storage, often
  `validate::Site` atomic counters. Nine reach MaybeUninit, six exceed array limits, two involve
  raw pointers and one is a closure constant. These require additional semantics or explicit
  budgets; uninitialized storage cannot be replaced with initialized values.
- **Input limits and pointer/effect operations:** larger arrays or nested hardware shapes exceed
  current budgets. Raw pointers, slice iterators, projected writes, atomics and async machinery
  need additional models. Raising a budget alone does not solve missing semantics.

Floating-point remainder, bit observation and some math functions remain unsupported despite
float inputs now being modeled. Type invariants and verified caller bounds would also turn
several unconstrained root refutations into meaningful conditional checks. Loop invariants and
hardware/async effects remain separate work.

## Measurement procedure and cost

New measurements use the
[repeatable survey runner](https://github.com/hxyulin/miren/blob/main/tools/README.md).
It discovers workspace
library and binary units, completes inventories before verification, and checks units independently:

```sh
python3 tools/fleet_survey.py /path/to/fleet-2027 --output /tmp/fleet-survey-001 \
  --solver "$PWD/.venv/bin/z3"
```

Use a fresh output directory and `--previous /tmp/fleet-survey-001/summary.json` for a later
comparison. The runner freezes analyzer binaries, restores recorded Cargo source inputs, and retains
missing units and compiler failures as partial collection. Exit zero means every unit's results
were collected, including REFUTED and UNKNOWN; it does not establish whole-firmware safety.
The measurements above are historical and are not automatically updated by this command.

First inventory each complete workspace, because verification failures can prevent Cargo from
building dependent crates. From the relevant workspace root:

```sh
# Root workspace: all seven embedded shared libraries.
/path/to/miren/target/release/cargo-miren --summary \
  --workspace --exclude xtask --lib --target thumbv7em-none-eabihf --locked

# bsp/dm-mc02 and bsp/rm-c: library and binary targets of their members.
/path/to/miren/target/release/cargo-miren --summary \
  --workspace --target thumbv7em-none-eabihf --locked
```

Next invoke the direct driver's `--json --verify --` mode for each ARM report's recorded
`rustc_arguments`, from the same working directory and with Cargo's `CARGO_CRATE_NAME` restored.
The survey used four parallel compiler processes. Every replay reproduced the original
inventory's names, source spans and arguments. The direct driver stops after analysis; it does
not execute the firmware.

The dependency-retaining inventory builds took 13.5, 17.5 and 14.7 seconds, run concurrently.
Verification of the 32 already-built units took about 11 seconds in the original baseline,
35.4 seconds after input expansion, 63.8 seconds with retained dependency bodies, and 81.3 seconds
with aggregate constants on an Apple M3 Pro. The constant scan reuses the retained inventory.
The later runs execute more paths that previously stopped at input construction or calls.
Many roots still return UNKNOWN early, so this is not an estimate for full-firmware proof time.
Larger supported symbolic roots can cost much more.

The [latest JSON summary](https://hxyulin.github.io/miren/data/fleet-survey-constants.json)
records per-unit counts, source classification, changed roots and first-gap reasons. Raw solver
reports and build outputs remain local measurement artifacts. No entire workspace passed
verification; every scope still contains unsupported or refuted roots.
