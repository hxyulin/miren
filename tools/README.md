# Fleet survey runner

`fleet_survey.py` inventories every workspace library and binary target discovered beneath a fleet
checkout, excluding the host-only `xtask`. It skips `target`, `.git`, virtual environments and
Node dependencies. Pinned Cargo metadata supplies workspace membership and expected units;
metadata failures and missing units remain visible. Dependency and build-script roots are outside
this scope. Counts describe independently selected MIR roots, not line or firmware safety
coverage.

Build miren's release binaries first, with its pinned compiler and solver available. The runner
copies the analyzer and available sibling binaries into the output directory before inventory;
concurrent release rebuilds cannot replace queued verification binaries. From this checkout, use a
new output directory for every run:

```sh
python3 tools/fleet_survey.py /path/to/fleet-2027 --output /tmp/fleet-survey-001 \
  --solver "$PWD/.venv/bin/z3"
python3 tools/fleet_survey.py /path/to/fleet-2027 --output /tmp/fleet-survey-002 \
  --previous /tmp/fleet-survey-001/summary.json
```

The runner completes sequential Cargo inventories before starting bounded parallel direct-driver
verification. Verification failure in one unit cannot stop another unit. `--jobs` defaults to
four. Use `--analyzer`, `--cargo`, `--target`, `--profile`, `--features`, `--build-timeout`,
`--unit-timeout` and the five miren analysis-limit flags to select a configuration. Defaults use
ARM, dev, Cargo's default features and miren's conservative execution limits. Startup assumptions,
trusted contracts, induction and native counterexample execution are disabled. Inventory passes
`--no-config` so a fleet `miren.json` cannot change survey selectors or verification settings.

`summary.json` starts as partial and is replaced atomically as results arrive. A complete survey
means every expected unit was inventoried and its results collected, even if some roots refute or
remain unknown. Exit zero means complete collection, not a complete proof. A partial run exits
one; missing units are listed even when no roots could be recovered. Crashed, missing, malformed
or mismatched reports never count as proved. Raw inventories, verification JSONL, command records,
stdout and stderr remain in the output directory. Existing output directories are rejected.

Replay restores the report's captured compiler working directory and Cargo compiler environment.
Older inventories without environment capture are rejected for proof counting. The compiler
capture covers Cargo package/features/configuration variables, manifest and crate identity,
`OUT_DIR` and `DEP_*`; arbitrary custom environment inputs outside that capture are not guaranteed
reproducible. The runner fingerprints explicit compiler dependencies, transitive metadata and
proc-macro candidates in dependency search directories, adjacent `.rmeta.miren-origins.json`
sidecars (including their absence), generated `OUT_DIR` files and native search-directory inputs.
It checks these immediately before and after each unit's verification and again at completion.
Changed, added or missing inputs invalidate that unit's proof counts and leave collection partial.
Dependency/build traversal is limited to 100,000 files per unit. These are integrity checks on
live Cargo artifacts; the artifacts are not copied into the survey output. No application source
is rewritten. Cargo may download dependencies and refresh its analysis cache.

Provenance includes source revisions and dirty paths, analyzer binary hash, compiler/solver
versions, original/frozen binary hashes, source/build file hashes, target, profile, feature
request, limits and command logs. Source contents are hashed again at completion; changes
invalidate every collected proof even when Git's dirty paths remain the same. Diffs list added,
removed and changed root outcomes, using workspace/package/target/function identity so source line
shifts do not rename roots. They flag incompatible analysis configurations; compiler/environment
changes and generated-name changes still need review. Source function counts use a source-line
`fn` heuristic excluding closures; other generated roots remain separate. This classification is
not an AST coverage claim.

Run the standalone tests without compiling Rust:

```sh
python3 -m unittest discover -s tools -p 'test_*.py'
```

To publish a completed measurement, export its validated full summary:

```sh
python3 tools/fleet_survey_export.py /tmp/fleet-survey-002/summary.json \
  --output /tmp/fleet-survey-compact.json --measured-on 2026-10-09 \
  --previous /tmp/fleet-survey-001/summary.json
```

The exporter rejects partial or inconsistent current collections, missing roots, duplicate
identities, count mismatches, failed unit/workspace collection and changed source/artifact
evidence. It preserves every root through the existing schema-1 `root_columns`, sorted unit, file
and blocker tables, plus counts and source classification. The explicit measurement date is
required; it is not inferred from file timestamps. An optional previous full summary records
baseline counts, unit failures, outcome transitions, added/removed roots, previously proved
regressions and incompatible configurations. The previous collection may be partial, with its
status preserved in the comparison.

Comparisons also split transitions by both previous and current source classification, so a
changed source-span heuristic cannot appear as a proof gain. Changed first blockers on roots
that remain UNKNOWN are counted separately: clearing one unsupported operation can reveal another
without changing the root's outcome. Blocker text remains diagnostic evidence, not a stable
semantic category or a claim that later paths are supported.

All UNKNOWN first-blocker text changes are counted by previous/current classification. Detailed
text transitions cover roots classified as source functions in either collection, with that scope
explicit in the output; generated closure diagnostics can be very large and remain in the raw
reports. Compiler crate hashes and debug-type ordering can change without semantic progress, so
text changes alone do not establish that an unsupported operation was resolved. Null and empty
blockers retain distinct, deterministic ordering.

Compact provenance stores source and artifact aggregate SHA256 fingerprints instead of all
artifact paths. Artifact checkpoint coverage is explicit: older surveys have no artifact evidence
and report null for its fingerprint/unchanged flag; surveys recorded before pre-verification maps
were retained can report inventory, post-verification and completion checkpoints only. Unrecorded
compiler settings are not inferred from the target name. Export uses a deterministic atomic
replacement and changes no application code or documentation data automatically.

## Embassy main body survey

`fleet_main_survey.py` replays every exact Embassy main factory in the binary units of a complete
fleet survey. It verifies inventory identity and root completeness before selecting mains. Build
release binaries first, then use a new output directory:

```sh
python3 tools/fleet_main_survey.py --survey /tmp/fleet-survey-002/summary.json \
  --output /tmp/fleet-main-001
```

Each binary has three separately recorded roots: `async_body` selects
`____embassy_main_task::____embassy_main_task_inner_function` with `--async-entry`;
`task_registration` selects `__embassy_main`; `runtime_entry` selects `__cortex_m_rt_main`.
Async analysis constructs the fresh future and follows reached polls. Factory construction alone
cannot establish body coverage. Task registration does not poll deferred futures, and runtime
wrapper inputs describe arbitrary root state. Runtime wrapper counterexamples do not establish
reachable boot panics. Scheduling, startup history, cancellation, output drops and persistent-loop
induction remain outside the body scope.

`--unit` accepts exact unit identities and can be repeated for smaller probes. The output preserves
both expected and selected unit identities; a subset never satisfies the full-main milestone.
`--analyzer`, `--unit-timeout` and the five analysis-limit flags allow explicit configuration.
Every replay retains captured Cargo compiler arguments and environment while clearing ambient
miren policies. Startup assumptions, induction and native replay are disabled. Trusted contracts
and configured root preconditions require the explicit profile options below.
The analyzer is frozen before use. Source and dependency/generated-artifact fingerprints must
match the input survey and remain unchanged before, after and at completion.

Raw JSONL, command logs, stdout and stderr accompany `summary.json`. Missing wrapper bodies,
malformed reports, configuration changes, timeouts and process failures become failed UNKNOWN
collections. A partial collection exits one. A complete collection exits zero even if roots remain
UNKNOWN. `milestone_reached` requires complete coverage of every expected async body with an
unconditional PROVED or REFUTED result; outcomes of the other scopes cannot substitute for it.
This milestone describes analyzer outcomes under the recorded root domains, rather than verified
firmware boot behavior. Each root includes `analysis_domain`, `boot_reachability: unverified` and
`counterexample_evidence`. A refuted obligation with recorded abstractions is labeled
`abstract_model_counterexample`; other refuted obligations are `solver_counterexample`.
Neither label confirms a native panic or a reachable reset-to-main execution. Mutable-static
initialization guards can fail for an arbitrary incoming `true` flag even when their declared
initializer is `false`; establishing fresh boot state requires separate startup and interference
evidence. Failed collections retain no active counterexample evidence.

`fresh_future_entry_milestone_reached` separately records whether every expected application
async main actually entered its coroutine poll from the selected fresh-future factory. Each
async root includes `application_body_reached`, derived from the analyzer's feasible `body_entries`
records for the pinned compiler's exact factory `::{closure#0}` poll with the factory as the
call-chain root. Constructors, nested coroutines, inventory and `analyzed_bodies` cannot establish
entry; older reports without these records and truncated traversal records remain false. Full scope,
complete unit collection and unchanged source/artifact checkpoints are required. An UNKNOWN or
REFUTED
outcome can still record a reached application body. This entry milestone establishes neither
panic freedom, runtime traversal to the first poll or hardware boot reachability. It adds no
assumptions.

An assumption profile is opt-in and applies only to `async_body`; task registration and runtime
wrappers remain strict. Supply both flags:

```sh
python3 tools/fleet_main_survey.py --survey /tmp/fleet-survey-002/summary.json \
  --output /tmp/fleet-main-conditional-001 --allow-assumptions \
  --assumptions-profile /path/to/main-assumptions.json
```

The profile has `schema_version: 1` and a `units` object mapping exact known unit identities to
ordinary schema-1 miren contract configurations. Omitted units remain strict. Unknown unit keys are
rejected. `--unit` subsets can use a profile containing other known units without extending
coverage.
Alternatively, `--contracts FILE --allow-assumptions` applies one contract configuration to every
selected async body. The two profile forms are mutually exclusive. A contract selector that is
unused in a body can cause the analyzer to fail that collection; per-unit configurations avoid
mixing selectors for different boards.

The full input file is snapshotted byte for byte with a SHA256 hash. Normalized per-unit contract
snapshots, selected profiles and final source/snapshot hashes remain in the result. Changed policy
files or snapshots invalidate collected outcomes. Reports must contain the exact normalized
configuration. Every trusted call must match an explicitly trusted configured contract and its
instance selector, and root preconditions must match the recorded root configuration. Startup or
induction metadata remains rejected even with these flags.

Each collected root records `conditional` from its actual assumptions and trusted calls, including
REFUTED or UNKNOWN results that used a hypothesis. PROVED with configured preconditions is also
conditional even when the analyzer's status label is PROVED. Such outcomes cannot satisfy
`milestone_reached`. `conditional_milestone_reached` records the separate opt-in milestone only
when every expected async body has a collected PROVED, PROVED_WITH_ASSUMPTIONS or REFUTED result
with explicit conditional labels. UNKNOWN and incomplete or subset collections satisfy neither.
These profiles are hypotheses, not verified hardware models; the runner creates none automatically.

The repository also supplies explicit device-specific initialization hypotheses:

- `docs/public/data/fleet-main-stm32h7-hypothesis.json`: STM32H723VG DM-MC02 boards.
- `docs/public/data/fleet-main-stm32f4-hypothesis.json`: STM32F407IG RM-C boards.
- `docs/public/data/fleet-main-stm32-hypothesis.json`: the combined exact-unit policy.

Use the combined file with `--assumptions-profile` and `--allow-assumptions` as above. These
are manually selected trusted function boundaries, not a built-in emulator or a register model.
The device and board clock premises are recorded in every contract reason. ST documents these
variants in [RM0468](https://www.st.com/resource/en/reference_manual/dm00603761.pdf) and
[RM0090](https://www.st.com/en/microcontrollers-microprocessors/stm32f4-series/documentation.html).

The HAL initialization boundary assumes a successful first singleton claim, the supplied board
clock configuration, accessible hardware and completion of hardware-ready waits. This boundary
includes software initialization and is stronger than MMIO validity alone. It does not verify
clock setup or preserve the singleton guard as an analyzed check. Its `modifies` field is omitted:
the existing summary mechanism conservatively invalidates tracked Rust storage instead of
claiming initialization leaves statics unchanged. Unsupported returned ownership/alias shapes
remain UNKNOWN. The separate H7 reset-status boundary preserves the existing narrower policy.
There are no postconditions fixing observed register/reset values, no generic peripheral-address
allowlist and no assumed executor progress, SEV semantics or interrupt scheduling. Registration
and runtime scopes remain strict. Changing a device feature requires reviewing the corresponding
profile; a contract reason is an assumed device identity, not detection of physical hardware.

The initial combined replay on all twelve mains completes collection: three async bodies retain
unconditional RTT lifecycle refutations before HAL initialization, and nine are conditional
UNKNOWN after the initialization boundary. Eight H7 bodies reach GPIO Output::new for PC15;
the F4 body reaches LED GPIO initialization. All nine stop at Gpio::bsrr numeric pointer
arithmetic. Twelve registration roots remain PROVED and twelve ordinary runtime roots remain
REFUTED. This clears initialization traversal under the listed hypotheses, but adds no completed
async proof and does not satisfy the conditional supported-outcome milestone. Local raw evidence:
`/tmp/miren-stage126-main-stm32-20261009`; older published reset-only evidence stays separate.


`fleet_main_export.py` publishes compact evidence from a complete strict capture, with an optional
separate conditional capture:

```sh
python3 tools/fleet_main_export.py --strict /tmp/fleet-main-001/summary.json \
  --conditional /tmp/fleet-main-conditional-001/summary.json \
  --output docs/public/data/fleet-embassy-main-current.json
```

The exporter checks all 12 expected mains and their three exact scopes against the captured fleet
inventory. It revalidates raw reports, proof policies, compiler completion, frozen analyzer bytes,
source fingerprints, dependency checkpoints and policy snapshot bytes. A strict/conditional pair
must share captured survey, analyzer binaries, source revision, limits and unchanged input hashes.
Partial or subset captures, stale evidence and unsupported milestone claims fail without replacing
published evidence. Complete UNKNOWN results can be published with both outcome milestones false.
The exporter retains the separate fresh-future entry milestone, each async root's validated poll
entries, the total body-entry count and truncation metadata; missing legacy evidence stays false.

The deterministic output preserves strict and conditional outcomes separately, blocker locations
and call chains, actual assumptions, trusted calls and normalized per-unit contracts. It retains
exact source fingerprints, aggregate dependency fingerprints, raw report and summary hashes, and
exporter-tool hashes. Counterexample and query payloads are represented by canonical JSON SHA256
fingerprints; raw SMT, MIR and large dependency path maps remain in the original captures. Output
larger than 500 KiB is rejected before atomic replacement. Registration or runtime outcomes never
substitute for the async-body milestone, and conditional outcomes remain explicitly conditional.

Fleet compact comparisons retain every original blocker string and outcome transition. They also
label changed diagnostics using a grouping key that ignores rustc DefId indices, crate hashes and
ordering of complete `dyn` Binder entries. Different payload types, paths and operations remain
separate. This display grouping is not semantic equivalence or proof progress; unchanged UNKNOWN
roots remain UNKNOWN regardless of grouping. Malformed Binder lists are left unsorted.

Compiler inventories optionally report direct coroutine return types. Full fleet collections check
that inventory and verification metadata agree, label future construction separately from function
bodies and reject a polling proof in the function-only capture. Compact exports retain scope counts
and exact row indices for factories and unclassified legacy roots. Scope metadata changes no proof
outcomes; missing legacy metadata is not inferred from source names. All-main polling captures
remain separate.

## External GPIO model policies

The `fleet-main-stm32*-gpio-hypothesis.json` profiles compose the initialization policies above
with the public hardware API. The combined policy admits exactly GPIOC BSRR on H723VG and GPIOH
BSRR on F407IG, plus bounded forward byte-address transport in their 32-byte register regions.
No register read is allowed. Use the combined file explicitly:

```sh
python3 tools/fleet_main_survey.py --survey /tmp/fleet-survey-002/summary.json \
  --output /tmp/fleet-main-gpio-001 --allow-assumptions \
  --assumptions-profile docs/public/data/fleet-main-stm32-gpio-hypothesis.json
```

Normalized hardware policies are retained alongside function contracts. The runner admits only
that policy's exact namespaced hardware premise in `entry_assumptions`; startup and induction
remain rejected. Strict runs reject any used hardware premise. Compact exports preserve the
configuration, snapshot hashes and actual premise on UNKNOWN and REFUTED roots as well as proofs.
Legacy profiles without hardware retain their previous normalized representation.

The initial actual replay completes all twelve mains: nine use the exact modeled BSRR write and
advance to GPIO PUPDR reads, which remain UNKNOWN; three retain earlier RTT refutations without
using a hardware model. Registration remains twelve PROVED and ordinary runtime entry twelve
REFUTED. This is conditional traversal progress, not nine new proofs or a supported-outcome
milestone. Raw capture: `/tmp/miren-stage127-main-gpio-20261009`. The separate existing reset-only
and initialization-only publications remain unchanged.

The separate `fleet-main-stm32*-gpio-rmw-hypothesis.json` profiles opt into hardware schema 2.
They add exact independent u32 reads and writes for PUPDR, OTYPER, OSPEEDR and MODER on the same
GPIO ports, retaining write-only BSRR. Each read samples an arbitrary word; no readback, stability
or eventual hardware-ready value is promised. Select the combined RMW file with the same explicit
profile flags. Canonical hardware premises include the actual model version; schema 1 cannot
inherit read permission, and legacy empty read lists remain omitted.

The first schema-2 replay completes collection on all twelve mains. Nine paths execute BSRR and
read PUPDR, then stop inside the actual Rust callback at Pupdr::to_bits enum-to-u8 transmute.
This is a newly exposed Rust translation gap, not a register-read failure or demonstrated firmware
panic. Three earlier RTT refutations remain unchanged. Counterexamples that depend on sampled
register values are labeled as abstract device-correlation witnesses. Raw capture:
`/tmp/miren-stage128-main-gpio-rmw-20261009`.

Separate `fleet-main-stm32{h7,f4,}-gpio-frame-hypothesis.json` profiles add an explicit trusted
initialization storage effect to the schema-2 GPIO policies. The exact init call promises no
mutation, publication or retirement of pre-existing ordinary tracked storage; static/startup and
atomic precision remain invalidated. This stronger unverified premise is not a privacy inference
or an empty modifies list. Earlier profiles and captures remain unchanged. Main policy validation
requires the exact selector/effect/reason premise for every used storage-effect boundary and
rejects unused, duplicate, altered or unrelated premises. Hardware premises compose independently;
strict, registration and runtime scopes retain their original policies.

The additional `fleet-main-stm32{h7,f4,}-gpio-af-frame-hypothesis.json` profiles permit the two
alternate-function words for GPIOA/B/C/D/E/H in 40-byte regions, using the selected compiler PAC
base addresses. These remain explicit unverified access hypotheses; other ports/registers are
unmapped. The complete replay clears the future-frame loss and reaches RCC pointer constants on
eight H7 mains plus retired USB static storage on the F4 main. Outcomes remain three REFUTED and
nine UNKNOWN; no completed main proof or native boot claim is added.


The separate combined `fleet-main-stm32-gpio-af-static-validity-hypothesis.json` profile adds
explicit preservation of already-live modeled static allocation/type validity and existing
borrow/access rights at the exact initialization call. Static values may change; startup caches
and atomic precision remain invalidated. Dead epochs and retired/uninitialized subobjects cannot
be restored. It assumes neither zero refcounts nor unused USB storage. Its distinct effect must
appear in the exact recorded premise for a used boundary; the ordinary-frame profiles retain
their earlier behavior.

## Rust capability survey

`rust_capability_survey.py` checks `tests/capabilities/rust.json` independently of fleet.
Build release binaries, then supply a new output directory:

```sh
python3 tools/rust_capability_survey.py --output /tmp/rust-capabilities-001 \
  --solver "$PWD/.venv/bin/z3"
```

The manifest is shared with `cargo test -p miren --test rust_capabilities`. Each case runs on host
and ARM at O0/O2 with overflow checks and strict premises. Full reports, commands, binary hashes
and input hashes are retained. Exit zero means the declared P/R/U expectations and unknown
frontiers matched, not that all cases proved. Missing roots, assumptions, changed outcomes, absent
refutation witnesses and changed fixture/manifest inputs fail the collection. When a case declares
`unknown_category`, its producer cause must match on the same unfinished obligation as the expected
diagnostic. Legacy cases without that optional field retain diagnostic-only matching. The runner
does not execute counterexamples; valid native/mutation controls live in the Cargo integration test.

See [the capability roadmap](../docs/rust-capabilities.md) for scope and extension boundaries.
