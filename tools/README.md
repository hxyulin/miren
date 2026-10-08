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
published evidence. Complete UNKNOWN results can be published with both milestones false.

The deterministic output preserves strict and conditional outcomes separately, blocker locations
and call chains, actual assumptions, trusted calls and normalized per-unit contracts. It retains
exact source fingerprints, aggregate dependency fingerprints, raw report and summary hashes, and
exporter-tool hashes. Counterexample and query payloads are represented by canonical JSON SHA256
fingerprints; raw SMT, MIR and large dependency path maps remain in the original captures. Output
larger than 500 KiB is rejected before atomic replacement. Registration or runtime outcomes never
substitute for the async-body milestone, and conditional outcomes remain explicitly conditional.
