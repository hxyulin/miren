<!--@include: ../crates/miren-contracts/README.md-->

## A bounded call

Add the metadata crate to the code you want to annotate:

```toml
[dependencies]
miren-contracts = { git = "https://github.com/hxyulin/miren" }
```

```rust
use miren_contracts::{ensures, no_panic, requires};

#[no_panic]
#[requires(value < 15)]
#[ensures(result < 16)]
pub fn increment(value: u8) -> u8 {
    value + 1
}
```

`requires` constrains the root's input domain and must be proved at every analyzed call.
`ensures` is checked at each feasible return. Neither attribute provides runtime protection
against a caller violating the domain. Panic checking itself does not require annotations.

See the [contract example](examples.md#contracts-and-nested-inputs) and
[proof execution](proofs.md) for caller obligations and the trusted components.

Postconditions can inspect supported updated arguments through `final_<parameter>`, while ordinary
parameter names retain entry snapshots:

```rust
#[requires(state.count < 255)]
#[ensures(final_state.count > state.count)]
fn increment(state: &mut State) {
    state.count += 1;
}
```

The final_ prefix is reserved for these post-state bindings in functions with postconditions.

## Contracts without a source dependency

A JSON sidecar can attach the same checked contracts to unchanged application or dependency code.
For example, this checks the final state of the fleet controller's reset method:

```json
{
  "schema_version": 1,
  "functions": [
    {
      "function": "controller::Pid::reset",
      "arguments": ["state"],
      "no_panic": true,
      "ensures": ["final_state.integral == 0.0"]
    }
  ]
}
```

```sh
cargo miren --verify --summary --contracts contracts.json \
  --entry controller::Pid::reset -p controller --lib --target thumbv7em-none-eabihf
```

Function paths must be exact and crate-qualified. Optional argument names are positional aliases;
otherwise available MIR parameter names are used. Aliases cannot conflict with another parameter's
name. Checked preconditions restrict root inputs and become obligations at callers. Checked
postconditions are verified against actual returns and final state. The analyzer executes the
body, including when the sidecar names a function normally handled by a library model.
Nothing is added to the application binary.

Unknown fields, duplicate selectors, malformed predicates and unmatched selectors fail the run.
In Cargo mode matching is checked across the collected reports. A local definition can match
without being selected, but its contracts remain pending until an independent proof succeeds.
A dependency selector must match an analyzed call if its definition has no local inventory.

## Explicitly trusted call boundaries

An opaque formatter or another unsupported boundary can have a user-supplied summary. The tool
checks its caller's preconditions, then assumes the declared panic freedom, effects and return
constraints. This is an explicit exception to body verification. The following illustrates the
configuration shape; its claims need a separate review of the application's write_float function:

```json
{
  "schema_version": 1,
  "functions": [
    {
      "function": "application::write_float",
      "arguments": ["writer", "value", "precision"],
      "requires": ["precision <= 6"],
      "trusted": true,
      "no_panic": true,
      "modifies": ["writer"],
      "ensures": ["final_writer.len <= 32"],
      "reason": "Application review reference for this formatter and writer boundary"
    }
  ]
}
```

This example does not establish that precision <= 6 makes arbitrary float formatting panic-free,
or that the writer's length stays bounded. Those are user claims. Prefer a small application
wrapper whose exact behavior can be reviewed, rather than a blanket core::fmt exception.

Every root that uses a trusted summary is labeled **PROVED_WITH_ASSUMPTIONS**, counted separately
from PROVED, and fails strict verification. Accept these conditional results explicitly with:

```sh
cargo miren --verify --summary --contracts contracts.json --allow-assumptions --lib
```

The flag never accepts REFUTED or UNKNOWN. Selecting the trusted function itself as a root still
executes its actual body. An assumption about a callee cannot verify the callee's implementation.
Reports retain the full configuration and each used summary's clauses, reason, concrete compiler
instance, available crate hash and call-site source. The hash is recorded provenance, not a
configured version pin. A trusted function requires no_panic=true and a nonempty reason.
Some local binary builds do not compute a compiler crate hash. Reports omit that hash and the
verbose output explicitly says it is unavailable; the assumption is still recorded.

The return value is fresh within its supported Rust type. A fmt::Result can still be Err: assuming
no panic does not assume success, and a caller that panics on Err can be refuted. Trusted ensures
restrict the fresh return/state; ill-typed or inconsistent clauses yield UNKNOWN. Reference,
pointer, callable, destructor-bearing and alias-containing return shapes require further models.

A trusted boundary returning its mutable-reference argument can declare `returns_alias`, naming
one of its positional argument aliases. The input and output must both be mutable references to
the same pointee type; only the outer lifetime can differ. The returned value keeps the original
tracked allocation and field/index projection. For example, `"arguments": ["storage"]`,
`"returns_alias": "storage"` and `"modifies": []` claim that the function returns that reference
without modifying modeled storage. This is an explicit alias claim, not a fresh symbolic result.
An ensures predicate's `result` reads the returned pointee after the claimed effects.

Missing effects still invalidate storage, so such an alias cannot be used to retain stale facts.
Dead storage, escaping local mutable borrows, different pointee types, shared references, raw
pointers and aggregate alias returns remain unsupported. Returning an alias does not verify
Rust lifetime validity or make a local allocation live forever. It never verifies the assumed
function's implementation; selecting that function as a root still checks its body.

Effects are also explicit claims. Omitting modifies invalidates all modeled storage facts after
the call. Setting modifies to an empty array claims that no modeled storage changes. Listing an
argument permits arbitrary supported writes through that reference, preserves its known aliases,
and claims that other modeled storage is unchanged. A mutable byte slice retains its length;
scalar Cell references can also be listed. `final_<alias>` reads the resulting modeled state.
Unsupported effect shapes yield UNKNOWN. These frames do not verify general concurrent memory
or arbitrary raw-pointer effects.

Concrete synchronous guard destructors execute in the ordinary interpreter. A guard that invokes
a configured restoration leaf therefore checks that leaf's preconditions and records its trusted
contract, just like an explicit call. The callback and destructor body are still checked. Such
leaf assumptions establish only the reported conditional panic-freedom claim; they do not verify
interrupt exclusion or concurrent access. Unsupported drop glue remains UNKNOWN.

Trusted generic calls require an exact instance string, copied from the report's compiler
instance arguments, such as "[u8]". Matching uses the pinned compiler's representation and rejects
overlapping selectors. Trait resolution must still identify an ordinary concrete function;
dynamic dispatch and unsupported shims cannot be covered by a wildcard.

## External model API

Host integrations can build a `miren::ContractConfig` with public Rust types or write its JSON
representation. Existing `FunctionContract` entries describe explicit function boundaries and
Rust storage effects. The optional `hardware` field adds a versioned device model without replacing
application source. It is absent from legacy configuration and disabled in strict runs.

Hardware schema 1 supplies bounded byte-address transport and exact write-only u32 register
accesses for STM32H723VG or STM32F407IG. Schema 2 adds explicitly permitted independent reads.
Both are conditional models. The current devices require a 32-bit compiler pointer domain. Build
indicators must match the selected device; these indicators do not establish which physical chip
exists. Register access, device validity and absence of
unmodeled Rust storage effects remain explicit premises in the required reason.

The public `HardwareModel`, `HardwareDevice`, `MmioRegion` and `MmioWriteRegister` types are
serializable. `HardwareModel::new`, `with_region` and `with_write_register` build a policy;
`ContractConfig::with_hardware` combines it with function contracts. Call `validate()` before
serializing an in-memory model. The CLI validates loaded configuration again. For a working host
integration, run the example
[builder](https://github.com/hxyulin/miren/blob/main/crates/miren/examples/stm32_model.rs):

```sh
cargo run --locked -p miren --example stm32_model -- stm32h723vg > /tmp/h7-model.json
```

An integration can write the validated configuration to a sidecar and invoke miren with
`--contracts FILE --allow-assumptions`, then consume `--jsonl` reports. The same configuration can
include explicit function boundaries in `functions`; hardware permission does not supply a missing
function body. This API describes symbolic effects. It does not register executable emulator
callbacks or initialize an Embassy executor.

Its hardware section has this form; JSON addresses are decimal integers:

```json
{
  "schema_version": 1,
  "device": "stm32h723vg",
  "pointer_bits": 32,
  "reason": "UNVERIFIED GPIO access hypothesis with no unmodeled Rust storage effects",
  "regions": [{"name": "GPIOC", "start": 1476528128, "length": 32}],
  "write_registers": [{"name": "GPIOC_BSRR", "address": 1476528152}]
}
```

The model allows 1..16 disjoint regions of 1..4096 bytes inside the STM32 peripheral address
window and 1..64 uniquely named, aligned registers wholly inside those regions. Schema 1 admits
only exact unsigned 32-bit writes, including compiler-certified transparent u32 register values.
Admitted forward byte-address arithmetic must stay within a configured region without wrapping;
admitting transport alone grants no register access. Numeric hardware addresses never become
retained Rust allocations or references. Unmapped addresses, unsupported widths, reads without
permission and missing models stay UNKNOWN.
Hardware stores retain the existing conservative publication/startup history invalidation.

The interpreter executes the actual register write callback and its Rust assertions and arithmetic.
Only the final permitted hardware store has assumed semantics. Every root that uses transport or a
store records the exact device premise in `entry_assumptions`, even when it later refutes or stays
unknown. Completed proofs require explicit `--allow-assumptions`; that flag does not accept
REFUTED or UNKNOWN. Reports retain the complete model configuration and reached effect diagnostics.

This is the initial integration boundary. Future peripheral models can extend the versioned
operations and effects; Embassy state models need separate Rust initialization, publication and
lifetime semantics. The existing `--startup` and `--startup-isolated` premises remain explicit and
independent of hardware permission. No fixed register value, hardware readiness, instruction
behavior, executor progress or loop termination follows from these models.

Hardware schema 2 adds optional `read_registers`, containing the same `{name, address}` fields as
write registers. `with_read_register` opts into schema 2. Up to 64 reads and 64 writes are allowed,
with at least one permitted operation; reads and writes need independent direction permissions.
Legacy schema-1 models omit the empty read list and cannot gain read permission. The builder can
emit a complete GPIO policy with an optional argument:

```sh
cargo run --locked -p miren --example stm32_model -- stm32h723vg rmw > /tmp/h7-rmw-model.json
```

Each admitted read returns a fresh arbitrary u32 or its compiler-certified transparent wrapper.
It promises no fixed value, correlation between reads, readback after a write or eventual ready
bit. The actual `Reg::modify` body and callback execute before the independently permitted store.
Read-dependent counterexamples carry the explicit device-correlation abstraction reason; native
or physical-device confirmation remains separate. Reads retain the same conservative interference
invalidation as writes, and retained ordinary RAM reads keep their existing semantics.

Native replay refuses reports with hardware configuration or a recorded hardware-model premise,
including a counterexample reached before the first hardware operation. The API supplies symbolic
analysis effects without a native hardware execution implementation.

### Preserving ordinary storage at a trusted boundary

`FunctionContract.storage_effect` can opt into
`TrustedStorageEffect::PreserveExistingOrdinaryStorage`, serialized as
`"preserve_existing_ordinary_storage"`. The exact trusted call must have `no_panic` and a nonempty
reason, with no `modifies` list or alias return. This is a stronger conditional premise: the call
will not mutate, publish or retire any pre-existing ordinary tracked storage. It is not inferred
from argument reachability or the absence of a known alias.

For example, a HAL initialization model can retain the fresh application's future while leaving
singleton, clock and time-driver effects opaque:

```json
{
  "function": "embassy_stm32::init",
  "trusted": true,
  "no_panic": true,
  "storage_effect": "preserve_existing_ordinary_storage",
  "reason": "UNVERIFIED initialization and frame premise; static effects remain opaque"
}
```

The analyzer certifies pure owned boundary inputs against compiler types and actual symbolic
values before admitting this effect. References, raw pointers, interior mutable/atomic inputs and
opaque shapes remain unsupported. Existing dead allocations remain dead. Static views and startup
history are invalidated, and atomic values retain conservative interference. The model does not
promise unchanged hardware or static state, initialize an executor, or preserve storage across
later unrelated calls.

Every admitted use records the exact versioned selector/effect/reason premise and trusted call in
the report. Later REFUTED and UNKNOWN outcomes retain it. Strict defaults and existing omitted
`modifies` contracts keep their conservative behavior. Native replay refuses configured or recorded
storage effects because this API has no native implementation of the external boundary.
