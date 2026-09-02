# EIP-8282 Proof Closure

This repo holds Lean evidence for **three** EIP-8282 predeploy guarantees,
against pinned `ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1`
and the working EIP text at `lfglabs-dev/EIPs@b759aae8` (PR
[ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120), stacked
diff [lfglabs-dev/EIPs#1](https://github.com/lfglabs-dev/EIPs/pull/1)).

Lean theorems decide what is proved. `audit/guarantees.yaml` only classifies
them.

Each guarantee is evidenced in two layers:

1. **Abstract Lean 4 model** — the high-level algorithm. Supporting, not a substitute for bytecode.
2. **Pinned runtime bytecode under `EvmYul.EVM.Ξ`** — the real bytes, really executed. This is the load-bearing layer.

| # | ID | Abstract Lean | Pinned bytecode |
| --- | --- | --- | --- |
| 1 | `P-SUBMIT-1` | CHECKED | CHECKED (`∀` under WellFormed / CallHyp, plus kill-line traces) |
| 2 | `P-DRAIN-1` | CHECKED | CHECKED (`∀` under WellFormed / CallHyp, system path, plus kill-line traces) |
| 3 | `P-CONTROL-1` | CHECKED | CHECKED (`∀` under WellFormed / CallHyp, plus kill-line traces) |

Neither column is `Ξ ↔ Model`. **`A-ABSTRACT-TX` is OPEN at HIGH** and covers
the two remaining requirements for that claim: universal termination and
endpoint/post-state agreement. Read the next section before the table.

### The live gap: `A-ABSTRACT-TX`

`Eip8282.Audit.UniversalBoundary` is where the gap is stated, and it is the
first thing to read. It writes down the claim the campaign is aiming at,

```
UniversalXiCorrespondence kind :=
  ∀ c s call, PreCallRepresents kind c s call → AdmissibleCall c s call →
    ∃ w : XiHalts c,
      observe c.result = some (observeModel (Model.step s call)) ∧
        PostStateAgrees c s (Model.step s call)
```

with `c.result` the complete `EvmYul.EVM.Ξ` message call into the pinned runtime
for `kind`. Its residual `UniversalClosure kind` has two explicit parts:
`TerminationClosure` (a halting witness for every guarded call) and
`EndpointClosure` (the historical `hend` / `EndpointAgrees`, restated by R4 at
equal strength as `ExitAgrees`, together with post-account/storage refinement).
`universal_iff_endpointClosure` proves **the target and that combined residual**
equivalent, and proves neither.

That equivalence is the whole content, and it is a negative result in both
directions:

- `universal_of_endpointClosure` — the universal correspondence follows from
  the explicit termination and endpoint/post-state residuals. Neither is
  discharged here.
- `endpointClosure_of_universal` — those residuals are not an artefact of
  how R2/R3/R4/R5 staged their proofs. Anyone who proves the universal claim has
  proved it, so it cannot be routed around, restated away, or split into a
  cheaper hypothesis.

Every hypothesis is a named premise rather than a convention:
`PreCallRepresents` is carried separately. On user calls it relates the
pre-transfer model state `s` to the post-value-transfer world that `Ξ` begins
executing in, so an accepted `Model.userCall` balance increment is compared to
the already credited EVM entry account exactly once; on system calls it is the
ordinary `Represents` relation. `AdmissibleCall` names `env`
(the abstract step is *this* message call; a system step's `calldataNonempty`
is `!c.env.calldata.isEmpty`), `reachable` (`Model.Reachable s`,
not an arbitrary inhabitant of `Model.State`), and `gas_ge` / `fuel_ge` (the
campaign `CallHyp` gas bound and a 300000-step universal fuel bound; the latter
covers the known 64-record deposit drain, for which 80000 steps is insufficient).
Termination is deliberately outside that guard:
`TerminationClosure` must prove a `Nonempty (XiHalts c)` for every guarded call.
**Nothing here proves the pinned runtimes reach a halting instruction within
`universalFuelBound`**. The target also checks the successful `Ξ` account map at
the pinned predeploy against `Model.step`'s post-state; a revert must preserve
the pre-state. It is therefore not output-only.

A green build of that module is therefore *not* evidence that `Ξ` agrees with
`Model.step`. It is evidence that the gap is exactly the one
`audit/assumptions.yaml` already names. `A-ABSTRACT-TX` stays **OPEN at HIGH**
until both `TerminationClosure` and the endpoint/post-state `EndpointClosure`
are actually derived. It registers no guarantee ID, adds no wave, repeats no
finite-image conjunct, and carries no
`native_decide`, no project axiom and no `sorry`.

What has landed beneath it, and what each layer still leaves open:

| Layer | Module | Closes | Still owed |
| --- | --- | --- | --- |
| R4 | `Eip8282.Audit.XiTransport` | `X → Ξ` and the exit-instruction layer, **unconditionally** | endpoint agreement for every user/system path |
| R2 | `Eip8282.Audit.UserXiCorrespondence` | whole user-call composition, entry machine to `RETURN`/`REVERT`, under `UserCallEnv` | `hend`, supplied as an argument |
| R3 | `Eip8282.Audit.SystemXiCorrespondence` | whole system-call composition | `hendpoint`, supplied as an argument |
| R5 | `Eip8282.Audit.Reachable` | the coverage direction of the storage guard, on packed storage; never runs `Ξ` | that `Ξ` realises `applyUser` / `applySystem` |

Finite pinned traces (the kill-lines below) are canaries, not coverage: they
refute mutated bytecode, they do not quantify.

### What the bytecode layer does and does not say

`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent` is the registered
P-SUBMIT-1 parent. It is a CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, fuel ≥ 80000, user caller): every user-path `JUMPI @revert`
(bad `calldatasize`, underpay parameterized by the quoted fee, inhibitor,
value-on-getter, min-amount, stake) sits before the first `SSTORE`/`LOG0`;
a paying 184-byte deposit appends six calldata words at `tail*6` and
`LOG0`s the calldata; a paying 48-byte exit writes `CALLER` then pubkey
and `LOG0`s the 68-byte `msg.sender ‖ pubkey`; the empty-calldata getter
returns 32 bytes, and its completing CFG run records an empty `SSTORE`
overlay, so post-storage slots 0–3 read through that overlay equal the
pre-state (machine-derived, not a copy of the pre-state into the
observation); `fakeExponential` equals `Model.go` / `asmLoop` for all
excess (CFG fragment, **not** a proof that `Ξ` computes it). `A-ABSTRACT-TX`
is still OPEN at HIGH — R2 composes the whole user call only beneath the
endpoint premise `hend` — so this is not `Ξ ↔ Model` and not
`unfold userCall`.

The Wave-6 theorem `psubmit1_bytecode_parent` stays as a conjunct: it still
runs the pinned bytes of `pinned/bytecode/builder_{deposits,exits}/main.hex`
inside `EvmYul.EVM.Ξ` at two reachable-shaped images. What makes the parent
load-bearing rather than decorative is `Eip8282.Tests.PSubmit1Mutant`:
flipping **one byte** of the pinned deposit runtime (offset 158, `RETURN` →
`REVERT`) makes the *same* `submitFacts` evaluate to `false`; flipping the
user-path `LOG0` size at offset 274 (`PUSH1 184` → `PUSH1 0`) leaves the
six-word append intact but empties the log; and flipping the handle_input
fee `CALLVALUE` at offset 161 (`CALLVALUE` → `GAS`) lets an underpaying
184-byte deposit succeed and write. Those PCs are named on the CFG
fragments (`RETURN` suffix local 30, `CALLVALUE` handle_input relative 2,
`PUSH1 184` relative 114). The mutation is to bytecode, not to a model
function. `log_mutant_leaves_siblings_intact` and
`underpay_mutant_leaves_siblings_intact` prove those cuts leave
`PDrain1.drainFacts` and `PControl1.controlFacts` true.

`Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent` is the registered
P-CONTROL-1 parent. It is a CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, caller class): `CALLER = SYSTEM_ADDR` iff the opening `EQ` /
`JUMPI` lands on `read_requests`; nonempty system calldata stores
`INHIBITOR`, inhibited+empty stores `0`, else `max(0, excess+count−TARGET)`
for targets 8 and 2 (queue length unused); a paid user wraps
`SLOT_COUNT += 1` and leaves excess, while a system `store_excess` writes
`SLOT_COUNT := 0` (mod 2^256); exit init stores `INHIBITOR` at slot 0 then
returns runtime, and deposit init does not `SSTORE`. `A-ABSTRACT-TX` is still
OPEN at HIGH — R2/R3 compose the whole user and system calls only beneath the
endpoint premise — so this is not `Ξ ↔ Model` and not
`unfold userCall` / `systemCall`.

The Wave-1 theorem `pcontrol1_bytecode_parent` and Wave-5 theorem
`pcontrol1_nonempty_bytecode_parent` stay as conjuncts: they still run the
pinned bytes inside `EvmYul.EVM.Ξ`. Wave 5's nonempty images
(`QUEUE_HEAD = 0`, `QUEUE_TAIL ∈ {2,17,65}`) drain (`368` / `11776`
deposit bytes, `136` / `1088` exit bytes) *and* fold `SLOT_EXCESS` to
`97` / `103` (or latch `INHIBITOR` / clear to `0`). Those return sizes
and `HEAD`/`TAIL` moves are false if the queue were empty, so the
nonempty traces are not a restatement of Wave 1.

`Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent` is the registered
P-DRAIN-1 parent. It is a CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, fuel ≥ 80000, system caller `isUser = false`): system `SSTORE`
keys sit in `{SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL}` so every
slot `n ≥ 4` is unchanged; `n = min(tail-head, capOf)` with wrap-free
`SUB`/`ADD`, the oldest `n` packed items, full-drain pointers `(0,0)` and
partial `HEAD += n` with `TAIL` unchanged, caps 64/16; deposit amount
bytes 80–87 are little-endian of the big-endian packed field `∀` drained
index; a user fee quote does not move `HEAD`/`TAIL`. `A-ABSTRACT-TX` is still
OPEN at HIGH — R3 composes the whole system call only beneath the endpoint
premise — so this is not `Ξ ↔ Model` and does **not** claim
`Ξ` computes FIFO for every excess.

The Wave-6 theorem `pdrain1_bytecode_parent` stays as a conjunct: it still
runs the pinned bytes inside `EvmYul.EVM.Ξ` at the sampled queue depths.

P-CONTROL-1's kill-line, `Eip8282.Tests.PControl1Mutant`, feeds the same
`controlFacts` / `nonemptyControlFacts` the `∀` parent still contains:
builder_deposits offset 22 (`EQ` → `LT`), offset 571 (`PUSH1 8` → `9`),
and builder_exits offset 401 (`PUSH1 2` → `3`). With the gate cut,
`SYSTEM_ADDR` is answered as a user. With the deposit TARGET cut,
`depositQueue 2` stores excess `96` not `97`; with the exit cut,
`exitQueue 2` stores `102` not `103`. Those PCs are named on the CFG
fragments (`gateEqPc`, `update_excess` local 70). `wave5_mutants_leave_psubmit1_intact`
proves the TARGET cuts leave `PSubmit1.submitFacts` **true**. P-SUBMIT-1
never calls from `SYSTEM_ADDR` and never reaches `compute_excess`, so the
parent is not a restatement of a sibling.

P-DRAIN-1's kill-line, `Eip8282.Tests.PDrain1Mutant`, cuts six drain-only
bytes: the exit `MAX_PER_BLOCK` clamp at offset 244 (`PUSH1 16` → `PUSH1 8`),
the exit system `RECORD_SIZE` multiplier at offset 450 (`PUSH1 68` →
`PUSH1 64`), the deposit `MAX_PER_BLOCK` clamp at offset 304
(`PUSH1 64` → `PUSH1 32`), the partial-drain `QUEUE_HEAD` store at
deposit offset 483 (`PUSH1 2` → `PUSH1 9`), the same deposit store
retargeted onto slot 196 (`PUSH1 2` → `PUSH1 196`, first word of drained
item 32), and the exit partial-drain `QUEUE_HEAD` store at offset 313
(`PUSH1 2` → `PUSH1 25`, src word of drained exit item 7). Each makes the
*same* `drainFacts` evaluate to `false`, so `pdrain1_forall_parent` is
false of that bytecode. Those PCs are named on the CFG fragments
(exitClamp relative 18, depositClamp relative 19, `update_head+12`,
`store_excess+8`). With the exit-cap cut, seventeen
queued exits return 8 records and the head advances to 8; the under-cap
two-record drain is untouched. With the deposit-cap cut, sixty-five
queued deposits return 32 records and the head advances to 32; the
empty-queue and under-cap deposit drains are untouched. With the
Wave-3 head-slot cut, the 64-record drain still returns 11776 bytes but
writes the new head `64` into slot 9 (last remaining word of drained
item 0) instead of `QUEUE_HEAD`, so the remaining-word conjunct fails.
With the Wave-6 deposit head-slot cut, that same `64` is written into
slot 196 so `staleDepositPk1Is 32` fails. With the Wave-6 exit head-slot
cut, the new head `16` is written into slot 25 so `staleExitSrcIs 7`
fails. After the same traces the parent also pins leftover storage: all
six words of deposit item 0, all five remaining words of deposit item 1,
the first word of deposit item 32, all six words of deposit item 63,
still-queued deposit item 64, and all three words of exit items 0, 7 and
15. `drain_mutants_leave_siblings_intact` proves all six mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` **true**:
P-SUBMIT-1 never calls from `SYSTEM_ADDR`, and P-CONTROL-1's empty-queue
facts hold `QUEUE_HEAD = QUEUE_TAIL = 0`, so the partial-drain head
stores are never taken and `0 * RECORD_SIZE` is still 0.

Two disclosed costs, both in `audit/assumptions.yaml`:

- `A-NATIVE-DECIDE` — a cost limitation, not an irreducible definition. The
  four pinned images contain no `SHA3`, `BLOCKHASH`, call/create or
  precompile-dispatch opcode and `EvmRunner.run` applies `EVM.Ξ` directly
  instead of decoding transaction RLP, so the `opaque` `@[extern]` FFI
  constants and the `partial` RLP decoders are never reached; what the
  kernel cannot do is evaluate up to 80 000 interpreter steps of `Ξ`.
  `native_decide` is forced on the kept
  P-SUBMIT-1, P-CONTROL-1, and P-DRAIN-1 traces; the Lean compiler and the
  EVMYulLean interpreter join the trusted base for those theorems.
  `Eip8282.Audit.Trust` prints exactly which theorems carry it. The CFG
  `∀` conjuncts of `psubmit1_forall_parent`, `pcontrol1_forall_parent`,
  and `pdrain1_forall_parent` must not add `sorryAx`.
  It no longer covers the jumpdest tables. EVMYulLean `0ff72b2` makes `D_J`
  structurally recursive, so `deposit_D_J` / `exit_D_J` / `depositInit_D_J` /
  `exitInit_D_J` are `decide +kernel`. The three parents now say so in their
  own statements: `psubmit1_forall_parent`'s revert conjuncts quantify over
  `D_J depositRuntime ⟨0⟩` / `D_J exitRuntime ⟨0⟩` directly, and
  `pdrain1_forall_parent` / `pcontrol1_forall_parent` carry
  `Eip8282.Audit.Step.validJumps_are_Xi_tables` as their leading conjunct.
  The table the CFG layer steps is Ξ's own analysis of the pinned bytes,
  kernel-checked, not a hand-written array that happens to look right.
- `A-EVM-WORLD` — the world is synthetic (two accounts). All three `∀`
  parents are under `WellFormed` / `CallHyp`.

`A-ABSTRACT-TX` stays OPEN at HIGH, and `Eip8282.Audit.UniversalBoundary`
records both termination and endpoint/post-state agreement as its removal
criterion. See
[The live gap](#the-live-gap-a-abstract-tx).

Deployment provenance is still out of the current claim, but C4 no longer
stops at a CFG prefix. `PControl1.CtorXi.pcontrol1_ctor_xi_parent` runs the
full pinned 638-byte deposit and 503-byte exit init images under
`EvmYul.EVM.Ξ` and pins the buffer each returns to be `depositRuntime` /
`exitRuntime` byte for byte — the `code` that `Λ`'s step (115) installs —
with the exit ctor leaving slot 0 at `INHIBITOR`. That is what ties
`pinned/bytecode/*/ctor.hex` to `pinned/bytecode/*/main.hex`;
`audit/artifacts.lock.json` hashes the two files independently.

It is deliberately not `Λ` itself. `Λ` derives its address as
`KEC(RLP(sender, nonce))`, and the EIP-8282 contracts are genesis
predeploys, not `CREATE` outputs — so driving `Λ` would pin an address
that is provably not the predeploy address. No address derivation is
claimed, and `A-PINNED-SOURCE` stays **open**: nothing here observes chain
state. What remains is a single observation — the live codehash at
`0x0000bFF4…` / `0x000064D6…` against keccak of the pinned `main.hex`.

The three IDs are the smallest coherent audit surface:

1. **submission** — admission, money, atomic rejection, authentic append, caller binding;
2. **drain** — FIFO conservation, caps, encoding, queue reuse;
3. **control state** — fee, count, initial gating, reversible inhibition.

Wording, assumptions, source spans, next gates: `audit/guarantees.yaml`.

## Reproduce

Needs [elan](https://github.com/leanprover/elan) and Lean 4.31.0.

```bash
make audit-check
make prove
make check
```

`make prove` first runs `lake build EvmYul.FFI.ffi:dynlib`. That is not
optional: `native_decide` runs the compiled EVMYulLean interpreter, which
needs the keccak/sha2 FFI as shared objects. `lakefile.lean` passes both to
`lean` via `--load-dynlib`, `libleanffi.so` first (otherwise `memset_zero` is
unresolved).

One guarantee, plus its kill-line:

```bash
lake build EvmYul.FFI.ffi:dynlib
lake build Eip8282.Audit.Guarantees.PSubmit1 Eip8282.Tests.PSubmit1Mutant
```

The universal boundary on its own. It runs no `Ξ`, so it needs no FFI, and its
eight `#print axioms` lines in `Eip8282.Audit.Trust` must show exactly
`propext, Classical.choice, Quot.sound`:

```bash
lake build Eip8282.Audit.UniversalBoundary
```

## Layout

- `Eip8282/Audit/` — abstract model, `Bytecode` pins, the `EvmRunner` Ξ driver,
  guarantee modules, the `UniversalBoundary` statement of the open
  `A-ABSTRACT-TX` gap, trust report, facade
- `Eip8282/Tests/` — model mutants and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode kill-lines; not public guarantees
- `audit/` — registry, source map, assumptions, pins, universal-`∀` campaign (`CAMPAIGN.md`, orchestrator prompt)
- `AGENTS.md` / `.cursor/` — Cloud Agent environment (Lean 4.31) and campaign rules
- `pinned/` — frozen sys-asm sources, bytecode and EIP text (sha256-locked;
  `scripts/audit_metadata.py` also checks the Lean hex literals against them)
- `scripts/` — fail-closed checks

## Scope

In scope: Builder Deposit `0x0000bFF46984e3725691FA540a8C7589300D8282` and
Builder Exit `0x000064D678505ad48F8cCb093BC65613800E8282`.

Out of scope: EIP-7732 bidding, consensus-layer handling, BLS validity,
EIP-7685 wrapping, and on-chain deployment identity.

## Universal `∀` campaign

P-SUBMIT-1, P-CONTROL-1, and P-DRAIN-1 public parents are now those `∀`
theorems (`forall/psubmit1`, `forall/pcontrol1`, `forall/pdrain1`).
Plan, worker split, and PR stack: `audit/CAMPAIGN.md`. Single Cloud
orchestrator prompt: `audit/CLOUD_ORCHESTRATOR.md`.
