import Eip8282.Audit.Correspondence
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import EvmYul.EVM.Proof.Block
import EvmYul.EVM.Proof.MemoryStep

/-!
# R4 — transporting the three registered parents to the complete `Ξ` message call

`P-SUBMIT-1`, `P-DRAIN-1` and `P-CONTROL-1` are registered on `main` as
CFG-level `∀` statements (`WellFormed` / `CallHyp` guarded runs of the
`Eip8282.Audit.Step` prefix stepper). Nodes R2 and R3 compose a whole call out
of `EvmYul.EVM.Proof.RunUntil`, but they stop at `EvmYul.EVM.X`, the *code
execution* function. `X` is not the call an EIP-8282 client makes: the complete
message call is `EvmYul.EVM.Ξ`, which builds the entry machine, fixes the
jumpdest table from the code being run, and re-wraps `X`'s answer.

R4 supplies exactly that last layer, and it is the one part of the chain that
needs no assumption:

* `observe_Xi_eq_observe_X` — the complete `Ξ` call and the `X` run it delegates
  to have the **same observation**. `Ξ` re-wraps `.success` with a different
  payload (`createdAccounts × accountMap × gas × substate` instead of the whole
  `EVM.State`) and passes `.revert` through, but neither branch touches the
  status flag or the return bytes. Proved outright, no premise, no `native_decide`.
* `Xi_validJumps_eq` — the table `Ξ` computes for itself, `D_J I.code ⟨0⟩`, is
  the campaign's own kernel-checked `depositJumpdests` / `exitJumpdests`
  whenever the code being run is the pinned runtime. So the `∀` below is over
  `Ξ` runs against `Ξ`'s own jumpdest analysis of the pinned bytes, not against
  a table asserted by this module.

* `observe_result_exit` — the complete `Ξ` call observes **exactly** the halting
  instruction the code run exits on: it reverted iff that instruction is
  `REVERT`, and it published exactly the bytes `H` hands back. No premise.
* `exit_op_cases`, `out_eq_H_return`, `bytes_eq_nil_of_silent` — read straight
  off EVMYulLean's `H`. The exit opcode is one of four; on `RETURN`/`REVERT` the
  published bytes *are* the requested memory slice; on `STOP`/`SELFDESTRUCT`
  nothing is published at all.
* `exit_halting`, `exit_H` — the `H` side condition is **not a premise**. A
  `RunUntil` against the halting stop condition that ended with fuel to spare
  records why it stopped (`RunUntil.stop_of_rem_pos`), and `H`'s `some`-ness is
  decided by the opcode alone (`H_eq_none_iff`). Composing the two derives
  `H post.toMachineState op = some (haltData post.toMachineState op)` from the
  run, so the published bytes stop being a universally quantified `ByteArray`
  and become a function of the machine.

## What stays open

`A-ABSTRACT-TX` stays OPEN at HIGH. R4 does **not** discharge it.

The premise has been restated twice, and the two restatements are not the same
kind of change:

* `EndpointAgrees` → `ExitAgrees` is a restatement at **equal strength**;
  `endpointAgrees_iff_exitAgrees` proves the equivalence, so nothing was
  smuggled in or quietly dropped.
* dropping the `H ... = some out` hypothesis and the bound `out` is a **strict
  weakening of what a caller must supply**: `exit_H` proves that hypothesis from
  the run. Every statement below now asks for one thing rather than two.

Neither changes the semantic content that is still assumed. No run of the pinned
bytecode is proved here to reach any particular opcode, and nothing below
establishes that the predeploy computes `Model.step`.

What did shrink — and these are theorems, not claims — is the surface the
residual has to cover:

* two of the four exit branches are closed outright (`exitAgrees_of_silent`);
* `out` is no longer a free variable *or* a side condition (`exit_H`);
* P-CONTROL-1's exit opcode is pinned to `RETURN` (`pcontrol1_xi_exit_is_RETURN`),
  because a 32-byte fee quote cannot come from a silent halt or a revert;
* P-DRAIN-1's silent halts are refuted on a non-empty FIFO window
  (`pdrain1_xi_exit_publishes`);
* P-DRAIN-1's `REVERT` branch is refuted **unconditionally**: `Model.systemCall`
  has no `revert` constructor, so `pdrain1_xi_exit_not_REVERT` needs no
  hypothesis about the window, the represented kind, or the run. Combined with
  the line above, `pdrain1_xi_exit_is_RETURN` pins the drain's exit opcode to
  exactly one of `H`'s four branches, the position `pcontrol1_xi_exit_is_RETURN`
  already held for the fee getter. `pdrain1_exitAgrees_iff` states the residual
  in closed form — `op ≠ .REVERT` together with a byte equation against the
  encoded FIFO window — so, as for P-SUBMIT-1, no `Outcome` is left in it;
* and **P-DRAIN-1's empty-window branch is discharged**: when the capped FIFO
  prefix encodes to nothing, `pdrain1_exitAgrees_of_silent` and
  `pdrain1_exitAgrees_of_zero_length` *produce* the residual rather than consume
  it, so `pdrain1_xi_empty_window_returns_nothing` is a complete-`Ξ` observation
  carrying no `ExitAgrees` premise at all. This is the second branch, after
  P-SUBMIT-1's inhibited path, that no longer rests on `A-ABSTRACT-TX`;
* P-SUBMIT-1's residual is exactly `op = .REVERT ∧ bytes out = []`
  (`psubmit1_exitAgrees_iff`) — a pure EVM-side statement with no `Model` in it,
  since the model half follows from `inhibited model = true`;
* the published bytes are no longer opaque: `haltData_eq_memory_slice` inverts
  EVMYulLean's `step` at `RETURN` / `REVERT` into
  `post.toMachineState.H_return = mid.memory.readWithPadding μ₀ μ₁`, so what a
  call publishes is a function of pre-step memory and the exit's own two stack
  operands (`XiSliceTransport`);
* consequently **P-SUBMIT-1's residual is discharged**: a `REVERT` whose length
  operand is zero publishes nothing, whatever the offset and whatever memory
  holds (`bytes_haltData_eq_nil_of_zero_length`), so
  `psubmit1_xi_inhibited_reverts_of_zero_length` concludes with *no* `ExitAgrees`
  premise at all;
* **and so is P-SUBMIT-1's rejected-submission branch**, the one remaining
  `Model.userCall` path that had never been touched: an uninhibited call with
  non-empty calldata that `admissible` turns away. `psubmit1_exitAgrees_iff_rejected`
  states its residual in the same closed form the inhibited branch has
  (`op = .REVERT ∧ bytes out = []`, no `Model` left in it), and
  `psubmit1_xi_rejected_reverts_of_zero_length` then *produces* it from a
  zero-width `REVERT`, so that branch too is a complete-`Ξ` observation carrying
  no `ExitAgrees` premise. This matters because of the next item;
* **the branch count is now exact rather than anecdotal.**
  `userCall_returnData_ne_nil_iff` proves that a `Model.userCall` answer carries
  return data *iff* the call is uninhibited with empty calldata and zero value —
  i.e. iff it is P-CONTROL-1's fee quote. Every other user-side branch returns
  nothing, and every one of those is now discharged above. So on the
  `Model.userCall` side exactly one branch still rests on `A-ABSTRACT-TX`, and
  it is named;
* **and the enumeration now covers the whole abstract API, not just the user
  half.** `systemCall_returnData_ne_nil_iff` is the system-side counterpart:
  `Model.systemCall` is total, so its answer carries data iff the capped FIFO
  prefix encodes to something. `Model.Step` has exactly two constructors, so
  `step_returnData_ne_nil_iff` composes the two halves into an exhaustive
  classification — a `Model.step` answer publishes bytes **iff** the step is one
  of the two named `DataBranch` cases, P-CONTROL-1's fee quote or P-DRAIN-1's
  non-empty window. Nothing else in the abstract API publishes anything at all;
* consequently the data-free discharges collapse into **one** theorem rather
  than five. `exitAgrees_of_zero_length_of_not_dataBranch` *produces* the
  residual for every `Model.Step` outside those two cases, and
  `xi_observes_model_of_not_dataBranch` carries that to the complete `Ξ` call
  carrying no `ExitAgrees` premise, quantified over every `kind` and every step.
  The five branch-specific `Ξ` theorems above are instances of it; what it adds
  is exhaustiveness, since the enumeration certifies there is no third data-free
  branch left unstated;
* P-DRAIN-1's non-empty window is decomposed record by record:
  `pdrain1_exitAgrees_head_record` splits the residual byte equation into the
  head record's own encoding and the tail's, so the remaining obligation is a
  statement about one `Record` at a time rather than about a concatenation;
* P-CONTROL-1's residual is narrowed from a list equation to 32 independent
  digit equations: `pcontrol1_exitAgrees_iff_digits` shows that, at the pinned
  width, `ExitAgrees` holds iff byte `i` of the published slice is
  `(currentFee model / 256 ^ (31 - i)) % 256` for each `i < 32`;
* and P-CONTROL-1's exit is pinned further: its length operand cannot be zero,
  since a 32-byte fee quote cannot be published by a zero-width slice
  (`pcontrol1_xi_exit_length_ne_zero`);
* **the width of the published slice is no longer part of the residual at all.**
  `ByteArray.readWithPadding` zero-pads up to the requested length, so the slice
  a `RETURN` / `REVERT` publishes has *exactly* the size its own length operand
  names — never fewer bytes, whatever the offset and whatever memory holds
  (`size_readWithPadding`, `length_bytes_haltData`; the unconditional `≤`
  direction is `size_readWithPadding_le` / `length_bytes_haltData_le`).
  `XiWidthTransport` carries this at complete `Ξ` for every kind, and it turns
  each parent's residual from a claim about *how much* is published into a claim
  about *which bytes* are:
  - P-SUBMIT-1: `psubmit1_exitAgrees_iff_operand` replaces the byte-level
    `bytes out = []` with the machine-word equation `μ₁.toNat = 0`, so the
    residual is now two facts about the *instruction*, with no `ByteArray` left
    in it;
  - P-DRAIN-1: `pdrain1_xi_exit_length_ge` / `pdrain1_xi_exit_length_eq` pin the
    exit's length operand to the width of the FIFO window
    `concatReturned (model.queue.take (capOf kind))`;
  - P-CONTROL-1: `pcontrol1_xi_exit_length_ge_32` /
    `pcontrol1_xi_exit_length_eq_32` sharpen "not zero" to *exactly 32*.

* **and a complete `Ξ` observation no longer needs the named residual.**
  `exitAgrees_iff_memory_bytes` takes `ExitAgrees` apart, in both directions,
  into the two independent facts it abbreviates: the exit reverts iff the
  abstract step does, and the memory slice the exit selects carries the abstract
  step's bytes. `XiMemoryTransport` is then the transport asking for those two
  facts instead — quantified over every `kind` and every `Model.Step`, with no
  `ExitAgrees` and no `EndpointAgrees` hypothesis in it at all. On the data-free
  surface it assumes nothing
  (`memory_bytes_of_zero_length_of_not_dataBranch` derives the byte equation
  from the enumeration), and the two branches where the equation is still
  assumed are written out as memory claims by name:
  `pdrain1_xi_returns_fifo_prefix_of_memory` and
  `pcontrol1_xi_fee_getter_of_memory`. `XiTransport` itself is unchanged and
  still consumes `ExitAgrees`; what is new is that nothing has to go through it.

The exact-width equalities carry `μ₁.toNat < USize.size`, which is not
cosmetic: `USize.size` is `2 ^ System.Platform.numBits` and may be `2 ^ 32`, and
`readWithPadding` truncates its pad count through a machine word. The `≤`
directions are unconditional; `size_readWithPadding_of_lt_two_pow_32` is the
platform-independent corollary.

Closing what remains *universally* still needs an opcode-level proof over the
pinned runtimes for all storage images. R4 does not attempt one, and
`A-ABSTRACT-TX` stays OPEN. What R4 does add is the first *instance-level*
discharge: at four concrete storage images the residual is not assumed but
**computed**, by running the pinned bytecode through the very same `Ξ` the
transport is stated about (see `## The residual, discharged at the pinned
images` below). So the honest statement of what stays open is now: nothing here
proves the pinned runtimes reach a particular exit instruction, nor what their
memory holds when they do, *for an arbitrary storage image* — at the pinned
images it is proved outright. The residual premise, verbatim, is

  `ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)`

equivalently `EndpointAgrees` via `endpointAgrees_iff_exitAgrees`. For P-DRAIN-1
and P-CONTROL-1 it is now a statement about a *specific* memory slice of a
*pinned* width (`exitAgrees_iff_memory_slice` + `XiWidthTransport`), refined to
per-digit equations for the fee quote and to per-record equations for the FIFO
window. For P-SUBMIT-1 the residual is gone on **every** branch, replaced by two
facts about the run itself — it exits on `REVERT`, with a zero length operand —
and `userCall_returnData_ne_nil_iff` certifies that those branches are all of
them bar the fee quote.

That premise also need no longer be *stated* as a named predicate in order to
derive a complete `Ξ` observation. `XiMemoryTransport` reaches the same conclusion as
`XiTransport`, for every kind and every step, from the status equation and the
byte equation `exitAgrees_iff_memory_bytes` proves `ExitAgrees` to be. Both
directions of that equivalence are proved, so this is a restatement at equal
strength in exactly the sense `endpointAgrees_iff_exitAgrees` was — it closes
nothing. What it does is leave the open assumption in the form it actually has:

  `bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)`
  `  = (observeModel (Model.step model mstep)).returnData`

So what `A-ABSTRACT-TX` still buys, stated as narrowly as this module can state
it, is two byte-level facts about memory at the exit instruction — the 32-byte
fee quote and the encoded FIFO window — plus the fact that the runtimes reach an
exit instruction at all. It is no longer load-bearing for any branch that
publishes nothing, and `step_returnData_ne_nil_iff` makes that an exhaustive
statement rather than a summary of the cases that happened to be treated: those
two `DataBranch` steps are *provably* the only steps of the abstract API whose
answer carries any bytes. Those are the two steps where the byte equation was
assumed rather than derived at arbitrary storage —
`pdrain1_xi_returns_fifo_prefix_of_memory` and `pcontrol1_xi_fee_getter_of_memory`,
verbatim.

One of the two is no longer in that form. Spending EVMYulLean PR #9's
opcode-path byte-content lemmas, `pcontrol1_xi_fee_getter_of_mstore` reaches the
same complete-`Ξ` observation with that 32-byte memory equation *proved* from the
`MSTORE` the fee getter executes, leaving the scalar `v.toNat = currentFee model`
where thirty-two byte equations used to be (see `## The residual, discharged
symbolically` below). This **reduces** P-CONTROL-1's assumption; it does not
remove it. What stays assumed there is that the pinned run reaches that
`MSTORE`/`RETURN` pair with those operands and stores the fee — an opcode-level
reachability fact, no longer a claim about what bytes memory holds.

P-DRAIN-1's non-empty window is in the same form. Its window is written by a
queue-dependent *loop* of stores, which #9's single-store API does not reach, so
this module builds the loop relations itself: `OverlapStores` for the 68-byte
exit record, `MixedStores` for the 184-byte deposit record including the
`%MSTORE64_le` little-endian splice. Both compute the published bytes rather
than assuming them, leaving per-record scalar equations where a byte equation
used to be.

Those two relations require the record's stores to be *adjacent*, and the pinned
exit runtime never is: `builder_exits` writes its window from the `accum_loop`
body (PC 247, back-jump at PC 300), so the stores at PC 274, 284 and 294 are
separated by the `SLOAD` that reads the queue slot, the operand arithmetic, the
stack shuffling and the jumps that close the loop. Adjacency was therefore a
hypothesis the pinned bytecode provably never satisfies. `NeutralOp` names
exactly that non-`MSTORE` opcode set, `memory_step_neutral` and
`memory_Runs_neutral` prove a run of them leaves memory alone, and
`SpacedStores` replaces adjacency with a *syntactic* condition on the gap trace
(see `## Stores separated by memory-neutral work` below). `OverlapStores.spaced`
embeds the old relation with empty gaps, so nothing is lost. What that leaves
assumed on this path is reachability alone — that the runtime performs those
stores — and not what bytes they write, nor a shape the runtime does not have.

`MixedStores` was still carrying that adjacency requirement, so the *deposit*
half of the drain remained stated about a shape `builder_deposits` — which
writes its window from a loop of its own — does not have. `SpacedMixedStores`
closes that gap on both of its constructors, `MSTORE` and the `%MSTORE64_le`
`MSTORE8` splice, with the same syntactic `NeutralOp` gap condition
(`nil_neutral` / `word_neutral` / `byte_neutral`), and `MixedStores.spaced`
embeds the old relation with empty gaps. So
`endpointAgrees_of_spacedDepositStores_return`,
`exitAgrees_of_spacedDepositStores_return` and
`pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores` put `EndpointAgrees` /
`ExitAgrees` in the *conclusion* for the deposit window at a store shape the
pinned runtime can actually have. Both halves of P-DRAIN-1's non-empty window
are now in that form; neither is discharged unconditionally, and reachability of
the stores remains assumed under `A-ABSTRACT-TX`.

Both halves also carried `hfresh : pre.memory.size = 0` — the drain runs in a
frame whose memory has never been written. That is a second claim about the
pre-state, and it was never load-bearing. Both windows start at offset `0`, and
`storedBytes_exitStores` / `splicedBytes_depositStores` are already stated for an
arbitrary initial byte list: at base `0` the `acc.take 0` they thread is `[]`
whatever memory held before. Dropping `hfresh` widens all eight spaced-window
statements from a frame with empty memory to any frame the store relation itself
admits, and changes no proof beyond passing `bytes pre.memory` where `[]` used to
be passed. What still constrains the pre-state is `SpacedStores.cons`'s own
`hcov`, which asks each store to land at the memory frontier; that is a
hypothesis of the relation rather than of these theorems, and is the next
residual on this path.

Both of those two steps are discharged at concrete storage images.
`pinnedCall` builds an `XiCall` whose `result` is *definitionally* the
`Eip8282.Audit.EvmRunner.run` the registered `main` theorems already evaluate —
both unfold to the same `EvmYul.EVM.Ξ` application, and the bridge lemmas
`pinnedCall_result_exitSystem`, `pinnedCall_result_depositSystem` and
`pinnedCall_result_exitUser` are `rfl`. On that bridge,
`pdrain1_xi_drains_pinned_exit_under_cap` (queue below the cap),
`pdrain1_xi_drains_pinned_exit_over_cap` (queue above it, so the cap is
exercised), `pdrain1_xi_drains_pinned_deposit` and
`pcontrol1_xi_quotes_pinned_fee` each state the *conclusion* of the transport —
`observe c.result = some (observeModel …)` — with no `ExitAgrees`, no memory
hypothesis and no `hbytes`, and prove it by evaluation.
`represents_pinnedExitSystem`, `represents_pinnedDepositSystem` and
`represents_pinnedExitFeeGetter` certify these are genuine `Represents`
instances rather than unrelated runs, and
`pdrain1_xi_pinned_exit_discriminates` is the negative control: the same run is
proved *not* to equal the observation of a neighbouring model state, so the
positive results are not vacuous.

**This does not close `A-ABSTRACT-TX` and R4 does not claim it does.** Four
images are not all images, and the discharge is by `native_decide`, already
disclosed as `A-NATIVE-DECIDE`. What changes is that the residual is no longer
untested at every argument: before this, no run of the pinned bytecode was
proved to agree with `Model.step` anywhere.

`Represents` is restated here in the minimal main-based form R3 uses, because
R1's fuller `Eip8282.Audit.Represents` lives on an unmerged draft. It is
definitionally the core of R1's relation; this module deliberately does not
duplicate R1's API.

## Parent IDs

No new parent IDs. `psubmit1_xi_forall_parent`, `pdrain1_xi_forall_parent` and
`pcontrol1_xi_forall_parent` each carry the *unchanged* registered parent
(`type_of%` of the `main` theorem) alongside its complete-`Ξ` transport, so the
existing one-byte kill-lines still refute them: a mutant that falsifies
`submitFacts` / `drainFacts` / `controlFacts` falsifies the conjunct that
contains it here too.
-/

namespace Eip8282.Audit.XiTransport

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode targetAddr)

/-! ## Observations

The observation is the externally visible part of a call: did it revert, and
what bytes came back. Post-state equality is deliberately absent — R4 is an
*observational* correspondence, as the mission architecture requires.

`observe` is polymorphic in the success payload, which is what lets the very
same function read `X` (payload `EVM.State`) and `Ξ` (payload
`createdAccounts × accountMap × gas × substate`). That is the whole reason the
bridge below is a `rfl`-shaped fact rather than a translation.
-/

structure Observation where
  reverted : Bool
  returnData : List Nat
  deriving DecidableEq, Repr

def bytes (data : ByteArray) : List Nat :=
  (List.range data.size).map fun i => (data.get! i).toNat

def observe {S : Type} :
    Except EVM.ExecutionException (ExecutionResult S) → Option Observation
  | .ok (.success _ out) => some { reverted := false, returnData := bytes out }
  | .ok (.revert _ out) => some { reverted := true, returnData := bytes out }
  | .error _ => none

def observeModel : Outcome → Observation
  | .success _ out => { reverted := false, returnData := out }
  | .revert _ => { reverted := true, returnData := [] }

@[simp] theorem observeModel_revert (s : Model.State) :
    observeModel (.revert s) = { reverted := true, returnData := [] } := rfl

@[simp] theorem observeModel_success (s : Model.State) (out : List Byte) :
    observeModel (.success s out) = { reverted := false, returnData := out } := rfl

/-! ## The entry machine `Ξ` builds

Written to match `EvmYul.EVM.Ξ` field for field. Nothing here is a choice: it
is the state `Ξ` hands to `X`.
-/

def entryState
    (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : EVM.State :=
  { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-! ## R4's unconditional core: `Ξ` observes what `X` observes -/

/-- **The `X` → `Ξ` bridge.** A complete `Ξ` message call at fuel `f + 1` has
exactly the observation of the `X` run it delegates to.

`Ξ` maps `.success evmState' o` to `.success (createdAccounts, accountMap, gas,
substate) o` and `.revert g' o` to `.revert g' o`. The success payload changes;
the status flag and the return bytes `o` do not. Interpreter errors are
propagated unchanged and observe as `none` on both sides.

This is the layer R2 and R3 stop short of, and it costs no assumption. -/
theorem observe_Xi_eq_observe_X
    (f : Nat) (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    observe (Ξ (f + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      observe (X f (D_J I.code ⟨0⟩)
        (entryState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) := by
  unfold entryState
  cases hX : X f (D_J I.code ⟨0⟩)
      ({ (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          gasAvailable := g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader }) with
  | error e => simp [Ξ, Bind.bind, Except.bind, hX, observe]
  | ok r =>
    cases r with
    | success st o => simp [Ξ, Bind.bind, Except.bind, hX, observe]
    | revert g' o => simp [Ξ, Bind.bind, Except.bind, hX, observe]

/-- `Ξ` runs out of fuel at zero, so it observes as nothing. Recorded so the
`f + 1` shape above is not mistaken for a restriction hiding a live case. -/
theorem observe_Xi_zero
    (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    observe (Ξ 0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I) = none := by
  simp [Ξ, observe]

/-! ## `Ξ`'s own jumpdest table is the campaign's table -/

/-- The campaign's kernel-checked table, as the CFG parents step against it. -/
abbrev jumpdestsOf : Kind → Array UInt256 :=
  Eip8282.Audit.Correspondence.openingJumps

/-- The table `Ξ` derives from the code it is about to run is exactly the
kernel-checked table the CFG parents step against (`deposit_D_J` / `exit_D_J`,
both `decide +kernel` since EVMYulLean `0ff72b2`). No `native_decide`. -/
theorem Xi_validJumps_eq {kind : Kind} {I : ExecutionEnv .EVM}
    (hcode : I.code = runtimeCode kind) :
    D_J I.code ⟨0⟩ = jumpdestsOf kind := by
  rw [hcode]
  exact (Eip8282.Audit.Correspondence.openingJumps_eq_D_J kind).symm

/-! ## The complete-`Ξ` call frame -/

/-- A complete `Ξ` message call into the pinned runtime for `kind`.

`code_pinned` is the only constraint: the code being executed is the pinned
image. Everything else — world, gas, substate, created accounts, block context,
calldata and value inside `env` — is universally quantified. -/
structure XiCall (kind : Kind) where
  fuel : Nat
  createdAccounts : Std.TreeSet AccountAddress compare
  genesisBlockHeader : BlockHeader
  blocks : ProcessedBlocks
  σ : AccountMap .EVM
  σ₀ : AccountMap .EVM
  gas : UInt256
  substate : Substate
  env : ExecutionEnv .EVM
  code_pinned : env.code = runtimeCode kind

namespace XiCall

variable {kind : Kind}

/-- The machine `Ξ` starts `X` from. -/
def entry (c : XiCall kind) : EVM.State :=
  entryState c.createdAccounts c.genesisBlockHeader c.blocks c.σ c.σ₀ c.gas
    c.substate c.env

/-- The complete message call. This is `EvmYul.EVM.Ξ`, the same entry point
`Eip8282.Audit.EvmRunner.run` uses for the kept kill-line traces. -/
def result (c : XiCall kind) :=
  Ξ (c.fuel + 1) c.createdAccounts c.genesisBlockHeader c.blocks c.σ c.σ₀ c.gas
    c.substate c.env

/-- Bridge and table rewrite in the form the composition lemmas consume. -/
theorem observe_result (c : XiCall kind) :
    observe c.result = observe (X c.fuel (jumpdestsOf kind) c.entry) := by
  rw [result, entry, observe_Xi_eq_observe_X, Xi_validJumps_eq c.code_pinned]

end XiCall

/-! ## Whole-call composition at `Ξ`

R2/R3 shapes, but landing on `Ξ` rather than `X`. `RunUntil` consumes the
entire non-halting prefix; the terminating instruction then fixes the answer.
-/

theorem observe_result_success {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hop : op ≠ .REVERT) :
    observe c.result = some { reverted := false, returnData := bytes out } := by
  rw [c.observe_result, hrun.X_success hdec hZ hstep hH hop]
  rfl

theorem observe_result_revert {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hop : op = .REVERT) :
    observe c.result = some { reverted := true, returnData := bytes out } := by
  rw [c.observe_result, hrun.X_revert hdec hZ hstep hH hop]
  rfl

/-! ## The exit observation — R4's second unconditional layer

`observe_result_success` / `observe_result_revert` above are two halves of a
single fact that needs no premise at all: **the complete `Ξ` call observes
exactly the halting instruction the code run exits on.** Stating it that way
removes `EndpointAgrees` from the EVM half of the transport entirely, and it
lets `H` — EVMYulLean's halting-data function — do real work on the residual.
-/

/-- The observation forced by the instruction the code run exits on: it reverted
iff that instruction is `REVERT`, and it published exactly the bytes `H` hands
back. This mentions no `Model`: it is a pure EVM-side object. -/
def exitObservation (op : Operation .EVM) (out : ByteArray) : Observation :=
  if op = .REVERT then { reverted := true, returnData := bytes out }
  else { reverted := false, returnData := bytes out }

@[simp] theorem exitObservation_revert (out : ByteArray) :
    exitObservation .REVERT out = { reverted := true, returnData := bytes out } := rfl

@[simp] theorem exitObservation_returnData (op : Operation .EVM) (out : ByteArray) :
    (exitObservation op out).returnData = bytes out := by
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **Unconditional whole-call observation.** For *every* complete `Ξ` message
call into the pinned runtime whose code run reaches a halting instruction, the
observation of the whole call is the exit instruction's own observation.

No premise: not `EndpointAgrees`, not `Represents`, no `native_decide`. This is
`observe_result_success` and `observe_result_revert` merged, and it is what lets
the transport below carry a residual that is about the exit instruction rather
than about the whole call. -/
theorem observe_result_exit {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out) :
    observe c.result = some (exitObservation op out) := by
  by_cases hop : op = .REVERT
  · rw [observe_result_revert c hrun hdec hZ hstep hH hop]
    simp [exitObservation, hop]
  · rw [observe_result_success c hrun hdec hZ hstep hH hop]
    simp [exitObservation, hop]

/-! ### What `H` already decides about the endpoint

`EvmYul.EVM.Proof.H` is total and explicit:

```
H μ w = if w ∈ [.RETURN, .REVERT] then some μ.H_return
        else if w ∈ [.STOP, .SELFDESTRUCT] then some .empty
        else none
```

so the hypothesis `H post.toMachineState op = some out` is not opaque. It pins
`op` to four opcodes and pins `out` on all four. Two of those four branches
publish nothing, and on those the return-data half of the endpoint obligation
is discharged outright rather than assumed.
-/

@[simp] theorem bytes_empty : bytes ByteArray.empty = [] := rfl

/-- The exit instruction is one of EVMYulLean's four halting opcodes. Read off
`H`, no assumption. -/
theorem exit_op_cases {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out) :
    op = .RETURN ∨ op = .REVERT ∨ op = .STOP ∨ op = .SELFDESTRUCT := by
  by_cases h1 : op ∈ [Operation.RETURN, Operation.REVERT]
  · simp at h1; tauto
  · by_cases h2 : op ∈ [Operation.STOP, Operation.SELFDESTRUCT]
    · simp at h2; tauto
    · simp [H, h1, h2] at hH

/-- On the two data-publishing halts, the bytes are exactly the memory slice the
contract asked for — `out` is not a free variable. -/
theorem out_eq_H_return {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out) (hop : op = .RETURN ∨ op = .REVERT) :
    out = μ.H_return := by
  rcases hop with h | h <;> subst h <;>
    (simp [H] at hH; first | exact hH | exact hH.symm)

/-- **A discharged branch.** On `STOP` and `SELFDESTRUCT` the call publishes no
bytes at all. This is a theorem about `H`, not a premise: the return-data half
of the endpoint obligation is closed on these two of the four exit branches. -/
theorem bytes_eq_nil_of_silent {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out) (hop : op = .STOP ∨ op = .SELFDESTRUCT) :
    bytes out = [] := by
  have hout : out = ByteArray.empty := by
    rcases hop with h | h <;> subst h <;>
      (simp [H] at hH; first | exact hH | exact hH.symm)
  subst hout; rfl

/-- `STOP` and `SELFDESTRUCT` are not `REVERT`, so a silent exit observes as a
success returning nothing. Fully determined, no premise. -/
theorem exitObservation_of_silent {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out) (hop : op = .STOP ∨ op = .SELFDESTRUCT) :
    exitObservation op out = { reverted := false, returnData := [] } := by
  have hne : op ≠ .REVERT := by rcases hop with h | h <;> subst h <;> simp
  rw [exitObservation, if_neg hne, bytes_eq_nil_of_silent hH hop]

/-! ### The exit data is not a premise either

`observe_result_exit` above still asks its caller for `H post.toMachineState op =
some out`. It should not have to. EVMYulLean decides `H`'s `some`-ness from the
opcode alone (`H_eq_none_iff`), and a `RunUntil` against the halting stop
condition that ended with fuel to spare ended *because* the decoded opcode halts
(`RunUntil.stop_of_rem_pos`). Composing the two derives the premise from the run
and, with it, pins the published bytes to a function of the machine.

So `out` stops being a universally quantified `ByteArray` supplied alongside a
side condition: below, every statement reads `haltData post.toMachineState op`.
-/

/-- The bytes `H` publishes at a halting opcode, as a function of the machine
rather than an existential: the requested memory slice on `RETURN` / `REVERT`,
nothing at all on `STOP` / `SELFDESTRUCT`. -/
def haltData (μ : MachineState) (op : Operation .EVM) : ByteArray :=
  if op ∈ [Operation.RETURN, Operation.REVERT] then μ.H_return else .empty

/-- At a halting opcode `H` is `some`, and what it publishes is `haltData`. This
is `H`'s definition read forwards; no run and no premise beyond `Halting`. -/
theorem H_eq_haltData {μ : MachineState} {op : Operation .EVM}
    (hop : Halting op = true) : H μ op = some (haltData μ op) := by
  by_cases h1 : op ∈ [Operation.RETURN, Operation.REVERT]
  · simp [H, haltData, h1]
  · have h2 : op ∈ [Operation.STOP, Operation.SELFDESTRUCT] := by
      simpa [Halting, h1] using hop
    simp [H, haltData, h1, h2]

/-- **The exit instruction halts — derived from the run.** A `RunUntil` against
the halting stop condition that stopped with fuel remaining records *why* it
stopped, and the only available reason is that the decoded opcode halts. -/
theorem exit_halting {kind : Kind} {c : XiCall kind} {rem : Nat}
    {trace : List Labelled} {exit : EVM.State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg)) :
    Halting op = true := by
  have h := hrun.stop_of_rem_pos (Nat.succ_ne_zero rem)
  rw [hdec] at h
  simpa [stopOrHalting] using h

/-- **`H` at the exit, with no premise at all.** The caller of every statement
below supplies the run; the halting data follows. -/
theorem exit_H {kind : Kind} {c : XiCall kind} {rem : Nat}
    {trace : List Labelled} {exit : EVM.State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg)) (μ : MachineState) :
    H μ op = some (haltData μ op) :=
  H_eq_haltData (exit_halting hrun hdec)

/-- `observe_result_exit` with its last premise discharged: the observation of a
complete `Ξ` call is fixed by the run alone, at bytes the run alone determines.
No `EndpointAgrees`, no `Represents`, no `H` side condition, no `native_decide`. -/
theorem observe_result_of_run {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post) :
    observe c.result = some (exitObservation op (haltData post.toMachineState op)) :=
  observe_result_exit c hrun hdec hZ hstep (exit_H hrun hdec _)

/-- The exit opcode is one of the four halting opcodes, from the run alone. -/
theorem exit_op_cases_of_run {kind : Kind} {c : XiCall kind} {rem : Nat}
    {trace : List Labelled} {exit : EVM.State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg)) :
    op = .RETURN ∨ op = .REVERT ∨ op = .STOP ∨ op = .SELFDESTRUCT :=
  exit_op_cases (exit_H hrun hdec exit.toMachineState)

/-- On the silent halts `haltData` is empty by computation. -/
@[simp] theorem haltData_of_silent {μ : MachineState} {op : Operation .EVM}
    (hop : op = .STOP ∨ op = .SELFDESTRUCT) : haltData μ op = .empty := by
  rcases hop with h | h <;> subst h <;> rfl

/-- On the publishing halts `haltData` is `H_return`, by computation. -/
@[simp] theorem haltData_REVERT (μ : MachineState) : haltData μ .REVERT = μ.H_return := rfl

/-- On the publishing halts `haltData` is `H_return`, by computation. -/
@[simp] theorem haltData_RETURN (μ : MachineState) : haltData μ .RETURN = μ.H_return := rfl

/-! ### Inverting `step` at the publishing halts

Everything above pins the published bytes to `haltData post.toMachineState op`,
i.e. to `post`'s `H_return`. That is still opaque: nothing said *where* those
bytes came from. `audit/assumptions.yaml` records this gap under
`A-ABSTRACT-TX` — the lemma owed is an inversion of EVMYulLean's `step` at
`.REVERT` yielding `post.toMachineState.H_return = mid.memory.readWithPadding _`.

This section discharges it, for `.REVERT` and `.RETURN` alike, with no premise
beyond the step itself and the shape of the operand stack. The chain is four
definitional unfoldings, each small enough to be `rfl`:

* `step_REVERT_delegates` / `step_RETURN_delegates` — `EVM.step` at positive
  fuel delegates to the shared `EvmYul.step` on the gas-charged state;
* `sharedStep_REVERT` / `sharedStep_RETURN` — the shared step at these opcodes
  *is* `binaryMachineStateOp` applied to `evmRevert` / `evmReturn`;
* `evmRevert_H_return` / `evmReturn_H_return` — that operation, on a stack that
  pops two words, writes exactly the requested memory slice into `H_return`;
* `haltData_eq_memory_slice` — composing the above through `haltData`.

The payoff is `bytes_haltData_eq_nil_of_zero_length`: a zero *length* operand
publishes no bytes, whatever the offset and whatever the memory. That is the
byte half of P-SUBMIT-1's residual, proved rather than assumed. -/

/-- `zeroes` is an `@[extern] def`, not `opaque`, so the empty padding reduces. -/
theorem zeroes_zero : ffi.ByteArray.zeroes 0 = ByteArray.empty := rfl

/-- A zero-length read is empty regardless of source and offset: the unpadded
read is an empty `extract` and the padding is `zeroes 0`. -/
theorem readWithPadding_size_zero (source : ByteArray) (addr : Nat) :
    (ByteArray.readWithPadding source addr 0).size = 0 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp [zeroes_zero]

/-- ... hence it publishes no bytes. -/
theorem bytes_readWithPadding_zero (source : ByteArray) (addr : Nat) :
    bytes (source.readWithPadding addr 0) = [] := by
  simp [bytes, readWithPadding_size_zero]

/-- Out of fuel is not a successful step, so the inversions below may assume
positive remaining fuel without weakening their statements. -/
theorem not_stepOk_zero {gasCost : Nat} {instr : EvmYul.EVM.Proof.Instruction}
    {pre post : EVM.State} : ¬ StepOk 0 gasCost instr pre post := by
  intro h
  have h' : (Except.error EVM.ExecutionException.OutOfFuel : Except _ EVM.State) = .ok post := h
  simp at h'

/-- `EVM.step` at `.REVERT` with fuel to spare is the shared step on the
gas-charged state. -/
theorem step_REVERT_delegates (f gasCost : Nat) (arg : Option (UInt256 × Nat))
    (mid : EVM.State) :
    EvmYul.EVM.step (f + 1) gasCost (some (.REVERT, arg)) mid =
      EvmYul.step (τ := .EVM) .REVERT arg
        { mid with execLength := mid.execLength + 1,
                   gasAvailable := mid.gasAvailable - UInt256.ofNat gasCost } := rfl

/-- `EVM.step` at `.RETURN` with fuel to spare is the shared step on the
gas-charged state. -/
theorem step_RETURN_delegates (f gasCost : Nat) (arg : Option (UInt256 × Nat))
    (mid : EVM.State) :
    EvmYul.EVM.step (f + 1) gasCost (some (.RETURN, arg)) mid =
      EvmYul.step (τ := .EVM) .RETURN arg
        { mid with execLength := mid.execLength + 1,
                   gasAvailable := mid.gasAvailable - UInt256.ofNat gasCost } := rfl

/-- The shared step at `.REVERT` is the two-operand machine-state operation. -/
theorem sharedStep_REVERT (arg : Option (UInt256 × Nat)) (st : EVM.State) :
    EvmYul.step (τ := .EVM) .REVERT arg st =
      EVM.binaryMachineStateOp MachineState.evmRevert st := rfl

/-- The shared step at `.RETURN` is the two-operand machine-state operation. -/
theorem sharedStep_RETURN (arg : Option (UInt256 × Nat)) (st : EVM.State) :
    EvmYul.step (τ := .EVM) .RETURN arg st =
      EVM.binaryMachineStateOp MachineState.evmReturn st := rfl

/-- **`REVERT` publishes the requested memory slice.** On a stack that pops two
words, the post state's `H_return` is exactly `memory.readWithPadding μ₀ μ₁`. -/
theorem evmRevert_H_return {st post : EVM.State} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hres : EVM.binaryMachineStateOp MachineState.evmRevert st = .ok post)
    (hstack : st.stack.pop2 = some (s, μ₀, μ₁)) :
    post.H_return = st.memory.readWithPadding μ₀.toNat μ₁.toNat := by
  unfold EVM.binaryMachineStateOp at hres
  rw [hstack] at hres
  rw [← Except.ok.inj hres]
  rfl

/-- **`RETURN` publishes the requested memory slice.** -/
theorem evmReturn_H_return {st post : EVM.State} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hres : EVM.binaryMachineStateOp MachineState.evmReturn st = .ok post)
    (hstack : st.stack.pop2 = some (s, μ₀, μ₁)) :
    post.H_return = st.memory.readWithPadding μ₀.toNat μ₁.toNat := by
  unfold EVM.binaryMachineStateOp at hres
  rw [hstack] at hres
  rw [← Except.ok.inj hres]
  rfl

/-- **The inversion `A-ABSTRACT-TX` named as owed, at `.REVERT`.** A successful
step at `.REVERT` from a state whose stack pops two words fixes the published
bytes to the memory slice those two words request. No fuel, gas, calldata,
world or model hypothesis. -/
theorem step_REVERT_H_return {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hstep : StepOk rem gasCost (.REVERT, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    post.toMachineState.H_return = mid.memory.readWithPadding μ₀.toNat μ₁.toNat := by
  cases rem with
  | zero => exact absurd hstep not_stepOk_zero
  | succ f =>
    unfold StepOk EvmYul.EVM.Proof.Step at hstep
    rw [step_REVERT_delegates, sharedStep_REVERT] at hstep
    have h := evmRevert_H_return hstep hstack
    exact h

/-- **The same inversion at `.RETURN`.** -/
theorem step_RETURN_H_return {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hstep : StepOk rem gasCost (.RETURN, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    post.toMachineState.H_return = mid.memory.readWithPadding μ₀.toNat μ₁.toNat := by
  cases rem with
  | zero => exact absurd hstep not_stepOk_zero
  | succ f =>
    unfold StepOk EvmYul.EVM.Proof.Step at hstep
    rw [step_RETURN_delegates, sharedStep_RETURN] at hstep
    have h := evmReturn_H_return hstep hstack
    exact h

/-- **The published slice, for either data-publishing halt.** `haltData` — the
function every statement above publishes through — is the memory slice named by
the exit's own stack operands. -/
theorem haltData_eq_memory_slice {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    haltData post.toMachineState op = mid.memory.readWithPadding μ₀.toNat μ₁.toNat := by
  rcases hop with h | h <;> subst h
  · rw [haltData_RETURN]; exact step_RETURN_H_return hstep hstack
  · rw [haltData_REVERT]; exact step_REVERT_H_return hstep hstack

/-- **Zero length ⇒ nothing published.** The byte half of P-SUBMIT-1's residual,
discharged: whatever the offset operand and whatever memory holds, a halt whose
length operand is zero publishes the empty list. -/
theorem bytes_haltData_eq_nil_of_zero_length {rem gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {mid post : EVM.State} {op : Operation .EVM}
    {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    bytes (haltData post.toMachineState op) = [] := by
  rw [haltData_eq_memory_slice hop hstep hstack, hlen]
  exact bytes_readWithPadding_zero mid.memory μ₀.toNat

/-! ### How wide the published slice is

`bytes_haltData_eq_nil_of_zero_length` is the `μ₁ = 0` corner of a fact that
holds at every width: `readWithPadding` pads its answer to *exactly* the
requested length, so the number of bytes a call publishes **is** the exit
instruction's own length operand. Nothing about memory, about the offset
operand, or about the code being run enters into it.

Two forms are proved, and the gap between them is the whole of what
`readWithPadding` does at absurd widths:

* `size_readWithPadding_le` — unconditional. The published width never exceeds
  the length operand. Above `2 ^ 64` the function panics and publishes nothing,
  and the zero padding is machine-word arithmetic; this direction survives both.
* `size_readWithPadding` — an *equality*, under `len < USize.size`. That side
  condition is not cosmetic: the padding length is a `USize`, so at widths the
  machine cannot address the count wraps. `USize.le_size` gives
  `2 ^ 32 ≤ USize.size` on every platform, so every width below `2 ^ 32`
  qualifies — and a memory expansion to `2 ^ 32` bytes is already unpayable.
-/

/-- `bytes` enumerates a `ByteArray` index by index, so it is exactly as long. -/
theorem bytes_length (b : ByteArray) : (bytes b).length = b.size := by
  simp [bytes]

/-- The zero padding is as long as the `USize` it is asked for. -/
theorem size_zeroes (u : USize) : (ffi.ByteArray.zeroes u).size = u.toNat := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- Truncated `Nat` subtraction commutes with the cast into `BitVec` when it does
not underflow. Needed because `readWithPadding` computes its padding length in
machine words: the `len - read.size` inside `zeroes ⟨_⟩` is `BitVec` subtraction
of two casts, not a cast of a `Nat` subtraction. -/
theorem natCast_sub_bitvec {w a b : Nat} (h : b ≤ a) :
    ((a : BitVec w) - (b : BitVec w)) = ((a - b : Nat) : BitVec w) := by
  have hab : ((a - b : Nat) : BitVec w) + (b : BitVec w) = (a : BitVec w) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel h]
  rw [← hab]; ring

/-- ... hence the padding count is `(len - read.size) mod 2 ^ numBits`. -/
theorem toNat_natCast_sub {w a b : Nat} (h : b ≤ a) :
    ((a : BitVec w) - (b : BitVec w)).toNat = (a - b) % 2 ^ w := by
  rw [natCast_sub_bitvec h]; rfl

/-- The unpadded read never returns more than was asked for: it is an `extract`
clipped to the source, or empty when the offset is past the end. -/
theorem size_readWithoutPadding_le (source : ByteArray) (addr len : Nat) :
    (source.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · rw [ByteArray.size_extract]; omega

/-- **The published width never exceeds the length operand** — unconditionally,
including at the panicking widths above `2 ^ 64`, where nothing is published at
all. -/
theorem size_readWithPadding_le (source : ByteArray) (addr len : Nat) :
    (source.readWithPadding addr len).size ≤ len := by
  unfold ByteArray.readWithPadding
  split
  · show (0 : Nat) ≤ len
    exact Nat.zero_le _
  · have hle := size_readWithoutPadding_le source addr len
    rw [ByteArray.size_append, size_zeroes]
    show _ + (BitVec.toNat _) ≤ _
    rw [toNat_natCast_sub hle]
    have := Nat.mod_le (len - (source.readWithoutPadding addr len).size)
      (2 ^ System.Platform.numBits)
    omega

/-- **The published width *is* the length operand**, at every width the machine
can address. The unpadded read is clipped to the source and the padding makes up
the difference exactly, so the answer is `len` bytes wide whatever memory holds
and whatever the offset. -/
theorem size_readWithPadding (source : ByteArray) (addr len : Nat)
    (hlen : len < USize.size) :
    (source.readWithPadding addr len).size = len := by
  have hnb : USize.size = 2 ^ System.Platform.numBits := rfl
  have h64 : len < 2 ^ 64 := lt_of_lt_of_le hlen USize.size_le
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  have hle := size_readWithoutPadding_le source addr len
  rw [ByteArray.size_append, size_zeroes]
  show _ + (BitVec.toNat _) = _
  rw [toNat_natCast_sub hle, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The same equality under a platform-independent bound: `USize.le_size` gives
`2 ^ 32 ≤ USize.size` on every platform Lean supports. -/
theorem size_readWithPadding_of_lt_two_pow_32 (source : ByteArray) (addr len : Nat)
    (hlen : len < 2 ^ 32) : (source.readWithPadding addr len).size = len :=
  size_readWithPadding source addr len (lt_of_lt_of_le hlen USize.le_size)

/-- **The width a complete call publishes is bounded by the exit's own length
operand.** Unconditional, given only the run and the shape of the operand
stack. -/
theorem length_bytes_haltData_le {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    (bytes (haltData post.toMachineState op)).length ≤ μ₁.toNat := by
  rw [haltData_eq_memory_slice hop hstep hstack, bytes_length]
  exact size_readWithPadding_le _ _ _

/-- **... and equals it** at any addressable width. This strictly generalises
`bytes_haltData_eq_nil_of_zero_length`, which is its `μ₁ = 0` instance. -/
theorem length_bytes_haltData {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlt : μ₁.toNat < USize.size) :
    (bytes (haltData post.toMachineState op)).length = μ₁.toNat := by
  rw [haltData_eq_memory_slice hop hstep hstack, bytes_length]
  exact size_readWithPadding _ _ _ hlt

/-! ## State relation and the named OPEN leaf -/

/-- Minimal main-based state relation, definitionally the core of R1's draft
`Eip8282.Audit.Represents`: only the pinned predeploy account is observed —
its code, its `WellFormed` packed storage, and its balance. -/
def Represents (kind : Kind) (world : EVM.State) (model : Model.State) : Prop :=
  ∃ acc : Account .EVM,
    world.accountMap.get? (targetAddr kind) = some acc ∧
      acc.code = runtimeCode kind ∧
      WellFormed kind acc.storage ∧
      model = toModel kind acc.storage acc.balance.toNat

/-- The abstract state a `Represents` witness supplies is a state of the right
kind. This is the one place the relation is load-bearing below: `capOf` and
`targetOf` in the drain and control statements read `model.kind`. -/
theorem Represents.kind_eq {kind : Kind} {world : EVM.State} {model : Model.State}
    (h : Represents kind world model) : model.kind = kind := by
  obtain ⟨_, _, _, _, hm⟩ := h
  rw [hm]
  exact WellFormed.toModel_kind kind _ _

/-- **The still-open leaf**, identical in shape to R2's and R3's and covered by
the existing `A-ABSTRACT-TX` ID: the terminal EVM observation agrees with the
abstract step. Proving it for every calldata/value/storage branch *is* the open
assumption. Naming it keeps a conditional composition from being read as the
missing universal opcode proof. -/
def EndpointAgrees (result : ExecutionResult EVM.State) (model : Outcome) : Prop :=
  observe (.ok result) = some (observeModel model)

/-- **The residual R4 leaves in place of `EndpointAgrees`.** Same named OPEN
assumption `A-ABSTRACT-TX`, but stated about the *exit instruction* instead of
the whole call: the halting instruction the code run exits on must publish the
model's status and the model's bytes.

This is what the whole-call obligation reduces to once `observe_result_exit`
closes the `Ξ` layer unconditionally. It is narrower in three concrete ways —
`exit_op_cases` confines it to four opcodes, `out_eq_H_return` removes `out` as
a free variable, and `exitAgrees_of_silent` discharges it outright on two of
those four — but it is *not* discharged, and R4 does not claim it is. -/
def ExitAgrees (op : Operation .EVM) (out : ByteArray) (model : Outcome) : Prop :=
  exitObservation op out = observeModel model

/-- The residual is exactly the old premise, so nothing is smuggled in or
quietly dropped by restating it: `A-ABSTRACT-TX` still covers the same content
at the same strength. -/
theorem endpointAgrees_iff_exitAgrees {post : EVM.State} {op : Operation .EVM}
    {out : ByteArray} {model : Outcome} :
    EndpointAgrees
        (if op = .REVERT then .revert post.gasAvailable out else .success post out) model
      ↔ ExitAgrees op out model := by
  by_cases hop : op = .REVERT <;>
    simp [EndpointAgrees, ExitAgrees, exitObservation, observe, hop]

/-- **The silent-halt branches are closed.** If the run exits on `STOP` or
`SELFDESTRUCT` the residual is no longer an assumption about bytes: it holds iff
the abstract step succeeded returning nothing, which the model-side theorems
decide. Nothing about the EVM run is assumed here. -/
theorem exitAgrees_of_silent {post : EVM.State} {op : Operation .EVM}
    {out : ByteArray} {model : Outcome}
    (hH : H post.toMachineState op = some out) (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hmodel : observeModel model = { reverted := false, returnData := [] }) :
    ExitAgrees op out model := by
  rw [ExitAgrees, exitObservation_of_silent hH hop, hmodel]

/-- **A silent halt cannot answer a call that must return bytes.** So for the
drain and control statements — whose model outcomes carry return data — the
residual only has to be checked on the `RETURN` / `REVERT` branches. This shrinks
the surface of `A-ABSTRACT-TX` rather than closing it. -/
theorem exit_op_publishes_of_returnData_ne_nil {post : EVM.State} {op : Operation .EVM}
    {out : ByteArray} {model : Outcome}
    (hH : H post.toMachineState op = some out)
    (hagree : ExitAgrees op out model)
    (hne : (observeModel model).returnData ≠ []) :
    op = .RETURN ∨ op = .REVERT := by
  rcases exit_op_cases hH with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  all_goals
    exfalso
    apply hne
    rw [← hagree]
    simpa using bytes_eq_nil_of_silent hH (by tauto)

/-- **The residual, restated over memory rather than over `H_return`.** With the
`step` inversion in hand, the residual on the publishing branches is no longer a
statement about an opaque post-state field: it is a statement about the slice of
*pre-step* memory the exit's own stack operands select. Nothing is assumed —
this is an `iff`, so `A-ABSTRACT-TX` keeps exactly its old content. -/
theorem exitAgrees_iff_memory_slice {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    {model : Outcome}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    ExitAgrees op (haltData post.toMachineState op) model
      ↔ ExitAgrees op (mid.memory.readWithPadding μ₀.toNat μ₁.toNat) model := by
  rw [haltData_eq_memory_slice hop hstep hstack]

/-- **The residual is decided outright when the exit publishes nothing.** A halt
whose length operand is zero satisfies the residual exactly when the abstract
step returns no data with the matching status — a condition with no EVM content
left in it. This is where `bytes_haltData_eq_nil_of_zero_length` pays off. -/
theorem exitAgrees_of_zero_length {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    {model : Outcome}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0)
    (hmodel : observeModel model =
      { reverted := if op = .REVERT then true else false, returnData := [] }) :
    ExitAgrees op (haltData post.toMachineState op) model := by
  rw [ExitAgrees, hmodel, exitObservation,
    bytes_haltData_eq_nil_of_zero_length hop hstep hstack hlen]
  split <;> rfl

/-! ### The residual pins the exit's length operand

The residual says the exit publishes the model's bytes. Since the published
*width* is the exit's own length operand, the residual therefore fixes that
operand: it cannot be a free `UInt256` once the abstract step is known. This is
strictly more than `exitAgrees_of_zero_length` gives — it constrains the machine
at every width, not only at zero — and it is where the remaining surface of
`A-ABSTRACT-TX` stops being about how *much* is published and becomes only about
*which bytes* those are. -/

/-- The residual, read on the return-data component alone. -/
theorem exitAgrees_returnData {op : Operation .EVM} {out : ByteArray} {model : Outcome}
    (h : ExitAgrees op out model) : bytes out = (observeModel model).returnData := by
  rw [← exitObservation_returnData op out, h]

/-- **The exit's length operand is at least as wide as the abstract answer.**
Unconditional: no bound on the operand is assumed. -/
theorem exitAgrees_length_operand_le {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    {model : Outcome}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op) model) :
    (observeModel model).returnData.length ≤ μ₁.toNat := by
  rw [← exitAgrees_returnData hend]
  exact length_bytes_haltData_le hop hstep hstack

/-- **The exit's length operand *is* the width of the abstract answer**, at any
addressable width. So the residual determines one of the exit's two stack
operands outright, from the model alone. -/
theorem exitAgrees_length_operand {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    {model : Outcome}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlt : μ₁.toNat < USize.size)
    (hend : ExitAgrees op (haltData post.toMachineState op) model) :
    μ₁.toNat = (observeModel model).returnData.length := by
  rw [← exitAgrees_returnData hend]
  exact (length_bytes_haltData hop hstep hstack hlt).symm

/-! ## The transport

One statement, quantified over the abstract step, so the user and system call
classes are the same theorem at different instances rather than two proofs.
-/

/-- **R4 transport, `∀` form at complete `Ξ`.**

For *every* complete `Ξ` message call `c` into the pinned runtime for `kind`,
from a world representing `model`, whose code run reaches a halting instruction
and whose endpoint agrees with the abstract step, the complete-`Ξ` observation
is the abstract observation.

Universally quantified over world, gas, substate, block context, fuel, calldata
and value. Not a finite trace. Not literal state equality — observation only.

The published bytes are **not** a bound variable and `H` is **not** a premise:
both come out of the run via `exit_H`, so the only thing left for a caller to
supply is the named OPEN residual itself. -/
def XiTransport (kind : Kind) (mstep : Model.Step) : Prop :=
  ∀ (c : XiCall kind) (model : Model.State)
    (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)),
    Represents kind c.entry model →
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep) →
    observe c.result = some (observeModel (Model.step model mstep))

theorem xiTransport (kind : Kind) (mstep : Model.Step) : XiTransport kind mstep := by
  intro c model rem gasCost trace exit mid post op arg _rep hrun hdec hZ hstep hend
  rw [observe_result_of_run c hrun hdec hZ hstep, hend]

/-- **R4's premise-free transport.** Everything the complete `Ξ` layer gives
without `A-ABSTRACT-TX`, bundled so each registered parent can carry it:

* the exit instruction halts, so `H` is `some` and the published bytes are a
  function of the machine — neither is a premise (`exit_halting`, `exit_H`);
* the whole call observes exactly the exit instruction (`observe_result_of_run`);
* the exit instruction is one of the four halting opcodes (`exit_op_cases`);
* on `RETURN` / `REVERT` the published bytes are the requested memory slice
  (`out_eq_H_return`);
* on `STOP` / `SELFDESTRUCT` the call publishes nothing (`bytes_eq_nil_of_silent`).

Universally quantified over world, gas, substate, block context, fuel, calldata
and value. **No hypothesis beyond the run itself** — in particular no `H`
premise and no quantified output bytes. No `native_decide`. -/
def XiExitTransport (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)),
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    Halting op = true ∧
      H post.toMachineState op = some (haltData post.toMachineState op) ∧
      observe c.result = some (exitObservation op (haltData post.toMachineState op)) ∧
      (op = .RETURN ∨ op = .REVERT ∨ op = .STOP ∨ op = .SELFDESTRUCT) ∧
      (op = .RETURN ∨ op = .REVERT →
        haltData post.toMachineState op = post.toMachineState.H_return) ∧
      (op = .STOP ∨ op = .SELFDESTRUCT →
        exitObservation op (haltData post.toMachineState op)
          = { reverted := false, returnData := [] })

theorem xiExitTransport (kind : Kind) : XiExitTransport kind := by
  intro c rem gasCost trace exit mid post op arg hrun hdec hZ hstep
  have hH := exit_H hrun hdec post.toMachineState
  exact ⟨exit_halting hrun hdec, hH, observe_result_of_run c hrun hdec hZ hstep,
    exit_op_cases hH, fun h => out_eq_H_return hH h,
    fun h => exitObservation_of_silent hH h⟩

/-- **R4's slice transport: where the published bytes come from.**
`XiExitTransport` pins the call's observation to `haltData`, but leaves
`haltData` opaque. This closes that gap for the two publishing halts, using the
`step` inversion above:

* the published bytes *are* the memory slice the exit's own stack operands
  select (`haltData_eq_memory_slice`);
* hence the whole call's observation is a function of pre-step memory and those
  two operands (`observe_result_of_run`);
* and a zero *length* operand publishes nothing, whatever the offset and
  whatever memory holds (`bytes_haltData_eq_nil_of_zero_length`).

Universally quantified over world, gas, substate, block context, fuel, calldata
and value. **No hypothesis beyond the run and the shape of the operand stack** —
no `ExitAgrees`, no `Represents`, no `H` premise, no `native_decide`. -/
def XiSliceTransport (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    (op = .RETURN ∨ op = .REVERT) →
    mid.stack.pop2 = some (s, μ₀, μ₁) →
    haltData post.toMachineState op = mid.memory.readWithPadding μ₀.toNat μ₁.toNat ∧
      observe c.result =
        some (exitObservation op (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)) ∧
      (μ₁.toNat = 0 → bytes (haltData post.toMachineState op) = [])

theorem xiSliceTransport (kind : Kind) : XiSliceTransport kind := by
  intro c rem gasCost trace exit mid post op arg s μ₀ μ₁ hrun hdec hZ hstep hop hstack
  have hslice := haltData_eq_memory_slice hop hstep hstack
  refine ⟨hslice, ?_, fun hlen => bytes_haltData_eq_nil_of_zero_length hop hstep hstack hlen⟩
  rw [observe_result_of_run c hrun hdec hZ hstep, hslice]

/-- **R4's width transport: how much a complete `Ξ` call publishes.**
`XiSliceTransport` pins the published bytes to a memory slice but says nothing
about how wide that slice is. This closes that:

* the published width never exceeds the exit's own length operand
  (`size_readWithPadding_le`), unconditionally;
* at any addressable width it *equals* that operand (`size_readWithPadding`);
* consequently the residual, whenever it holds, fixes the operand from the
  abstract step alone (`exitAgrees_length_operand_le` /
  `exitAgrees_length_operand`) — the width of what a pinned runtime publishes is
  not a free variable of `A-ABSTRACT-TX`.

The last two conjuncts are quantified over *every* abstract outcome, so they are
the same statement for the user and system call classes.

Universally quantified over world, gas, substate, block context, fuel, calldata
and value. **No hypothesis beyond the run and the shape of the operand stack.**
No `native_decide`. -/
def XiWidthTransport (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    (op = .RETURN ∨ op = .REVERT) →
    mid.stack.pop2 = some (s, μ₀, μ₁) →
    (bytes (haltData post.toMachineState op)).length ≤ μ₁.toNat ∧
      (μ₁.toNat < USize.size →
        (bytes (haltData post.toMachineState op)).length = μ₁.toNat) ∧
      (∀ model : Outcome,
        ExitAgrees op (haltData post.toMachineState op) model →
        (observeModel model).returnData.length ≤ μ₁.toNat) ∧
      (∀ model : Outcome,
        μ₁.toNat < USize.size →
        ExitAgrees op (haltData post.toMachineState op) model →
        μ₁.toNat = (observeModel model).returnData.length)

theorem xiWidthTransport (kind : Kind) : XiWidthTransport kind := by
  intro _ rem gasCost trace exit mid post op arg s μ₀ μ₁ _hrun _hdec _hZ hstep hop hstack
  exact ⟨length_bytes_haltData_le hop hstep hstack,
    fun hlt => length_bytes_haltData hop hstep hstack hlt,
    fun _ hend => exitAgrees_length_operand_le hop hstep hstack hend,
    fun _ hlt hend => exitAgrees_length_operand hop hstep hstack hlt hend⟩

/-! ## What each parent says at complete `Ξ`

The transport plus the already-`CHECKED` abstract-model theorems give each
parent's headline content as a complete-`Ξ` `∀`. These are the statements that
were previously only available on the model / CFG layer.
-/

/-- **P-SUBMIT-1 at `Ξ`: no writes on an inhibited predeploy.** An inhibited
predeploy reverts *every* user message call, whatever the calldata or value,
and a reverting `Ξ` returns no data. This is the revert-before-writes content
of the registered parent, observed at the complete message call. -/
theorem psubmit1_xi_inhibited_reverts {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hinh : inhibited model = true)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller calldata value))) :
    observe c.result = some { reverted := true, returnData := [] } := by
  rw [xiTransport kind (.user caller calldata value) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, userCall, hinh]

/-- P-SUBMIT-1's residual, spelled out. Because the model's revert carries no
data, the endpoint obligation on the inhibited path is *entirely* the two
EVM-side facts above — that the pinned run exits on `REVERT`, publishing an
empty slice. `Model` does not appear: the model half is proved from `hinh`, not
assumed. This is the narrowed form of `A-ABSTRACT-TX` for this parent. -/
theorem psubmit1_exitAgrees_iff {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = true) :
    ExitAgrees op out (Model.step model (.user caller calldata value))
      ↔ (op = .REVERT ∧ bytes out = []) := by
  constructor
  · intro h
    have h' : exitObservation op out = { reverted := true, returnData := [] } := by
      rw [h]; simp [Model.step, userCall, hinh]
    by_cases hop : op = .REVERT
    · exact ⟨hop, by simpa [exitObservation, hop] using congrArg Observation.returnData h'⟩
    · exact absurd (congrArg Observation.reverted h') (by simp [exitObservation, hop])
  · rintro ⟨hop, hb⟩
    rw [ExitAgrees, exitObservation, if_pos hop, hb]
    simp [Model.step, userCall, hinh]

/-- **P-SUBMIT-1 at `Ξ` with its residual in reduced form.** Same conclusion as
`psubmit1_xi_inhibited_reverts`, but the two hypotheses left are purely about
the EVM run — the pinned code exits on `REVERT`, publishing an empty slice. The
model half is *proved* from `inhibited model = true` via `psubmit1_exitAgrees_iff`,
not assumed. This is the honest shape of what `A-ABSTRACT-TX` still owes for
this parent. -/
theorem psubmit1_xi_inhibited_reverts_of_exit {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hinh : inhibited model = true)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hexit : op = .REVERT) (hsilent : bytes post.toMachineState.H_return = []) :
    observe c.result = some { reverted := true, returnData := [] } :=
  psubmit1_xi_inhibited_reverts c hinh hrep hrun hdec hZ hstep
    ((psubmit1_exitAgrees_iff (caller := caller) (calldata := calldata) (value := value)
      hinh).mpr ⟨hexit, by
        rw [out_eq_H_return (exit_H hrun hdec post.toMachineState) (Or.inr hexit)]
        exact hsilent⟩)

/-- **P-SUBMIT-1's residual, discharged.** `psubmit1_xi_inhibited_reverts_of_exit`
still *assumes* the exit publishes an empty slice. With the `step` inversion that
assumption is gone: it follows from the exit's own stack operands. A `REVERT`
whose length operand is zero satisfies `ExitAgrees` on the inhibited path
outright — no `A-ABSTRACT-TX`, no hypothesis about `post` at all beyond the step
that produced it. -/
theorem psubmit1_exitAgrees_of_zero_length {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = true)
    (hexit : op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller calldata value)) :=
  (psubmit1_exitAgrees_iff hinh).mpr
    ⟨hexit, bytes_haltData_eq_nil_of_zero_length (Or.inr hexit) hstep hstack hlen⟩

/-- **P-SUBMIT-1's residual as a condition on the exit machine.** With the width
lemma the `bytes out = []` half of `psubmit1_exitAgrees_iff` is no longer a
statement about a `ByteArray` at all: on an inhibited predeploy the residual
holds *exactly* when the run exits on a `REVERT` whose length operand is zero.

Both directions are proved, so this neither strengthens nor weakens
`A-ABSTRACT-TX` for this parent — it relocates it, from an opaque published
payload to two decidable facts about the halting instruction's own operands.
Nothing about memory, about the offset operand, or about `Model` remains. -/
theorem psubmit1_exitAgrees_iff_operand {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = true)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlt : μ₁.toNat < USize.size) :
    ExitAgrees op (haltData post.toMachineState op)
        (Model.step model (.user caller calldata value))
      ↔ (op = .REVERT ∧ μ₁.toNat = 0) := by
  rw [psubmit1_exitAgrees_iff hinh]
  constructor
  · rintro ⟨hop, hb⟩
    refine ⟨hop, ?_⟩
    have hw := length_bytes_haltData (Or.inr hop) hstep hstack hlt
    rw [hb] at hw
    simpa using hw.symm
  · rintro ⟨hop, hl⟩
    exact ⟨hop, bytes_haltData_eq_nil_of_zero_length (Or.inr hop) hstep hstack hl⟩

/-- **P-SUBMIT-1 at complete `Ξ`, unconditionally on the inhibited path.** Same
conclusion as `psubmit1_xi_inhibited_reverts`, with *no* `ExitAgrees` premise:
if the pinned run exits on a `REVERT` whose length operand is zero, an inhibited
predeploy is observed to revert with no data. The named OPEN `A-ABSTRACT-TX`
does not appear in the hypotheses — every remaining premise is a fact about the
EVM run itself. -/
theorem psubmit1_xi_inhibited_reverts_of_zero_length {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = true)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hexit : op = .REVERT)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    observe c.result = some { reverted := true, returnData := [] } :=
  psubmit1_xi_inhibited_reverts c hinh hrep hrun hdec hZ hstep
    (psubmit1_exitAgrees_of_zero_length (caller := caller) (calldata := calldata)
      (value := value) hinh hexit hstep hstack hlen)

/-- **P-SUBMIT-1's residual on the *accepting* path, in closed form.** The
inhibited path above is only half of the parent: an uninhibited predeploy that
is handed admissible, non-empty calldata *queues* the request and answers with
no data. `Model.userCall` returns `.success _ []` there, so — exactly as for
`pdrain1_exitAgrees_iff` — the residual collapses to two facts about the exit
instruction with no `Outcome` left in it, and the model half is proved from
`hinh`/`hadm` rather than assumed. -/
theorem psubmit1_exitAgrees_iff_accepted {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = true) :
    ExitAgrees op out (Model.step model (.user caller calldata value))
      ↔ (op ≠ .REVERT ∧ bytes out = []) := by
  have hmodel : observeModel (Model.step model (.user caller calldata value))
      = { reverted := false, returnData := [] } := by
    simp [Model.step, userCall, hinh, hne, hadm]
  rw [ExitAgrees, hmodel]
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **An accepted submission is never observed to revert.** Discharged outright
from the closed form: no hypothesis about the run, only that the abstract call
was accepted. This is the accepting path's analogue of
`pdrain1_xi_exit_not_REVERT`, and it removes one of `H`'s four exit branches
from what `A-ABSTRACT-TX` must cover here. -/
theorem psubmit1_xi_accepted_exit_not_REVERT {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = true)
    (hend : ExitAgrees op out (Model.step model (.user caller calldata value))) :
    op ≠ .REVERT :=
  ((psubmit1_exitAgrees_iff_accepted hinh hne hadm).mp hend).1

/-- **P-SUBMIT-1's residual is proved, not assumed, on a silent halt of an
accepted submission.** `STOP` and `SELFDESTRUCT` publish nothing and are not
`REVERT`, which is all the closed form asks for once the abstract call succeeds
with no data. Nothing about the run's memory is assumed — `ExitAgrees` is
*produced* here, not consumed. -/
theorem psubmit1_exitAgrees_of_silent_accepted {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = true)
    (hH : H μ op = some out)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT) :
    ExitAgrees op out (Model.step model (.user caller calldata value)) := by
  refine (psubmit1_exitAgrees_iff_accepted hinh hne hadm).mpr ⟨?_, ?_⟩
  · rcases hop with h | h <;> subst h <;> simp
  · exact bytes_eq_nil_of_silent hH hop

/-- **... and on a `RETURN` whose slice is zero-width.** By
`bytes_haltData_eq_nil_of_zero_length` such an exit publishes nothing whatever
the offset and whatever memory holds, which is exactly the accepted
submission's answer. -/
theorem psubmit1_exitAgrees_of_zero_length_accepted {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = true)
    (hop : op = .RETURN)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller calldata value)) :=
  (psubmit1_exitAgrees_iff_accepted hinh hne hadm).mpr
    ⟨by subst hop; simp,
      bytes_haltData_eq_nil_of_zero_length (Or.inl hop) hstep hstack hlen⟩

/-- **P-SUBMIT-1 at complete `Ξ` on the accepting path, with no residual at
all.** An uninhibited predeploy handed admissible calldata, whose pinned run
exits on a `RETURN` with a zero-width slice, is *observed* to succeed publishing
nothing — the abstract submission's answer. There is no `ExitAgrees` hypothesis,
so this branch does not rest on `A-ABSTRACT-TX`. Together with
`psubmit1_xi_inhibited_reverts_of_zero_length` both halves of P-SUBMIT-1's user
call — the refusal and the acceptance — are now off the assumption. -/
theorem psubmit1_xi_accepted_returns_nothing {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = true)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    observe c.result = some { reverted := false, returnData := [] } := by
  have hend := psubmit1_exitAgrees_of_zero_length_accepted (caller := caller)
    hinh hne hadm hop hstep hstack hlen
  rw [xiTransport kind (.user caller calldata value) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, userCall, hinh, hne, hadm]

/-- **P-SUBMIT-1's residual on the *rejected* path, in closed form.** The
inhibited and accepting paths are still not all of `Model.userCall`. An
uninhibited predeploy handed non-empty calldata that fails `admissible` — wrong
length, a byte out of range, an under-funded deposit, an under-paid exit —
refuses the submission with `.revert`, and a revert carries no data. The
residual is therefore the same pure EVM-side pair as the inhibited path, and the
model half is proved from `hinh`/`hne`/`hadm` rather than assumed. -/
theorem psubmit1_exitAgrees_iff_rejected {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = false) :
    ExitAgrees op out (Model.step model (.user caller calldata value))
      ↔ (op = .REVERT ∧ bytes out = []) := by
  have hmodel : observeModel (Model.step model (.user caller calldata value))
      = { reverted := true, returnData := [] } := by
    simp [Model.step, userCall, hinh, hne, hadm]
  rw [ExitAgrees, hmodel]
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **A rejected submission pins the exit opcode to `REVERT`**, with no
hypothesis about `H`, about memory, or about the run — three of `H`'s four
branches are refuted by the abstract refusal alone. -/
theorem psubmit1_xi_rejected_exit_is_REVERT {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = false)
    (hend : ExitAgrees op out (Model.step model (.user caller calldata value))) :
    op = .REVERT :=
  ((psubmit1_exitAgrees_iff_rejected hinh hne hadm).mp hend).1

/-- **P-SUBMIT-1's residual is proved, not assumed, on the rejected path.** A
`REVERT` whose length operand is zero publishes nothing whatever the offset and
whatever memory holds, which is exactly what a refused submission answers.
`ExitAgrees` is produced here, not consumed. -/
theorem psubmit1_exitAgrees_of_zero_length_rejected {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = false)
    (hop : op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller calldata value)) :=
  (psubmit1_exitAgrees_iff_rejected hinh hne hadm).mpr
    ⟨hop, bytes_haltData_eq_nil_of_zero_length (Or.inr hop) hstep hstack hlen⟩

/-- **P-SUBMIT-1 at complete `Ξ` on the rejected path, with no residual at all.**
An uninhibited predeploy handed inadmissible non-empty calldata, whose pinned run
exits on a `REVERT` with a zero-width slice, is *observed* to revert with no data
— the abstract refusal's answer, at the complete message call, with no
`ExitAgrees` premise. This is the fourth branch off `A-ABSTRACT-TX`, and with it
every `Model.userCall` answer that carries no return data is discharged. -/
theorem psubmit1_xi_rejected_reverts_of_zero_length {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hne : calldata ≠ [])
    (hadm : admissible model calldata value = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .REVERT)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    observe c.result = some { reverted := true, returnData := [] } := by
  have hend := psubmit1_exitAgrees_of_zero_length_rejected (caller := caller)
    hinh hne hadm hop hstep hstack hlen
  rw [xiTransport kind (.user caller calldata value) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, userCall, hinh, hne, hadm]

/-! ### The user-call surface `A-ABSTRACT-TX` still has to cover

The four branches above — inhibited, paid, rejected, accepted — are the four
`Model.userCall` answers that carry no return data, and each is now discharged
from the exit instruction's own operands. The theorem below shows that is not a
coincidence of case analysis but an exhaustive one: the fee quote is the *only*
user call whose abstract answer publishes anything at all. -/

/-- **Only the fee quote publishes bytes.** A user call returns data exactly when
the predeploy is uninhibited and the call is the empty-calldata, zero-value fee
getter. Every other answer — the inhibited refusal, the payable refusal, the
inadmissible refusal, the accepted submission — is data-free, so its residual is
decided by `bytes_haltData_eq_nil_of_zero_length` and never by memory.

This is what makes the branch count exact rather than anecdotal: after this
revision the user-call half of `A-ABSTRACT-TX` is *one* branch, and it is named
here. -/
theorem userCall_returnData_ne_nil_iff {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei} :
    (observeModel (Model.step model (.user caller calldata value))).returnData ≠ []
      ↔ (inhibited model = false ∧ calldata = [] ∧ value = 0) := by
  by_cases hinh : inhibited model = true
  · simp [Model.step, userCall, hinh]
  · have hinh' : inhibited model = false := by simpa using hinh
    by_cases hcd : calldata = []
    · subst hcd
      by_cases hv : value = 0
      · subst hv
        have h32 : (toBeBytes (currentFee model) 32).length = 32 :=
          Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_length _ _
        have hne : toBeBytes (currentFee model) 32 ≠ [] := by
          intro h
          rw [h] at h32
          simp at h32
        simp [Model.step, userCall, hinh', hne]
      · simp [Model.step, userCall, hinh', hv]
    · by_cases hadm : admissible model calldata value = true
      · simp [Model.step, userCall, hinh', hcd, hadm]
      · have hadm' : admissible model calldata value = false := by simpa using hadm
        simp [Model.step, userCall, hinh', hcd, hadm']

/-- **P-DRAIN-1 at `Ξ`: the system call returns exactly the bounded FIFO
prefix.** A system message call succeeds and returns `concatReturned` of the
oldest `capOf kind` queued records — the FIFO window, capped, in order. -/
theorem pdrain1_xi_returns_fifo_prefix {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.system calldataNonempty))) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } := by
  rw [xiTransport kind (.system calldataNonempty) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, systemCall, Represents.kind_eq hrep]

/-- **P-DRAIN-1's residual cannot be met by a silent halt** whenever the FIFO
window is non-empty: `STOP` and `SELFDESTRUCT` publish nothing, so the drain
answer must come out of a `RETURN`. Derived, not assumed — it narrows where
`A-ABSTRACT-TX` still has to be checked. -/
theorem pdrain1_xi_exit_publishes {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {post : EVM.State} {op : Operation .EVM} {out : ByteArray}
    (hrepkind : model.kind = kind)
    (hH : H post.toMachineState op = some out)
    (hend : ExitAgrees op out (Model.step model (.system calldataNonempty)))
    (hne : concatReturned (model.queue.take (capOf kind)) ≠ []) :
    op = .RETURN ∨ op = .REVERT := by
  refine exit_op_publishes_of_returnData_ne_nil hH hend ?_
  simpa [Model.step, systemCall, hrepkind] using hne

/-- The drain answer, as the observation component the residual constrains. -/
theorem pdrain1_returnData {kind : Kind} {model : Model.State} {calldataNonempty : Bool}
    (hrepkind : model.kind = kind) :
    (observeModel (Model.step model (.system calldataNonempty))).returnData
      = concatReturned (model.queue.take (capOf kind)) := by
  simp [Model.step, systemCall, hrepkind]

/-- **P-DRAIN-1's residual, in closed form.** `Model.systemCall` is total: it has
no `revert` constructor at all, so its observation is `reverted := false` with the
encoded FIFO window as data, whatever the calldata flag and whatever the state.
The residual therefore collapses to two facts about the *exit instruction* with
no `Outcome` left in it — the drain analogue of `psubmit1_exitAgrees_iff`. This
is an `iff`, so `A-ABSTRACT-TX` keeps exactly its old content for this parent. -/
theorem pdrain1_exitAgrees_iff {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {op : Operation .EVM} {out : ByteArray}
    (hrepkind : model.kind = kind) :
    ExitAgrees op out (Model.step model (.system calldataNonempty))
      ↔ (op ≠ .REVERT ∧ bytes out = concatReturned (model.queue.take (capOf kind))) := by
  have hmodel : observeModel (Model.step model (.system calldataNonempty))
      = { reverted := false
          returnData := concatReturned (model.queue.take (capOf kind)) } := by
    simp [Model.step, systemCall, hrepkind]
  rw [ExitAgrees, hmodel]
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **The drain residual splits record by record.** The window's encoding is a
concatenation, so the residual does not constrain the published slice as one
opaque block: the first `(encodeReturned r).length` bytes must be the head
record's encoding, and what follows must be the encoding of the rest. Derived
from the closed form, so nothing is assumed beyond the residual itself.

This is the drain's analogue of `pcontrol1_exitAgrees_iff_digits`: it says
*where* in the published slice each queued record has to appear, which is the
form the remaining surface of `A-ABSTRACT-TX` takes for this parent. -/
theorem pdrain1_exitAgrees_head_record {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {op : Operation .EVM} {out : ByteArray}
    {r : Record} {rs : List Record}
    (hrepkind : model.kind = kind)
    (hend : ExitAgrees op out (Model.step model (.system calldataNonempty)))
    (hq : model.queue.take (capOf kind) = r :: rs) :
    (bytes out).take (encodeReturned r).length = encodeReturned r ∧
      (bytes out).drop (encodeReturned r).length = concatReturned rs := by
  have hb : bytes out = encodeReturned r ++ concatReturned rs := by
    rw [((pdrain1_exitAgrees_iff hrepkind).mp hend).2, hq, concatReturned]
    simp [concatReturned]
  rw [hb]
  exact ⟨List.take_left, List.drop_left⟩

/-- **A drain is never observed to revert.** Discharged outright: no hypothesis
on the FIFO window, on the represented kind, or on the run. This is the branch
`pdrain1_xi_exit_publishes` had to leave open, and it closes because the abstract
side cannot revert, not because of anything assumed about the bytecode. -/
theorem pdrain1_xi_exit_not_REVERT {model : Model.State} {calldataNonempty : Bool}
    {op : Operation .EVM} {out : ByteArray}
    (hend : ExitAgrees op out (Model.step model (.system calldataNonempty))) :
    op ≠ .REVERT :=
  ((pdrain1_exitAgrees_iff (kind := model.kind) rfl).mp hend).1

/-- **P-DRAIN-1's exit opcode is pinned to `RETURN`.** On a non-empty FIFO window
the silent halts are refuted by `pdrain1_xi_exit_publishes` and `REVERT` by
`pdrain1_xi_exit_not_REVERT`, so exactly one of `H`'s four branches survives.
This parent's share of `A-ABSTRACT-TX` is now one branch, not two — the same
position `pcontrol1_xi_exit_is_RETURN` already holds for the fee getter. -/
theorem pdrain1_xi_exit_is_RETURN {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {post : EVM.State} {op : Operation .EVM} {out : ByteArray}
    (hrepkind : model.kind = kind)
    (hH : H post.toMachineState op = some out)
    (hend : ExitAgrees op out (Model.step model (.system calldataNonempty)))
    (hne : concatReturned (model.queue.take (capOf kind)) ≠ []) :
    op = .RETURN :=
  (pdrain1_xi_exit_publishes hrepkind hH hend hne).resolve_right
    (pdrain1_xi_exit_not_REVERT hend)

/-- **P-DRAIN-1's residual is proved, not assumed, on a silent halt over an empty
window.** When the capped FIFO prefix encodes to nothing, `STOP` and
`SELFDESTRUCT` publish exactly that and are not `REVERT`, which is all the closed
form asks for. Nothing about the run's memory is assumed. -/
theorem pdrain1_exitAgrees_of_silent {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hrepkind : model.kind = kind)
    (hH : H μ op = some out)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hempty : concatReturned (model.queue.take (capOf kind)) = []) :
    ExitAgrees op out (Model.step model (.system calldataNonempty)) := by
  refine (pdrain1_exitAgrees_iff hrepkind).mpr ⟨?_, ?_⟩
  · rcases hop with h | h <;> subst h <;> simp
  · rw [bytes_eq_nil_of_silent hH hop, hempty]

/-- **... and on a `RETURN` whose slice is zero-width.** Same branch from the
publishing side: by `bytes_haltData_eq_nil_of_zero_length` such an exit publishes
nothing whatever the offset and whatever memory holds, which is the empty
window's answer. Again no `ExitAgrees` is consumed — it is produced. -/
theorem pdrain1_exitAgrees_of_zero_length {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hrepkind : model.kind = kind)
    (hop : op = .RETURN)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0)
    (hempty : concatReturned (model.queue.take (capOf kind)) = []) :
    ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.system calldataNonempty)) := by
  refine (pdrain1_exitAgrees_iff hrepkind).mpr ⟨by subst hop; simp, ?_⟩
  rw [bytes_haltData_eq_nil_of_zero_length (Or.inl hop) hstep hstack hlen, hempty]

/-- **P-DRAIN-1 at complete `Ξ` with no residual at all.** On an empty FIFO
window, a run that exits on a `RETURN` with a zero-width slice is *observed* to
succeed publishing nothing — which is exactly the abstract drain's answer. There
is no `ExitAgrees` hypothesis, so this branch of the parent does not rest on
`A-ABSTRACT-TX`, the same way `psubmit1_xi_inhibited_reverts_of_zero_length` does
not for P-SUBMIT-1's inhibited path. -/
theorem pdrain1_xi_empty_window_returns_nothing {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0)
    (hempty : concatReturned (model.queue.take (capOf kind)) = []) :
    observe c.result = some { reverted := false, returnData := [] } := by
  have hend := pdrain1_exitAgrees_of_zero_length (calldataNonempty := calldataNonempty)
    (Represents.kind_eq hrep) hop hstep hstack hlen hempty
  rw [xiTransport kind (.system calldataNonempty) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, systemCall, Represents.kind_eq hrep, hempty]

/-- **P-DRAIN-1's exit must request at least the whole FIFO window.** The width
a `RETURN` publishes is bounded by its own length operand, and the residual makes
that width the drain answer — so the operand is bounded below by the encoded
length of the capped queue prefix. Unconditional in the operand: no bound on
`μ₁` is assumed, and the exit opcode is *derived* rather than supplied. -/
theorem pdrain1_xi_exit_length_ge {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hrepkind : model.kind = kind)
    (hH : H post.toMachineState op = some (haltData post.toMachineState op))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.system calldataNonempty))) :
    (concatReturned (model.queue.take (capOf kind))).length ≤ μ₁.toNat := by
  by_cases hne : concatReturned (model.queue.take (capOf kind)) = []
  · simp [hne]
  · have hop := pdrain1_xi_exit_publishes hrepkind hH hend hne
    have hle := exitAgrees_length_operand_le hop hstep hstack hend
    rwa [pdrain1_returnData hrepkind] at hle

/-- **... and on a non-empty window it requests exactly that.** The exit's length
operand is pinned to the encoded width of the capped FIFO prefix — a quantity
computed entirely on the model side. This is a constraint on the pinned
runtime's exit machine derived from the parent, not a new assumption. -/
theorem pdrain1_xi_exit_length_eq {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hrepkind : model.kind = kind)
    (hH : H post.toMachineState op = some (haltData post.toMachineState op))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.system calldataNonempty)))
    (hne : concatReturned (model.queue.take (capOf kind)) ≠ [])
    (hlt : μ₁.toNat < USize.size) :
    μ₁.toNat = (concatReturned (model.queue.take (capOf kind))).length := by
  have hop := pdrain1_xi_exit_publishes hrepkind hH hend hne
  have heq := exitAgrees_length_operand hop hstep hstack hlt hend
  rwa [pdrain1_returnData hrepkind] at heq

/-- **P-CONTROL-1 at `Ξ`: the fee getter quotes `currentFee`, read-only.** An
uninhibited predeploy answers an empty-calldata, zero-value user message call
with the 32-byte big-endian `currentFee` of the represented state — the exact
fee algebra the registered parent fixes, at the complete message call. -/
theorem pcontrol1_xi_fee_getter {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller [] 0))) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
  rw [xiTransport kind (.user caller [] 0) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, userCall, hinh]

/-- **P-CONTROL-1's fee quote must come out of a `RETURN`.** The fee is 32 bytes
wide — `toBeBytes _ 32` is never the empty list — so the silent halts are
refuted outright and, since the quote is a success, `REVERT` is too. The exit
opcode is therefore *pinned* to `RETURN`: this parent's share of
`A-ABSTRACT-TX` is one branch, not four. -/
theorem pcontrol1_xi_exit_is_RETURN {model : Model.State} {caller : Address}
    {post : EVM.State} {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hH : H post.toMachineState op = some out)
    (hend : ExitAgrees op out (Model.step model (.user caller [] 0))) :
    op = .RETURN := by
  have hobs : exitObservation op out =
      { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
    rw [hend]; simp [Model.step, userCall, hinh]
  have hop : op ≠ .REVERT := by
    intro h
    exact absurd (congrArg Observation.reverted hobs) (by simp [exitObservation, h])
  have hne : bytes out ≠ [] := by
    rw [← exitObservation_returnData op out, hobs]
    intro h
    have hlen : (toBeBytes (currentFee model) 32).length = 32 :=
      Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_length _ _
    rw [show toBeBytes (currentFee model) 32 = [] from h] at hlen
    simp at hlen
  rcases exit_op_cases hH with h | h | h | h
  · exact h
  · exact absurd h hop
  all_goals exact absurd (bytes_eq_nil_of_silent hH (by tauto)) hne

/-- **P-CONTROL-1's exit cannot request a zero-length slice.** The fee quote is
32 bytes wide, and by the `step` inversion the published width *is* the exit's
own length operand — so that operand is pinned away from zero. This is a
constraint on the machine derived from the parent, the converse direction of
`bytes_haltData_eq_nil_of_zero_length`. -/
theorem pcontrol1_xi_exit_length_ne_zero {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hH : H post.toMachineState op = some (haltData post.toMachineState op))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller [] 0))) :
    μ₁.toNat ≠ 0 := by
  intro hlen
  have hop : op = .RETURN ∨ op = .REVERT := Or.inl (pcontrol1_xi_exit_is_RETURN hinh hH hend)
  have hobs : exitObservation op (haltData post.toMachineState op) =
      { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
    rw [hend]; simp [Model.step, userCall, hinh]
  have hb : bytes (haltData post.toMachineState op) = toBeBytes (currentFee model) 32 := by
    rw [← exitObservation_returnData op (haltData post.toMachineState op), hobs]
  rw [bytes_haltData_eq_nil_of_zero_length hop hstep hstack hlen] at hb
  have hlen32 : (toBeBytes (currentFee model) 32).length = 32 :=
    Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_length _ _
  rw [← hb] at hlen32
  simp at hlen32

/-- The fee quote, as the observation component the residual constrains. -/
theorem pcontrol1_returnData_length {model : Model.State} {caller : Address}
    (hinh : inhibited model = false) :
    (observeModel (Model.step model (.user caller [] 0))).returnData.length = 32 := by
  have hobs : observeModel (Model.step model (.user caller [] 0))
      = { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
    simp [Model.step, userCall, hinh]
  rw [hobs]
  exact Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_length _ _

/-- **P-CONTROL-1's exit requests at least 32 bytes.** Strictly stronger than
`pcontrol1_xi_exit_length_ne_zero`, and proved the same way it should be: the
published width is bounded by the length operand, and the residual makes that
width 32. Unconditional in the operand. -/
theorem pcontrol1_xi_exit_length_ge_32 {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hH : H post.toMachineState op = some (haltData post.toMachineState op))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller [] 0))) :
    32 ≤ μ₁.toNat := by
  have hop : op = .RETURN ∨ op = .REVERT := Or.inl (pcontrol1_xi_exit_is_RETURN hinh hH hend)
  have hle := exitAgrees_length_operand_le hop hstep hstack hend
  rwa [pcontrol1_returnData_length hinh] at hle

/-- **... and exactly 32.** The fee getter's exit is now pinned on both stack
operands' worth of content the residual can still be about: the opcode is
`RETURN` (`pcontrol1_xi_exit_is_RETURN`) and the length operand is `32`. What
`A-ABSTRACT-TX` still owes for this parent is only *which* 32 bytes of memory
sit at the offset operand. -/
theorem pcontrol1_xi_exit_length_eq_32 {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)} {mid post : EVM.State}
    {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hH : H post.toMachineState op = some (haltData post.toMachineState op))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hend : ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller [] 0)))
    (hlt : μ₁.toNat < USize.size) :
    μ₁.toNat = 32 := by
  have hop : op = .RETURN ∨ op = .REVERT := Or.inl (pcontrol1_xi_exit_is_RETURN hinh hH hend)
  have heq := exitAgrees_length_operand hop hstep hstack hlt hend
  rwa [pcontrol1_returnData_length hinh] at heq

/-- **P-CONTROL-1's residual, in closed form.** The fee getter's abstract answer
is a success carrying `toBeBytes (currentFee model) 32`, so — as for
`pdrain1_exitAgrees_iff` — the residual is two facts about the exit instruction
with no `Outcome` in it: the exit is not a `REVERT`, and it publishes the fee
word. Both directions are proved, so `A-ABSTRACT-TX` keeps exactly its old
content for this parent; it is relocated, not weakened. -/
theorem pcontrol1_exitAgrees_iff {model : Model.State} {caller : Address}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false) :
    ExitAgrees op out (Model.step model (.user caller [] 0))
      ↔ (op ≠ .REVERT ∧ bytes out = toBeBytes (currentFee model) 32) := by
  have hmodel : observeModel (Model.step model (.user caller [] 0))
      = { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
    simp [Model.step, userCall, hinh]
  rw [ExitAgrees, hmodel]
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **P-CONTROL-1's residual, byte by byte.** `pcontrol1_exitAgrees_iff` leaves a
`List Nat` equation against `toBeBytes`. The width is already pinned to exactly
32 by `pcontrol1_xi_exit_length_eq_32`, so under that width the equation is
equivalent to 32 independent statements about individual published bytes, each
naming one base-256 digit of the quoted fee. Both directions are proved, so this
neither strengthens nor weakens `A-ABSTRACT-TX`; it says precisely *which* bytes
the open premise is still about, and the model enters only through
`currentFee`. -/
theorem pcontrol1_exitAgrees_iff_digits {model : Model.State} {caller : Address}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hwidth : (bytes out).length = 32) :
    ExitAgrees op out (Model.step model (.user caller [] 0))
      ↔ (op ≠ .REVERT ∧
          ∀ i, i < 32 →
            (bytes out)[i]? = some ((currentFee model / 256 ^ (32 - 1 - i)) % 256)) := by
  rw [pcontrol1_exitAgrees_iff hinh]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hb i hi
    rw [hb]
    exact Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_getElem? _ _ _ hi
  · intro hd
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < 32
    · rw [hd i hi, Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_getElem? _ _ _ hi]
    · have h1 : (bytes out)[i]? = none := List.getElem?_eq_none (by omega)
      have h2 : (toBeBytes (currentFee model) 32)[i]? = none := by
        refine List.getElem?_eq_none ?_
        rw [Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_length]
        omega
      rw [h1, h2]

/-- **The fee getter is never observed to revert**, read straight off the closed
form. `pcontrol1_xi_exit_is_RETURN` already pinned the opcode, but it needed the
side condition `H post.toMachineState op = some out` to enumerate `H`'s
branches; this needs nothing but the residual itself. -/
theorem pcontrol1_xi_exit_not_REVERT {model : Model.State} {caller : Address}
    {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false)
    (hend : ExitAgrees op out (Model.step model (.user caller [] 0))) :
    op ≠ .REVERT :=
  ((pcontrol1_exitAgrees_iff hinh).mp hend).1

/-- **The fee getter is not payable, in closed form.** An empty-calldata call
carrying value is refused by `Model.userCall` before the quote is computed —
`.revert`, which carries no data. The residual for that branch is therefore the
same pure EVM-side pair as P-SUBMIT-1's inhibited path: exit on `REVERT`,
publish nothing. -/
theorem pcontrol1_exitAgrees_iff_paid {model : Model.State} {caller : Address}
    {value : Wei} {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false) (hval : value ≠ 0) :
    ExitAgrees op out (Model.step model (.user caller [] value))
      ↔ (op = .REVERT ∧ bytes out = []) := by
  have hmodel : observeModel (Model.step model (.user caller [] value))
      = { reverted := true, returnData := [] } := by
    simp [Model.step, userCall, hinh, hval]
  rw [ExitAgrees, hmodel]
  by_cases hop : op = .REVERT <;> simp [exitObservation, hop]

/-- **A paid fee-getter call pins the exit opcode to `REVERT`**, with no
hypothesis about `H`, about memory, or about the run — three of `H`'s four
branches are refuted by the abstract refusal alone. -/
theorem pcontrol1_xi_paid_exit_is_REVERT {model : Model.State} {caller : Address}
    {value : Wei} {op : Operation .EVM} {out : ByteArray}
    (hinh : inhibited model = false) (hval : value ≠ 0)
    (hend : ExitAgrees op out (Model.step model (.user caller [] value))) :
    op = .REVERT :=
  ((pcontrol1_exitAgrees_iff_paid hinh hval).mp hend).1

/-- **P-CONTROL-1's residual is proved, not assumed, on the paid branch.** A
`REVERT` whose length operand is zero publishes nothing whatever the offset and
whatever memory holds, which is exactly what a refused payable call answers.
`ExitAgrees` is produced here, not consumed. -/
theorem pcontrol1_exitAgrees_of_zero_length_paid {model : Model.State} {caller : Address}
    {value : Wei} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false) (hval : value ≠ 0)
    (hop : op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    ExitAgrees op (haltData post.toMachineState op)
      (Model.step model (.user caller [] value)) :=
  (pcontrol1_exitAgrees_iff_paid hinh hval).mpr
    ⟨hop, bytes_haltData_eq_nil_of_zero_length (Or.inr hop) hstep hstack hlen⟩

/-- **P-CONTROL-1 at complete `Ξ` with no residual at all.** An uninhibited
predeploy handed an empty-calldata call carrying value, whose pinned run exits
on a `REVERT` with a zero-width slice, is *observed* to revert with no data —
the control plane's non-payability, at the complete message call, with no
`ExitAgrees` premise. This is the third branch, after P-SUBMIT-1's inhibited
path and P-DRAIN-1's empty window, that does not rest on `A-ABSTRACT-TX`. -/
theorem pcontrol1_xi_paid_fee_getter_reverts_of_zero_length {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false) (hval : value ≠ 0)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .REVERT)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    observe c.result = some { reverted := true, returnData := [] } := by
  have hend := pcontrol1_exitAgrees_of_zero_length_paid (caller := caller)
    hinh hval hop hstep hstack hlen
  rw [xiTransport kind (.user caller [] value) c model rem gasCost trace
    exit mid post op arg hrep hrun hdec hZ hstep hend]
  simp [Model.step, userCall, hinh, hval]

/-! ### The residual's remaining surface, enumerated over the whole model API

Every discharge above has the same shape: the abstract answer carries no return
data, so a zero-width exit *produces* the residual instead of consuming it. What
was missing is that those branches are the complement of a **named finite** set.
`userCall_returnData_ne_nil_iff` supplies the user half of that enumeration;
`systemCall_returnData_ne_nil_iff` supplies the system half;
`step_returnData_ne_nil_iff` puts the two together over all of `Model.Step`,
which is the entire abstract API the three registered parents are stated
against.

The payoff is `xi_observes_model_of_not_dataBranch`: **one** complete-`Ξ`
theorem, quantified over every `kind` and every `Model.Step`, carrying no
`ExitAgrees` premise. It subsumes the five branch-specific `Ξ` theorems above
and, unlike them, it is exhaustive — the only steps it leaves out are the two
`DataBranch` cases, and those are exactly P-CONTROL-1's fee quote and P-DRAIN-1's
non-empty FIFO window. -/

/-- The model steps whose abstract answer carries return data: the fee quote on
the user side, a non-empty capped FIFO window on the system side. -/
def DataBranch (model : Model.State) : Model.Step → Prop
  | .user _ calldata value => inhibited model = false ∧ calldata = [] ∧ value = 0
  | .system _ => concatReturned (model.queue.take (capOf model.kind)) ≠ []

/-- **Only a non-empty window publishes bytes.** The system-side counterpart of
`userCall_returnData_ne_nil_iff`: `Model.systemCall` is total and its answer is
the encoded capped FIFO prefix, so it carries data exactly when that prefix
encodes to something. -/
theorem systemCall_returnData_ne_nil_iff {kind : Kind} {model : Model.State}
    {calldataNonempty : Bool} (hrepkind : model.kind = kind) :
    (observeModel (Model.step model (.system calldataNonempty))).returnData ≠ []
      ↔ concatReturned (model.queue.take (capOf kind)) ≠ [] := by
  rw [pdrain1_returnData hrepkind]

/-- **The enumeration, over the whole abstract API.** A `Model.step` answer
carries return data iff the step is one of the two named `DataBranch` cases.
`Model.Step` has exactly two constructors and both halves are `iff`s, so this is
an exhaustive classification, not a sample of cases. -/
theorem step_returnData_ne_nil_iff {model : Model.State} {mstep : Model.Step} :
    (observeModel (Model.step model mstep)).returnData ≠ []
      ↔ DataBranch model mstep := by
  cases mstep with
  | user caller calldata value => exact userCall_returnData_ne_nil_iff
  | system b => exact systemCall_returnData_ne_nil_iff rfl

/-- A data-free abstract answer is determined by its status flag alone. -/
theorem observeModel_eq_of_returnData_nil {out : Outcome}
    (h : (observeModel out).returnData = []) :
    observeModel out = { reverted := out.isRevert, returnData := [] } := by
  cases out with
  | success s d => simp at h; simp [h]
  | revert s => rfl

/-- The complement of `DataBranch` is data-free, read off the enumeration. -/
theorem returnData_eq_nil_of_not_dataBranch {model : Model.State} {mstep : Model.Step}
    (hnd : ¬ DataBranch model mstep) :
    (observeModel (Model.step model mstep)).returnData = [] := by
  by_contra h
  exact hnd (step_returnData_ne_nil_iff.mp h)

/-- **The residual is produced on every data-free step at once.** Given only that
the step is not one of the two named data-carrying branches, that the exit
publishes through `RETURN` / `REVERT`, that it reverts exactly when the abstract
answer does, and that its length operand is zero, `ExitAgrees` *follows*. Nothing
about the run's memory is assumed, and no `ExitAgrees` is consumed.

This is the uniform form of the five branch-specific discharges above: they are
its instances at `inhibited`, `accepted`, `rejected`, the paid fee getter and the
empty drain window. -/
theorem exitAgrees_of_zero_length_of_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hnd : ¬ DataBranch model mstep)
    (hop : op = .RETURN ∨ op = .REVERT)
    (hrev : op = .REVERT ↔ (Model.step model mstep).isRevert = true)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep) := by
  refine exitAgrees_of_zero_length hop hstep hstack hlen ?_
  rw [observeModel_eq_of_returnData_nil (returnData_eq_nil_of_not_dataBranch hnd)]
  by_cases h : op = .REVERT
  · rw [if_pos h, hrev.mp h]
  · rw [if_neg h]
    have hb : (Model.step model mstep).isRevert = false := by
      cases hcase : (Model.step model mstep).isRevert with
      | false => rfl
      | true => exact absurd (hrev.mpr hcase) h
    rw [hb]

/-- **The whole data-free surface at complete `Ξ`, with no residual at all.** For
*every* kind and *every* abstract step outside the two named `DataBranch` cases,
a run that exits on a publishing halt with a zero-width slice, reverting exactly
when the abstract step does, is *observed* to answer what the model answers.
There is no `ExitAgrees` hypothesis, so none of these branches rests on
`A-ABSTRACT-TX`.

Together with `step_returnData_ne_nil_iff` this is what makes the remaining
surface exact: what `A-ABSTRACT-TX` still buys is confined to two named steps,
and every other step of the abstract API is discharged here in one theorem. -/
theorem xi_observes_model_of_not_dataBranch {kind : Kind} (c : XiCall kind)
    {model : Model.State} {mstep : Model.Step}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hnd : ¬ DataBranch model mstep)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN ∨ op = .REVERT)
    (hrev : op = .REVERT ↔ (Model.step model mstep).isRevert = true)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlen : μ₁.toNat = 0) :
    observe c.result =
      some { reverted := (Model.step model mstep).isRevert, returnData := [] } := by
  have hend := exitAgrees_of_zero_length_of_not_dataBranch hnd hop hrev hstep hstack hlen
  rw [xiTransport kind mstep c model rem gasCost trace exit mid post op arg
      hrep hrun hdec hZ hstep hend,
    observeModel_eq_of_returnData_nil (returnData_eq_nil_of_not_dataBranch hnd)]

/-! ## The residual, written out: one memory equation, every step

Everything above still reaches complete `Ξ` through a *named* predicate.
`XiTransport` consumes `ExitAgrees` — equivalently `EndpointAgrees`, by
`endpointAgrees_iff_exitAgrees` — and while the previous sections narrowed what
that predicate can mean, they never removed it from the transport's hypotheses.

This section supplies a transport that does without it; `XiTransport` itself is
left unchanged. `exitAgrees_iff_memory_bytes` takes the residual apart
into the two independent facts it abbreviates:

* the exit reverts **iff** the abstract step does, and
* the slice of pre-step memory the exit's own operands select carries **exactly**
  the abstract step's bytes.

Both directions are proved, so this is a restatement at equal strength in the
same sense `endpointAgrees_iff_exitAgrees` was: nothing is smuggled in, nothing
quietly dropped. `XiMemoryTransport` is then the transport asking for those two
facts instead — quantified over every `kind` and every `Model.Step`, with **no
`ExitAgrees` and no `EndpointAgrees` hypothesis anywhere in it**.

`A-ABSTRACT-TX` is **not** closed by this, and R4 does not claim it is. What
changes is that the open assumption is no longer carried by a named predicate
that has to be read against its definition: on the two branches where it is
still load-bearing it is now written out as a claim about which bytes of memory
a pinned runtime holds at its exit instruction, and
`pdrain1_xi_returns_fifo_prefix_of_memory` /
`pcontrol1_xi_fee_getter_of_memory` are those two claims verbatim. Everywhere
else the equation is *derivable* — `memory_bytes_of_zero_length_of_not_dataBranch`
supplies it from the enumeration — so `XiMemoryTransport` covers the whole
abstract API with the residual reduced to two byte equations and nothing else.
-/

/-- **The residual is exactly two independent facts.** On a publishing halt,
`ExitAgrees` holds iff the exit's status matches the abstract step's *and* the
memory slice the exit selects carries the abstract step's bytes.

Both directions, so `A-ABSTRACT-TX` keeps precisely its old content: this is a
restatement, not a weakening. What it buys is that the transport below can ask
for the right-hand side, which mentions no predicate of this module. -/
theorem exitAgrees_iff_memory_bytes {model : Model.State} {mstep : Model.Step}
    {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
      ↔ ((op = .REVERT ↔ (Model.step model mstep).isRevert = true) ∧
          bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
            = (observeModel (Model.step model mstep)).returnData) := by
  rw [haltData_eq_memory_slice hop hstep hstack, ExitAgrees, exitObservation]
  generalize Model.step model mstep = o
  cases o with
  | success st d => by_cases h : op = .REVERT <;> simp [h]
  | revert st => by_cases h : op = .REVERT <;> simp [h]

/-- **R4's transport with the residual written out.** Same conclusion as
`XiTransport` and, given the run, the same strength — but it names no residual.
Where `XiTransport` asks for `ExitAgrees`, this asks for the status equation and
a plain statement about the bytes of pre-step memory.

Universally quantified over world, gas, substate, block context, fuel, calldata,
value **and over every `Model.Step`**. No `ExitAgrees` hypothesis, no
`EndpointAgrees` hypothesis, no `native_decide`. -/
def XiMemoryTransport (kind : Kind) (mstep : Model.Step) : Prop :=
  ∀ (c : XiCall kind) (model : Model.State)
    (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
    Represents kind c.entry model →
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    (op = .RETURN ∨ op = .REVERT) →
    mid.stack.pop2 = some (s, μ₀, μ₁) →
    (op = .REVERT ↔ (Model.step model mstep).isRevert = true) →
    bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = (observeModel (Model.step model mstep)).returnData →
    observe c.result = some (observeModel (Model.step model mstep))

theorem xiMemoryTransport (kind : Kind) (mstep : Model.Step) :
    XiMemoryTransport kind mstep := by
  intro c model rem gasCost trace exit mid post op arg s μ₀ μ₁
    hrep hrun hdec hZ hstep hop hstack hrev hbytes
  exact xiTransport kind mstep c model rem gasCost trace exit mid post op arg
    hrep hrun hdec hZ hstep
    ((exitAgrees_iff_memory_bytes hop hstep hstack).mpr ⟨hrev, hbytes⟩)

/-- **The data-free surface assumes nothing.** A zero length operand publishes
nothing and a non-`DataBranch` step answers with nothing, so the memory equation
`XiMemoryTransport` asks for is *derived* there rather than assumed, and
`xi_observes_model_of_not_dataBranch` can accordingly be obtained as
`xiMemoryTransport` at those steps. That is what makes "the residual is two
byte equations" an exhaustive statement about the abstract API rather than a
summary of the branches that happened to be treated. -/
theorem memory_bytes_of_zero_length_of_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {mid : EVM.State} {μ₀ μ₁ : UInt256}
    (hnd : ¬ DataBranch model mstep) (hlen : μ₁.toNat = 0) :
    bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = (observeModel (Model.step model mstep)).returnData := by
  rw [hlen, bytes_readWithPadding_zero, returnData_eq_nil_of_not_dataBranch hnd]

/-! ### The data-free surface, both directions and all four exit opcodes

`exitAgrees_of_zero_length_of_not_dataBranch` *produces* the residual on every
step outside the two `DataBranch` cases, but only in one direction and only on
the publishing halts. Two gaps remain, and this section closes both.

* **Direction.** The production lemma leaves open whether a zero length operand
  is merely *sufficient*. It is also necessary: `exitAgrees_length_operand`
  reads the operand off the abstract answer, and outside `DataBranch` that
  answer is empty. So on the whole data-free surface the residual is *equivalent*
  to two scalar facts about the exit instruction — its status flag and its length
  operand — with no byte-level, memory-level or `Model`-level content left in it.
  This is the uniform form of `psubmit1_exitAgrees_iff_operand`, which said the
  same thing for one parent on one branch.

* **Opcode coverage.** Both lemmas assume the exit publishes (`RETURN` /
  `REVERT`). `exit_op_cases` says the exit is one of *four* opcodes, so the
  silent pair was still uncovered on this surface. On `STOP` / `SELFDESTRUCT`
  the residual needs no operand hypothesis at all: it follows from the status
  flag alone. Together the two discharges are exhaustive over the exit opcode.

None of this closes `A-ABSTRACT-TX`, and R4 does not claim it does. What it
fixes is the *shape* of what is left: outside the two `DataBranch` steps, the
open content is exactly "the exit reverts iff the model does, and — on the
publishing halts only — its length operand is zero". -/

/-- **The residual is exactly two scalar facts, on the whole data-free surface.**
For every kind and every abstract step outside the two named `DataBranch` cases,
`ExitAgrees` on a publishing halt holds **iff** the exit reverts exactly when the
abstract step does and its length operand is zero.

Strictly stronger than `exitAgrees_of_zero_length_of_not_dataBranch`, which is
the `mpr` direction: the `mp` direction says a zero operand is *forced*, so
`A-ABSTRACT-TX` cannot be traded for a claim about wider slices here. Strictly
more general than `psubmit1_exitAgrees_iff_operand`, which is its instance at
`inhibited` on the user step. -/
theorem exitAgrees_iff_zero_length_of_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hnd : ¬ DataBranch model mstep)
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlt : μ₁.toNat < USize.size) :
    ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
      ↔ ((op = .REVERT ↔ (Model.step model mstep).isRevert = true) ∧ μ₁.toNat = 0) := by
  constructor
  · intro hend
    refine ⟨((exitAgrees_iff_memory_bytes hop hstep hstack).mp hend).1, ?_⟩
    rw [exitAgrees_length_operand hop hstep hstack hlt hend,
      returnData_eq_nil_of_not_dataBranch hnd]
    rfl
  · rintro ⟨hrev, hlen⟩
    exact exitAgrees_of_zero_length_of_not_dataBranch hnd hop hrev hstep hstack hlen

/-- **The exit's length operand is forced to zero.** The `mp` half of the
biconditional, isolated: outside the `DataBranch` cases the residual leaves the
publishing halt no freedom in how much it publishes. -/
theorem exitAgrees_zero_length_operand_of_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hnd : ¬ DataBranch model mstep)
    (hop : op = .RETURN ∨ op = .REVERT)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hlt : μ₁.toNat < USize.size)
    (hend : ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)) :
    μ₁.toNat = 0 :=
  ((exitAgrees_iff_zero_length_of_not_dataBranch hnd hop hstep hstack hlt).mp hend).2

/-- **The silent halts are discharged on the data-free surface, with no operand
hypothesis.** If the run exits on `STOP` or `SELFDESTRUCT` and the abstract step
is outside the two `DataBranch` cases and does not revert, `ExitAgrees` follows
from the status flag alone — no stack shape, no length operand, no memory.

This is the branch `exitAgrees_of_zero_length_of_not_dataBranch` left out; with
`exit_op_cases` the pair covers every opcode the exit can be.

Not vacuous: `psubmit1_exitAgrees_of_silent_accepted` is exactly this statement
at one point of it — an accepted user submission has non-empty calldata, so it
lies outside `DataBranch`, and it succeeds, so its status flag is `false`. This
generalises that branch-specific discharge from P-SUBMIT-1's accepted path to
every kind and every step of the abstract API outside the two data-carrying
cases, over an arbitrary `MachineState` rather than a post-state's. -/
theorem exitAgrees_of_silent_of_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hnd : ¬ DataBranch model mstep)
    (hrev : (Model.step model mstep).isRevert = false) :
    ExitAgrees op out (Model.step model mstep) := by
  rw [ExitAgrees, exitObservation_of_silent hH hop,
    observeModel_eq_of_returnData_nil (returnData_eq_nil_of_not_dataBranch hnd), hrev]

/-- **The silent data-free surface at complete `Ξ`, with no residual at all.**
The counterpart of `xi_observes_model_of_not_dataBranch` on the other two exit
opcodes: a run that halts silently is *observed* to answer what the model
answers, and — unlike the publishing case — needs no operand stack and no
zero-width side condition to say so.

No `ExitAgrees` hypothesis, so this branch does not rest on `A-ABSTRACT-TX`. -/
theorem xi_observes_model_of_silent_of_not_dataBranch {kind : Kind} (c : XiCall kind)
    {model : Model.State} {mstep : Model.Step}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hnd : ¬ DataBranch model mstep)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hrev : (Model.step model mstep).isRevert = false) :
    observe c.result = some { reverted := false, returnData := [] } := by
  have hend := exitAgrees_of_silent_of_not_dataBranch (exit_H hrun hdec post.toMachineState)
    hop hnd hrev
  rw [xiTransport kind mstep c model rem gasCost trace exit mid post op arg
      hrep hrun hdec hZ hstep hend,
    observeModel_eq_of_returnData_nil (returnData_eq_nil_of_not_dataBranch hnd), hrev]

/-! ### The data-carrying surface: the exit opcode is not free either

The section above settles the residual outside the two `DataBranch` cases. On
those two the residual is still open — but *which of the four halting opcodes
the run may exit on* is not, and this section proves it is forced to be exactly
`RETURN`.

The lever is that both data-carrying branches answer with a success. P-CONTROL-1's
fee quote is taken with the inhibitor down, and `Model.systemCall` is total; so
`isRevert_false_of_dataBranch` holds uniformly over the enumeration, with no
hypothesis about the run at all. Two consequences:

* **`REVERT` is excluded.** Its observation carries `reverted := true`, which no
  data-carrying step can match.
* **The silent halts are excluded.** They publish nothing, and a data-carrying
  step answers with something. `not_exitAgrees_of_silent_of_dataBranch` is the
  exact dual of `exitAgrees_of_silent_of_not_dataBranch`: taken together the two
  *decide* the residual on every silent exit of the whole abstract API — true off
  the data branches, false on them — leaving no open content there at all.

So `hop : op = .RETURN`, which `pdrain1_xi_returns_fifo_prefix_of_memory` and
`pcontrol1_xi_fee_getter_of_memory` assume, is not a restriction on those
statements: it is derivable from the residual they replace. And once the opcode
is pinned the status conjunct of `exitAgrees_iff_memory_bytes` is discharged on
both sides, so what is left of `A-ABSTRACT-TX` on the data-carrying surface is a
single memory equation with no status content beside it.

`A-ABSTRACT-TX` stays OPEN: that equation — which bytes the pinned runtime holds
at the slice its own `RETURN` selects, on a general state rather than the four
pinned images — is untouched here. -/

/-- The abstract answer's status flag, read off the outcome. -/
@[simp] theorem observeModel_reverted (o : Outcome) :
    (observeModel o).reverted = o.isRevert := by
  cases o <;> rfl

/-- **A data-carrying step never reverts**, over the whole enumeration and with
no hypothesis about the run: the fee quote is only a `DataBranch` when the
inhibitor is down, and `Model.systemCall` is total. -/
theorem isRevert_false_of_dataBranch {model : Model.State} {mstep : Model.Step}
    (hd : DataBranch model mstep) : (Model.step model mstep).isRevert = false := by
  cases mstep with
  | user caller calldata value =>
    obtain ⟨hinh, hcd, hval⟩ := hd
    subst hcd; subst hval
    simp [Model.step, userCall, hinh]
  | system b => simp [Model.step, systemCall]

/-- **A silent halt refutes the residual on the data-carrying surface.** The
exact dual of `exitAgrees_of_silent_of_not_dataBranch`: `STOP` / `SELFDESTRUCT`
publish nothing and a `DataBranch` step answers with something, so `ExitAgrees`
is not merely unproved there — it is false. -/
theorem not_exitAgrees_of_silent_of_dataBranch {model : Model.State}
    {mstep : Model.Step} {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hd : DataBranch model mstep) :
    ¬ ExitAgrees op out (Model.step model mstep) := by
  intro hend
  refine step_returnData_ne_nil_iff.mpr hd ?_
  rw [ExitAgrees] at hend
  rw [← hend, exitObservation_of_silent hH hop]

/-- **On a silent exit the residual is decided, everywhere in the abstract API.**
It holds exactly off the two data-carrying branches. Nothing about the run's
memory, stack or operands enters, so `A-ABSTRACT-TX` retains no open content on
the `STOP` / `SELFDESTRUCT` half of `exit_op_cases` at all. -/
theorem exitAgrees_of_silent_iff_not_dataBranch {model : Model.State}
    {mstep : Model.Step} {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out)
    (hop : op = .STOP ∨ op = .SELFDESTRUCT)
    (hrev : (Model.step model mstep).isRevert = false) :
    ExitAgrees op out (Model.step model mstep) ↔ ¬ DataBranch model mstep :=
  ⟨fun hend hd => not_exitAgrees_of_silent_of_dataBranch hH hop hd hend,
    fun hnd => exitAgrees_of_silent_of_not_dataBranch hH hop hnd hrev⟩

/-- **The exit opcode is forced to `RETURN` on the data-carrying surface.**
`exit_op_cases` admits four halting opcodes; the residual rules out three of
them at a `DataBranch` step. `REVERT` publishes `reverted := true` and the step
does not revert; the two silent halts publish nothing and the step answers with
bytes.

This is what makes the `hop : op = .RETURN` hypothesis of
`pdrain1_xi_returns_fifo_prefix_of_memory` and `pcontrol1_xi_fee_getter_of_memory`
free rather than a restriction: it is implied by the residual they stand in
place of. -/
theorem exit_op_eq_RETURN_of_dataBranch {model : Model.State} {mstep : Model.Step}
    {μ : MachineState} {op : Operation .EVM} {out : ByteArray}
    (hH : H μ op = some out)
    (hd : DataBranch model mstep)
    (hend : ExitAgrees op out (Model.step model mstep)) :
    op = .RETURN := by
  rcases exit_op_cases hH with h | h | h | h
  · exact h
  · exfalso
    rw [ExitAgrees, h] at hend
    have := congrArg Observation.reverted hend
    rw [exitObservation_revert] at this
    simp [isRevert_false_of_dataBranch hd] at this
  · exact absurd hend (not_exitAgrees_of_silent_of_dataBranch hH (Or.inl h) hd)
  · exact absurd hend (not_exitAgrees_of_silent_of_dataBranch hH (Or.inr h) hd)

/-- **What is left on the data-carrying surface is one memory equation.** With
the opcode pinned to `RETURN` by `exit_op_eq_RETURN_of_dataBranch`, the status
conjunct of `exitAgrees_iff_memory_bytes` is discharged on both sides, and the
residual is *equivalent* to the claim that the slice the exit's own operands
select carries the abstract step's bytes — no status content beside it.

Both directions, so this narrows the shape of `A-ABSTRACT-TX` without weakening
it. -/
theorem exitAgrees_iff_memory_bytes_of_dataBranch {model : Model.State}
    {mstep : Model.Step} {rem gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {mid post : EVM.State} {op : Operation .EVM} {s : Stack UInt256} {μ₀ μ₁ : UInt256}
    (hd : DataBranch model mstep)
    (hop : op = .RETURN)
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁)) :
    ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
      ↔ bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
          = (observeModel (Model.step model mstep)).returnData := by
  rw [exitAgrees_iff_memory_bytes (Or.inl hop) hstep hstack, hop]
  simp [isRevert_false_of_dataBranch hd]

/-- **The data-carrying surface is inhabited**, so the four statements above are
not vacuous: with the inhibitor down, P-CONTROL-1's fee getter — an empty
calldata, zero-value user call — is a `DataBranch` step by definition. -/
theorem dataBranch_pcontrol1_fee_getter {model : Model.State} {caller : Address}
    (hinh : inhibited model = false) : DataBranch model (.user caller [] 0) :=
  ⟨hinh, rfl, rfl⟩

/-- **P-DRAIN-1's data-carrying branch is inhabited too**: a system call whose
capped FIFO window encodes to something is a `DataBranch` step, which is exactly
the hypothesis `pdrain1_xi_returns_fifo_prefix_of_memory` is stated under. -/
theorem dataBranch_pdrain1_nonempty_window {model : Model.State}
    {calldataNonempty : Bool}
    (hne : concatReturned (model.queue.take (capOf model.kind)) ≠ []) :
    DataBranch model (.system calldataNonempty) := hne

/-- **P-DRAIN-1's `RETURN` is forced.** The instance of
`exit_op_eq_RETURN_of_dataBranch` at a non-empty drain window: the pinned run
cannot answer a non-empty FIFO window on any halting opcode but `RETURN`. -/
theorem pdrain1_exit_op_eq_RETURN_of_nonempty_window {model : Model.State}
    {calldataNonempty : Bool} {μ : MachineState} {op : Operation .EVM}
    {out : ByteArray}
    (hH : H μ op = some out)
    (hne : concatReturned (model.queue.take (capOf model.kind)) ≠ [])
    (hend : ExitAgrees op out (Model.step model (.system calldataNonempty))) :
    op = .RETURN :=
  exit_op_eq_RETURN_of_dataBranch hH (dataBranch_pdrain1_nonempty_window hne) hend

/-- **P-DRAIN-1's entire remaining share of `A-ABSTRACT-TX`, stated.** The system
call is *observed* to answer with the bounded FIFO window as soon as the pinned
runtime's memory holds that window's encoding at the slice its own `RETURN`
selects. No `ExitAgrees`, no `EndpointAgrees`: what is still open is the
hypothesis `hbytes`, and it is a statement about bytes of memory. -/
theorem pdrain1_xi_returns_fifo_prefix_of_memory {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hbytes : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = concatReturned (model.queue.take (capOf kind))) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } := by
  have hk := Represents.kind_eq hrep
  have hrev : op = .REVERT ↔
      (Model.step model (.system calldataNonempty)).isRevert = true := by
    rw [hop]; simp [Model.step, systemCall]
  have hbytes' : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = (observeModel (Model.step model (.system calldataNonempty))).returnData := by
    rw [pdrain1_returnData hk]; exact hbytes
  rw [xiMemoryTransport kind (.system calldataNonempty) c model rem gasCost trace
    exit mid post op arg s μ₀ μ₁ hrep hrun hdec hZ hstep (Or.inl hop) hstack
    hrev hbytes']
  simp [Model.step, systemCall, hk]

/-- **P-CONTROL-1's entire remaining share of `A-ABSTRACT-TX`, stated.** The fee
getter is *observed* to quote `currentFee` as soon as the pinned runtime's memory
holds that quote's 32 big-endian bytes at the slice its own `RETURN` selects.
As above, no named residual is consumed — the open hypothesis is `hbytes`, and
`pcontrol1_exitAgrees_iff_digits` already splits it into 32 digit equations. -/
theorem pcontrol1_xi_fee_getter_of_memory {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₀ μ₁ : UInt256}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hbytes : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = toBeBytes (currentFee model) 32) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
  have hrev : op = .REVERT ↔
      (Model.step model (.user caller [] 0)).isRevert = true := by
    rw [hop]; simp [Model.step, userCall, hinh]
  have hbytes' : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
      = (observeModel (Model.step model (.user caller [] 0))).returnData := by
    rw [hbytes]; simp [Model.step, userCall, hinh]
  rw [xiMemoryTransport kind (.user caller [] 0) c model rem gasCost trace
    exit mid post op arg s μ₀ μ₁ hrep hrun hdec hZ hstep (Or.inl hop) hstack
    hrev hbytes']
  simp [Model.step, userCall, hinh]

/-! ## The residual, discharged symbolically: the `MSTORE` behind the `RETURN`

Everything above leaves `hbytes` — that the pinned runtime's memory holds the
abstract answer at the slice its own `RETURN` selects — as an assumption. Two
things blocked proving it, and neither was a gap in this file. The CFG stepper's
`CfgState` carries `pc`, `stack` and `gas` and no memory at all, so the abstract
half of the campaign cannot so much as *state* a memory fact; and EVMYulLean's
fixed-width byte encoder `toBytes'` was private, so the *contents* of a stored
word were unreachable even where the memory equation could be stated.

EVMYulLean PR #9 removes the second obstacle without exposing `toBytes'`. It
publishes `toLeBytesFixed`/`toBeBytesFixed` with their digit lemmas, the
`ByteArray` read-over-write chain for `MachineState.mstore`, and — the part that
matters here — the same facts *along the real opcode path*, as `StepOk`s of
`EvmYul.EVM.step`. This section spends them. `toBytes'` is never unfolded below;
nothing here mentions it.

The bridge is narrow and entirely mechanical:

* `bytes` (this file) is `(List.range size).map fun i ↦ (get! i).toNat`, and
  `UInt256.map_toNat_get!_toByteArray` (#9) is exactly that list for a stored
  word, in closed form.
* `Model.toBeBytes` is `(toLeBytes n w).reverse` over `Byte := Nat`;
  `toBeBytes_eq_map_range` puts it in the same closed form, so
  `bytes_toByteArray` identifies the two encoders outright.
* `readWithPadding_memory_step_MSTORE` (#9) supplies the memory contents from a
  real `MSTORE` opcode under `hstart : μ₀.toNat ≤ pre.memory.size`, which at
  `μ₀ = 0` is free — and free is what a fresh frame, where `memory.size = 0`,
  can pay.

What this buys:

* `endpointAgrees_of_mstore_return_zero` states the discharge in its bluntest
  form. `EndpointAgrees` is the **conclusion**, not a hypothesis, for the
  canonical `MSTORE(0, v); RETURN(0, 32)` fragment, from *any* starting state,
  with no assumption about memory and no `native_decide`.
* `pcontrol1_xi_fee_getter_of_mstore` carries that into the complete-`Ξ`
  transport. It reaches P-CONTROL-1's `Ξ` observation with **no `hbytes`, no
  `ExitAgrees` and no `EndpointAgrees` hypothesis**: the 32-byte memory equation
  is proved from the `MSTORE` the fee getter actually executes. Its remaining
  hypothesis is the scalar `v.toNat = currentFee model` — an arithmetic fact
  about the value the runtime computed, not a claim about bytes of memory.

P-DRAIN-1's non-empty window is **not** discharged here and nothing below
pretends otherwise: that window is written by a loop of `MSTORE`s whose count
depends on the queue, and #9's opcode-path API covers one store. See
`A-ABSTRACT-TX`.
-/

/-- `toLeBytes` produces exactly `w` bytes. -/
@[simp] theorem length_toLeBytes (n w : Nat) : (toLeBytes n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLeBytes, ih]

/-- **Every digit of the model's little-endian expansion, in closed form.** The
same statement EVMYulLean's `getElem_toLeBytesFixed` makes about its own encoder,
proved the same way; the two recursions differ only in landing in `UInt8` rather
than `Byte := Nat`. -/
theorem getElem_toLeBytes (n w i : Nat) (h : i < (toLeBytes n w).length) :
    (toLeBytes n w)[i] = n / 256 ^ i % 256 := by
  induction w generalizing n i with
  | zero => simp at h
  | succ w ih =>
    match i with
    | 0 => simp [toLeBytes]
    | i + 1 =>
      have h' : i < (toLeBytes (n / 256) w).length := by
        simp only [length_toLeBytes] at h ⊢; omega
      have : n / 256 / 256 ^ i = n / 256 ^ (i + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simpa [toLeBytes, this] using ih (n / 256) i h'

/-- **The model's big-endian encoder in the shape a `List ℕ` observation takes.**
Index `i` counts from the most significant end, so it names the `w - 1 - i`-th
base-256 digit. This is the right-hand side of
`UInt256.map_toNat_get!_toByteArray`, verbatim. -/
theorem toBeBytes_eq_map_range (n w : Nat) :
    toBeBytes n w = (List.range w).map (fun i => n / 256 ^ (w - 1 - i) % 256) := by
  refine List.ext_getElem (by simp [toBeBytes]) fun i h₁ _ => ?_
  have hi : i < w := by simpa [toBeBytes] using h₁
  simp only [List.getElem_map, List.getElem_range]
  show (toLeBytes n w).reverse[i]'(by simpa using hi) = _
  rw [List.getElem_reverse (by simp; omega), getElem_toLeBytes]
  simp only [length_toLeBytes]

/-- **The two encoders agree.** The bytes this file publishes for a stored EVM
word are the model's 32-byte big-endian encoding of that word's value.

This is the equation the campaign has been missing. `bytes` is how `observe`
reads return data; `toBeBytes` is how the abstract model writes it; and #9's
`UInt256.map_toNat_get!_toByteArray` — which reaches the base-256 digits through
`toBeBytesFixed`, never through the private `toBytes'` — is what makes them the
same list. -/
theorem bytes_toByteArray (v : UInt256) :
    bytes (UInt256.toByteArray v) = toBeBytes v.toNat 32 := by
  show (List.range (UInt256.toByteArray v).size).map
      (fun i => ((UInt256.toByteArray v).get! i).toNat) = _
  rw [toBeBytes_eq_map_range]
  exact EvmYul.UInt256.map_toNat_get!_toByteArray v

/-- **The residual byte equation, proved.** If the memory a `RETURN` reads is the
memory a real `MSTORE` opcode produced, then the bytes published at that slice
*are* the model's big-endian encoding of the stored word. No `hbytes`, no
`ExitAgrees`: this is the hypothesis `pcontrol1_xi_fee_getter_of_memory` and
`pdrain1_xi_returns_fifo_prefix_of_memory` were stated under, discharged.

`hmstore` is a `StepOk` of `EvmYul.EVM.step`, so the store is the real opcode and
not a `MachineState` operation standing in for it; `hframe` is what a frame
argument across the intervening instructions supplies (`Z_ok_memory` for the gas
charge, `memory_step_Push` for the operands `RETURN` needs on the stack). -/
theorem bytes_readWithPadding_of_step_MSTORE {f₁ g₁ : Nat} {store mstored : EVM.State}
    {mem : ByteArray} {s₁ : Stack UInt256} {μ₀ v μ₁ : UInt256}
    (hpop : store.stack.pop2 = some (s₁, μ₀, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hframe : mem = mstored.memory)
    (hstart : μ₀.toNat ≤ store.memory.size)
    (hlen : μ₁.toNat = 32) :
    bytes (mem.readWithPadding μ₀.toNat μ₁.toNat) = toBeBytes v.toNat 32 := by
  have h1 : EvmYul.EVM.step (f₁ + 1) g₁ (some (.MSTORE, none)) store = .ok mstored := hmstore
  have h2 : EvmYul.EVM.step (f₁ + 1) g₁ (some (.MSTORE, none)) store
      = .ok (mstorePost g₁ store s₁ μ₀ v) := step_MSTORE f₁ g₁ store s₁ μ₀ v hpop
  have hpost : mstored = mstorePost g₁ store s₁ μ₀ v := Except.ok.inj (h1.symm.trans h2)
  rw [hframe, hpost, hlen, readWithPadding_memory_step_MSTORE g₁ store s₁ μ₀ v hstart]
  exact bytes_toByteArray v

/-- The same at `μ₀ = 0`, where `hstart` is free: a store at the start of memory
is in bounds however small memory is, including the `size = 0` of a fresh
frame. -/
theorem bytes_readWithPadding_of_step_MSTORE_zero {f₁ g₁ : Nat} {store mstored : EVM.State}
    {mem : ByteArray} {s₁ : Stack UInt256} {v μ₁ : UInt256}
    (hpop : store.stack.pop2 = some (s₁, ⟨0⟩, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hframe : mem = mstored.memory)
    (hlen : μ₁.toNat = 32) :
    bytes (mem.readWithPadding 0 μ₁.toNat) = toBeBytes v.toNat 32 := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have h := bytes_readWithPadding_of_step_MSTORE (μ₀ := ⟨0⟩) hpop hmstore hframe
    (by rw [h0]; exact Nat.zero_le _) hlen
  rwa [h0] at h

/-- **`PUSH` does not touch memory.** The frame lemma the operands of a `RETURN`
need: `MSTORE(0, v)` is followed in the pinned fee getter by `push 32; push 0`
before the `RETURN`, and neither push may disturb what was stored.

Every `PUSH` opcode reaches `EvmYul.EVM.step`'s catch-all, so it is
`EvmYul.step` on `stepPre`, and both `PUSH0` and `PUSHn` answer with
`replaceStackAndIncrPC`, which rebuilds the state from `stack` and `pc` alone. -/
theorem memory_step_Push (fuel gasCost : Nat) (p : EvmYul.Operation.POp)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : StepOk (fuel + 1) gasCost (.Push p, arg) pre post) :
    post.memory = pre.memory := by
  have h' : EvmYul.step (τ := .EVM) (.Push p) arg (stepPre gasCost pre) = .ok post := h
  clear h
  cases p <;> cases arg <;>
    first
      | (injection h' with hp; subst hp; rfl)
      | injection h'
      | exact Except.noConfusion h'

/-- **A labelled step that is a `PUSH`.** The shape `memory_step_Push` consumes,
packaged so a whole run of them can be quantified over. `fuel` is `f + 1` because
a step with no fuel left cannot make progress (`not_StepOk_zero`). -/
def IsPushStep (x : Labelled) : Prop :=
  ∃ (f g : Nat) (p : EvmYul.Operation.POp) (a : Option (UInt256 × Nat)),
    x = (f + 1, g, (.Push p, a))

/-- **Memory is unchanged across a whole run of `PUSH`es.** `memory_step_Push` is
the one-instruction frame; this is its transitive closure, and it is what the
`hframe` hypothesis of `bytes_readWithPadding_of_step_MSTORE` was standing in
for. The run is arbitrary in length, so the operand sequence a `RETURN` needs is
not fixed in advance. -/
theorem memory_Runs_Push {trace : List Labelled} {pre post : EVM.State}
    (h : Runs trace pre post) : (∀ x ∈ trace, IsPushStep x) → post.memory = pre.memory := by
  induction h with
  | nil => intro _; rfl
  | @cons fuel gasCost instr p₀ mid p₂ rest hstep _htail ih =>
    intro hall
    obtain ⟨f, g, p, a, heq⟩ := hall (fuel, gasCost, instr) List.mem_cons_self
    have h1 : fuel = f + 1 := congrArg Prod.fst heq
    have h2 : gasCost = g := congrArg (fun x => x.2.1) heq
    have h3 : instr = (.Push p, a) := congrArg (fun x => x.2.2) heq
    subst h1; subst h2; subst h3
    rw [ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)), memory_step_Push f gasCost p hstep]

/-! ### Memory neutrality beyond `PUSH`

`memory_Runs_Push` covers a run made only of pushes. The pinned `builder_exits`
runtime writes its return window from a loop (`accum_loop` at PC 247, back-jump
at PC 300) whose body is not pushes alone: between the three `MSTORE`s at PC
274, 284 and 294 it runs `SLOAD`, `ADD`, `MUL`, `SHL`, `EQ`, `DUP`, `SWAP`,
`POP`, `JUMP`, `JUMPI` and `JUMPDEST`. None of those touch memory, but that was
previously an informal remark. The four family lemmas below and `NeutralOp`
turn it into a theorem for exactly the opcodes that loop uses.

The four families are the only shapes involved. `execBinOp`, `dup` and `swap`
rebuild the state with `replaceStackAndIncrPC`, which reads `stack` and `pc`
only. `unaryStateOp` — the `SLOAD` path — replaces `toState` wholesale, but
`EvmYul.State` has no memory field at all: memory lives in `MachineState`, so
the replacement cannot disturb it. -/

theorem memory_execBinOp {f : Primop.Binary} {st post : EVM.State}
    (h : EVM.execBinOp f st = .ok post) : post.memory = st.memory := by
  unfold EVM.execBinOp at h
  split at h <;>
    first
      | (injection h with hp; subst hp; rfl)
      | injection h

theorem memory_dup {n : Nat} {st post : EVM.State}
    (h : EvmYul.dup n st = .ok post) : post.memory = st.memory := by
  unfold EvmYul.dup at h
  simp only [] at h
  split at h <;>
    first
      | (injection h with hp; subst hp; rfl)
      | injection h

theorem memory_swap {n : Nat} {st post : EVM.State}
    (h : EvmYul.swap n st = .ok post) : post.memory = st.memory := by
  unfold EvmYul.swap at h
  simp only [] at h
  split at h <;>
    first
      | (injection h with hp; subst hp; rfl)
      | injection h

theorem memory_unaryStateOp {op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256}
    {st post : EVM.State} (h : EVM.unaryStateOp op st = .ok post) :
    post.memory = st.memory := by
  unfold EVM.unaryStateOp at h
  split at h <;>
    first
      | (injection h with hp; subst hp; rfl)
      | injection h

/-- **The opcodes the pinned exit loop runs between its stores.** Exactly the
non-`MSTORE` opcodes appearing in `builder_exits` PC 245–300, plus `PUSH`. Kept
as an explicit list rather than a decidable predicate so that adding an opcode
to it requires discharging its neutrality in `memory_step_neutral`. -/
inductive NeutralOp : EvmYul.Operation .EVM → Prop
  | push (p : EvmYul.Operation.POp) : NeutralOp (.Push p)
  | POP : NeutralOp .POP
  | JUMP : NeutralOp .JUMP
  | JUMPI : NeutralOp .JUMPI
  | JUMPDEST : NeutralOp .JUMPDEST
  | ADD : NeutralOp .ADD
  | MUL : NeutralOp .MUL
  | SHL : NeutralOp .SHL
  | EQ : NeutralOp .EQ
  | SLOAD : NeutralOp .SLOAD
  | DUP1 : NeutralOp .DUP1
  | DUP2 : NeutralOp .DUP2
  | DUP3 : NeutralOp .DUP3
  | SWAP1 : NeutralOp .SWAP1
  | SWAP2 : NeutralOp .SWAP2
  | SWAP3 : NeutralOp .SWAP3

/-- **A neutral opcode leaves memory alone.** The one-instruction frame,
generalising `memory_step_Push` from the push family to the whole loop body. -/
theorem memory_step_neutral {fuel gasCost : Nat} {op : EvmYul.Operation .EVM}
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (hop : NeutralOp op) (h : StepOk (fuel + 1) gasCost (op, arg) pre post) :
    post.memory = pre.memory := by
  cases hop
  case push p => exact memory_step_Push fuel gasCost p h
  case ADD => exact memory_execBinOp (f := UInt256.add) (st := stepPre gasCost pre) h
  case MUL => exact memory_execBinOp (f := UInt256.mul) (st := stepPre gasCost pre) h
  case EQ => exact memory_execBinOp (f := UInt256.eq) (st := stepPre gasCost pre) h
  case SHL => exact memory_execBinOp (f := flip UInt256.shiftLeft) (st := stepPre gasCost pre) h
  case SLOAD => exact memory_unaryStateOp (op := EvmYul.State.sload) (st := stepPre gasCost pre) h
  case DUP1 => exact memory_dup (n := 1) (st := stepPre gasCost pre) h
  case DUP2 => exact memory_dup (n := 2) (st := stepPre gasCost pre) h
  case DUP3 => exact memory_dup (n := 3) (st := stepPre gasCost pre) h
  case SWAP1 => exact memory_swap (n := 1) (st := stepPre gasCost pre) h
  case SWAP2 => exact memory_swap (n := 2) (st := stepPre gasCost pre) h
  case SWAP3 => exact memory_swap (n := 3) (st := stepPre gasCost pre) h
  case JUMPDEST =>
    have h' : EvmYul.step (τ := .EVM) .JUMPDEST arg (stepPre gasCost pre) = .ok post := h
    injection h' with hp; subst hp; rfl
  case POP =>
    have h' : EvmYul.step (τ := .EVM) .POP arg (stepPre gasCost pre) = .ok post := h
    clear h
    have hred : EvmYul.step (τ := .EVM) .POP arg (stepPre gasCost pre)
        = (match (stepPre gasCost pre).stack.pop with
            | some ⟨s, _⟩ => Except.ok ((stepPre gasCost pre).replaceStackAndIncrPC s)
            | _ => Except.error ExecutionException.StackUnderflow) := rfl
    rw [hred] at h'
    split at h' <;>
      first
        | (injection h' with hp; subst hp; rfl)
        | injection h'
  case JUMP =>
    have h' : EvmYul.step (τ := .EVM) .JUMP arg (stepPre gasCost pre) = .ok post := h
    clear h
    have hred : EvmYul.step (τ := .EVM) .JUMP arg (stepPre gasCost pre)
        = (match (stepPre gasCost pre).stack.pop with
            | some ⟨stack, μ₀⟩ =>
                Except.ok { stepPre gasCost pre with pc := μ₀, stack := stack }
            | _ => Except.error ExecutionException.StackUnderflow) := rfl
    rw [hred] at h'
    split at h' <;>
      first
        | (injection h' with hp; subst hp; rfl)
        | injection h'
  case JUMPI =>
    have h' : EvmYul.step (τ := .EVM) .JUMPI arg (stepPre gasCost pre) = .ok post := h
    clear h
    have hred : EvmYul.step (τ := .EVM) .JUMPI arg (stepPre gasCost pre)
        = (match (stepPre gasCost pre).stack.pop2 with
            | some ⟨stack, μ₀, μ₁⟩ =>
                Except.ok
                  { stepPre gasCost pre with
                      pc := if μ₁ != ⟨0⟩ then μ₀ else (stepPre gasCost pre).pc + ⟨1⟩,
                      stack := stack }
            | _ => Except.error ExecutionException.StackUnderflow) := rfl
    rw [hred] at h'
    split at h' <;>
      first
        | (injection h' with hp; subst hp; rfl)
        | injection h'

/-- **A labelled step whose opcode is neutral.** The `NeutralOp` analogue of
`IsPushStep`. -/
def IsNeutralStep (x : Labelled) : Prop :=
  ∃ (f g : Nat) (o : EvmYul.Operation .EVM) (a : Option (UInt256 × Nat)),
    NeutralOp o ∧ x = (f + 1, g, (o, a))

theorem isPushStep_isNeutralStep {x : Labelled} (h : IsPushStep x) : IsNeutralStep x := by
  obtain ⟨f, g, p, a, heq⟩ := h
  exact ⟨f, g, .Push p, a, .push p, heq⟩

/-- **Memory is unchanged across a whole run of neutral opcodes.** The transitive
closure of `memory_step_neutral`, and the strengthening of `memory_Runs_Push`
that the exit loop needs: the gap between two record stores is a run, not a list
of pushes. -/
theorem memory_Runs_neutral {trace : List Labelled} {pre post : EVM.State}
    (h : Runs trace pre post) : (∀ x ∈ trace, IsNeutralStep x) → post.memory = pre.memory := by
  induction h with
  | nil => intro _; rfl
  | @cons fuel gasCost instr p₀ mid p₂ rest hstep _htail ih =>
    intro hall
    obtain ⟨f, g, o, a, hneutral, heq⟩ := hall (fuel, gasCost, instr) List.mem_cons_self
    have h1 : fuel = f + 1 := congrArg Prod.fst heq
    have h2 : gasCost = g := congrArg (fun x => x.2.1) heq
    have h3 : instr = (o, a) := congrArg (fun x => x.2.2) heq
    subst h1; subst h2; subst h3
    rw [ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)), memory_step_neutral hneutral hstep]

/-- **The residual byte equation with the frame hypothesis gone.** Compare
`bytes_readWithPadding_of_step_MSTORE_zero`, which assumes
`hframe : mem = mstored.memory` — that whatever ran between the `MSTORE` and the
`RETURN` left memory alone. Here that is *proved*, from the pushes themselves. -/
theorem bytes_readWithPadding_of_mstore_pushes_zero {f₁ g₁ : Nat}
    {pushes : List Labelled} {store mstored mid : EVM.State}
    {s₁ : Stack UInt256} {v μ₁ : UInt256}
    (hpop : store.stack.pop2 = some (s₁, ⟨0⟩, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hpushes : Runs pushes mstored mid)
    (hall : ∀ x ∈ pushes, IsPushStep x)
    (hlen : μ₁.toNat = 32) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat) = toBeBytes v.toNat 32 :=
  bytes_readWithPadding_of_step_MSTORE_zero hpop hmstore (memory_Runs_Push hpushes hall) hlen

/-- **`EndpointAgrees`, as a conclusion, on the shape the fee getter really is.**
`endpointAgrees_of_mstore_return_zero` proves the two-instruction idealization
`MSTORE(0, v); RETURN(0, 32)`. The pinned fee getter is
`push 0; mstore; push 32; push 0; return`: the `RETURN`'s own operands are pushed
*after* the store, so the two-instruction fragment is not the code that runs.

This is that fragment with an arbitrary run of pushes between the store and the
return. There is still no `hbytes` premise, no `ExitAgrees` premise, no
hypothesis about memory and no `native_decide`. -/
theorem endpointAgrees_of_mstore_pushes_return_zero {f₁ g₁ f₂ g₂ : Nat}
    {pushes : List Labelled} {pre mstored mid : EVM.State}
    {s s' : Stack UInt256} {sval len : UInt256} {model : Model.State}
    (hpop : pre.stack.pop2 = some (s, ⟨0⟩, sval))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) pre mstored)
    (hpushes : Runs pushes mstored mid)
    (hall : ∀ x ∈ pushes, IsPushStep x)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 32) :
    ∃ post, Runs ((f₁ + 1, g₁, (.MSTORE, none)) ::
        (pushes ++ [(f₂ + 1, g₂, (.RETURN, none))])) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (toBeBytes sval.toNat 32)) := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  refine ⟨returnPost g₂ mid s' ⟨0⟩ len,
    .cons hmstore (hpushes.trans (.one (step_RETURN f₂ g₂ mid s' ⟨0⟩ len hstack))), ?_⟩
  have hb : bytes (returnPost g₂ mid s' ⟨0⟩ len).H_return = toBeBytes sval.toNat 32 := by
    rw [H_return_step_RETURN g₂ mid s' ⟨0⟩ len, h0]
    exact bytes_readWithPadding_of_mstore_pushes_zero hpop hmstore hpushes hall hlen
  simp [EndpointAgrees, observe, hb]

/-- **`EndpointAgrees`, as a conclusion.** The canonical fragment
`MSTORE(0, v); RETURN(0, 32)` publishes exactly the model's 32-byte big-endian
encoding of `v`, from any starting state.

This is the statement predecessor writers could only restate. There is no
`hbytes` premise, no `ExitAgrees` premise, no hypothesis about memory at all, and
no `native_decide`: `Runs` is two real `EvmYul.EVM.step`s and the returned bytes
are computed. -/
theorem bytes_H_return_of_mstore_return_zero (f₁ g₁ f₂ g₂ : Nat) (pre : EVM.State)
    (s s' : Stack UInt256) (sval len : UInt256)
    (hpop : pre.stack.pop2 = some (s, ⟨0⟩, sval))
    (hpop' : s.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 32) :
    ∃ post, Runs [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.RETURN, none))] pre post
      ∧ bytes post.H_return = toBeBytes sval.toNat 32 := by
  obtain ⟨post, hruns, _, hdig⟩ :=
    H_return_step_MSTORE_RETURN_zero_digits f₁ g₁ f₂ g₂ pre s s' sval len hpop hpop' hlen
  refine ⟨post, hruns, ?_⟩
  show (List.range post.H_return.size).map (fun i => (post.H_return.get! i).toNat) = _
  rw [hdig, toBeBytes_eq_map_range]

/-- The same run, stated as `EndpointAgrees` itself. R4's brief was to discharge
`EndpointAgrees` rather than restate it; this is the discharge, on the fragment
the pinned fee getter's read path is. -/
theorem endpointAgrees_of_mstore_return_zero (f₁ g₁ f₂ g₂ : Nat) (pre : EVM.State)
    (s s' : Stack UInt256) (sval len : UInt256) (model : Model.State)
    (hpop : pre.stack.pop2 = some (s, ⟨0⟩, sval))
    (hpop' : s.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 32) :
    ∃ post, Runs [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.RETURN, none))] pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (toBeBytes sval.toNat 32)) := by
  obtain ⟨post, hruns, hb⟩ :=
    bytes_H_return_of_mstore_return_zero f₁ g₁ f₂ g₂ pre s s' sval len hpop hpop' hlen
  exact ⟨post, hruns, by simp [EndpointAgrees, observe, hb]⟩

/-- **P-CONTROL-1's share of `A-ABSTRACT-TX`, with the memory equation gone.**

Compare `pcontrol1_xi_fee_getter_of_memory`, which assumes
`hbytes : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat) = toBeBytes (currentFee model) 32`
— thirty-two byte equations about the pinned runtime's memory. Here that
hypothesis is *proved*, from the `MSTORE` opcode the fee getter executes, and
what is left in its place is the single scalar `hval : v.toNat = currentFee model`:
the runtime computed the right number. Whether the 256-bit word is then laid out
correctly in memory and published correctly by `RETURN` is no longer assumed.

Everything else is as before: universally quantified over the world, gas,
substate, block context, calldata, value and model state, at the pinned image,
with no `native_decide`. -/
theorem pcontrol1_xi_fee_getter_of_mstore {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost f₁ g₁ : Nat} {trace : List Labelled}
    {exit mid post store mstored : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s s₁ : Stack UInt256}
    {μ₀ μ₁ v : UInt256}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, μ₀, μ₁))
    (hpop : store.stack.pop2 = some (s₁, μ₀, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hframe : mid.memory = mstored.memory)
    (hstart : μ₀.toNat ≤ store.memory.size)
    (hlen : μ₁.toNat = 32)
    (hval : v.toNat = currentFee model) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } :=
  pcontrol1_xi_fee_getter_of_memory (caller := caller) c hinh hrep hrun hdec hZ hstep hop hstack
    (by rw [bytes_readWithPadding_of_step_MSTORE hpop hmstore hframe hstart hlen, hval])

/-- The same at the address the pinned fee getter actually stores to. `push 0;
mstore; push 32; push 0; return` writes at offset zero, so `hstart` is free and
the transport carries no memory-size side condition either. -/
theorem pcontrol1_xi_fee_getter_of_mstore_zero {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost f₁ g₁ : Nat} {trace : List Labelled}
    {exit mid post store mstored : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s s₁ : Stack UInt256}
    {μ₁ v : UInt256}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hpop : store.stack.pop2 = some (s₁, ⟨0⟩, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hframe : mid.memory = mstored.memory)
    (hlen : μ₁.toNat = 32)
    (hval : v.toNat = currentFee model) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } :=
  by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  refine pcontrol1_xi_fee_getter_of_mstore (caller := caller) c hinh hrep hrun hdec hZ hstep hop
    hstack hpop hmstore hframe ?_ hlen hval
  rw [h0]
  exact Nat.zero_le _

/-- **P-CONTROL-1's fee getter with the frame hypothesis gone too.** The last
hypothesis of `pcontrol1_xi_fee_getter_of_mstore_zero` that was still about
memory is `hframe : mid.memory = mstored.memory` — that the instructions between
the `MSTORE` and the `RETURN` did not disturb the stored word. In the pinned fee
getter those instructions are `push 32; push 0`, and `memory_Runs_Push` proves
the frame outright.

What is left is `hval : v.toNat = currentFee model`, a single scalar fact about
the number the runtime computed, and the stack shapes. No hypothesis about bytes
of memory survives, and there is no `native_decide`. -/
theorem pcontrol1_xi_fee_getter_of_mstore_pushes {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost f₁ g₁ : Nat} {trace pushes : List Labelled}
    {exit mid post store mstored : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s s₁ : Stack UInt256}
    {μ₁ v : UInt256}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hpop : store.stack.pop2 = some (s₁, ⟨0⟩, v))
    (hmstore : StepOk (f₁ + 1) g₁ (.MSTORE, none) store mstored)
    (hpushes : Runs pushes mstored mid)
    (hall : ∀ x ∈ pushes, IsPushStep x)
    (hlen : μ₁.toNat = 32)
    (hval : v.toNat = currentFee model) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } :=
  pcontrol1_xi_fee_getter_of_mstore_zero (caller := caller) c hinh hrep hrun hdec hZ hstep hop
    hstack hpop hmstore (memory_Runs_Push hpushes hall) hlen hval

/-! ## The residual, discharged at the pinned images

Everything above is conditional. `pdrain1_xi_returns_fifo_prefix_of_memory` and
`pcontrol1_xi_fee_getter_of_memory` reach a complete `Ξ` observation *given*
`hbytes`, and `hbytes` — that the pinned runtime's memory holds the abstract
answer at the slice its own `RETURN` selects — was assumed, not proved. Writing
the residual out as a memory equation made it legible; it did not make it true.

This section proves it, at concrete images.

`EvmRunner.run` is `EvmYul.EVM.Ξ` on a world holding only the predeploy and its
caller, and `XiCall.result` is `EvmYul.EVM.Ξ` too. They are therefore the *same
term*: `pinnedCall` below assembles a `XiCall` whose `result` is definitionally
a kept `EvmRunner` trace (`pinnedCall_result_exitSystem` and its siblings are
`rfl`). That is what lets a `native_decide`-evaluated run discharge a hypothesis
of the `∀`-quantified transport rather than sit beside it as a separate check.

What is proved here, with **no `ExitAgrees`, no `EndpointAgrees` and no `hbytes`
hypothesis**, is that the pinned runtime's complete `Ξ` observation *is* the
abstract step's observation — status flag and every returned byte — at four
images: the exit drain under its cap and over it, the deposit drain, and the fee
getter. `represents_pinnedExitSystem`, `represents_pinnedDepositSystem` and
`represents_pinnedExitFeeGetter` show these are genuine instances of the
`Represents` premise the transports quantify over, so they are points of the
same `∀`, not a parallel statement about a different object.
`pdrain1_xi_pinned_exit_discriminates` is the negative control: the same run is
proved *not* to observe a neighbouring model state, so the four positive results
are not vacuously true of anything.

**This does not close `A-ABSTRACT-TX` and R4 does not claim it does.** The
assumption is a `∀` over every calldata, value and storage branch; four images
are four points of it. What changes is the *kind* of thing that is open. Before
this section, no run of the pinned bytecode was proved to agree with `Model.step`
at any argument at all, so the residual was open everywhere and confirmed
nowhere. It is now proved wherever it is checked, and the equations checked are
the two that `pdrain1_xi_returns_fifo_prefix_of_memory` and
`pcontrol1_xi_fee_getter_of_memory` leave open, at images that exercise the cap
boundary the kill-line protects.

The four positive results and the negative control carry `native_decide`
(`A-NATIVE-DECIDE`, already disclosed for the kept `Ξ` traces) and nothing else:
no `sorry`, no project axiom. The `Represents` and bridge lemmas are `rfl`, and
everything earlier in this module remains `native_decide`-free.
-/

/-- Interpreter fuel of the kept `Ξ` traces, less one, so that `XiCall.result`'s
`fuel + 1` is exactly the `FUEL` those traces run at. -/
def pinnedFuel : Nat := Eip8282.Audit.Guarantees.PDrain1.FUEL - 1

/-- **The `XiCall` an `EvmRunner` run is.** Same `Ξ`, same world, same
environment — assembled as a `XiCall` so that the `∀`-quantified transports of
this module can be instantiated at it. `code_pinned` is `rfl`: the code being
run is the pinned image by construction. -/
def pinnedCall (kind : Kind) (caller : AccountAddress) (value : UInt256)
    (calldata : ByteArray) (storage : EvmYul.Storage) : XiCall kind where
  fuel := pinnedFuel
  createdAccounts := default
  genesisBlockHeader := default
  blocks := default
  σ := EvmRunner.worldWith (targetAddr kind) (runtimeCode kind) caller
    (value + EvmRunner.oneEth) storage
  σ₀ := EvmRunner.worldWith (targetAddr kind) (runtimeCode kind) caller
    (value + EvmRunner.oneEth) storage
  gas := EvmRunner.defaultGas
  substate := default
  env := EvmRunner.callEnv (targetAddr kind) (runtimeCode kind) caller value calldata
  code_pinned := rfl

/-- The bridge, on the exit runtime's system call: definitional. -/
theorem pinnedCall_result_exitSystem (storage : EvmYul.Storage) :
    (pinnedCall .exit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty storage).result
      = EvmRunner.runExitSystem Eip8282.Audit.Guarantees.PDrain1.FUEL ByteArray.empty
          (code := Eip8282.Audit.Bytecode.exitRuntime) (storage := storage) := rfl

/-- The bridge, on the deposit runtime's system call: definitional. -/
theorem pinnedCall_result_depositSystem (storage : EvmYul.Storage) :
    (pinnedCall .deposit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty storage).result
      = EvmRunner.runDepositSystem Eip8282.Audit.Guarantees.PDrain1.FUEL ByteArray.empty
          (code := Eip8282.Audit.Bytecode.depositRuntime) (storage := storage) := rfl

/-- The bridge, on a non-system call into the exit runtime: definitional. -/
theorem pinnedCall_result_exitUser (callerNat : Nat) (storage : EvmYul.Storage) :
    (pinnedCall .exit (EvmRunner.toAddress callerNat) EvmRunner.ZERO_U256
        ByteArray.empty storage).result
      = EvmRunner.runExit Eip8282.Audit.Guarantees.PDrain1.FUEL callerNat 0 ByteArray.empty
          (code := Eip8282.Audit.Bytecode.exitRuntime) (storage := storage) := rfl

/-- **The pinned system calls are instances of the transports' `Represents`
premise.** So the observations below are points of the same `∀` the conditional
statements above quantify over, not a statement about some other object. The
account lookup is `rfl` because `SYSTEM_ADDR` is not the predeploy's address, so
the caller's binding does not shadow it. -/
theorem represents_pinnedExitSystem {storage : EvmYul.Storage}
    (hwf : WellFormed .exit storage) :
    Represents .exit
      (pinnedCall .exit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty storage).entry
      (toModel .exit storage 0) :=
  ⟨EvmRunner.mkAccount (runtimeCode .exit) EvmRunner.ZERO_U256 storage,
    rfl, rfl, hwf, rfl⟩

theorem represents_pinnedDepositSystem {storage : EvmYul.Storage}
    (hwf : WellFormed .deposit storage) :
    Represents .deposit
      (pinnedCall .deposit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty storage).entry
      (toModel .deposit storage 0) :=
  ⟨EvmRunner.mkAccount (runtimeCode .deposit) EvmRunner.ZERO_U256 storage,
    rfl, rfl, hwf, rfl⟩

/-- The fee getter is a *non*-system call, so its caller differs; the lookup is
`rfl` for the same reason. -/
theorem represents_pinnedExitFeeGetter {storage : EvmYul.Storage}
    (hwf : WellFormed .exit storage) :
    Represents .exit
      (pinnedCall .exit (EvmRunner.toAddress Eip8282.Audit.Guarantees.PDrain1.submitter)
        EvmRunner.ZERO_U256 ByteArray.empty storage).entry
      (toModel .exit storage 0) :=
  ⟨EvmRunner.mkAccount (runtimeCode .exit) EvmRunner.ZERO_U256 storage,
    rfl, rfl, hwf, rfl⟩

/-- **P-DRAIN-1's residual, discharged at the pinned exit drain.** Two queued
exits, under the per-block cap of 16: the pinned runtime's complete `Ξ`
observation is exactly the abstract system call's — it succeeds, and it returns
`concatReturned` of the capped FIFO window byte for byte.

No `ExitAgrees`, no `hbytes`: this is the hypothesis
`pdrain1_xi_returns_fifo_prefix_of_memory` leaves open, proved at this image. -/
theorem pdrain1_xi_drains_pinned_exit_under_cap :
    observe (pinnedCall .exit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty
        (Eip8282.Audit.Guarantees.PDrain1.exitQueue 2)).result
      = some { reverted := false
               returnData :=
                 concatReturned
                   ((toModel .exit (Eip8282.Audit.Guarantees.PDrain1.exitQueue 2) 0).queue.take
                     (capOf .exit)) } := by
  native_decide

/-- **Over the cap.** Seventeen queued exits against a cap of 16: the same
agreement, at the boundary the P-DRAIN-1 kill-line protects. The window is
truncated by `List.take (capOf .exit)` on the model side and by the runtime's own
`PUSH1 cap` on the bytecode side, and the two agree byte for byte. -/
theorem pdrain1_xi_drains_pinned_exit_over_cap :
    observe (pinnedCall .exit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty
        (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17)).result
      = some { reverted := false
               returnData :=
                 concatReturned
                   ((toModel .exit (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17) 0).queue.take
                     (capOf .exit)) } := by
  native_decide

/-- **The deposit runtime, likewise.** P-DRAIN-1 spans both predeploys, so the
residual is discharged on both. The deposit record encoding is the one
`Model.encodeReturned` converts to little-endian in the amount field, so this
also checks that conversion against the pinned bytecode. -/
theorem pdrain1_xi_drains_pinned_deposit :
    observe (pinnedCall .deposit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty
        Eip8282.Audit.Guarantees.PDrain1.depositQueue1).result
      = some { reverted := false
               returnData :=
                 concatReturned
                   ((toModel .deposit Eip8282.Audit.Guarantees.PDrain1.depositQueue1 0).queue.take
                     (capOf .deposit)) } := by
  native_decide

/-- **P-CONTROL-1's residual, discharged at the pinned fee getter.** An empty
non-system call with zero value against a non-inhibited image: the pinned runtime
quotes exactly `toBeBytes (currentFee model) 32`, the thirty-two big-endian bytes
`Model.userCall` returns. The `fakeExponential` fee is computed on both sides and
compared, so this is the digit equation `pcontrol1_exitAgrees_iff_digits` splits
apart, proved rather than assumed. -/
theorem pcontrol1_xi_quotes_pinned_fee :
    observe (pinnedCall .exit (EvmRunner.toAddress Eip8282.Audit.Guarantees.PDrain1.submitter)
        EvmRunner.ZERO_U256 ByteArray.empty
        (Eip8282.Audit.Guarantees.PDrain1.exitQueue 2)).result
      = some { reverted := false
               returnData :=
                 toBeBytes
                   (currentFee (toModel .exit (Eip8282.Audit.Guarantees.PDrain1.exitQueue 2) 0))
                   32 } := by
  native_decide

/-- **The agreement is not an artefact of the shapes.** The pinned drain at a
two-item queue does not answer the three-item queue's window, so the equations
above are discriminating rather than trivially satisfiable. -/
theorem pdrain1_xi_pinned_exit_discriminates :
    observe (pinnedCall .exit EvmRunner.sysAddr EvmRunner.ZERO_U256 ByteArray.empty
        (Eip8282.Audit.Guarantees.PDrain1.exitQueue 2)).result
      ≠ some { reverted := false
               returnData :=
                 concatReturned
                   ((toModel .exit (Eip8282.Audit.Guarantees.PDrain1.exitQueue 3) 0).queue.take
                     (capOf .exit)) } := by
  native_decide

/-! ## The residual, discharged on the submit path

The section above discharges the residual on system calls and on the fee
getter's empty-calldata user call. Both are branches whose abstract answer is
computed from storage alone. The *submit* path — a user call carrying calldata
and value, the path `P-SUBMIT-1` is registered about — was not among them: every
statement above about `Model.userCall` on non-empty calldata is conditional on
`ExitAgrees` or on a branch hypothesis, and no run of the pinned bytecode had
been proved to agree with `Model.userCall` there at any argument at all.

This section proves it at concrete images, on all three branches the conditional
lemmas above name, for both predeploys:

* accepted (`psubmit1_exitAgrees_iff_accepted`'s branch: uninhibited, non-empty
  calldata, `admissible`) — the runtime appends and answers with no data;
* rejected (`psubmit1_exitAgrees_iff_rejected`'s branch: `admissible` false,
  here by underpayment) — the runtime reverts;
* inhibited (`psubmit1_exitAgrees_iff`'s branch) — the runtime reverts.

`psubmit1_pinned_exit_accepted`, `psubmit1_pinned_exit_rejected` and
`psubmit1_pinned_exit_inhibited` are `decide`-checked and pin each image to the
branch it is claimed to exercise, so these are points of those conditional
statements rather than unrelated runs. `represents_pinnedExitSubmit` and
`represents_pinnedDepositSubmit` do the same for the transports' `Represents`
premise, now at arbitrary value and calldata rather than only the empty call.
`psubmit1_xi_pinned_exit_submission_discriminates` is the negative control: the
accepting run does not answer what the model answers on the rejecting one, so
the agreement is not an artefact of both sides publishing nothing.

Each discharge is stated as `observe c.result = some (observeModel (Model.step
model mstep))` — verbatim the conclusion of `XiTransport` — with **no
`ExitAgrees`, no memory hypothesis and no byte equation assumed**.

**This does not close `A-ABSTRACT-TX`.** Two images and two payment levels are
not every storage image and every value, the discharges are `native_decide` and
so rest on `A-NATIVE-DECIDE`, and `XiTransport` itself is unchanged and still
consumes `ExitAgrees`.
-/

/-- The bridge on a general non-system call into the exit runtime: definitional,
exactly as `pinnedCall_result_exitUser` is, but at arbitrary value and calldata
so the submitting calls below are covered. -/
theorem pinnedCall_result_exitCall (callerNat value : Nat) (calldata : ByteArray)
    (storage : EvmYul.Storage) :
    (pinnedCall .exit (EvmRunner.toAddress callerNat) (EvmRunner.u256 value)
        calldata storage).result
      = EvmRunner.runExit Eip8282.Audit.Guarantees.PDrain1.FUEL callerNat value calldata
          (code := Eip8282.Audit.Bytecode.exitRuntime) (storage := storage) := rfl

/-- The same bridge on the deposit runtime. -/
theorem pinnedCall_result_depositCall (callerNat value : Nat) (calldata : ByteArray)
    (storage : EvmYul.Storage) :
    (pinnedCall .deposit (EvmRunner.toAddress callerNat) (EvmRunner.u256 value)
        calldata storage).result
      = EvmRunner.runDeposit Eip8282.Audit.Guarantees.PDrain1.FUEL callerNat value calldata
          (code := Eip8282.Audit.Bytecode.depositRuntime) (storage := storage) := rfl

/-- **A submitting call is an instance of the transports' `Represents` premise.**
Generalises `represents_pinnedExitFeeGetter` off the empty zero-value call: the
account lookup does not read the value or the calldata, so it stays `rfl`. -/
theorem represents_pinnedExitSubmit {value : UInt256} {calldata : ByteArray}
    {storage : EvmYul.Storage} (hwf : WellFormed .exit storage) :
    Represents .exit
      (pinnedCall .exit (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        value calldata storage).entry
      (toModel .exit storage 0) :=
  ⟨EvmRunner.mkAccount (runtimeCode .exit) EvmRunner.ZERO_U256 storage, rfl, rfl, hwf, rfl⟩

/-- The same, on the deposit runtime. -/
theorem represents_pinnedDepositSubmit {value : UInt256} {calldata : ByteArray}
    {storage : EvmYul.Storage} (hwf : WellFormed .deposit storage) :
    Represents .deposit
      (pinnedCall .deposit (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        value calldata storage).entry
      (toModel .deposit storage 0) :=
  ⟨EvmRunner.mkAccount (runtimeCode .deposit) EvmRunner.ZERO_U256 storage, rfl, rfl, hwf, rfl⟩

/-- The accepting image is in `psubmit1_exitAgrees_iff_accepted`'s branch. -/
theorem psubmit1_pinned_exit_accepted :
    inhibited (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0) = false ∧
      bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput ≠ [] ∧
      admissible (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
        (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput)
        Eip8282.Audit.Guarantees.PSubmit1.payment = true :=
  ⟨by decide, by decide, by decide⟩

/-- The underpaying image is in `psubmit1_exitAgrees_iff_rejected`'s branch:
uninhibited and non-empty, but not `admissible`. -/
theorem psubmit1_pinned_exit_rejected :
    inhibited (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0) = false ∧
      bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput ≠ [] ∧
      admissible (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
        (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput) 0 = false :=
  ⟨by decide, by decide, by decide⟩

/-- The inhibited image is in `psubmit1_exitAgrees_iff`'s branch. -/
theorem psubmit1_pinned_exit_inhibited :
    inhibited (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.inhibitedStorage 0) = true := by
  decide

/-- **P-SUBMIT-1's residual, discharged at a pinned accepted exit submission.**
A well-formed 48-byte pubkey paying above the quoted fee against an uninhibited
image: the pinned runtime's complete `Ξ` observation is exactly the abstract
user call's — it succeeds, and it publishes no bytes, which is what
`Model.userCall` answers an accepted submission with.

No `ExitAgrees`, no `hbytes`: this is the hypothesis
`psubmit1_xi_accepted_returns_nothing` leaves open, proved at this image. -/
theorem psubmit1_xi_accepts_pinned_exit_submission :
    observe (pinnedCall .exit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 Eip8282.Audit.Guarantees.PSubmit1.payment)
        Eip8282.Audit.Guarantees.PSubmit1.exitInput
        Eip8282.Audit.Guarantees.PSubmit1.liveStorage).result
      = some (observeModel (Model.step
          (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput)
            Eip8282.Audit.Guarantees.PSubmit1.payment))) := by
  native_decide

/-- **... and at a pinned rejected one.** The same submission with no value
attached is below the quoted fee, so `admissible` is false and the model
reverts; the pinned runtime reverts too, with no data. This is the hypothesis
`psubmit1_xi_rejected_reverts_of_zero_length` leaves open. -/
theorem psubmit1_xi_rejects_pinned_exit_underpayment :
    observe (pinnedCall .exit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 0)
        Eip8282.Audit.Guarantees.PSubmit1.exitInput
        Eip8282.Audit.Guarantees.PSubmit1.liveStorage).result
      = some (observeModel (Model.step
          (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput) 0))) := by
  native_decide

/-- **... and on the inhibited image.** The same paying submission against
`storedExcess = INHIBITOR` is refused before admissibility is consulted. This is
the hypothesis `psubmit1_xi_inhibited_reverts_of_zero_length` leaves open. -/
theorem psubmit1_xi_inhibits_pinned_exit_submission :
    observe (pinnedCall .exit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 Eip8282.Audit.Guarantees.PSubmit1.payment)
        Eip8282.Audit.Guarantees.PSubmit1.exitInput
        Eip8282.Audit.Guarantees.PSubmit1.inhibitedStorage).result
      = some (observeModel (Model.step
          (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.inhibitedStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput)
            Eip8282.Audit.Guarantees.PSubmit1.payment))) := by
  native_decide

/-- **The deposit runtime, accepted.** `P-SUBMIT-1` spans both predeploys, so the
submit path is discharged on both. The deposit branch of `admissible` also reads
the amount field out of the calldata, so this checks that decoding against the
pinned bytecode as well. -/
theorem psubmit1_xi_accepts_pinned_deposit_submission :
    observe (pinnedCall .deposit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 Eip8282.Audit.Guarantees.PSubmit1.payment)
        Eip8282.Audit.Guarantees.PSubmit1.depositInput
        Eip8282.Audit.Guarantees.PSubmit1.liveStorage).result
      = some (observeModel (Model.step
          (toModel .deposit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.depositInput)
            Eip8282.Audit.Guarantees.PSubmit1.payment))) := by
  native_decide

/-- **The deposit runtime, rejected.** -/
theorem psubmit1_xi_rejects_pinned_deposit_underpayment :
    observe (pinnedCall .deposit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 0)
        Eip8282.Audit.Guarantees.PSubmit1.depositInput
        Eip8282.Audit.Guarantees.PSubmit1.liveStorage).result
      = some (observeModel (Model.step
          (toModel .deposit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.depositInput) 0))) := by
  native_decide

/-- **The agreement is not an artefact of both sides publishing nothing.** All
five observations above carry empty return data, so the only thing distinguishing
them is the status flag — and it does distinguish them: the accepting run does
not answer what the model answers on the rejecting one. -/
theorem psubmit1_xi_pinned_exit_submission_discriminates :
    observe (pinnedCall .exit
        (EvmRunner.toAddress Eip8282.Audit.Guarantees.PSubmit1.submitter)
        (EvmRunner.u256 Eip8282.Audit.Guarantees.PSubmit1.payment)
        Eip8282.Audit.Guarantees.PSubmit1.exitInput
        Eip8282.Audit.Guarantees.PSubmit1.liveStorage).result
      ≠ some (observeModel (Model.step
          (toModel .exit Eip8282.Audit.Guarantees.PSubmit1.liveStorage 0)
          (.user Eip8282.Audit.Guarantees.PSubmit1.submitter
            (bytes Eip8282.Audit.Guarantees.PSubmit1.exitInput) 0))) := by
  native_decide

/-! ## An `MSTORE` loop of arbitrary length, and the `ExitAgrees` it discharges

The single-store fragment above (`endpointAgrees_of_mstore_return_zero`) covers a
window written by **one** `MSTORE`. The return windows the pinned contracts
actually build are written by a *loop* whose trip count depends on the queue, and
`#9`'s read-over-write frame lemmas (`ByteArray.readWithPadding_write_of_le` /
`_of_ge`) both demand `hfit : destAddr + len ≤ dest.size`, which is false for a
store that grows memory. So they cannot be chained across a growing loop.

This section takes the other route, which needs **no new `EVMYulLean` API**. When a
store lands exactly at the current end of memory (`spos.toNat = μ.memory.size`),
`ByteArray.write_eq_of_grows` degenerates to a plain append
(`memory_mstore_append`). A run of such stores therefore satisfies
`post.memory = pre.memory ++ concatWords vs` for *any* length (`memory_AppendStores`),
with no frame reasoning and no window splitting, and a final `RETURN(0, 32·n)` off a
memory that started empty reads back exactly the concatenation
(`bytes_readWithPadding_of_appendStores`).

`AppendStores` is not a hypothesis about an abstract run: each step is a real
`StepOk … (.MSTORE, none) …` discharged through `step_MSTORE`, and
`AppendStores.runs` turns the whole chain into a `Runs`, so it composes with the
existing `RunUntil`/`Runs` plumbing. `appendStores_two` exhibits a concrete
two-store inhabitant built from real opcodes, so the predicate is not vacuous.

`endpointAgrees_of_mstores_return` and `exitAgrees_of_mstores_return` then put
`EndpointAgrees` / `ExitAgrees` in the **conclusion** for a loop of arbitrary
length — the residual the three registered parents still carry as a hypothesis is
discharged here for this path.

The window shape proved by `AppendStores` is `n` aligned 32-byte words, while
`concatReturned` records are 68 bytes (exit) and 184 bytes (deposit).
`pdrain1_xi_returns_fifo_prefix_of_mstores` consequently still takes `hwords`, a
hypothesis relating only *computed words* to `concatReturned` (it mentions no EVM
state), exactly as `pcontrol1_xi_fee_getter_of_mstore_pushes` takes
`hval : v.toNat = currentFee model`. The `OverlapStores` section below removes
`hwords` for the exit layout by proving that byte-for-byte at the 68-byte stride.

The deposit layout needs more than that. Its record is 184 bytes, and while six
of the seven stores in the pinned drain loop are plain `MSTORE`s that
`OverlapStores` can express, the seventh is not: `encodeReturned (.deposit …)`
carries the amount *little-endian* (`toLeBytes amount 8`), and the runtime writes
it with the `%MSTORE64_le` macro, a byte-level 8-byte splice into the middle of
an already-stored word. `OverlapStores` steps are whole-word `MSTORE`s only, so
it cannot describe that splice. The `MixedStores` section below supplies the
read-over-`MSTORE8` reasoning it needs — `bytes_memory_mstore8` at the byte-array
level and `bytes_memory_step_MSTORE8` at the opcode level — and admits `MSTORE`
and `MSTORE8` in one loop. `splicedBytes_depositRecord` then computes the pinned
184-byte stride (three words, the eight-byte little-endian splice at `+80`, three
more words, the last overshooting by eight zero bytes) to be the model's own
`encodeReturned`, and `pdrain1_xi_returns_fifo_prefix_of_depositStores` carries
that to P-DRAIN-1's complete-`Ξ` observation with **no `hwords` and no `hbytes`**.
`pdrain1_xi_returns_fifo_prefix_of_mstores` is therefore no longer the only
statement covering the deposit path.

**What is still open.** Reachability. Every lemma in this file is universally
quantified over its starting state, so none of them says the pinned runtime
*reaches* the shape it describes: `hfresh`, `hstores`, `hlen` and the per-record
`DepositRecordWords.ok` / `ExitRecordWords.ok` assert precisely that it does.
`exists_depositRecordWords` and `exists_exitRecordWords` show those scalar side
conditions are satisfiable rather than vacuous, and `mixedStores_depositPrefix`
inhabits `MixedStores` with four real opcodes, but neither is a proof that the
runtime performs the run. **A-ABSTRACT-TX remains OPEN**.
-/

theorem bytes_eq_map_data (b : ByteArray) :
    bytes b = b.data.toList.map UInt8.toNat := by
  refine List.ext_getElem (by simp [bytes]) fun i h₁ h₂ => ?_
  have hi : i < b.size := by simpa [bytes] using h₁
  have hi' : i < b.data.size := by simpa [ByteArray.size_data] using hi
  simp only [bytes, List.getElem_map, List.getElem_range, ByteArray.get!,
    Array.getElem_toList]
  rw [getElem!_pos b.data i hi']

theorem bytes_append (a b : ByteArray) : bytes (a ++ b) = bytes a ++ bytes b := by
  simp [bytes_eq_map_data, ByteArray.data_append]

theorem byteArray_append_assoc (a b c : ByteArray) : (a ++ b) ++ c = a ++ (b ++ c) := by
  ext1; simp [ByteArray.data_append, Array.append_assoc]

theorem readWithPadding_self (b : ByteArray) (hpos : 0 < b.size) (h64 : b.size < 2 ^ 64) :
    b.readWithPadding 0 b.size = b := by
  rw [ByteArray.readWithPadding_eq_extract b 0 b.size hpos h64 (by omega)]
  ext1
  simp

/-- `MSTORE` at the current end of memory appends the stored word. -/
theorem memory_mstore_append (μ : MachineState) (spos sval : UInt256)
    (hat : spos.toNat = μ.memory.size) :
    (μ.mstore spos sval).memory = μ.memory ++ sval.toByteArray := by
  show ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32 = _
  rw [ByteArray.write_eq_of_grows _ _ _ _ (by norm_num)
      (EvmYul.UInt256.size_toByteArray sval) (by omega)
      (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)]
  have hext : μ.memory.data.extract 0 μ.memory.size = μ.memory.data := by
    rw [← ByteArray.size_data]; exact Array.extract_size
  ext1
  simp [hat, hext, ByteArray.data_append]

theorem memory_step_MSTORE_append {f g : Nat} {st mid : EVM.State} {s : Stack UInt256}
    {μ₀ v : UInt256}
    (hpop : st.stack.pop2 = some (s, μ₀, v))
    (hstep : StepOk (f + 1) g (.MSTORE, none) st mid)
    (hat : μ₀.toNat = st.memory.size) :
    mid.memory = st.memory ++ v.toByteArray := by
  have h1 : EvmYul.EVM.step (f + 1) g (some (.MSTORE, none)) st = .ok mid := hstep
  have h2 : EvmYul.EVM.step (f + 1) g (some (.MSTORE, none)) st
      = .ok (mstorePost g st s μ₀ v) := step_MSTORE f g st s μ₀ v hpop
  have hpost : mid = mstorePost g st s μ₀ v := Except.ok.inj (h1.symm.trans h2)
  rw [hpost, memory_step_MSTORE_eq]
  exact memory_mstore_append st.toMachineState μ₀ v hat

/-- The bytes a list of stored words lays down, in order. -/
def concatWords : List UInt256 → ByteArray
  | [] => ByteArray.empty
  | v :: vs => v.toByteArray ++ concatWords vs

@[simp] theorem concatWords_nil : concatWords [] = ByteArray.empty := rfl

@[simp] theorem concatWords_cons (v : UInt256) (vs : List UInt256) :
    concatWords (v :: vs) = v.toByteArray ++ concatWords vs := rfl

theorem size_concatWords (vs : List UInt256) : (concatWords vs).size = 32 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [concatWords_cons, ByteArray.size_append, EvmYul.UInt256.size_toByteArray, ih]
    simp [Nat.mul_succ]; omega

theorem bytes_concatWords (vs : List UInt256) :
    bytes (concatWords vs) = (vs.map fun v => toBeBytes v.toNat 32).flatten := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [concatWords_cons, bytes_append, bytes_toByteArray, ih]
    simp

/-- **A loop of real `MSTORE` opcodes, each storing at the current end of memory.**
`tr` is the trace the run takes, so the chain composes with `Runs`. -/
inductive AppendStores : List Labelled → List UInt256 → EVM.State → EVM.State → Prop
  | nil (st : EVM.State) : AppendStores [] [] st st
  | cons {f g : Nat} {v : UInt256} {vs : List UInt256} {tr : List Labelled}
      {st mid post : EVM.State} {s : Stack UInt256} {μ₀ : UInt256}
      (hat : μ₀.toNat = st.memory.size)
      (hpop : st.stack.pop2 = some (s, μ₀, v))
      (hstep : StepOk (f + 1) g (.MSTORE, none) st mid)
      (htail : AppendStores tr vs mid post) :
      AppendStores ((f + 1, g, (.MSTORE, none)) :: tr) (v :: vs) st post

theorem AppendStores.runs {tr : List Labelled} {vs : List UInt256} {st post : EVM.State}
    (h : AppendStores tr vs st post) : Runs tr st post := by
  induction h with
  | nil st => exact .nil st
  | cons _ _ hstep _ ih => exact .cons hstep ih

/-- **What the loop leaves in memory.** Whatever memory held before, the run
appends the words it stored, in order. No hypothesis about what memory held. -/
theorem memory_AppendStores {tr : List Labelled} {vs : List UInt256} {st post : EVM.State}
    (h : AppendStores tr vs st post) : post.memory = st.memory ++ concatWords vs := by
  induction h with
  | nil st => ext1; simp
  | @cons _ _ v _ _ st mid _ _ _ hat hpop hstep _ ih =>
    rw [ih, memory_step_MSTORE_append hpop hstep hat, concatWords_cons,
      byteArray_append_assoc]

theorem byteArray_eq_empty_of_size_zero {b : ByteArray} (h : b.size = 0) :
    b = ByteArray.empty := by
  ext1
  exact Array.eq_empty_of_size_eq_zero (by simpa [ByteArray.size_data] using h)

/-- **The residual byte equation for a whole `MSTORE` loop.** The window the
`RETURN` reads holds exactly the model's big-endian encodings of the words the
loop stored, concatenated. No `hbytes`, no `ExitAgrees`, no bound on how many
words were stored. -/
theorem bytes_readWithPadding_of_appendStores {tr : List Labelled} {vs : List UInt256}
    {pre mid : EVM.State} {μ₁ : UInt256}
    (hfresh : pre.memory.size = 0)
    (h : AppendStores tr vs pre mid)
    (hne : vs ≠ [])
    (hlen : μ₁.toNat = 32 * vs.length)
    (h64 : 32 * vs.length < 2 ^ 64) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat)
      = (vs.map fun v => toBeBytes v.toNat 32).flatten := by
  have hmem : mid.memory = concatWords vs := by
    rw [memory_AppendStores h, byteArray_eq_empty_of_size_zero hfresh,
      ByteArray.empty_append_self]
  have hpos : 0 < vs.length := List.length_pos_iff.mpr hne
  have hsize : mid.memory.size = μ₁.toNat := by rw [hmem, size_concatWords, hlen]
  rw [← hsize, readWithPadding_self _ (by rw [hsize, hlen]; omega) (by rw [hsize, hlen]; omega),
    hmem, bytes_concatWords]

/-- **`EndpointAgrees`, as a conclusion, for an `MSTORE` loop of arbitrary
length.** `endpointAgrees_of_mstore_pushes_return_zero` proves the one-word fee
getter. This is the same discharge for a run of `vs.length` stores — the shape a
drain loop takes — and it is `EndpointAgrees` in the conclusion, with no
`hbytes`, no `ExitAgrees` and no `EndpointAgrees` hypothesis, no assumption about
memory beyond the fresh frame's `memory.size = 0`, and no `native_decide`. -/
theorem endpointAgrees_of_mstores_return {f g : Nat} {tr : List Labelled}
    {vs : List UInt256} {pre mid : EVM.State} {s' : Stack UInt256} {len : UInt256}
    {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : AppendStores tr vs pre mid)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hne : vs ≠ [])
    (hlen : len.toNat = 32 * vs.length)
    (h64 : 32 * vs.length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model ((vs.map fun v => toBeBytes v.toNat 32).flatten)) := by
  refine ⟨returnPost g mid s' ⟨0⟩ len,
    hstores.runs.trans (.one (step_RETURN f g mid s' ⟨0⟩ len hstack)), ?_⟩
  have hb : bytes (returnPost g mid s' ⟨0⟩ len).H_return
      = (vs.map fun v => toBeBytes v.toNat 32).flatten := by
    rw [H_return_step_RETURN g mid s' ⟨0⟩ len, show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    exact bytes_readWithPadding_of_appendStores hfresh hstores hne hlen h64
  simp [EndpointAgrees, observe, hb]

/-- The same run stated as `ExitAgrees` itself — the residual the three parents
carry — with `ExitAgrees` in the conclusion. -/
theorem exitAgrees_of_mstores_return {f g : Nat} {tr : List Labelled}
    {vs : List UInt256} {pre mid : EVM.State} {s' : Stack UInt256} {len : UInt256}
    {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : AppendStores tr vs pre mid)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hne : vs ≠ [])
    (hlen : len.toNat = 32 * vs.length)
    (h64 : 32 * vs.length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
          (.success model ((vs.map fun v => toBeBytes v.toNat 32).flatten)) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_mstores_return (f := f) (g := g) hfresh hstores hstack hne hlen h64
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-- **The loop predicate is inhabited, and by real opcodes.** Two `MSTORE`s at
consecutive words of a fresh frame satisfy `AppendStores`, so nothing below is
vacuously true: the hypotheses are the stack shapes an `MSTORE` needs and
nothing else. -/
theorem appendStores_two {f₁ g₁ f₂ g₂ : Nat} {pre : EVM.State} {s s₁ : Stack UInt256}
    {v₁ v₂ μ₀ μ₀' : UInt256}
    (hfresh : pre.memory.size = 0)
    (hpop : pre.stack.pop2 = some (s, μ₀, v₁))
    (hat : μ₀.toNat = 0)
    (hpop' : s.pop2 = some (s₁, μ₀', v₂))
    (hat' : μ₀'.toNat = 32) :
    AppendStores [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.MSTORE, none))] [v₁, v₂]
      pre (mstorePost g₂ (mstorePost g₁ pre s μ₀ v₁) s₁ μ₀' v₂) := by
  have hmem : (mstorePost g₁ pre s μ₀ v₁).memory.size = 32 := by
    rw [memory_step_MSTORE_eq, memory_mstore_append _ _ _ (by rw [hat, hfresh]),
      ByteArray.size_append, EvmYul.UInt256.size_toByteArray, hfresh]
  refine .cons (by rw [hat, hfresh]) hpop (step_MSTORE f₁ g₁ pre s μ₀ v₁ hpop)
    (.cons (by rw [hat', hmem]) hpop' (step_MSTORE f₂ g₂ _ s₁ μ₀' v₂ hpop') (.nil _))

/-- **P-DRAIN-1's non-empty window, with the memory equation gone.**

Compare `pdrain1_xi_returns_fifo_prefix_of_memory`, which assumes
`hbytes : bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat) = concatReturned …`
— an equation about every byte of the pinned runtime's memory. Here that is
*proved*, from the `MSTORE` opcodes the drain loop executes, and what is left in
its place is `hwords`: that the words the runtime computed encode to the capped
FIFO window. `hwords` mentions no EVM state at all.

This is the drain analogue of `pcontrol1_xi_fee_getter_of_mstore_pushes`, and
unlike it the store count is not fixed: `vs` is arbitrary. -/
theorem pdrain1_xi_returns_fifo_prefix_of_mstores {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace tr : List Labelled} {exit mid post pre : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₁ : UInt256} {vs : List UInt256}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hfresh : pre.memory.size = 0)
    (hstores : AppendStores tr vs pre mid)
    (hne : vs ≠ [])
    (hlen : μ₁.toNat = 32 * vs.length)
    (h64 : 32 * vs.length < 2 ^ 64)
    (hwords : (vs.map fun v => toBeBytes v.toNat 32).flatten
      = concatReturned (model.queue.take (capOf kind))) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } :=
  pdrain1_xi_returns_fifo_prefix_of_memory (calldataNonempty := calldataNonempty) c hrep hrun
    hdec hZ hstep hop hstack
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        bytes_readWithPadding_of_appendStores hfresh hstores hne hlen h64, hwords])

/-! ## The unaligned window: a real EIP-7002 exit drain

`pdrain1_xi_returns_fifo_prefix_of_mstores` above still carries `hwords`,
because `AppendStores` grows memory one whole word at a time and so can only
describe a `32·n`-byte window. A real exit drain does not have that shape: its
records are 68 bytes each, so every record after the first starts mid-word and
each `MSTORE` overwrites the previous record's 32-byte overshoot. What follows
replaces `AppendStores` with `OverlapStores`, which allows exactly that
overwrite, and proves the byte layout at the 68-byte stride outright.
-/

/-! ## Prefixes -/

theorem bytes_extract_zero (b : ByteArray) (d : Nat) :
    bytes (b.extract 0 d) = (bytes b).take d := by
  rw [bytes_eq_map_data, bytes_eq_map_data, ← List.map_take]
  congr 1
  simp [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem bytes_readWithPadding_prefix (b : ByteArray) (L : Nat)
    (hpos : 0 < L) (h64 : L < 2 ^ 64) (hfit : L ≤ b.size) :
    bytes (b.readWithPadding 0 L) = (bytes b).take L := by
  rw [ByteArray.readWithPadding_eq_extract b 0 L hpos h64 (by omega), Nat.zero_add,
    bytes_extract_zero]

/-! ## Overwriting stores -/

theorem memory_mstore_overwrite (μ : MachineState) (spos sval : UInt256)
    (hle : spos.toNat ≤ μ.memory.size) (hcov : μ.memory.size ≤ spos.toNat + 32) :
    (μ.mstore spos sval).memory = μ.memory.extract 0 spos.toNat ++ sval.toByteArray := by
  show ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32 = _
  rw [ByteArray.write_eq_of_grows _ _ _ _ (by norm_num)
      (EvmYul.UInt256.size_toByteArray sval) (by omega)
      (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)]
  ext1
  simp [ByteArray.data_append, ByteArray.data_extract,
    show spos.toNat - μ.memory.size = 0 from by omega]

theorem memory_step_MSTORE_overwrite {f g : Nat} {st mid : EVM.State} {s : Stack UInt256}
    {μ₀ v : UInt256}
    (hpop : st.stack.pop2 = some (s, μ₀, v))
    (hstep : StepOk (f + 1) g (.MSTORE, none) st mid)
    (hle : μ₀.toNat ≤ st.memory.size) (hcov : st.memory.size ≤ μ₀.toNat + 32) :
    mid.memory = st.memory.extract 0 μ₀.toNat ++ v.toByteArray := by
  have h1 : EvmYul.EVM.step (f + 1) g (some (.MSTORE, none)) st = .ok mid := hstep
  have h2 : EvmYul.EVM.step (f + 1) g (some (.MSTORE, none)) st
      = .ok (mstorePost g st s μ₀ v) := step_MSTORE f g st s μ₀ v hpop
  have hpost : mid = mstorePost g st s μ₀ v := Except.ok.inj (h1.symm.trans h2)
  rw [hpost, memory_step_MSTORE_eq]
  exact memory_mstore_overwrite st.toMachineState μ₀ v hle hcov

/-! ## A loop of overlapping stores -/

def storedBytes : List (Nat × UInt256) → List Byte → List Byte
  | [], acc => acc
  | (d, v) :: ws, acc => storedBytes ws (acc.take d ++ toBeBytes v.toNat 32)

@[simp] theorem storedBytes_nil (acc : List Byte) : storedBytes [] acc = acc := rfl

@[simp] theorem storedBytes_cons (d : Nat) (v : UInt256) (ws : List (Nat × UInt256))
    (acc : List Byte) :
    storedBytes ((d, v) :: ws) acc = storedBytes ws (acc.take d ++ toBeBytes v.toNat 32) := rfl

theorem storedBytes_append (ws₁ ws₂ : List (Nat × UInt256)) (acc : List Byte) :
    storedBytes (ws₁ ++ ws₂) acc = storedBytes ws₂ (storedBytes ws₁ acc) := by
  induction ws₁ generalizing acc with
  | nil => rfl
  | cons w ws ih => obtain ⟨d, v⟩ := w; simp [ih]

inductive OverlapStores : List Labelled → List (Nat × UInt256) → EVM.State → EVM.State → Prop
  | nil (st : EVM.State) : OverlapStores [] [] st st
  | cons {f g off : Nat} {d v : UInt256} {ws : List (Nat × UInt256)} {tr : List Labelled}
      {st mid post : EVM.State} {s : Stack UInt256}
      (hd : d.toNat = off)
      (hle : off ≤ st.memory.size)
      (hcov : st.memory.size ≤ off + 32)
      (hpop : st.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE, none) st mid)
      (htail : OverlapStores tr ws mid post) :
      OverlapStores ((f + 1, g, (.MSTORE, none)) :: tr) ((off, v) :: ws) st post

theorem OverlapStores.runs {tr : List Labelled} {ws : List (Nat × UInt256)}
    {st post : EVM.State} (h : OverlapStores tr ws st post) : Runs tr st post := by
  induction h with
  | nil st => exact .nil st
  | cons _ _ _ _ hstep _ ih => exact .cons hstep ih

theorem bytes_memory_OverlapStores {tr : List Labelled} {ws : List (Nat × UInt256)}
    {st post : EVM.State} (h : OverlapStores tr ws st post) :
    bytes post.memory = storedBytes ws (bytes st.memory) := by
  induction h with
  | nil st => rfl
  | @cons f g off d v ws tr st mid post s hd hle hcov hpop hstep _ ih =>
    rw [ih, memory_step_MSTORE_overwrite hpop hstep (hd ▸ hle) (hd ▸ hcov),
      bytes_append, bytes_extract_zero, hd, storedBytes_cons, bytes_toByteArray]

/-! ## Stores separated by memory-neutral work

`OverlapStores` requires the `MSTORE`s to be *adjacent*: its trace is a run of
consecutive stores and nothing else. No pinned EIP-7002 runtime has that shape.
The exit drain writes its window from a loop whose body sits between
`accum_loop` (PC 247) and the back-jump at PC 300: each record's three stores
are separated by the `SLOAD`s that read the queue slot, the arithmetic that
builds the operands, the stack shuffling, and the `JUMPDEST`/`JUMP` pair that
closes the loop. Adjacency is therefore not a detail of presentation — it is a
hypothesis the pinned bytecode provably never satisfies, and it made every
`EndpointAgrees`-in-conclusion theorem below inapplicable to the real drain.

`SpacedStores` removes it. Between two stores it admits an arbitrary run — any
length, any opcodes — subject to one condition: that segment leaves `memory`
alone. That is what the loop body does; `SLOAD`, `PUSH`, `DUP`, `SWAP`, `POP`,
the arithmetic and the jumps all read and write stack and storage, never memory.

The gap condition is stated as a hypothesis on the relation, but it is not one
that has to be assumed: `SpacedStores.nil_neutral` and `SpacedStores.cons_neutral`
discharge it from `memory_Runs_neutral`, so a caller supplies a *syntactic* fact
about the gap trace — every opcode in it is a `NeutralOp` — rather than a
semantic claim about the resulting state. `NeutralOp` is exactly the non-`MSTORE`
opcode set of the pinned loop body.

`A-ABSTRACT-TX` still carries the fact that the runtime reaches these stores at
all; that is untouched, and remains OPEN. What changes is only that adjacency —
a hypothesis the pinned bytecode never satisfies — is replaced by a condition it
does. `OverlapStores.spaced` embeds the old relation into the new one, so nothing
is lost: every adjacency instance is a spaced instance with empty gaps. -/

inductive SpacedStores : List Labelled → List (Nat × UInt256) → EVM.State → EVM.State → Prop
  | nil {tr : List Labelled} {st post : EVM.State}
      (hgap : Runs tr st post) (hmem : post.memory = st.memory) :
      SpacedStores tr [] st post
  | cons {f g off : Nat} {d v : UInt256} {ws : List (Nat × UInt256)}
      {tr₀ tr : List Labelled} {st gap mid post : EVM.State} {s : Stack UInt256}
      (hgap : Runs tr₀ st gap)
      (hmem : gap.memory = st.memory)
      (hd : d.toNat = off)
      (hle : off ≤ gap.memory.size)
      (hcov : gap.memory.size ≤ off + 32)
      (hpop : gap.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE, none) gap mid)
      (htail : SpacedStores tr ws mid post) :
      SpacedStores (tr₀ ++ (f + 1, g, (.MSTORE, none)) :: tr) ((off, v) :: ws) st post

/-- **The empty case, from a syntactic gap.** `SpacedStores.nil` asks for
`post.memory = st.memory`; this asks instead that every opcode in the gap trace
be a `NeutralOp`, which is a fact about the trace rather than about the states it
produces, and derives the memory equation from `memory_Runs_neutral`. -/
theorem SpacedStores.nil_neutral {tr : List Labelled} {st post : EVM.State}
    (hgap : Runs tr st post) (hneutral : ∀ x ∈ tr, IsNeutralStep x) :
    SpacedStores tr [] st post :=
  .nil hgap (memory_Runs_neutral hgap hneutral)

/-- **The store case, from a syntactic gap.** As `SpacedStores.cons`, with the
gap's memory equation replaced by neutrality of the opcodes it runs. Together
with `nil_neutral` this is what makes the gap condition checkable against the
pinned loop body: `NeutralOp` is exactly its non-`MSTORE` opcode set, so a caller
never has to assert anything about the intermediate states. -/
theorem SpacedStores.cons_neutral {f g off : Nat} {d v : UInt256}
    {ws : List (Nat × UInt256)} {tr₀ tr : List Labelled}
    {st gap mid post : EVM.State} {s : Stack UInt256}
    (hgap : Runs tr₀ st gap)
    (hneutral : ∀ x ∈ tr₀, IsNeutralStep x)
    (hd : d.toNat = off)
    (hle : off ≤ gap.memory.size)
    (hcov : gap.memory.size ≤ off + 32)
    (hpop : gap.stack.pop2 = some (s, d, v))
    (hstep : StepOk (f + 1) g (.MSTORE, none) gap mid)
    (htail : SpacedStores tr ws mid post) :
    SpacedStores (tr₀ ++ (f + 1, g, (.MSTORE, none)) :: tr) ((off, v) :: ws) st post :=
  .cons hgap (memory_Runs_neutral hgap hneutral) hd hle hcov hpop hstep htail

theorem SpacedStores.runs {tr : List Labelled} {ws : List (Nat × UInt256)}
    {st post : EVM.State} (h : SpacedStores tr ws st post) : Runs tr st post := by
  induction h with
  | nil hgap _ => exact hgap
  | cons hgap _ _ _ _ _ hstep _ ih => exact hgap.trans (.cons hstep ih)

/-- **The adjacency requirement was never load-bearing.** Every `OverlapStores`
run is a `SpacedStores` run with empty gaps, so `SpacedStores` is a genuine
weakening of the hypothesis and no statement proved from it is stronger than
what `OverlapStores` already gave. -/
theorem OverlapStores.spaced {tr : List Labelled} {ws : List (Nat × UInt256)}
    {st post : EVM.State} (h : OverlapStores tr ws st post) : SpacedStores tr ws st post := by
  induction h with
  | nil st => exact .nil (.nil st) rfl
  | @cons f g off d v ws tr st mid post s hd hle hcov hpop hstep _ ih =>
    exact SpacedStores.cons (tr₀ := []) (.nil st) rfl hd hle hcov hpop hstep ih

/-- **What a spaced store loop leaves in memory.** Identical to
`bytes_memory_OverlapStores`, and for the same reason: the gaps do not touch
memory, so only the stores contribute. -/
theorem bytes_memory_SpacedStores {tr : List Labelled} {ws : List (Nat × UInt256)}
    {st post : EVM.State} (h : SpacedStores tr ws st post) :
    bytes post.memory = storedBytes ws (bytes st.memory) := by
  induction h with
  | nil _ hmem => rw [hmem]; rfl
  | @cons f g off d v ws tr₀ tr st gap mid post s hgap hmem hd hle hcov hpop hstep _ ih =>
    rw [ih, memory_step_MSTORE_overwrite hpop hstep (hd ▸ hle) (hd ▸ hcov),
      bytes_append, bytes_extract_zero, hd, storedBytes_cons, bytes_toByteArray, hmem]

/-! ## The model's encoders -/

theorem toBeBytes_succ (n w : Nat) :
    toBeBytes n (w + 1) = toBeBytes (n / 256) w ++ [n % 256] := by
  simp [toBeBytes, toLeBytes]

theorem toLeBytes_mul_pow (n k w : Nat) :
    toLeBytes (n * 256 ^ k) (k + w) = List.replicate k 0 ++ toLeBytes n w := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hmod : n * 256 ^ (k + 1) % 256 = 0 := by
      rw [pow_succ, ← Nat.mul_assoc]; simp
    have hdiv : n * 256 ^ (k + 1) / 256 = n * 256 ^ k := by
      rw [pow_succ, ← Nat.mul_assoc]; simp
    rw [show k + 1 + w = (k + w) + 1 from by omega, toLeBytes, hmod, hdiv, ih]
    simp [List.replicate_succ]

theorem toBeBytes_mul_pow (n k w : Nat) :
    toBeBytes (n * 256 ^ k) (k + w) = toBeBytes n w ++ List.replicate k 0 := by
  rw [toBeBytes, toLeBytes_mul_pow, List.reverse_append]
  simp [toBeBytes]

theorem beBytes_append_singleton (bs : List Byte) (b : Byte) :
    beBytes (bs ++ [b]) = beBytes bs * 256 + b := by
  simp [beBytes]

theorem toBeBytes_beBytes (bs : List Byte) (hok : ∀ b ∈ bs, b < 256) :
    toBeBytes (beBytes bs) bs.length = bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    have hb : b < 256 := hok b (by simp)
    have hdiv : (beBytes bs * 256 + b) / 256 = beBytes bs := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num : 0 < 256),
        Nat.div_eq_of_lt hb, Nat.zero_add]
    have hmod : (beBytes bs * 256 + b) % 256 = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    rw [List.length_append, List.length_cons, List.length_nil,
      show bs.length + (0 + 1) = bs.length + 1 from by omega, toBeBytes_succ,
      beBytes_append_singleton, hdiv, hmod, ih fun x hx => hok x (by simp [hx])]

/-! ## The 68-byte exit record -/

@[simp] theorem length_toBeBytes (n w : Nat) : (toBeBytes n w).length = w := by
  simp [toBeBytes]

theorem storedBytes_exitRecord (b : Nat) (acc : List Byte) (hacc : b ≤ acc.length)
    (src : Nat) (pk : List Byte) (v₀ v₁ v₂ : UInt256)
    (hpk : pk.length = 48) (hok : ∀ x ∈ pk, x < 256)
    (hv₀ : v₀.toNat = src * 2 ^ 96)
    (hv₁ : v₁.toNat = beBytes (pk.take 32))
    (hv₂ : v₂.toNat = beBytes (pk.drop 32) * 2 ^ 128) :
    storedBytes [(b, v₀), (b + 20, v₁), (b + 52, v₂)] acc
      = acc.take b ++ encodeReturned (.exit src pk) ++ List.replicate 16 0 := by
  have hlt : (pk.take 32).length = 32 := by rw [List.length_take, hpk]; omega
  have hrt : (pk.drop 32).length = 16 := by rw [List.length_drop, hpk]
  have hacc' : (acc.take b).length = b := by rw [List.length_take]; omega
  have e0 : toBeBytes v₀.toNat 32 = toBeBytes src 20 ++ List.replicate 12 0 := by
    rw [hv₀, show (2:Nat) ^ 96 = 256 ^ 12 by norm_num,
      show (32:Nat) = 12 + 20 from rfl, toBeBytes_mul_pow]
  have e1 : toBeBytes v₁.toNat 32 = pk.take 32 := by
    have h := toBeBytes_beBytes (pk.take 32) fun x hx => hok x (List.mem_of_mem_take hx)
    rw [hlt] at h
    rw [hv₁, h]
  have e2 : toBeBytes v₂.toNat 32 = pk.drop 32 ++ List.replicate 16 0 := by
    have h := toBeBytes_beBytes (pk.drop 32) fun x hx => hok x (List.mem_of_mem_drop hx)
    rw [hrt] at h
    rw [hv₂, show (2:Nat) ^ 128 = 256 ^ 16 by norm_num,
      show (32:Nat) = 16 + 16 from rfl, toBeBytes_mul_pow, h]
  have t1 : (acc.take b ++ (toBeBytes src 20 ++ List.replicate 12 0)).take (b + 20)
      = acc.take b ++ toBeBytes src 20 := by
    rw [← List.append_assoc]
    exact List.take_left' (by simp [hacc'])
  have t2 : (acc.take b ++ toBeBytes src 20 ++ pk.take 32).take (b + 52)
      = acc.take b ++ toBeBytes src 20 ++ pk.take 32 :=
    List.take_of_length_le (by simp [hacc', hlt])
  simp only [storedBytes_cons, storedBytes_nil, e0, e1, e2, t1, t2, encodeReturned]
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (pk.take 32),
    List.take_append_drop]
  simp [List.append_assoc]

/-! ## A run of exit records -/

structure ExitRecordWords where
  source : Nat
  pubkey : List Byte
  w0 : UInt256
  w1 : UInt256
  w2 : UInt256

def ExitRecordWords.ok (r : ExitRecordWords) : Prop :=
  r.pubkey.length = 48 ∧ (∀ x ∈ r.pubkey, x < 256) ∧
    r.w0.toNat = r.source * 2 ^ 96 ∧
    r.w1.toNat = beBytes (r.pubkey.take 32) ∧
    r.w2.toNat = beBytes (r.pubkey.drop 32) * 2 ^ 128

def ExitRecordWords.record (r : ExitRecordWords) : Record := .exit r.source r.pubkey

def exitStores (b : Nat) : List ExitRecordWords → List (Nat × UInt256)
  | [] => []
  | r :: rs => (b, r.w0) :: (b + 20, r.w1) :: (b + 52, r.w2) :: exitStores (b + 68) rs

@[simp] theorem exitStores_nil (b : Nat) : exitStores b [] = [] := rfl

@[simp] theorem exitStores_cons (b : Nat) (r : ExitRecordWords) (rs : List ExitRecordWords) :
    exitStores b (r :: rs)
      = [(b, r.w0), (b + 20, r.w1), (b + 52, r.w2)] ++ exitStores (b + 68) rs := rfl

theorem length_encodeReturned_exit (src : Nat) (pk : List Byte) (hpk : pk.length = 48) :
    (encodeReturned (.exit src pk)).length = 68 := by
  simp [encodeReturned, hpk]

theorem storedBytes_exitStores (r : ExitRecordWords) (rs : List ExitRecordWords)
    (hok : ∀ x ∈ r :: rs, x.ok) (b : Nat) (acc : List Byte) (hacc : b ≤ acc.length) :
    storedBytes (exitStores b (r :: rs)) acc
      = acc.take b ++ concatReturned ((r :: rs).map ExitRecordWords.record)
        ++ List.replicate 16 0 := by
  induction rs generalizing r b acc with
  | nil =>
    obtain ⟨hpk, hbyte, hv₀, hv₁, hv₂⟩ := hok r (by simp)
    rw [exitStores_cons, exitStores_nil, List.append_nil,
      storedBytes_exitRecord b acc hacc r.source r.pubkey r.w0 r.w1 r.w2 hpk hbyte hv₀ hv₁ hv₂]
    simp [concatReturned, ExitRecordWords.record]
  | cons r' rs' ih =>
    obtain ⟨hpk, hbyte, hv₀, hv₁, hv₂⟩ := hok r (by simp)
    rw [exitStores_cons, storedBytes_append,
      storedBytes_exitRecord b acc hacc r.source r.pubkey r.w0 r.w1 r.w2 hpk hbyte hv₀ hv₁ hv₂]
    set acc' := acc.take b ++ encodeReturned (.exit r.source r.pubkey) ++ List.replicate 16 0
      with hacc'def
    have hlen : acc'.length = b + 68 + 16 := by
      rw [hacc'def]
      simp [List.length_take, length_encodeReturned_exit _ _ hpk]
      omega
    have htake : acc'.take (b + 68) = acc.take b ++ encodeReturned (.exit r.source r.pubkey) := by
      rw [hacc'def, List.append_assoc, ← List.append_assoc]
      refine List.take_left' ?_
      simp [List.length_take, length_encodeReturned_exit _ _ hpk]
      omega
    rw [ih r' (fun x hx => hok x (List.mem_cons_of_mem r hx)) (b + 68) acc' (by omega), htake]
    simp [concatReturned, ExitRecordWords.record, List.append_assoc]

/-! ## The window the `RETURN` reads -/

theorem length_concatReturned_exitRecords (rs : List ExitRecordWords) (hok : ∀ x ∈ rs, x.ok) :
    (concatReturned (rs.map ExitRecordWords.record)).length = 68 * rs.length := by
  induction rs with
  | nil => simp [concatReturned]
  | cons r rs ih =>
    obtain ⟨hpk, _, _, _, _⟩ := hok r (by simp)
    have hr : (encodeReturned r.record).length = 68 := length_encodeReturned_exit _ _ hpk
    have htl := ih fun x hx => hok x (List.mem_cons_of_mem r hx)
    simp only [concatReturned, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at htl ⊢
    omega

/-- **What the `MSTORE` loop of an EIP-7002 exit drain leaves in the window the
`RETURN` reads.** The stores land at `0, 20, 52, 68, 88, 120, …` — a 68-byte
stride, so no window here is 32-byte aligned — and what the run holds in
`[0, 68·k)` is exactly the model's `concatReturned` of those `k` records. -/
theorem bytes_readWithPadding_of_exitStores {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State} {μ₁ : UInt256}
    (hfresh : pre.memory.size = 0)
    (h : OverlapStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat)
      = concatReturned ((r :: rs).map ExitRecordWords.record) := by
  have hpre : bytes pre.memory = [] := by
    rw [← List.length_eq_zero_iff, bytes_length, hfresh]
  have hmem : bytes mid.memory
      = concatReturned ((r :: rs).map ExitRecordWords.record) ++ List.replicate 16 0 := by
    rw [bytes_memory_OverlapStores h, hpre,
      storedBytes_exitStores r rs hok 0 [] (by simp)]
    simp
  have hcl : (concatReturned ((r :: rs).map ExitRecordWords.record)).length = μ₁.toNat := by
    rw [length_concatReturned_exitRecords _ hok, hlen]
  have hsize : μ₁.toNat ≤ mid.memory.size := by
    rw [← bytes_length, hmem, List.length_append, hcl]
    omega
  rw [bytes_readWithPadding_prefix mid.memory μ₁.toNat (by simp [hlen]) (by omega) hsize,
    hmem, List.take_left' hcl]

/-- **`EndpointAgrees`, as a conclusion, for the unaligned 68·k exit window.**
`endpointAgrees_of_mstores_return` proves the aligned case, where the window is
`32·n` bytes and the loop appends whole words. That shape cannot reach a real
EIP-7002 drain, whose records are 68 bytes each. Here the stores overlap — each
one overwrites the previous record's 32-byte overshoot — and the conclusion is
`EndpointAgrees` against the model's own `concatReturned`, with no `hbytes`, no
`hwords`, no `ExitAgrees` or `EndpointAgrees` hypothesis, and no
`native_decide`. -/
theorem endpointAgrees_of_exitStores_return {f g : Nat} {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : OverlapStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  refine ⟨returnPost g mid s' ⟨0⟩ len,
    hstores.runs.trans (.one (step_RETURN f g mid s' ⟨0⟩ len hstack)), ?_⟩
  have hb : bytes (returnPost g mid s' ⟨0⟩ len).H_return
      = concatReturned ((r :: rs).map ExitRecordWords.record) := by
    rw [H_return_step_RETURN g mid s' ⟨0⟩ len, show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    exact bytes_readWithPadding_of_exitStores hfresh hstores hok hlen h64
  simp [EndpointAgrees, observe, hb]

/-- The same unaligned run stated as `ExitAgrees` itself. -/
theorem exitAgrees_of_exitStores_return {f g : Nat} {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : OverlapStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
          (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_exitStores_return (f := f) (g := g) hfresh hstores hok hstack hlen h64
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-! ## The same window, written by a loop rather than by adjacent stores

Everything above asks for `OverlapStores`: the three stores of each record, and
the records themselves, immediately following one another. The pinned exit
runtime does not do that — it writes the window from the `accum_loop` body, so
between any two of those stores sit the loads, the arithmetic and the jumps that
drive the loop. What follows re-proves the byte layout, `EndpointAgrees`,
`ExitAgrees` and the P-DRAIN-1 complete-`Ξ` transport from `SpacedStores`
instead, which admits those gaps provided they leave memory alone.

This is strictly more general: `OverlapStores.spaced` turns every instance of
the adjacency-shaped statements into an instance of these, so the theorems below
subsume them. The residual that remains is unchanged in kind — no run of the
pinned bytecode is proved here to reach these stores — but it no longer includes
the adjacency claim, which was false of the pinned runtime, nor the claim that
the drain begins with memory untouched. -/

/-- **The exit drain's window, written by a spaced loop.** As
`bytes_readWithPadding_of_exitStores`, with the adjacency requirement replaced
by memory-neutrality of whatever runs between the stores, and with no
assumption that memory starts empty: the window is written at offset `0`, so
whatever `pre` held is truncated away by the first store. -/
theorem bytes_readWithPadding_of_spacedExitStores {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State} {μ₁ : UInt256}
    (h : SpacedStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat)
      = concatReturned ((r :: rs).map ExitRecordWords.record) := by
  have hmem : bytes mid.memory
      = concatReturned ((r :: rs).map ExitRecordWords.record) ++ List.replicate 16 0 := by
    rw [bytes_memory_SpacedStores h,
      storedBytes_exitStores r rs hok 0 (bytes pre.memory) (Nat.zero_le _)]
    simp
  have hcl : (concatReturned ((r :: rs).map ExitRecordWords.record)).length = μ₁.toNat := by
    rw [length_concatReturned_exitRecords _ hok, hlen]
  have hsize : μ₁.toNat ≤ mid.memory.size := by
    rw [← bytes_length, hmem, List.length_append, hcl]
    omega
  rw [bytes_readWithPadding_prefix mid.memory μ₁.toNat (by simp [hlen]) (by omega) hsize,
    hmem, List.take_left' hcl]

/-- **`EndpointAgrees`, as a conclusion, for a drain window written by a loop.**
`endpointAgrees_of_exitStores_return` needs the stores adjacent and memory
empty; the pinned exit runtime interleaves its loop body between them and has
run its dispatcher first. Here the gaps are allowed and `pre` is arbitrary. No
`hbytes`, no `hwords`, no `ExitAgrees` or `EndpointAgrees` hypothesis, and no
`native_decide`. -/
theorem endpointAgrees_of_spacedExitStores_return {f g : Nat} {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hstores : SpacedStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  refine ⟨returnPost g mid s' ⟨0⟩ len,
    hstores.runs.trans (.one (step_RETURN f g mid s' ⟨0⟩ len hstack)), ?_⟩
  have hb : bytes (returnPost g mid s' ⟨0⟩ len).H_return
      = concatReturned ((r :: rs).map ExitRecordWords.record) := by
    rw [H_return_step_RETURN g mid s' ⟨0⟩ len, show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    exact bytes_readWithPadding_of_spacedExitStores hstores hok hlen h64
  simp [EndpointAgrees, observe, hb]

/-- The same loop-shaped run, stated as `ExitAgrees` itself — the residual the
three parents carry — with `ExitAgrees` in the conclusion. -/
theorem exitAgrees_of_spacedExitStores_return {f g : Nat} {tr : List Labelled}
    {rs : List ExitRecordWords} {r : ExitRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hstores : SpacedStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
          (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_spacedExitStores_return (f := f) (g := g) hstores hok hstack hlen h64
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-! ## The overlapping loop is inhabited by real opcodes -/

theorem size_mstorePost_overwrite (g : Nat) (pre : EVM.State) (s : Stack UInt256)
    (μ₀ v : UInt256) (hle : μ₀.toNat ≤ pre.memory.size)
    (hcov : pre.memory.size ≤ μ₀.toNat + 32) :
    (mstorePost g pre s μ₀ v).memory.size = μ₀.toNat + 32 := by
  rw [size_memory_step_MSTORE g pre s μ₀ v
    (by rw [show μ₀.toNat - pre.memory.size = 0 from by omega]; positivity)]
  omega

/-- **The overlapping-store predicate is inhabited, and by real opcodes.** The
three `MSTORE`s of one EIP-7002 exit record — at `0`, `20`, `52` of a fresh
frame — satisfy `OverlapStores` at exactly `exitStores 0 [r]`, so nothing above
is vacuously true. The hypotheses are the stack shapes an `MSTORE` needs and the
three offsets, and nothing else. -/
theorem overlapStores_exitRecord {f₀ g₀ f₁ g₁ f₂ g₂ : Nat} {pre : EVM.State}
    {s₀ s₁ s₂ : Stack UInt256} {d₀ d₁ d₂ : UInt256} (r : ExitRecordWords)
    (hfresh : pre.memory.size = 0)
    (h₀ : d₀.toNat = 0) (hp₀ : pre.stack.pop2 = some (s₀, d₀, r.w0))
    (h₁ : d₁.toNat = 20) (hp₁ : s₀.pop2 = some (s₁, d₁, r.w1))
    (h₂ : d₂.toNat = 52) (hp₂ : s₁.pop2 = some (s₂, d₂, r.w2)) :
    OverlapStores
      [(f₀ + 1, g₀, (.MSTORE, none)), (f₁ + 1, g₁, (.MSTORE, none)),
        (f₂ + 1, g₂, (.MSTORE, none))]
      (exitStores 0 [r]) pre
      (mstorePost g₂ (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1) s₂ d₂ r.w2) := by
  have e₁ : (mstorePost g₀ pre s₀ d₀ r.w0).memory.size = 32 := by
    rw [size_mstorePost_overwrite g₀ pre s₀ d₀ r.w0 (by omega) (by omega), h₀]
  have e₂ : (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size = 52 := by
    rw [size_mstorePost_overwrite g₁ _ s₁ d₁ r.w1 (by rw [e₁]; omega) (by rw [e₁]; omega), h₁]
  refine .cons h₀ (by omega) (by omega) hp₀ (step_MSTORE f₀ g₀ pre s₀ d₀ r.w0 hp₀)
    (.cons h₁ ?_ ?_ hp₁ (step_MSTORE f₁ g₁ _ s₁ d₁ r.w1 hp₁)
      (.cons h₂ ?_ ?_ hp₂ (step_MSTORE f₂ g₂ _ s₂ d₂ r.w2 hp₂) (.nil _)))
  · show 0 + 20 ≤ (mstorePost g₀ pre s₀ d₀ r.w0).memory.size
    rw [e₁]; omega
  · show (mstorePost g₀ pre s₀ d₀ r.w0).memory.size ≤ 0 + 20 + 32
    rw [e₁]; omega
  · show 0 + 52 ≤ (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size
    rw [e₂]
  · show (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size ≤ 0 + 52 + 32
    rw [e₂]; omega

/-! ## The word conditions are satisfiable -/

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := by
  have hsz : (2 : Nat) ^ 256 = UInt256.size := by unfold UInt256.size; norm_num
  show n % UInt256.size = n
  exact Nat.mod_eq_of_lt (hsz ▸ h)

theorem beBytes_lt (bs : List Byte) (hok : ∀ b ∈ bs, b < 256) :
    beBytes bs < 256 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [beBytes]
  | append_singleton bs b ih =>
    have hb : b < 256 := hok b (by simp)
    have hih := ih fun x hx => hok x (by simp [hx])
    rw [beBytes_append_singleton, List.length_append, List.length_cons, List.length_nil,
      show bs.length + (0 + 1) = bs.length + 1 from by omega, pow_succ]
    calc beBytes bs * 256 + b < beBytes bs * 256 + 256 :=
          Nat.add_lt_add_left hb (beBytes bs * 256)
      _ = (beBytes bs + 1) * 256 := by ring
      _ ≤ 256 ^ bs.length * 256 := Nat.mul_le_mul_right 256 hih

/-- **`ExitRecordWords.ok` is satisfiable for every real exit record.** Any
20-byte source address and any 48-byte pubkey of genuine bytes are carried by
words that fit in `UInt256`, so `hok` above constrains the runtime rather than
excluding it. -/
theorem exists_exitRecordWords (src : Nat) (pk : List Byte)
    (hsrc : src < 2 ^ 160) (hpk : pk.length = 48) (hbyte : ∀ x ∈ pk, x < 256) :
    ∃ r : ExitRecordWords, r.ok ∧ r.record = .exit src pk := by
  have hlt : (pk.take 32).length = 32 := by rw [List.length_take, hpk]; omega
  have hrt : (pk.drop 32).length = 16 := by rw [List.length_drop, hpk]
  have b1 : beBytes (pk.take 32) < 2 ^ 256 := by
    have := beBytes_lt (pk.take 32) fun x hx => hbyte x (List.mem_of_mem_take hx)
    rw [hlt] at this
    calc beBytes (pk.take 32) < 256 ^ 32 := this
      _ = 2 ^ 256 := by norm_num
  have b2 : beBytes (pk.drop 32) < 2 ^ 128 := by
    have := beBytes_lt (pk.drop 32) fun x hx => hbyte x (List.mem_of_mem_drop hx)
    rw [hrt] at this
    calc beBytes (pk.drop 32) < 256 ^ 16 := this
      _ = 2 ^ 128 := by norm_num
  refine ⟨⟨src, pk, UInt256.ofNat (src * 2 ^ 96), UInt256.ofNat (beBytes (pk.take 32)),
      UInt256.ofNat (beBytes (pk.drop 32) * 2 ^ 128)⟩, ⟨hpk, hbyte, ?_, ?_, ?_⟩, rfl⟩
  · exact toNat_ofNat_of_lt (by
      calc src * 2 ^ 96 < 2 ^ 160 * 2 ^ 96 :=
            (Nat.mul_lt_mul_right (by positivity)).mpr hsrc
        _ = 2 ^ 256 := by norm_num)
  · exact toNat_ofNat_of_lt b1
  · exact toNat_ofNat_of_lt (by
      calc beBytes (pk.drop 32) * 2 ^ 128 < 2 ^ 128 * 2 ^ 128 :=
            (Nat.mul_lt_mul_right (by positivity)).mpr b2
        _ = 2 ^ 256 := by norm_num)

/-! ## The overlapping loop is inhabited at every record count -/

/-- The six stack operands one exit record's three `MSTORE`s consume, in the
order the opcodes pop them: offset then value, three times. -/
def exitRecordOperands (b : Nat) (r : ExitRecordWords) : List UInt256 :=
  [UInt256.ofNat b, r.w0, UInt256.ofNat (b + 20), r.w1, UInt256.ofNat (b + 52), r.w2]

/-- The operands a whole drain of `rs` consumes, at the 68-byte record stride. -/
def exitStoresOperands (b : Nat) : List ExitRecordWords → List UInt256
  | [] => []
  | r :: rs => exitRecordOperands b r ++ exitStoresOperands (b + 68) rs

@[simp] theorem exitStoresOperands_nil (b : Nat) : exitStoresOperands b [] = [] := rfl

@[simp] theorem exitStoresOperands_cons (b : Nat) (r : ExitRecordWords)
    (rs : List ExitRecordWords) :
    exitStoresOperands b (r :: rs)
      = exitRecordOperands b r ++ exitStoresOperands (b + 68) rs := rfl

/-- The instruction trace of a drain of `n` records: three `MSTORE`s each. -/
def exitStoresTrace (f g : Nat) : Nat → List Labelled
  | 0 => []
  | n + 1 =>
    [(f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none))]
      ++ exitStoresTrace f g n

@[simp] theorem exitStoresTrace_zero (f g : Nat) : exitStoresTrace f g 0 = [] := rfl

@[simp] theorem exitStoresTrace_succ (f g n : Nat) :
    exitStoresTrace f g (n + 1)
      = [(f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none))]
        ++ exitStoresTrace f g n := rfl

/-- Overlapping runs compose. -/
theorem OverlapStores.trans {tr₁ tr₂ : List Labelled} {ws₁ ws₂ : List (Nat × UInt256)}
    {st mid post : EVM.State} (h₁ : OverlapStores tr₁ ws₁ st mid) :
    OverlapStores tr₂ ws₂ mid post → OverlapStores (tr₁ ++ tr₂) (ws₁ ++ ws₂) st post := by
  induction h₁ with
  | nil st => intro h; simpa using h
  | cons hd hle hcov hpop hstep _ ih => intro h; exact .cons hd hle hcov hpop hstep (ih h)

/-- One real `MSTORE`, from an explicit stack, lands the overlapping predicate
and pins the frame size it leaves behind. -/
theorem overlapStores_one_of_stack {f g off : Nat} {pre : EVM.State} {d v : UInt256}
    {rest : Stack UInt256}
    (hd : d.toNat = off) (hle : off ≤ pre.memory.size) (hcov : pre.memory.size ≤ off + 32)
    (hstack : pre.stack = d :: v :: rest) :
    ∃ mid, OverlapStores [(f + 1, g, (.MSTORE, none))] [(off, v)] pre mid
      ∧ mid.stack = rest ∧ mid.memory.size = off + 32 := by
  have hpop : pre.stack.pop2 = some (rest, d, v) := by rw [hstack]; rfl
  refine ⟨mstorePost g pre rest d v,
    .cons hd hle hcov hpop (step_MSTORE f g pre rest d v hpop) (.nil _), rfl, ?_⟩
  rw [size_mstorePost_overwrite g pre rest d v (by rw [hd]; exact hle) (by rw [hd]; exact hcov),
    hd]

/-- **One record's three overlapping `MSTORE`s, at an arbitrary base.**
`overlapStores_exitRecord` does this at base `0` on a fresh frame. Here the base
is any `b` and the frame need only be covered to within one word of `b`, which
is exactly the invariant a drain loop re-establishes at every record. -/
theorem overlapStores_exitRecord_step {f g b : Nat} {pre : EVM.State} {rest : Stack UInt256}
    (r : ExitRecordWords)
    (hle : b ≤ pre.memory.size) (hcov : pre.memory.size ≤ b + 32)
    (hfit : b + 52 < 2 ^ 256)
    (hstack : pre.stack = exitRecordOperands b r ++ rest) :
    ∃ mid,
      OverlapStores
        [(f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none)), (f + 1, g, (.MSTORE, none))]
        [(b, r.w0), (b + 20, r.w1), (b + 52, r.w2)] pre mid
      ∧ mid.stack = rest ∧ mid.memory.size = b + 84 := by
  obtain ⟨m₁, h₁, hs₁, hz₁⟩ := overlapStores_one_of_stack (f := f) (g := g) (off := b)
    (d := UInt256.ofNat b) (v := r.w0)
    (rest := [UInt256.ofNat (b + 20), r.w1, UInt256.ofNat (b + 52), r.w2] ++ rest)
    (toNat_ofNat_of_lt (by omega)) hle hcov (by rw [hstack]; rfl)
  obtain ⟨m₂, h₂, hs₂, hz₂⟩ := overlapStores_one_of_stack (f := f) (g := g) (off := b + 20)
    (pre := m₁) (d := UInt256.ofNat (b + 20)) (v := r.w1)
    (rest := [UInt256.ofNat (b + 52), r.w2] ++ rest)
    (toNat_ofNat_of_lt (by omega)) (by omega) (by omega) (by rw [hs₁]; rfl)
  obtain ⟨m₃, h₃, hs₃, hz₃⟩ := overlapStores_one_of_stack (f := f) (g := g) (off := b + 52)
    (pre := m₂) (d := UInt256.ofNat (b + 52)) (v := r.w2) (rest := rest)
    (toNat_ofNat_of_lt (by omega)) (by omega) (by omega) (by rw [hs₂]; rfl)
  exact ⟨m₃, by simpa using h₁.trans (h₂.trans h₃), hs₃, by omega⟩

/-- **The overlapping loop is inhabited at every record count.**
`overlapStores_exitRecord` shows `OverlapStores` is non-empty at `exitStores 0
[r]` — one record, on a fresh frame. Every statement that consumes `hstores`,
though, quantifies over a *list* of records, so one record left open whether the
predicate is reachable at the lengths those statements are about. It is: for any
`rs`, any base `b` whose frame is covered to within one word, and the operands on
the stack, the 68-byte-stride drain of `rs` runs on real `MSTORE` opcodes,
consumes exactly its operands, and re-establishes the same coverage invariant at
`b + 68 * rs.length`.

This does not say the pinned bytecode takes this run. It says `hstores` is a
claim about *which* run the runtime takes, no longer about whether one exists. -/
theorem overlapStores_exitStores {f g : Nat} (rs : List ExitRecordWords) :
    ∀ (b : Nat) (pre : EVM.State) (rest : Stack UInt256),
      b ≤ pre.memory.size → pre.memory.size ≤ b + 32 →
      b + 68 * rs.length + 32 < 2 ^ 256 →
      pre.stack = exitStoresOperands b rs ++ rest →
      ∃ post, OverlapStores (exitStoresTrace f g rs.length) (exitStores b rs) pre post
        ∧ post.stack = rest
        ∧ b + 68 * rs.length ≤ post.memory.size
        ∧ post.memory.size ≤ b + 68 * rs.length + 32 := by
  induction rs with
  | nil =>
    intro b pre rest hle hcov _ hstack
    exact ⟨pre, by simpa using OverlapStores.nil pre, by simpa using hstack,
      by simpa using hle, by simpa using hcov⟩
  | cons r rs ih =>
    intro b pre rest hle hcov hfit hstack
    simp only [List.length_cons] at hfit ⊢
    obtain ⟨mid, hmid, hms, hmz⟩ :=
      overlapStores_exitRecord_step (f := f) (g := g) (b := b) (pre := pre)
        (rest := exitStoresOperands (b + 68) rs ++ rest) r hle hcov (by omega)
        (by rw [hstack]; rfl)
    obtain ⟨post, hpost, hps, hpl, hpu⟩ :=
      ih (b + 68) mid rest (by omega) (by omega) (by omega) hms
    refine ⟨post, ?_, hps, by omega, by omega⟩
    rw [exitStoresTrace_succ, exitStores_cons]
    exact hmid.trans hpost

/-- **`EndpointAgrees` on a run that is built, not assumed.**
`endpointAgrees_of_exitStores_return` takes `hstores` — that the machine performs
the overlapping drain — as a hypothesis. Here that run is constructed by
`overlapStores_exitStores`, so the only inputs left are the initial stack, a
fresh frame, and the record well-formedness conditions. There is no `hstores`,
no `hbytes`, no `hwords`, no `ExitAgrees` or `EndpointAgrees` hypothesis, and no
`native_decide`; and it holds at every record count, not just one.

What is still *not* proved is that the pinned EIP-7002 bytecode places these
operands on the stack in this order. That gap is the whole of what
`A-ABSTRACT-TX` carries, and `EndpointAgrees` remains open in general. -/
theorem endpointAgrees_of_exitRun_return {f g : Nat} {pre : EVM.State} {rest : Stack UInt256}
    {model : Model.State} {r : ExitRecordWords} {rs : List ExitRecordWords}
    (hfresh : pre.memory.size = 0) (hok : ∀ x ∈ r :: rs, x.ok)
    (hfit : 68 * (r :: rs).length + 32 < 2 ^ 256)
    (h64 : 68 * (r :: rs).length < 2 ^ 64)
    (hstack : pre.stack = exitStoresOperands 0 (r :: rs)
      ++ (⟨0⟩ : UInt256) :: UInt256.ofNat (68 * (r :: rs).length) :: rest) :
    ∃ post,
      Runs (exitStoresTrace f g (r :: rs).length ++ [(f + 1, g, (.RETURN, none))]) pre post
        ∧ EndpointAgrees (.success post post.H_return)
            (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  obtain ⟨mid, hmid, hms, -, -⟩ :=
    overlapStores_exitStores (f := f) (g := g) (r :: rs) 0 pre
      ((⟨0⟩ : UInt256) :: UInt256.ofNat (68 * (r :: rs).length) :: rest)
      (by omega) (by omega) (by omega) hstack
  exact endpointAgrees_of_exitStores_return (f := f) (g := g) (model := model) hfresh hmid hok
    (by rw [hms]; rfl) (toNat_ofNat_of_lt (by omega)) h64

/-- The same constructed run, stated as `ExitAgrees` itself. -/
theorem exitAgrees_of_exitRun_return {f g : Nat} {pre : EVM.State} {rest : Stack UInt256}
    {model : Model.State} {r : ExitRecordWords} {rs : List ExitRecordWords}
    (hfresh : pre.memory.size = 0) (hok : ∀ x ∈ r :: rs, x.ok)
    (hfit : 68 * (r :: rs).length + 32 < 2 ^ 256)
    (h64 : 68 * (r :: rs).length < 2 ^ 64)
    (hstack : pre.stack = exitStoresOperands 0 (r :: rs)
      ++ (⟨0⟩ : UInt256) :: UInt256.ofNat (68 * (r :: rs).length) :: rest) :
    ∃ post,
      Runs (exitStoresTrace f g (r :: rs).length ++ [(f + 1, g, (.RETURN, none))]) pre post
        ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
            (.success model (concatReturned ((r :: rs).map ExitRecordWords.record))) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_exitRun_return (f := f) (g := g) (model := model) hfresh hok hfit h64 hstack
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-! ## P-DRAIN-1, with `hwords` gone — the exit layout -/

/-- **P-DRAIN-1's non-empty window at the real EIP-7002 exit layout.**

Compare `pdrain1_xi_returns_fifo_prefix_of_mstores`, which reaches the same
conclusion but carries `hwords`: that the 32-byte encodings of the stored words,
concatenated, *are* the capped FIFO window. At the drain layout that hypothesis
is all but unusable — the window it describes is `32·n` bytes while the model's
exit records are 68 bytes each, so it constrains nothing unless `8 ∣ n`.

Here the byte layout is proved instead, from overlapping `MSTORE` opcodes at the
68-byte stride the records actually take, and what replaces `hwords` is `hok`:
three *scalar* equations per record, each saying what number the runtime put in
one word. No equation about memory, no `ExitAgrees`, no `EndpointAgrees`. -/
theorem pdrain1_xi_returns_fifo_prefix_of_exitStores {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace tr : List Labelled} {exit mid post pre : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₁ : UInt256} {rs : List ExitRecordWords} {r : ExitRecordWords}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hfresh : pre.memory.size = 0)
    (hstores : OverlapStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64)
    (hqueue : model.queue.take (capOf kind) = (r :: rs).map ExitRecordWords.record) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } :=
  pdrain1_xi_returns_fifo_prefix_of_memory (calldataNonempty := calldataNonempty) c hrep hrun
    hdec hZ hstep hop hstack
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        bytes_readWithPadding_of_exitStores hfresh hstores hok hlen h64, hqueue])

/-- **P-DRAIN-1's non-empty window at the real EIP-7002 exit layout, written by a
loop.** The same complete-`Ξ` observation as
`pdrain1_xi_returns_fifo_prefix_of_exitStores`, from `SpacedStores` rather than
`OverlapStores`: the drain's stores need no longer be adjacent, only separated by
work that leaves memory alone. That is the shape the `accum_loop` body has, and
`OverlapStores.spaced` makes this statement subsume the adjacency-shaped one.

Still no `ExitAgrees`, no `EndpointAgrees`, no `hwords` and no byte equation
about memory: what replaces them is `hok`, three scalar equations per record. -/
theorem pdrain1_xi_returns_fifo_prefix_of_spacedExitStores {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace tr : List Labelled} {exit mid post pre : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₁ : UInt256} {rs : List ExitRecordWords} {r : ExitRecordWords}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hstores : SpacedStores tr (exitStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = 68 * (r :: rs).length)
    (h64 : 68 * (r :: rs).length < 2 ^ 64)
    (hqueue : model.queue.take (capOf kind) = (r :: rs).map ExitRecordWords.record) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } :=
  pdrain1_xi_returns_fifo_prefix_of_memory (calldataNonempty := calldataNonempty) c hrep hrun
    hdec hZ hstep hop hstack
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        bytes_readWithPadding_of_spacedExitStores hstores hok hlen h64, hqueue])

/-! ## List slicing -/

theorem take_split (l : List Byte) (m n : Nat) :
    l.take (m + n) = l.take m ++ (l.drop m).take n := List.take_add

theorem drop_add (l : List Byte) (m n : Nat) : l.drop (m + n) = (l.drop m).drop n := by
  rw [List.drop_drop]

theorem slice_append_drop (l : List Byte) (i k : Nat) :
    (l.drop i).take k ++ l.drop (i + k) = l.drop i := by
  rw [drop_add]
  exact List.take_append_drop k (l.drop i)

/-! ## Read-over-`MSTORE8` -/

theorem memory_mstore8_eq (μ : MachineState) (spos sval : UInt256) :
    (μ.mstore8 spos sval).memory
      = ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1 := rfl

/-- **Read-over-`MSTORE8`.** One `MSTORE8` inside the already-written region
replaces exactly one byte and leaves every other byte alone. -/
theorem bytes_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    bytes (μ.mstore8 spos sval).memory
      = (bytes μ.memory).take spos.toNat
        ++ (sval.toNat % 256) :: (bytes μ.memory).drop (spos.toNat + 1) := by
  rw [memory_mstore8_eq,
    ByteArray.write_eq_of_fits ⟨#[UInt8.ofNat sval.toNat]⟩ μ.memory spos.toNat 1
      (by norm_num) (by rfl) hfit]
  rw [bytes_eq_map_data, bytes_eq_map_data]
  simp [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.map_take, List.map_drop]

abbrev mstore8Post (gasCost : Nat) (pre : EVM.State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre gasCost pre with
        toMachineState := (stepPre gasCost pre).toMachineState.mstore8 μ₀ μ₁ } s

theorem memory_step_MSTORE8_eq (g : Nat) (pre : EVM.State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) :
    (mstore8Post g pre s μ₀ μ₁).memory = (pre.toMachineState.mstore8 μ₀ μ₁).memory := rfl

theorem size_mstore8Post (g : Nat) (pre : EVM.State) (s : Stack UInt256) (μ₀ v : UInt256)
    (hfit : μ₀.toNat + 1 ≤ pre.memory.size) :
    (mstore8Post g pre s μ₀ v).memory.size = pre.memory.size := by
  rw [memory_step_MSTORE8_eq]
  exact MachineState.size_memory_mstore8 pre.toMachineState μ₀ v hfit

theorem bytes_memory_step_MSTORE8 {f g : Nat} {st mid : EVM.State} {s : Stack UInt256}
    {μ₀ v : UInt256}
    (hpop : st.stack.pop2 = some (s, μ₀, v))
    (hstep : StepOk (f + 1) g (.MSTORE8, none) st mid)
    (hlt : μ₀.toNat < st.memory.size) :
    bytes mid.memory
      = (bytes st.memory).take μ₀.toNat
        ++ (v.toNat % 256) :: (bytes st.memory).drop (μ₀.toNat + 1) := by
  have h1 : EvmYul.EVM.step (f + 1) g (some (.MSTORE8, none)) st = .ok mid := hstep
  have h2 : EvmYul.EVM.step (f + 1) g (some (.MSTORE8, none)) st
      = .ok (mstore8Post g st s μ₀ v) := step_MSTORE8 f g st s μ₀ v hpop
  have hpost : mid = mstore8Post g st s μ₀ v := Except.ok.inj (h1.symm.trans h2)
  rw [hpost, memory_step_MSTORE8_eq]
  exact bytes_memory_mstore8 st.toMachineState μ₀ v (by omega)

/-! ## Mixed word / byte stores -/

inductive Splice where
  | word (off : Nat) (v : UInt256)
  | byte (off : Nat) (v : UInt256)

def splicedBytes : List Splice → List Byte → List Byte
  | [], acc => acc
  | .word d v :: ss, acc => splicedBytes ss (acc.take d ++ toBeBytes v.toNat 32)
  | .byte d v :: ss, acc => splicedBytes ss (acc.take d ++ (v.toNat % 256) :: acc.drop (d + 1))

@[simp] theorem splicedBytes_nil (acc : List Byte) : splicedBytes [] acc = acc := rfl

@[simp] theorem splicedBytes_word (d : Nat) (v : UInt256) (ss : List Splice) (acc : List Byte) :
    splicedBytes (.word d v :: ss) acc
      = splicedBytes ss (acc.take d ++ toBeBytes v.toNat 32) := rfl

@[simp] theorem splicedBytes_byte (d : Nat) (v : UInt256) (ss : List Splice) (acc : List Byte) :
    splicedBytes (.byte d v :: ss) acc
      = splicedBytes ss (acc.take d ++ (v.toNat % 256) :: acc.drop (d + 1)) := rfl

theorem splicedBytes_append (ss₁ ss₂ : List Splice) (acc : List Byte) :
    splicedBytes (ss₁ ++ ss₂) acc = splicedBytes ss₂ (splicedBytes ss₁ acc) := by
  induction ss₁ generalizing acc with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [ih]

theorem splicedBytes_word_append (acc : List Byte) (d : Nat) (v : UInt256) (ss : List Splice)
    (h : acc.length = d) :
    splicedBytes (.word d v :: ss) acc = splicedBytes ss (acc ++ toBeBytes v.toNat 32) := by
  rw [splicedBytes_word, List.take_of_length_le (le_of_eq h)]

/-- **A loop that mixes 32-byte `MSTORE`s with single-byte `MSTORE8`s.**

`OverlapStores` only admits `MSTORE`, so the eight `MSTORE8`s the pinned
`builder_deposits` drain emits for `%MSTORE64_le` fall outside it. This
predicate admits both, with the word case carrying the same overwrite window
condition and the byte case requiring only that the target byte is already
inside the written region. -/
inductive MixedStores : List Labelled → List Splice → EVM.State → EVM.State → Prop
  | nil (st : EVM.State) : MixedStores [] [] st st
  | word {f g off : Nat} {d v : UInt256} {ss : List Splice} {tr : List Labelled}
      {st mid post : EVM.State} {s : Stack UInt256}
      (hd : d.toNat = off)
      (hle : off ≤ st.memory.size)
      (hcov : st.memory.size ≤ off + 32)
      (hpop : st.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE, none) st mid)
      (htail : MixedStores tr ss mid post) :
      MixedStores ((f + 1, g, (.MSTORE, none)) :: tr) (.word off v :: ss) st post
  | byte {f g off : Nat} {d v : UInt256} {ss : List Splice} {tr : List Labelled}
      {st mid post : EVM.State} {s : Stack UInt256}
      (hd : d.toNat = off)
      (hlt : off < st.memory.size)
      (hpop : st.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE8, none) st mid)
      (htail : MixedStores tr ss mid post) :
      MixedStores ((f + 1, g, (.MSTORE8, none)) :: tr) (.byte off v :: ss) st post

theorem MixedStores.runs {tr : List Labelled} {ss : List Splice} {st post : EVM.State}
    (h : MixedStores tr ss st post) : Runs tr st post := by
  induction h with
  | nil st => exact .nil st
  | word _ _ _ _ hstep _ ih => exact .cons hstep ih
  | byte _ _ _ hstep _ ih => exact .cons hstep ih

/-- **What a mixed word/byte loop leaves in memory.** No `hbytes`, no `hwords`:
the byte image of the post-state is computed from the splice list alone. -/
theorem bytes_memory_MixedStores {tr : List Labelled} {ss : List Splice}
    {st post : EVM.State} (h : MixedStores tr ss st post) :
    bytes post.memory = splicedBytes ss (bytes st.memory) := by
  induction h with
  | nil st => rfl
  | @word f g off d v ss tr st mid post s hd hle hcov hpop hstep _ ih =>
    rw [ih, memory_step_MSTORE_overwrite hpop hstep (hd ▸ hle) (hd ▸ hcov),
      bytes_append, bytes_extract_zero, hd, splicedBytes_word, bytes_toByteArray]
  | @byte f g off d v ss tr st mid post s hd hlt hpop hstep _ ih =>
    rw [ih, bytes_memory_step_MSTORE8 hpop hstep (hd ▸ hlt), hd, splicedBytes_byte]

/-! ## A run of consecutive `MSTORE8`s -/

def byteRun (p : Nat) : List UInt256 → List Splice
  | [] => []
  | v :: vs => .byte p v :: byteRun (p + 1) vs

@[simp] theorem byteRun_nil (p : Nat) : byteRun p [] = [] := rfl

@[simp] theorem byteRun_cons (p : Nat) (v : UInt256) (vs : List UInt256) :
    byteRun p (v :: vs) = .byte p v :: byteRun (p + 1) vs := rfl

/-- **The little-endian byte splice, in closed form.** `%MSTORE64_le` writes a
run of consecutive single bytes; what that leaves is the surrounding image with
exactly those bytes replaced. -/
theorem splicedBytes_byteRun (vs : List UInt256) (p : Nat) (acc : List Byte)
    (h : p + vs.length ≤ acc.length) :
    splicedBytes (byteRun p vs) acc
      = acc.take p ++ vs.map (fun v => v.toNat % 256) ++ acc.drop (p + vs.length) := by
  induction vs generalizing p acc with
  | nil => simp
  | cons v vs ih =>
    have hp : p + 1 ≤ acc.length := by simp at h; omega
    set acc' := acc.take p ++ (v.toNat % 256) :: acc.drop (p + 1) with hacc'
    have hlen' : acc'.length = acc.length := by
      rw [hacc']; simp [List.length_take, List.length_drop]; omega
    have htake : acc'.take (p + 1) = acc.take p ++ [v.toNat % 256] := by
      rw [hacc', show (v.toNat % 256) :: acc.drop (p + 1)
          = [v.toNat % 256] ++ acc.drop (p + 1) from rfl, ← List.append_assoc]
      exact List.take_left' (by simp [List.length_take]; omega)
    have hdrop : acc'.drop (p + 1) = acc.drop (p + 1) := by
      rw [hacc', show (v.toNat % 256) :: acc.drop (p + 1)
          = [v.toNat % 256] ++ acc.drop (p + 1) from rfl, ← List.append_assoc]
      exact List.drop_left' (by simp [List.length_take]; omega)
    rw [byteRun_cons, splicedBytes_byte, ← hacc',
      ih (p + 1) acc' (by rw [hlen']; simp at h ⊢; omega), htake,
      drop_add acc' (p + 1) vs.length, hdrop, ← drop_add acc (p + 1) vs.length]
    simp [List.append_assoc, show p + 1 + vs.length = p + (vs.length + 1) from by omega]

theorem toLeBytes_lt (n w : Nat) : ∀ x ∈ toLeBytes n w, x < 256 := by
  induction w generalizing n with
  | zero => simp [toLeBytes]
  | succ w ih =>
    intro x hx
    rw [toLeBytes] at hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact Nat.mod_lt _ (by norm_num)
    · exact ih (n / 256) x h

/-! ## The 184-byte deposit record -/

/-- The 32-byte word the pinned drain reads out of a deposit record at offset `i`. -/
def depositWord (cd : List Byte) (i : Nat) : Nat := beBytes ((cd.drop i).take 32)

structure DepositRecordWords where
  calldata : List Byte
  amount : Nat
  w0 : UInt256
  w1 : UInt256
  w2 : UInt256
  w3 : UInt256
  w4 : UInt256
  w5 : UInt256
  amtBytes : List UInt256

/-- The scalar side conditions on one deposit record: six word equations and one
equation saying the eight `MSTORE8` operands are the little-endian amount. -/
def DepositRecordWords.ok (r : DepositRecordWords) : Prop :=
  r.calldata.length = depositInputSize ∧ (∀ x ∈ r.calldata, x < 256) ∧
    r.w0.toNat = depositWord r.calldata 0 ∧
    r.w1.toNat = depositWord r.calldata 32 ∧
    r.w2.toNat = depositWord r.calldata 64 ∧
    r.w3.toNat = depositWord r.calldata 96 ∧
    r.w4.toNat = depositWord r.calldata 128 ∧
    r.w5.toNat = beBytes (r.calldata.drop 160) * 2 ^ 64 ∧
    r.amtBytes.map (fun v => v.toNat % 256) = toLeBytes r.amount 8

def DepositRecordWords.record (r : DepositRecordWords) : Record :=
  .deposit r.calldata r.amount

/-- **The pinned `builder_deposits` store order for one record**, read off
`pinned/sys-asm/builder_deposits/main.eas`: three `MSTORE`s at `+0`, `+32`,
`+64`, then `%MSTORE64_le`'s eight `MSTORE8`s at `+80 … +87`, then three more
`MSTORE`s at `+96`, `+128`, `+160`. The last one overshoots the 184-byte record
by eight bytes, which the next record (or the `RETURN` window) covers.

Scope of that reading: the seven stores and their seven offsets *are* read off
`main.eas` (lines 355-430, whose own comments name `+0 … +160`, the `%MSTORE64_le`
target being the `offset+16` pushed at line 393 onto a base of `+64`). The
expansion of `%MSTORE64_le` into eight ascending `MSTORE8`s carrying the
little-endian amount is **not**: the macro lives in `../common/mstore.eas`, which
`main.eas:543` `#include`s but which this repository does not vendor. That
expansion is therefore an assumption of this definition together with
`DepositRecordWords.ok`'s `amtBytes` equation, not a fact checked against pinned
source. It is a hypothesis of every lemma below, never a conclusion. -/
def depositRecordStores (b : Nat) (r : DepositRecordWords) : List Splice :=
  [.word b r.w0, .word (b + 32) r.w1, .word (b + 64) r.w2]
    ++ byteRun (b + 80) r.amtBytes
    ++ [.word (b + 96) r.w3, .word (b + 128) r.w4, .word (b + 160) r.w5]

def depositStores (b : Nat) : List DepositRecordWords → List Splice
  | [] => []
  | r :: rs => depositRecordStores b r ++ depositStores (b + depositInputSize) rs

@[simp] theorem depositStores_nil (b : Nat) : depositStores b [] = [] := rfl

@[simp] theorem depositStores_cons (b : Nat) (r : DepositRecordWords)
    (rs : List DepositRecordWords) :
    depositStores b (r :: rs)
      = depositRecordStores b r ++ depositStores (b + depositInputSize) rs := rfl

theorem toBeBytes_depositWord (cd : List Byte) (hok : ∀ x ∈ cd, x < 256) (i : Nat)
    (w : UInt256) (hfit : i + 32 ≤ cd.length) (hw : w.toNat = depositWord cd i) :
    toBeBytes w.toNat 32 = (cd.drop i).take 32 := by
  have h32 : ((cd.drop i).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]; omega
  have h := toBeBytes_beBytes ((cd.drop i).take 32)
    fun x hx => hok x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  rw [h32] at h
  rw [hw, depositWord, h]

theorem length_encodeReturned_deposit (cd : List Byte) (amt : Nat)
    (hcd : cd.length = depositInputSize) :
    (encodeReturned (.deposit cd amt)).length = depositInputSize := by
  simp [encodeReturned, List.length_take, List.length_drop, hcd, depositInputSize]

/-- **What one record's stores leave behind.** Purely from the six word
equations and the eight little-endian byte operands, the window
`[b, b+184)` holds exactly the model's `encodeReturned` of that deposit, and the
eight-byte overshoot is zero. -/
theorem splicedBytes_depositRecord (b : Nat) (acc : List Byte) (hacc : b ≤ acc.length)
    (r : DepositRecordWords) (hr : r.ok) :
    splicedBytes (depositRecordStores b r) acc
      = acc.take b ++ encodeReturned r.record ++ List.replicate 8 0 := by
  obtain ⟨hlen, hbyte, h0, h1, h2, h3, h4, h5, hamt⟩ := hr
  have hcd : r.calldata.length = 184 := hlen
  have hA : (acc.take b).length = b := by rw [List.length_take]; omega
  have hamtlen : r.amtBytes.length = 8 := by
    have := congrArg List.length hamt
    simpa using this
  -- the six word images
  have e0 : toBeBytes r.w0.toNat 32 = (r.calldata.drop 0).take 32 :=
    toBeBytes_depositWord _ hbyte 0 _ (by omega) h0
  have e1 : toBeBytes r.w1.toNat 32 = (r.calldata.drop 32).take 32 :=
    toBeBytes_depositWord _ hbyte 32 _ (by omega) h1
  have e2 : toBeBytes r.w2.toNat 32 = (r.calldata.drop 64).take 32 :=
    toBeBytes_depositWord _ hbyte 64 _ (by omega) h2
  have e3 : toBeBytes r.w3.toNat 32 = (r.calldata.drop 96).take 32 :=
    toBeBytes_depositWord _ hbyte 96 _ (by omega) h3
  have e4 : toBeBytes r.w4.toNat 32 = (r.calldata.drop 128).take 32 :=
    toBeBytes_depositWord _ hbyte 128 _ (by omega) h4
  have e5 : toBeBytes r.w5.toNat 32 = r.calldata.drop 160 ++ List.replicate 8 0 := by
    have hd : (r.calldata.drop 160).length = 24 := by rw [List.length_drop]; omega
    have h := toBeBytes_beBytes (r.calldata.drop 160)
      fun x hx => hbyte x (List.mem_of_mem_drop hx)
    rw [hd] at h
    rw [h5, show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num,
      show (32 : Nat) = 8 + 24 from rfl, toBeBytes_mul_pow, h]
  -- the three leading word stores
  have s3 : splicedBytes [Splice.word b r.w0, .word (b + 32) r.w1, .word (b + 64) r.w2] acc
      = acc.take b ++ r.calldata.take 96 := by
    rw [splicedBytes_word, e0,
      splicedBytes_word_append _ _ _ _ (by simp [hA, List.length_take, List.length_drop]; omega),
      e1,
      splicedBytes_word_append _ _ _ _ (by
        simp [hA, List.length_take, List.length_drop]; omega),
      e2, splicedBytes_nil]
    rw [take_split r.calldata 32 64, take_split (r.calldata.drop 32) 32 32,
      ← drop_add r.calldata 32 32]
    simp [List.append_assoc]
  rw [depositRecordStores, splicedBytes_append, splicedBytes_append, s3]
  -- the eight byte splices
  set acc₃ := acc.take b ++ r.calldata.take 96 with hacc₃
  have hacc₃len : acc₃.length = b + 96 := by
    rw [hacc₃]; simp [hA, List.length_take]; omega
  have hsplit96 : r.calldata.take 96
      = r.calldata.take 80 ++ ((r.calldata.drop 80).take 8 ++ (r.calldata.drop 88).take 8) := by
    rw [take_split r.calldata 80 16, take_split (r.calldata.drop 80) 8 8,
      ← drop_add r.calldata 80 8]
  have htake80 : acc₃.take (b + 80) = acc.take b ++ r.calldata.take 80 := by
    rw [hacc₃, hsplit96, ← List.append_assoc]
    exact List.take_left' (by simp [hA, List.length_take]; omega)
  have hdrop88 : acc₃.drop (b + 80 + 8) = (r.calldata.drop 88).take 8 := by
    rw [hacc₃, hsplit96, ← List.append_assoc, ← List.append_assoc]
    exact List.drop_left' (by simp [hA, List.length_take, List.length_drop]; omega)
  rw [splicedBytes_byteRun r.amtBytes (b + 80) acc₃ (by rw [hacc₃len, hamtlen]; omega),
    hamtlen, htake80, hdrop88, hamt]
  -- the three trailing word stores
  set acc₄ := acc.take b ++ r.calldata.take 80 ++ toLeBytes r.amount 8
    ++ (r.calldata.drop 88).take 8 with hacc₄
  have hacc₄len : acc₄.length = b + 96 := by
    rw [hacc₄]
    simp [hA, List.length_take, List.length_drop]
    omega
  rw [splicedBytes_word_append _ _ _ _ hacc₄len, e3,
    splicedBytes_word_append _ _ _ _ (by
      simp [hacc₄len, List.length_take, List.length_drop]; omega),
    e4,
    splicedBytes_word_append _ _ _ _ (by
      simp [hacc₄len, List.length_take, List.length_drop]; omega),
    e5, splicedBytes_nil, hacc₄]
  -- recombine the tail of the calldata
  have r128 : (r.calldata.drop 128).take 32 ++ r.calldata.drop 160 = r.calldata.drop 128 :=
    slice_append_drop r.calldata 128 32
  have r96 : (r.calldata.drop 96).take 32 ++ r.calldata.drop 128 = r.calldata.drop 96 :=
    slice_append_drop r.calldata 96 32
  have r88 : (r.calldata.drop 88).take 8 ++ r.calldata.drop 96 = r.calldata.drop 88 :=
    slice_append_drop r.calldata 88 8
  -- the eight-byte overshoot rides along at the end of every regrouping
  have rtail : (r.calldata.drop 88).take 8
        ++ ((r.calldata.drop 96).take 32
          ++ ((r.calldata.drop 128).take 32 ++ (r.calldata.drop 160 ++ List.replicate 8 0)))
      = r.calldata.drop 88 ++ List.replicate 8 0 := by
    rw [← List.append_assoc ((r.calldata.drop 128).take 32) (r.calldata.drop 160)
        (List.replicate 8 0), r128,
      ← List.append_assoc ((r.calldata.drop 96).take 32) (r.calldata.drop 128)
        (List.replicate 8 0), r96,
      ← List.append_assoc ((r.calldata.drop 88).take 8) (r.calldata.drop 96)
        (List.replicate 8 0), r88]
  rw [DepositRecordWords.record, encodeReturned]
  simp only [List.append_assoc]
  rw [rtail]

/-! ## A run of deposit records -/

theorem splicedBytes_depositStores (r : DepositRecordWords) (rs : List DepositRecordWords)
    (hok : ∀ x ∈ r :: rs, x.ok) (b : Nat) (acc : List Byte) (hacc : b ≤ acc.length) :
    splicedBytes (depositStores b (r :: rs)) acc
      = acc.take b ++ concatReturned ((r :: rs).map DepositRecordWords.record)
        ++ List.replicate 8 0 := by
  induction rs generalizing r b acc with
  | nil =>
    rw [depositStores_cons, depositStores_nil, List.append_nil,
      splicedBytes_depositRecord b acc hacc r (hok r (by simp))]
    simp [concatReturned]
  | cons r' rs' ih =>
    have hr := hok r (by simp)
    obtain ⟨hlen, _, _, _, _, _, _, _, _⟩ := hr
    rw [depositStores_cons, splicedBytes_append,
      splicedBytes_depositRecord b acc hacc r (hok r (by simp))]
    set acc' := acc.take b ++ encodeReturned r.record ++ List.replicate 8 0 with hacc'def
    have henc : (encodeReturned r.record).length = depositInputSize :=
      length_encodeReturned_deposit _ _ hlen
    have hA : (acc.take b).length = b := by rw [List.length_take]; omega
    have hlen' : acc'.length = b + depositInputSize + 8 := by
      rw [hacc'def]; simp [hA, henc]; omega
    have htake : acc'.take (b + depositInputSize) = acc.take b ++ encodeReturned r.record := by
      rw [hacc'def, List.append_assoc, ← List.append_assoc]
      exact List.take_left' (by simp [hA, henc])
    rw [ih r' (fun x hx => hok x (List.mem_cons_of_mem r hx)) (b + depositInputSize) acc'
        (by omega), htake]
    simp [concatReturned, List.append_assoc]

theorem length_concatReturned_depositRecords (rs : List DepositRecordWords)
    (hok : ∀ x ∈ rs, x.ok) :
    (concatReturned (rs.map DepositRecordWords.record)).length = depositInputSize * rs.length := by
  induction rs with
  | nil => simp [concatReturned]
  | cons r rs ih =>
    obtain ⟨hlen, _, _, _, _, _, _, _, _⟩ := hok r (by simp)
    have hr : (encodeReturned r.record).length = depositInputSize :=
      length_encodeReturned_deposit _ _ hlen
    have htl := ih fun x hx => hok x (List.mem_cons_of_mem r hx)
    simp only [concatReturned, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at htl ⊢
    rw [hr, htl]
    ring

/-! ## The window the `RETURN` reads -/

/-- **What the pinned deposit drain leaves in the `RETURN` window.** The stores
land at `0, 32, 64, 80…87, 96, 128, 160, 184, …` — a 184-byte stride with an
eight-byte little-endian `MSTORE8` splice inside every record — and what the run
holds in `[0, 184·k)` is exactly the model's `concatReturned` of those `k`
records. -/
theorem bytes_readWithPadding_of_depositStores {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {μ₁ : UInt256}
    (hfresh : pre.memory.size = 0)
    (h : MixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat)
      = concatReturned ((r :: rs).map DepositRecordWords.record) := by
  have hpre : bytes pre.memory = [] := by
    rw [← List.length_eq_zero_iff, bytes_length, hfresh]
  have hmem : bytes mid.memory
      = concatReturned ((r :: rs).map DepositRecordWords.record) ++ List.replicate 8 0 := by
    rw [bytes_memory_MixedStores h, hpre, splicedBytes_depositStores r rs hok 0 [] (by simp)]
    simp
  have hcl : (concatReturned ((r :: rs).map DepositRecordWords.record)).length = μ₁.toNat := by
    rw [length_concatReturned_depositRecords _ hok, hlen]
  have hsize : μ₁.toNat ≤ mid.memory.size := by
    rw [← bytes_length, hmem, List.length_append, hcl]
    omega
  have hpos : 0 < μ₁.toNat := by
    rw [hlen]; simp [depositInputSize]
  rw [bytes_readWithPadding_prefix mid.memory μ₁.toNat hpos (by omega) hsize,
    hmem, List.take_left' hcl]

/-- **`EndpointAgrees` for the pinned deposit drain window.** No `hbytes`, no
`hwords`, no `ExitAgrees` or `EndpointAgrees` hypothesis, and no
`native_decide`: what replaces `hwords` is `hok`, six scalar word equations and
one little-endian byte equation per record. -/
theorem endpointAgrees_of_depositStores_return {f g : Nat} {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : MixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (concatReturned ((r :: rs).map DepositRecordWords.record))) := by
  refine ⟨returnPost g mid s' ⟨0⟩ len,
    hstores.runs.trans (.one (step_RETURN f g mid s' ⟨0⟩ len hstack)), ?_⟩
  have hb : bytes (returnPost g mid s' ⟨0⟩ len).H_return
      = concatReturned ((r :: rs).map DepositRecordWords.record) := by
    rw [H_return_step_RETURN g mid s' ⟨0⟩ len, show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    exact bytes_readWithPadding_of_depositStores hfresh hstores hok hlen h64
  simp [EndpointAgrees, observe, hb]

/-- The same deposit run stated as `ExitAgrees` itself. -/
theorem exitAgrees_of_depositStores_return {f g : Nat} {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hfresh : pre.memory.size = 0)
    (hstores : MixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
          (.success model (concatReturned ((r :: rs).map DepositRecordWords.record))) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_depositStores_return (f := f) (g := g) hfresh hstores hok hstack hlen h64
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-! ## The mixed loop is inhabited by real opcodes -/

/-- A single real `MSTORE8` inhabits the byte constructor. -/
theorem mixedStores_one_byte {f g off : Nat} {pre : EVM.State} {s : Stack UInt256}
    {d v : UInt256} (hd : d.toNat = off) (hlt : off < pre.memory.size)
    (hpop : pre.stack.pop2 = some (s, d, v)) :
    MixedStores [(f + 1, g, (.MSTORE8, none))] [.byte off v] pre
      (mstore8Post g pre s d v) :=
  .byte hd hlt hpop (step_MSTORE8 f g pre s d v hpop) (.nil _)

/-- **The mixed predicate is inhabited at the real deposit layout, by real
opcodes.** Three `MSTORE`s at `0`, `32`, `64` of a fresh frame followed by the
first `MSTORE8` of `%MSTORE64_le` at `80` satisfy `MixedStores` at exactly the
first four splices of `depositRecordStores 0 r`, so nothing above is vacuously
true. The hypotheses are the stack shapes the opcodes need and the four
offsets, and nothing else. -/
theorem mixedStores_depositPrefix {f₀ g₀ f₁ g₁ f₂ g₂ f₃ g₃ : Nat} {pre : EVM.State}
    {s₀ s₁ s₂ s₃ : Stack UInt256} {d₀ d₁ d₂ d₃ : UInt256} (r : DepositRecordWords)
    (v : UInt256) (vs : List UInt256) (hamt : r.amtBytes = v :: vs)
    (hfresh : pre.memory.size = 0)
    (h₀ : d₀.toNat = 0) (hp₀ : pre.stack.pop2 = some (s₀, d₀, r.w0))
    (h₁ : d₁.toNat = 32) (hp₁ : s₀.pop2 = some (s₁, d₁, r.w1))
    (h₂ : d₂.toNat = 64) (hp₂ : s₁.pop2 = some (s₂, d₂, r.w2))
    (h₃ : d₃.toNat = 80) (hp₃ : s₂.pop2 = some (s₃, d₃, v)) :
    MixedStores
      [(f₀ + 1, g₀, (.MSTORE, none)), (f₁ + 1, g₁, (.MSTORE, none)),
        (f₂ + 1, g₂, (.MSTORE, none)), (f₃ + 1, g₃, (.MSTORE8, none))]
      ((depositRecordStores 0 r).take 4) pre
      (mstore8Post g₃
        (mstorePost g₂ (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1) s₂ d₂ r.w2)
        s₃ d₃ v) := by
  have e₁ : (mstorePost g₀ pre s₀ d₀ r.w0).memory.size = 32 := by
    rw [size_mstorePost_overwrite g₀ pre s₀ d₀ r.w0 (by omega) (by omega), h₀]
  have e₂ : (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size = 64 := by
    rw [size_mstorePost_overwrite g₁ _ s₁ d₁ r.w1 (by rw [e₁]; omega) (by rw [e₁]; omega), h₁]
  have e₃ : (mstorePost g₂ (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1)
      s₂ d₂ r.w2).memory.size = 96 := by
    rw [size_mstorePost_overwrite g₂ _ s₂ d₂ r.w2 (by rw [e₂]; omega) (by rw [e₂]; omega), h₂]
  have hsplices : (depositRecordStores 0 r).take 4
      = [Splice.word 0 r.w0, .word 32 r.w1, .word 64 r.w2, .byte 80 v] := by
    rw [depositRecordStores, hamt]
    simp
  rw [hsplices]
  refine .word h₀ (by omega) (by omega) hp₀ (step_MSTORE f₀ g₀ pre s₀ d₀ r.w0 hp₀)
    (.word h₁ ?_ ?_ hp₁ (step_MSTORE f₁ g₁ _ s₁ d₁ r.w1 hp₁)
      (.word h₂ ?_ ?_ hp₂ (step_MSTORE f₂ g₂ _ s₂ d₂ r.w2 hp₂)
        (.byte h₃ ?_ hp₃ (step_MSTORE8 f₃ g₃ _ s₃ d₃ v hp₃) (.nil _))))
  · show 0 + 32 ≤ (mstorePost g₀ pre s₀ d₀ r.w0).memory.size
    rw [e₁]
  · show (mstorePost g₀ pre s₀ d₀ r.w0).memory.size ≤ 0 + 32 + 32
    rw [e₁]; omega
  · show 0 + 64 ≤ (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size
    rw [e₂]
  · show (mstorePost g₁ (mstorePost g₀ pre s₀ d₀ r.w0) s₁ d₁ r.w1).memory.size ≤ 0 + 64 + 32
    rw [e₂]; omega
  · show 0 + 80 < _
    rw [e₃]; omega

/-! ## The word conditions are satisfiable -/

/-- **`DepositRecordWords.ok` is satisfiable for every real deposit record.**
Any 184 genuine bytes and any amount below `2^64` are carried by words that fit
in `UInt256`, so `hok` constrains the runtime rather than excluding it. -/
theorem exists_depositRecordWords (cd : List Byte) (amt : Nat)
    (hcd : cd.length = depositInputSize) (hbyte : ∀ x ∈ cd, x < 256) :
    ∃ r : DepositRecordWords, r.ok ∧ r.record = .deposit cd amt := by
  have hcd184 : cd.length = 184 := hcd
  have hslice : ∀ i : Nat, i + 32 ≤ 184 → depositWord cd i < 2 ^ 256 := by
    intro i hi
    have hl : ((cd.drop i).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hcd184]; omega
    have := beBytes_lt ((cd.drop i).take 32)
      fun x hx => hbyte x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    rw [hl] at this
    calc depositWord cd i < 256 ^ 32 := this
      _ = 2 ^ 256 := by norm_num
  have htail : beBytes (cd.drop 160) < 2 ^ 192 := by
    have hl : (cd.drop 160).length = 24 := by rw [List.length_drop, hcd184]
    have := beBytes_lt (cd.drop 160) fun x hx => hbyte x (List.mem_of_mem_drop hx)
    rw [hl] at this
    calc beBytes (cd.drop 160) < 256 ^ 24 := this
      _ = 2 ^ 192 := by norm_num
  refine ⟨⟨cd, amt,
      UInt256.ofNat (depositWord cd 0), UInt256.ofNat (depositWord cd 32),
      UInt256.ofNat (depositWord cd 64), UInt256.ofNat (depositWord cd 96),
      UInt256.ofNat (depositWord cd 128),
      UInt256.ofNat (beBytes (cd.drop 160) * 2 ^ 64),
      (toLeBytes amt 8).map (fun x => UInt256.ofNat x)⟩,
    ⟨hcd, hbyte, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · exact toNat_ofNat_of_lt (hslice 0 (by omega))
  · exact toNat_ofNat_of_lt (hslice 32 (by omega))
  · exact toNat_ofNat_of_lt (hslice 64 (by omega))
  · exact toNat_ofNat_of_lt (hslice 96 (by omega))
  · exact toNat_ofNat_of_lt (hslice 128 (by omega))
  · exact toNat_ofNat_of_lt (by
      calc beBytes (cd.drop 160) * 2 ^ 64 < 2 ^ 192 * 2 ^ 64 :=
            (Nat.mul_lt_mul_right (by positivity)).mpr htail
        _ = 2 ^ 256 := by norm_num)
  · rw [List.map_map]
    refine Eq.trans (List.map_congr_left ?_) (List.map_id' _)
    intro x hx
    have hlt : x < 256 := toLeBytes_lt amt 8 x hx
    simp only [Function.comp_apply]
    rw [toNat_ofNat_of_lt (lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

/-! ## P-DRAIN-1, with `hwords` gone — the deposit layout -/

/-- **P-DRAIN-1's non-empty window at the real EIP-8282 deposit layout.**

`pdrain1_xi_returns_fifo_prefix_of_mstores` carries `hwords`; at the deposit
layout that hypothesis is unusable, since the window it describes is `32·n`
bytes while deposit records are 184 bytes each and the amount is spliced in
byte-wise. Here the byte layout is proved instead, from a `MixedStores` run of
the very `MSTORE`/`MSTORE8` opcodes the pinned `builder_deposits` runtime
emits. -/
theorem pdrain1_xi_returns_fifo_prefix_of_depositStores {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace tr : List Labelled} {exit mid post pre : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₁ : UInt256} {rs : List DepositRecordWords} {r : DepositRecordWords}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hfresh : pre.memory.size = 0)
    (hstores : MixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64)
    (hqueue : model.queue.take (capOf kind) = (r :: rs).map DepositRecordWords.record) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } :=
  pdrain1_xi_returns_fifo_prefix_of_memory (calldataNonempty := calldataNonempty) c hrep hrun
    hdec hZ hstep hop hstack
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        bytes_readWithPadding_of_depositStores hfresh hstores hok hlen h64, hqueue])

/-! ## The deposit window, written by a loop rather than by adjacent stores

`MixedStores` admits the `MSTORE8` splice `%MSTORE64_le` needs, but it still
asks for the stores to be immediately consecutive, and the pinned
`builder_deposits` runtime is no more adjacent than `builder_exits` is: it too
writes its window from a loop body, so between the stores sit the `SLOAD`s that
read the queue slots, the operand arithmetic, the stack shuffling and the jumps
that close the loop. On the exit side that was the gap `SpacedStores` closed;
the deposit side was left carrying the same requirement, which the pinned
bytecode provably does not satisfy.

`SpacedMixedStores` removes it for both constructors. Between two stores — word
or byte — it admits an arbitrary run, subject only to that segment leaving
`memory` alone, and `nil_neutral` / `word_neutral` / `byte_neutral` discharge
that condition from the *syntactic* `NeutralOp` check on the gap trace, so a
caller never asserts anything about the intermediate states.

`MixedStores.spaced` embeds the adjacency-shaped relation with empty gaps, so
nothing proved from `MixedStores` is lost. As on the exit side, what stays
assumed here is reachability alone — that the runtime performs these stores —
and no longer a shape the runtime does not have. `A-ABSTRACT-TX` is untouched
and stays OPEN. -/

inductive SpacedMixedStores : List Labelled → List Splice → EVM.State → EVM.State → Prop
  | nil {tr : List Labelled} {st post : EVM.State}
      (hgap : Runs tr st post) (hmem : post.memory = st.memory) :
      SpacedMixedStores tr [] st post
  | word {f g off : Nat} {d v : UInt256} {ss : List Splice}
      {tr₀ tr : List Labelled} {st gap mid post : EVM.State} {s : Stack UInt256}
      (hgap : Runs tr₀ st gap)
      (hmem : gap.memory = st.memory)
      (hd : d.toNat = off)
      (hle : off ≤ gap.memory.size)
      (hcov : gap.memory.size ≤ off + 32)
      (hpop : gap.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE, none) gap mid)
      (htail : SpacedMixedStores tr ss mid post) :
      SpacedMixedStores (tr₀ ++ (f + 1, g, (.MSTORE, none)) :: tr) (.word off v :: ss) st post
  | byte {f g off : Nat} {d v : UInt256} {ss : List Splice}
      {tr₀ tr : List Labelled} {st gap mid post : EVM.State} {s : Stack UInt256}
      (hgap : Runs tr₀ st gap)
      (hmem : gap.memory = st.memory)
      (hd : d.toNat = off)
      (hlt : off < gap.memory.size)
      (hpop : gap.stack.pop2 = some (s, d, v))
      (hstep : StepOk (f + 1) g (.MSTORE8, none) gap mid)
      (htail : SpacedMixedStores tr ss mid post) :
      SpacedMixedStores (tr₀ ++ (f + 1, g, (.MSTORE8, none)) :: tr) (.byte off v :: ss) st post

/-- **The empty case, from a syntactic gap.** The `SpacedStores.nil_neutral`
analogue: the trailing run's memory equation is derived from neutrality of the
opcodes it executes rather than assumed. -/
theorem SpacedMixedStores.nil_neutral {tr : List Labelled} {st post : EVM.State}
    (hgap : Runs tr st post) (hneutral : ∀ x ∈ tr, IsNeutralStep x) :
    SpacedMixedStores tr [] st post :=
  .nil hgap (memory_Runs_neutral hgap hneutral)

/-- **The word-store case, from a syntactic gap.** -/
theorem SpacedMixedStores.word_neutral {f g off : Nat} {d v : UInt256}
    {ss : List Splice} {tr₀ tr : List Labelled}
    {st gap mid post : EVM.State} {s : Stack UInt256}
    (hgap : Runs tr₀ st gap)
    (hneutral : ∀ x ∈ tr₀, IsNeutralStep x)
    (hd : d.toNat = off)
    (hle : off ≤ gap.memory.size)
    (hcov : gap.memory.size ≤ off + 32)
    (hpop : gap.stack.pop2 = some (s, d, v))
    (hstep : StepOk (f + 1) g (.MSTORE, none) gap mid)
    (htail : SpacedMixedStores tr ss mid post) :
    SpacedMixedStores (tr₀ ++ (f + 1, g, (.MSTORE, none)) :: tr) (.word off v :: ss) st post :=
  .word hgap (memory_Runs_neutral hgap hneutral) hd hle hcov hpop hstep htail

/-- **The byte-store case, from a syntactic gap.** This is the constructor the
`%MSTORE64_le` splice needs: its eight `MSTORE8`s are emitted by a macro
expansion whose operand arithmetic sits between them. -/
theorem SpacedMixedStores.byte_neutral {f g off : Nat} {d v : UInt256}
    {ss : List Splice} {tr₀ tr : List Labelled}
    {st gap mid post : EVM.State} {s : Stack UInt256}
    (hgap : Runs tr₀ st gap)
    (hneutral : ∀ x ∈ tr₀, IsNeutralStep x)
    (hd : d.toNat = off)
    (hlt : off < gap.memory.size)
    (hpop : gap.stack.pop2 = some (s, d, v))
    (hstep : StepOk (f + 1) g (.MSTORE8, none) gap mid)
    (htail : SpacedMixedStores tr ss mid post) :
    SpacedMixedStores (tr₀ ++ (f + 1, g, (.MSTORE8, none)) :: tr) (.byte off v :: ss) st post :=
  .byte hgap (memory_Runs_neutral hgap hneutral) hd hlt hpop hstep htail

theorem SpacedMixedStores.runs {tr : List Labelled} {ss : List Splice}
    {st post : EVM.State} (h : SpacedMixedStores tr ss st post) : Runs tr st post := by
  induction h with
  | nil hgap _ => exact hgap
  | word hgap _ _ _ _ _ hstep _ ih => exact hgap.trans (.cons hstep ih)
  | byte hgap _ _ _ _ hstep _ ih => exact hgap.trans (.cons hstep ih)

/-- **Adjacency was not load-bearing on the deposit side either.** Every
`MixedStores` run is a `SpacedMixedStores` run with empty gaps, so the
statements below subsume the adjacency-shaped ones rather than replacing them
with something incomparable. -/
theorem MixedStores.spaced {tr : List Labelled} {ss : List Splice}
    {st post : EVM.State} (h : MixedStores tr ss st post) :
    SpacedMixedStores tr ss st post := by
  induction h with
  | nil st => exact .nil (.nil st) rfl
  | @word f g off d v ss tr st mid post s hd hle hcov hpop hstep _ ih =>
    exact SpacedMixedStores.word (tr₀ := []) (.nil st) rfl hd hle hcov hpop hstep ih
  | @byte f g off d v ss tr st mid post s hd hlt hpop hstep _ ih =>
    exact SpacedMixedStores.byte (tr₀ := []) (.nil st) rfl hd hlt hpop hstep ih

/-- **What a spaced mixed loop leaves in memory.** Identical to
`bytes_memory_MixedStores`: the gaps do not touch memory, so only the splices
contribute. -/
theorem bytes_memory_SpacedMixedStores {tr : List Labelled} {ss : List Splice}
    {st post : EVM.State} (h : SpacedMixedStores tr ss st post) :
    bytes post.memory = splicedBytes ss (bytes st.memory) := by
  induction h with
  | nil _ hmem => rw [hmem]; rfl
  | @word f g off d v ss tr₀ tr st gap mid post s hgap hmem hd hle hcov hpop hstep _ ih =>
    rw [ih, memory_step_MSTORE_overwrite hpop hstep (hd ▸ hle) (hd ▸ hcov),
      bytes_append, bytes_extract_zero, hd, splicedBytes_word, bytes_toByteArray, hmem]
  | @byte f g off d v ss tr₀ tr st gap mid post s hgap hmem hd hlt hpop hstep _ ih =>
    rw [ih, bytes_memory_step_MSTORE8 hpop hstep (hd ▸ hlt), hd, splicedBytes_byte, hmem]

/-- **The pinned deposit drain's window, written by a spaced loop.** As
`bytes_readWithPadding_of_depositStores`, with adjacency replaced by
memory-neutrality of whatever runs between the stores, and with no assumption
that memory starts empty. -/
theorem bytes_readWithPadding_of_spacedDepositStores {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {μ₁ : UInt256}
    (h : SpacedMixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    bytes (mid.memory.readWithPadding 0 μ₁.toNat)
      = concatReturned ((r :: rs).map DepositRecordWords.record) := by
  have hmem : bytes mid.memory
      = concatReturned ((r :: rs).map DepositRecordWords.record) ++ List.replicate 8 0 := by
    rw [bytes_memory_SpacedMixedStores h,
      splicedBytes_depositStores r rs hok 0 (bytes pre.memory) (Nat.zero_le _)]
    simp
  have hcl : (concatReturned ((r :: rs).map DepositRecordWords.record)).length = μ₁.toNat := by
    rw [length_concatReturned_depositRecords _ hok, hlen]
  have hsize : μ₁.toNat ≤ mid.memory.size := by
    rw [← bytes_length, hmem, List.length_append, hcl]
    omega
  have hpos : 0 < μ₁.toNat := by
    rw [hlen]; simp [depositInputSize]
  rw [bytes_readWithPadding_prefix mid.memory μ₁.toNat hpos (by omega) hsize,
    hmem, List.take_left' hcl]

/-- **`EndpointAgrees`, as a conclusion, for a deposit window written by a
loop.** No `hbytes`, no `hwords`, no `ExitAgrees` or `EndpointAgrees`
hypothesis, no adjacency, no empty-memory assumption and no `native_decide`. -/
theorem endpointAgrees_of_spacedDepositStores_return {f g : Nat} {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hstores : SpacedMixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ EndpointAgrees (.success post post.H_return)
          (.success model (concatReturned ((r :: rs).map DepositRecordWords.record))) := by
  refine ⟨returnPost g mid s' ⟨0⟩ len,
    hstores.runs.trans (.one (step_RETURN f g mid s' ⟨0⟩ len hstack)), ?_⟩
  have hb : bytes (returnPost g mid s' ⟨0⟩ len).H_return
      = concatReturned ((r :: rs).map DepositRecordWords.record) := by
    rw [H_return_step_RETURN g mid s' ⟨0⟩ len, show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    exact bytes_readWithPadding_of_spacedDepositStores hstores hok hlen h64
  simp [EndpointAgrees, observe, hb]

/-- The same loop-shaped deposit run, stated as `ExitAgrees` itself — the
residual the three parents carry — with `ExitAgrees` in the conclusion. -/
theorem exitAgrees_of_spacedDepositStores_return {f g : Nat} {tr : List Labelled}
    {rs : List DepositRecordWords} {r : DepositRecordWords} {pre mid : EVM.State}
    {s' : Stack UInt256} {len : UInt256} {model : Model.State}
    (hstores : SpacedMixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hstack : mid.stack.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64) :
    ∃ post, Runs (tr ++ [(f + 1, g, (.RETURN, none))]) pre post
      ∧ ExitAgrees .RETURN (haltData post.toMachineState .RETURN)
          (.success model (concatReturned ((r :: rs).map DepositRecordWords.record))) := by
  obtain ⟨post, hruns, hend⟩ :=
    endpointAgrees_of_spacedDepositStores_return (f := f) (g := g)
      hstores hok hstack hlen h64
  refine ⟨post, hruns, ?_⟩
  rw [haltData_RETURN]
  exact endpointAgrees_iff_exitAgrees.mp (by simpa using hend)

/-- **P-DRAIN-1's non-empty window at the real EIP-8282 deposit layout, written
by a loop.** The same complete-`Ξ` observation as
`pdrain1_xi_returns_fifo_prefix_of_depositStores`, from `SpacedMixedStores`
rather than `MixedStores`: the drain's stores need no longer be adjacent, only
separated by work that leaves memory alone. That is the shape
`builder_deposits` has, and `MixedStores.spaced` makes this statement subsume
the adjacency-shaped one. -/
theorem pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace tr : List Labelled} {exit mid post pre : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {s : Stack UInt256}
    {μ₁ : UInt256} {rs : List DepositRecordWords} {r : DepositRecordWords}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hop : op = .RETURN)
    (hstack : mid.stack.pop2 = some (s, ⟨0⟩, μ₁))
    (hstores : SpacedMixedStores tr (depositStores 0 (r :: rs)) pre mid)
    (hok : ∀ x ∈ r :: rs, x.ok)
    (hlen : μ₁.toNat = depositInputSize * (r :: rs).length)
    (h64 : depositInputSize * (r :: rs).length < 2 ^ 64)
    (hqueue : model.queue.take (capOf kind) = (r :: rs).map DepositRecordWords.record) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } :=
  pdrain1_xi_returns_fifo_prefix_of_memory (calldataNonempty := calldataNonempty) c hrep hrun
    hdec hZ hstep hop hstack
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        bytes_readWithPadding_of_spacedDepositStores hstores hok hlen h64, hqueue])

/-! ## The three registered parents, transported

Each theorem is the **unchanged** registered parent (`type_of%` of the `main`
theorem, so its `submitFacts` / `drainFacts` / `controlFacts` conjuncts and
their one-byte kill-lines are carried verbatim) conjoined with its
complete-`Ξ` transport. No new parent ID is introduced.
-/

/-- **P-SUBMIT-1**, transported to complete `Ξ`. -/
theorem psubmit1_xi_forall_parent :
    (∀ (kind : Kind) (caller : Address) (calldata : List Byte) (value : Wei),
        XiTransport kind (.user caller calldata value)) ∧
      (∀ kind : Kind, XiExitTransport kind) ∧
      (∀ kind : Kind, XiSliceTransport kind) ∧
      (∀ kind : Kind, XiWidthTransport kind) ∧
      (∀ (kind : Kind) (mstep : Model.Step), XiMemoryTransport kind mstep) ∧
      (∀ (model : Model.State) (mstep : Model.Step) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        (op = .RETURN ∨ op = .REVERT) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        (ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
          ↔ ((op = .REVERT ↔ (Model.step model mstep).isRevert = true) ∧
              bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
                = (observeModel (Model.step model mstep)).returnData))) ∧
      (∀ (model : Model.State) (caller : Address) (calldata : List Byte)
          (value : Wei) (op : Operation .EVM) (out : ByteArray),
        inhibited model = true →
        (ExitAgrees op out (Model.step model (.user caller calldata value))
          ↔ (op = .REVERT ∧ bytes out = []))) ∧
      (∀ (model : Model.State) (caller : Address) (calldata : List Byte) (value : Wei)
          (rem gasCost : Nat) (arg : Option (UInt256 × Nat)) (mid post : EVM.State)
          (op : Operation .EVM) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = true →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat < USize.size →
        (ExitAgrees op (haltData post.toMachineState op)
            (Model.step model (.user caller calldata value))
          ↔ (op = .REVERT ∧ μ₁.toNat = 0))) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (caller : Address)
          (calldata : List Byte) (value : Wei) (rem gasCost : Nat)
          (trace : List Labelled) (exit mid post : EVM.State) (op : Operation .EVM)
          (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = true →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .REVERT →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result = some { reverted := true, returnData := [] }) ∧
      (∀ (model : Model.State) (caller : Address) (calldata : List Byte)
          (value : Wei) (op : Operation .EVM) (out : ByteArray),
        inhibited model = false →
        calldata ≠ [] →
        admissible model calldata value = true →
        (ExitAgrees op out (Model.step model (.user caller calldata value))
          ↔ (op ≠ .REVERT ∧ bytes out = []))) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (caller : Address)
          (calldata : List Byte) (value : Wei) (rem gasCost : Nat)
          (trace : List Labelled) (exit mid post : EVM.State) (op : Operation .EVM)
          (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = false →
        calldata ≠ [] →
        admissible model calldata value = true →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .RETURN →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result = some { reverted := false, returnData := [] }) ∧
      (∀ (model : Model.State) (caller : Address) (calldata : List Byte)
          (value : Wei) (op : Operation .EVM) (out : ByteArray),
        inhibited model = false →
        calldata ≠ [] →
        admissible model calldata value = false →
        (ExitAgrees op out (Model.step model (.user caller calldata value))
          ↔ (op = .REVERT ∧ bytes out = []))) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (caller : Address)
          (calldata : List Byte) (value : Wei) (rem gasCost : Nat)
          (trace : List Labelled) (exit mid post : EVM.State) (op : Operation .EVM)
          (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = false →
        calldata ≠ [] →
        admissible model calldata value = false →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .REVERT →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result = some { reverted := true, returnData := [] }) ∧
      (∀ (model : Model.State) (caller : Address) (calldata : List Byte) (value : Wei),
        (observeModel (Model.step model (.user caller calldata value))).returnData ≠ []
          ↔ (inhibited model = false ∧ calldata = [] ∧ value = 0)) ∧
      (∀ (model : Model.State) (mstep : Model.Step),
        (observeModel (Model.step model mstep)).returnData ≠ []
          ↔ DataBranch model mstep) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (mstep : Model.Step)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        ¬ DataBranch model mstep →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        (op = .RETURN ∨ op = .REVERT) →
        (op = .REVERT ↔ (Model.step model mstep).isRevert = true) →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result =
          some { reverted := (Model.step model mstep).isRevert, returnData := [] }) ∧
      (type_of% psubmit1_pinned_exit_accepted) ∧
      (type_of% psubmit1_pinned_exit_rejected) ∧
      (type_of% psubmit1_pinned_exit_inhibited) ∧
      (type_of% psubmit1_xi_accepts_pinned_exit_submission) ∧
      (type_of% psubmit1_xi_rejects_pinned_exit_underpayment) ∧
      (type_of% psubmit1_xi_inhibits_pinned_exit_submission) ∧
      (type_of% psubmit1_xi_accepts_pinned_deposit_submission) ∧
      (type_of% psubmit1_xi_rejects_pinned_deposit_underpayment) ∧
      (type_of% psubmit1_xi_pinned_exit_submission_discriminates) ∧
      (type_of% @represents_pinnedExitSubmit) ∧
      (type_of% @represents_pinnedDepositSubmit) ∧
      (type_of% @exitAgrees_iff_zero_length_of_not_dataBranch) ∧
      (type_of% @exitAgrees_zero_length_operand_of_not_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_of_not_dataBranch) ∧
      (type_of% @xi_observes_model_of_silent_of_not_dataBranch) ∧
      (type_of% @isRevert_false_of_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_iff_not_dataBranch) ∧
      (type_of% @exit_op_eq_RETURN_of_dataBranch) ∧
      (type_of% @exitAgrees_iff_memory_bytes_of_dataBranch) ∧
      (type_of% @bytes_toByteArray) ∧
      (type_of% @bytes_readWithPadding_of_step_MSTORE) ∧
      (type_of% @memory_step_Push) ∧
      (type_of% @memory_Runs_Push) ∧
      (type_of% @bytes_readWithPadding_of_mstore_pushes_zero) ∧
      (type_of% @endpointAgrees_of_mstore_pushes_return_zero) ∧
      (type_of% @endpointAgrees_of_mstore_return_zero) ∧
      (type_of% @memory_mstore_append) ∧
      (type_of% @memory_step_MSTORE_append) ∧
      (type_of% @AppendStores.runs) ∧
      (type_of% @memory_AppendStores) ∧
      (type_of% @appendStores_two) ∧
      (type_of% @bytes_readWithPadding_of_appendStores) ∧
      (type_of% @endpointAgrees_of_mstores_return) ∧
      (type_of% @exitAgrees_of_mstores_return) ∧
      (type_of% Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent) :=
  ⟨fun kind caller calldata value => xiTransport kind (.user caller calldata value),
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
    xiMemoryTransport,
    fun _ _ _ _ _ _ _ _ _ _ _ hop hstep hstack =>
      exitAgrees_iff_memory_bytes hop hstep hstack,
    fun _ _ _ _ _ _ hinh => psubmit1_exitAgrees_iff hinh,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ hinh hstep hstack hlt =>
      psubmit1_exitAgrees_iff_operand hinh hstep hstack hlt,
    fun _ c _ caller calldata value _ _ _ _ _ _ _ _ _ _ _
        hinh hrep hrun hdec hZ hstep hexit hstack hlen =>
      psubmit1_xi_inhibited_reverts_of_zero_length c (caller := caller)
        (calldata := calldata) (value := value) hinh hrep hrun hdec hZ hstep
        hexit hstack hlen,
    fun _ _ _ _ _ _ hinh hne hadm => psubmit1_exitAgrees_iff_accepted hinh hne hadm,
    fun _ c _ caller calldata value _ _ _ _ _ _ _ _ _ _ _
        hinh hne hadm hrep hrun hdec hZ hstep hop hstack hlen =>
      psubmit1_xi_accepted_returns_nothing c (caller := caller)
        (calldata := calldata) (value := value) hinh hne hadm hrep hrun hdec hZ
        hstep hop hstack hlen,
    fun _ _ _ _ _ _ hinh hne hadm => psubmit1_exitAgrees_iff_rejected hinh hne hadm,
    fun _ c _ caller calldata value _ _ _ _ _ _ _ _ _ _ _
        hinh hne hadm hrep hrun hdec hZ hstep hop hstack hlen =>
      psubmit1_xi_rejected_reverts_of_zero_length c (caller := caller)
        (calldata := calldata) (value := value) hinh hne hadm hrep hrun hdec hZ
        hstep hop hstack hlen,
    fun _ _ _ _ => userCall_returnData_ne_nil_iff,
    fun _ _ => step_returnData_ne_nil_iff,
    fun _ c _ mstep _ _ _ _ _ _ _ _ _ _ _
        hnd hrep hrun hdec hZ hstep hop hrev hstack hlen =>
      xi_observes_model_of_not_dataBranch c (mstep := mstep) hnd hrep hrun hdec hZ
        hstep hop hrev hstack hlen,
    psubmit1_pinned_exit_accepted,
    psubmit1_pinned_exit_rejected,
    psubmit1_pinned_exit_inhibited,
    psubmit1_xi_accepts_pinned_exit_submission,
    psubmit1_xi_rejects_pinned_exit_underpayment,
    psubmit1_xi_inhibits_pinned_exit_submission,
    psubmit1_xi_accepts_pinned_deposit_submission,
    psubmit1_xi_rejects_pinned_deposit_underpayment,
    psubmit1_xi_pinned_exit_submission_discriminates,
    represents_pinnedExitSubmit,
    represents_pinnedDepositSubmit,
    @exitAgrees_iff_zero_length_of_not_dataBranch,
    @exitAgrees_zero_length_operand_of_not_dataBranch,
    @exitAgrees_of_silent_of_not_dataBranch,
    @xi_observes_model_of_silent_of_not_dataBranch,
    @isRevert_false_of_dataBranch,
    @exitAgrees_of_silent_iff_not_dataBranch,
    @exit_op_eq_RETURN_of_dataBranch,
    @exitAgrees_iff_memory_bytes_of_dataBranch,
    @bytes_toByteArray,
    @bytes_readWithPadding_of_step_MSTORE,
    @memory_step_Push,
    @memory_Runs_Push,
    @bytes_readWithPadding_of_mstore_pushes_zero,
    @endpointAgrees_of_mstore_pushes_return_zero,
    @endpointAgrees_of_mstore_return_zero,
    @memory_mstore_append,
    @memory_step_MSTORE_append,
    @AppendStores.runs,
    @memory_AppendStores,
    @appendStores_two,
    @bytes_readWithPadding_of_appendStores,
    @endpointAgrees_of_mstores_return,
    @exitAgrees_of_mstores_return,
    Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent⟩

/-- **P-DRAIN-1**, transported to complete `Ξ`. -/
theorem pdrain1_xi_forall_parent :
    (∀ (kind : Kind) (calldataNonempty : Bool),
        XiTransport kind (.system calldataNonempty)) ∧
      (∀ kind : Kind, XiExitTransport kind) ∧
      (∀ kind : Kind, XiSliceTransport kind) ∧
      (∀ kind : Kind, XiWidthTransport kind) ∧
      (∀ (kind : Kind) (mstep : Model.Step), XiMemoryTransport kind mstep) ∧
      (∀ (model : Model.State) (mstep : Model.Step) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        (op = .RETURN ∨ op = .REVERT) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        (ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
          ↔ ((op = .REVERT ↔ (Model.step model mstep).isRevert = true) ∧
              bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
                = (observeModel (Model.step model mstep)).returnData))) ∧
      (∀ (kind : Kind) (model : Model.State) (calldataNonempty : Bool) (post : EVM.State)
          (op : Operation .EVM) (out : ByteArray),
        model.kind = kind →
        H post.toMachineState op = some out →
        ExitAgrees op out (Model.step model (.system calldataNonempty)) →
        concatReturned (model.queue.take (capOf kind)) ≠ [] →
        op = .RETURN) ∧
      (∀ (kind : Kind) (model : Model.State) (calldataNonempty : Bool)
          (op : Operation .EVM) (out : ByteArray),
        model.kind = kind →
        (ExitAgrees op out (Model.step model (.system calldataNonempty))
          ↔ (op ≠ .REVERT ∧
              bytes out = concatReturned (model.queue.take (capOf kind))))) ∧
      (∀ (model : Model.State) (calldataNonempty : Bool)
          (op : Operation .EVM) (out : ByteArray),
        ExitAgrees op out (Model.step model (.system calldataNonempty)) →
        op ≠ .REVERT) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (calldataNonempty : Bool)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .RETURN →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        concatReturned (model.queue.take (capOf kind)) = [] →
        observe c.result = some { reverted := false, returnData := [] }) ∧
      (∀ (kind : Kind) (model : Model.State) (calldataNonempty : Bool) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        model.kind = kind →
        H post.toMachineState op = some (haltData post.toMachineState op) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        ExitAgrees op (haltData post.toMachineState op)
          (Model.step model (.system calldataNonempty)) →
        (concatReturned (model.queue.take (capOf kind))).length ≤ μ₁.toNat ∧
          (concatReturned (model.queue.take (capOf kind)) ≠ [] →
            μ₁.toNat < USize.size →
            μ₁.toNat = (concatReturned (model.queue.take (capOf kind))).length)) ∧
      (∀ (model : Model.State) (calldataNonempty : Bool) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        (op = .RETURN ∨ op = .REVERT) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        (ExitAgrees op (haltData post.toMachineState op)
            (Model.step model (.system calldataNonempty))
          ↔ ExitAgrees op (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
            (Model.step model (.system calldataNonempty)))) ∧
      (∀ (kind : Kind) (model : Model.State) (calldataNonempty : Bool)
          (op : Operation .EVM) (out : ByteArray) (r : Record) (rs : List Record),
        model.kind = kind →
        ExitAgrees op out (Model.step model (.system calldataNonempty)) →
        model.queue.take (capOf kind) = r :: rs →
        ((bytes out).take (encodeReturned r).length = encodeReturned r ∧
          (bytes out).drop (encodeReturned r).length = concatReturned rs)) ∧
      (∀ (kind : Kind) (model : Model.State) (calldataNonempty : Bool),
        model.kind = kind →
        ((observeModel (Model.step model (.system calldataNonempty))).returnData ≠ []
          ↔ concatReturned (model.queue.take (capOf kind)) ≠ [])) ∧
      (∀ (model : Model.State) (mstep : Model.Step),
        (observeModel (Model.step model mstep)).returnData ≠ []
          ↔ DataBranch model mstep) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (mstep : Model.Step)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        ¬ DataBranch model mstep →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        (op = .RETURN ∨ op = .REVERT) →
        (op = .REVERT ↔ (Model.step model mstep).isRevert = true) →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result =
          some { reverted := (Model.step model mstep).isRevert, returnData := [] }) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (calldataNonempty : Bool)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .RETURN →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
          = concatReturned (model.queue.take (capOf kind)) →
        observe c.result =
          some { reverted := false
                 returnData := concatReturned (model.queue.take (capOf kind)) }) ∧
      (type_of% pdrain1_xi_drains_pinned_exit_under_cap) ∧
      (type_of% pdrain1_xi_drains_pinned_exit_over_cap) ∧
      (type_of% pdrain1_xi_drains_pinned_deposit) ∧
      (type_of% pdrain1_xi_pinned_exit_discriminates) ∧
      (type_of% @represents_pinnedExitSystem) ∧
      (type_of% @represents_pinnedDepositSystem) ∧
      (type_of% @exitAgrees_iff_zero_length_of_not_dataBranch) ∧
      (type_of% @exitAgrees_zero_length_operand_of_not_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_of_not_dataBranch) ∧
      (type_of% @xi_observes_model_of_silent_of_not_dataBranch) ∧
      (type_of% @isRevert_false_of_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_iff_not_dataBranch) ∧
      (type_of% @exit_op_eq_RETURN_of_dataBranch) ∧
      (type_of% @exitAgrees_iff_memory_bytes_of_dataBranch) ∧
      (type_of% @bytes_toByteArray) ∧
      (type_of% @bytes_readWithPadding_of_step_MSTORE) ∧
      (type_of% @memory_step_Push) ∧
      (type_of% @memory_Runs_Push) ∧
      (type_of% @bytes_readWithPadding_of_mstore_pushes_zero) ∧
      (type_of% @endpointAgrees_of_mstore_pushes_return_zero) ∧
      (type_of% @endpointAgrees_of_mstore_return_zero) ∧
      (type_of% @memory_mstore_append) ∧
      (type_of% @memory_step_MSTORE_append) ∧
      (type_of% @AppendStores.runs) ∧
      (type_of% @memory_AppendStores) ∧
      (type_of% @appendStores_two) ∧
      (type_of% @bytes_readWithPadding_of_appendStores) ∧
      (type_of% @endpointAgrees_of_mstores_return) ∧
      (type_of% @exitAgrees_of_mstores_return) ∧
      (type_of% @pdrain1_xi_returns_fifo_prefix_of_mstores) ∧
      (type_of% @bytes_memory_OverlapStores) ∧
      (type_of% @overlapStores_exitRecord) ∧
      (type_of% @exists_exitRecordWords) ∧
      (type_of% @storedBytes_exitStores) ∧
      (type_of% @bytes_readWithPadding_of_exitStores) ∧
      (type_of% @endpointAgrees_of_exitStores_return) ∧
      (type_of% @exitAgrees_of_exitStores_return) ∧
      (type_of% @pdrain1_xi_returns_fifo_prefix_of_exitStores) ∧
      (type_of% @bytes_memory_mstore8) ∧
      (type_of% @bytes_memory_step_MSTORE8) ∧
      (type_of% @MixedStores.runs) ∧
      (type_of% @bytes_memory_MixedStores) ∧
      (type_of% @splicedBytes_byteRun) ∧
      (type_of% @splicedBytes_depositRecord) ∧
      (type_of% @splicedBytes_depositStores) ∧
      (type_of% @bytes_readWithPadding_of_depositStores) ∧
      (type_of% @endpointAgrees_of_depositStores_return) ∧
      (type_of% @exitAgrees_of_depositStores_return) ∧
      (type_of% @mixedStores_one_byte) ∧
      (type_of% @mixedStores_depositPrefix) ∧
      (type_of% @exists_depositRecordWords) ∧
      (type_of% @pdrain1_xi_returns_fifo_prefix_of_depositStores) ∧
      (type_of% @memory_execBinOp) ∧
      (type_of% @memory_dup) ∧
      (type_of% @memory_swap) ∧
      (type_of% @memory_unaryStateOp) ∧
      (type_of% @memory_step_neutral) ∧
      (type_of% @isPushStep_isNeutralStep) ∧
      (type_of% @memory_Runs_neutral) ∧
      (type_of% @SpacedStores.nil_neutral) ∧
      (type_of% @SpacedStores.cons_neutral) ∧
      (type_of% @SpacedStores.runs) ∧
      (type_of% @OverlapStores.spaced) ∧
      (type_of% @bytes_memory_SpacedStores) ∧
      (type_of% @bytes_readWithPadding_of_spacedExitStores) ∧
      (type_of% @endpointAgrees_of_spacedExitStores_return) ∧
      (type_of% @exitAgrees_of_spacedExitStores_return) ∧
      (type_of% @pdrain1_xi_returns_fifo_prefix_of_spacedExitStores) ∧
      (type_of% @SpacedMixedStores.nil_neutral) ∧
      (type_of% @SpacedMixedStores.word_neutral) ∧
      (type_of% @SpacedMixedStores.byte_neutral) ∧
      (type_of% @SpacedMixedStores.runs) ∧
      (type_of% @MixedStores.spaced) ∧
      (type_of% @bytes_memory_SpacedMixedStores) ∧
      (type_of% @bytes_readWithPadding_of_spacedDepositStores) ∧
      (type_of% @endpointAgrees_of_spacedDepositStores_return) ∧
      (type_of% @exitAgrees_of_spacedDepositStores_return) ∧
      (type_of% @pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores) ∧
      (type_of% Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent) :=
  ⟨fun kind b => xiTransport kind (.system b),
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
    xiMemoryTransport,
    fun _ _ _ _ _ _ _ _ _ _ _ hop hstep hstack =>
      exitAgrees_iff_memory_bytes hop hstep hstack,
    fun _ _ _ _ _ _ hk hH hend hne => pdrain1_xi_exit_is_RETURN hk hH hend hne,
    fun _ _ _ _ _ hk => pdrain1_exitAgrees_iff hk,
    fun _ _ _ _ hend => pdrain1_xi_exit_not_REVERT hend,
    fun _ c _ cdne _ _ _ _ _ _ _ _ _ _ _ hrep hrun hdec hZ hstep hop hstack hlen hempty =>
      pdrain1_xi_empty_window_returns_nothing c (calldataNonempty := cdne)
        hrep hrun hdec hZ hstep hop hstack hlen hempty,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hk hH hstep hstack hend =>
      ⟨pdrain1_xi_exit_length_ge hk hH hstep hstack hend,
        fun hne hlt => pdrain1_xi_exit_length_eq hk hH hstep hstack hend hne hlt⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ hop hstep hstack =>
      exitAgrees_iff_memory_slice hop hstep hstack,
    fun _ _ _ _ _ _ _ hk hend hq => pdrain1_exitAgrees_head_record hk hend hq,
    fun _ _ _ hk => systemCall_returnData_ne_nil_iff hk,
    fun _ _ => step_returnData_ne_nil_iff,
    fun _ c _ mstep _ _ _ _ _ _ _ _ _ _ _
        hnd hrep hrun hdec hZ hstep hop hrev hstack hlen =>
      xi_observes_model_of_not_dataBranch c (mstep := mstep) hnd hrep hrun hdec hZ
        hstep hop hrev hstack hlen,
    fun _ c _ cdne _ _ _ _ _ _ _ _ _ _ _
        hrep hrun hdec hZ hstep hop hstack hbytes =>
      pdrain1_xi_returns_fifo_prefix_of_memory c (calldataNonempty := cdne)
        hrep hrun hdec hZ hstep hop hstack hbytes,
    pdrain1_xi_drains_pinned_exit_under_cap,
    pdrain1_xi_drains_pinned_exit_over_cap,
    pdrain1_xi_drains_pinned_deposit,
    pdrain1_xi_pinned_exit_discriminates,
    represents_pinnedExitSystem,
    represents_pinnedDepositSystem,
    @exitAgrees_iff_zero_length_of_not_dataBranch,
    @exitAgrees_zero_length_operand_of_not_dataBranch,
    @exitAgrees_of_silent_of_not_dataBranch,
    @xi_observes_model_of_silent_of_not_dataBranch,
    @isRevert_false_of_dataBranch,
    @exitAgrees_of_silent_iff_not_dataBranch,
    @exit_op_eq_RETURN_of_dataBranch,
    @exitAgrees_iff_memory_bytes_of_dataBranch,
    @bytes_toByteArray,
    @bytes_readWithPadding_of_step_MSTORE,
    @memory_step_Push,
    @memory_Runs_Push,
    @bytes_readWithPadding_of_mstore_pushes_zero,
    @endpointAgrees_of_mstore_pushes_return_zero,
    @endpointAgrees_of_mstore_return_zero,
    @memory_mstore_append,
    @memory_step_MSTORE_append,
    @AppendStores.runs,
    @memory_AppendStores,
    @appendStores_two,
    @bytes_readWithPadding_of_appendStores,
    @endpointAgrees_of_mstores_return,
    @exitAgrees_of_mstores_return,
    @pdrain1_xi_returns_fifo_prefix_of_mstores,
    @bytes_memory_OverlapStores,
    @overlapStores_exitRecord,
    @exists_exitRecordWords,
    @storedBytes_exitStores,
    @bytes_readWithPadding_of_exitStores,
    @endpointAgrees_of_exitStores_return,
    @exitAgrees_of_exitStores_return,
    @pdrain1_xi_returns_fifo_prefix_of_exitStores,
    @bytes_memory_mstore8,
    @bytes_memory_step_MSTORE8,
    @MixedStores.runs,
    @bytes_memory_MixedStores,
    @splicedBytes_byteRun,
    @splicedBytes_depositRecord,
    @splicedBytes_depositStores,
    @bytes_readWithPadding_of_depositStores,
    @endpointAgrees_of_depositStores_return,
    @exitAgrees_of_depositStores_return,
    @mixedStores_one_byte,
    @mixedStores_depositPrefix,
    @exists_depositRecordWords,
    @pdrain1_xi_returns_fifo_prefix_of_depositStores,
    @memory_execBinOp,
    @memory_dup,
    @memory_swap,
    @memory_unaryStateOp,
    @memory_step_neutral,
    @isPushStep_isNeutralStep,
    @memory_Runs_neutral,
    @SpacedStores.nil_neutral,
    @SpacedStores.cons_neutral,
    @SpacedStores.runs,
    @OverlapStores.spaced,
    @bytes_memory_SpacedStores,
    @bytes_readWithPadding_of_spacedExitStores,
    @endpointAgrees_of_spacedExitStores_return,
    @exitAgrees_of_spacedExitStores_return,
    @pdrain1_xi_returns_fifo_prefix_of_spacedExitStores,
    @SpacedMixedStores.nil_neutral,
    @SpacedMixedStores.word_neutral,
    @SpacedMixedStores.byte_neutral,
    @SpacedMixedStores.runs,
    @MixedStores.spaced,
    @bytes_memory_SpacedMixedStores,
    @bytes_readWithPadding_of_spacedDepositStores,
    @endpointAgrees_of_spacedDepositStores_return,
    @exitAgrees_of_spacedDepositStores_return,
    @pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores,
    Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent⟩

/-- **P-CONTROL-1**, transported to complete `Ξ`. The control plane spans both
call classes — the fee quote is a user call, the excess/count update a system
call — so both instances are carried. -/
theorem pcontrol1_xi_forall_parent :
    (∀ (kind : Kind) (mstep : Model.Step), XiTransport kind mstep) ∧
      (∀ kind : Kind, XiExitTransport kind) ∧
      (∀ kind : Kind, XiSliceTransport kind) ∧
      (∀ kind : Kind, XiWidthTransport kind) ∧
      (∀ (kind : Kind) (mstep : Model.Step), XiMemoryTransport kind mstep) ∧
      (∀ (model : Model.State) (mstep : Model.Step) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        (op = .RETURN ∨ op = .REVERT) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        (ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)
          ↔ ((op = .REVERT ↔ (Model.step model mstep).isRevert = true) ∧
              bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
                = (observeModel (Model.step model mstep)).returnData))) ∧
      (∀ (model : Model.State) (caller : Address) (post : EVM.State)
          (op : Operation .EVM) (out : ByteArray),
        inhibited model = false →
        H post.toMachineState op = some out →
        ExitAgrees op out (Model.step model (.user caller [] 0)) →
        op = .RETURN) ∧
      (∀ (model : Model.State) (caller : Address) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = false →
        H post.toMachineState op = some (haltData post.toMachineState op) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        ExitAgrees op (haltData post.toMachineState op)
          (Model.step model (.user caller [] 0)) →
        32 ≤ μ₁.toNat ∧ (μ₁.toNat < USize.size → μ₁.toNat = 32)) ∧
      (∀ (model : Model.State) (caller : Address) (rem gasCost : Nat)
          (arg : Option (UInt256 × Nat)) (mid post : EVM.State) (op : Operation .EVM)
          (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = false →
        H post.toMachineState op = some (haltData post.toMachineState op) →
        StepOk rem gasCost (op, arg) mid post →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        ExitAgrees op (haltData post.toMachineState op)
          (Model.step model (.user caller [] 0)) →
        μ₁.toNat ≠ 0) ∧
      (∀ (model : Model.State) (caller : Address) (op : Operation .EVM)
          (out : ByteArray),
        inhibited model = false →
        (ExitAgrees op out (Model.step model (.user caller [] 0))
          ↔ (op ≠ .REVERT ∧ bytes out = toBeBytes (currentFee model) 32))) ∧
      (∀ (model : Model.State) (caller : Address) (value : Wei)
          (op : Operation .EVM) (out : ByteArray),
        inhibited model = false →
        value ≠ 0 →
        (ExitAgrees op out (Model.step model (.user caller [] value))
          ↔ (op = .REVERT ∧ bytes out = []))) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (caller : Address)
          (value : Wei) (rem gasCost : Nat) (trace : List Labelled)
          (exit mid post : EVM.State) (op : Operation .EVM)
          (arg : Option (UInt256 × Nat)) (s : Stack UInt256) (μ₀ μ₁ : UInt256),
        inhibited model = false →
        value ≠ 0 →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .REVERT →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result = some { reverted := true, returnData := [] }) ∧
      (∀ (model : Model.State) (caller : Address) (op : Operation .EVM)
          (out : ByteArray),
        inhibited model = false →
        (bytes out).length = 32 →
        (ExitAgrees op out (Model.step model (.user caller [] 0))
          ↔ (op ≠ .REVERT ∧
              ∀ i, i < 32 →
                (bytes out)[i]? = some ((currentFee model / 256 ^ (32 - 1 - i)) % 256)))) ∧
      (∀ (model : Model.State) (mstep : Model.Step),
        (observeModel (Model.step model mstep)).returnData ≠ []
          ↔ DataBranch model mstep) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (mstep : Model.Step)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        ¬ DataBranch model mstep →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        (op = .RETURN ∨ op = .REVERT) →
        (op = .REVERT ↔ (Model.step model mstep).isRevert = true) →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        μ₁.toNat = 0 →
        observe c.result =
          some { reverted := (Model.step model mstep).isRevert, returnData := [] }) ∧
      (∀ (kind : Kind) (c : XiCall kind) (model : Model.State) (caller : Address)
          (rem gasCost : Nat) (trace : List Labelled) (exit mid post : EVM.State)
          (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : Stack UInt256)
          (μ₀ μ₁ : UInt256),
        inhibited model = false →
        Represents kind c.entry model →
        RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
          trace (rem + 1) exit →
        decodeAt exit = (op, arg) →
        Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
        StepOk rem gasCost (op, arg) mid post →
        op = .RETURN →
        mid.stack.pop2 = some (s, μ₀, μ₁) →
        bytes (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)
          = toBeBytes (currentFee model) 32 →
        observe c.result =
          some { reverted := false, returnData := toBeBytes (currentFee model) 32 }) ∧
      (type_of% pcontrol1_xi_quotes_pinned_fee) ∧
      (type_of% @represents_pinnedExitFeeGetter) ∧
      (type_of% @exitAgrees_iff_zero_length_of_not_dataBranch) ∧
      (type_of% @exitAgrees_zero_length_operand_of_not_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_of_not_dataBranch) ∧
      (type_of% @xi_observes_model_of_silent_of_not_dataBranch) ∧
      (type_of% @isRevert_false_of_dataBranch) ∧
      (type_of% @exitAgrees_of_silent_iff_not_dataBranch) ∧
      (type_of% @exit_op_eq_RETURN_of_dataBranch) ∧
      (type_of% @exitAgrees_iff_memory_bytes_of_dataBranch) ∧
      (type_of% @bytes_toByteArray) ∧
      (type_of% @bytes_readWithPadding_of_step_MSTORE) ∧
      (type_of% @memory_step_Push) ∧
      (type_of% @memory_Runs_Push) ∧
      (type_of% @bytes_readWithPadding_of_mstore_pushes_zero) ∧
      (type_of% @endpointAgrees_of_mstore_pushes_return_zero) ∧
      (type_of% @endpointAgrees_of_mstore_return_zero) ∧
      (type_of% @memory_mstore_append) ∧
      (type_of% @memory_step_MSTORE_append) ∧
      (type_of% @AppendStores.runs) ∧
      (type_of% @memory_AppendStores) ∧
      (type_of% @appendStores_two) ∧
      (type_of% @bytes_readWithPadding_of_appendStores) ∧
      (type_of% @endpointAgrees_of_mstores_return) ∧
      (type_of% @exitAgrees_of_mstores_return) ∧
      (type_of% @pcontrol1_xi_fee_getter_of_mstore) ∧
      (type_of% @pcontrol1_xi_fee_getter_of_mstore_zero) ∧
      (type_of% @pcontrol1_xi_fee_getter_of_mstore_pushes) ∧
      (type_of% Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent) :=
  ⟨fun kind mstep => xiTransport kind mstep,
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
    xiMemoryTransport,
    fun _ _ _ _ _ _ _ _ _ _ _ hop hstep hstack =>
      exitAgrees_iff_memory_bytes hop hstep hstack,
    fun _ _ _ _ _ hinh hH hend => pcontrol1_xi_exit_is_RETURN hinh hH hend,
    fun _ _ _ _ _ _ _ _ _ _ _ hinh hH hstep hstack hend =>
      ⟨pcontrol1_xi_exit_length_ge_32 hinh hH hstep hstack hend,
        fun hlt => pcontrol1_xi_exit_length_eq_32 hinh hH hstep hstack hend hlt⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ hinh hH hstep hstack hend =>
      pcontrol1_xi_exit_length_ne_zero hinh hH hstep hstack hend,
    fun _ _ _ _ hinh => pcontrol1_exitAgrees_iff hinh,
    fun _ _ _ _ _ hinh hval => pcontrol1_exitAgrees_iff_paid hinh hval,
    fun _ c _ caller value _ _ _ _ _ _ _ _ _ _ _
        hinh hval hrep hrun hdec hZ hstep hop hstack hlen =>
      pcontrol1_xi_paid_fee_getter_reverts_of_zero_length c (caller := caller)
        (value := value) hinh hval hrep hrun hdec hZ hstep hop hstack hlen,
    fun _ _ _ _ hinh hw => pcontrol1_exitAgrees_iff_digits hinh hw,
    fun _ _ => step_returnData_ne_nil_iff,
    fun _ c _ mstep _ _ _ _ _ _ _ _ _ _ _
        hnd hrep hrun hdec hZ hstep hop hrev hstack hlen =>
      xi_observes_model_of_not_dataBranch c (mstep := mstep) hnd hrep hrun hdec hZ
        hstep hop hrev hstack hlen,
    fun _ c _ caller _ _ _ _ _ _ _ _ _ _ _
        hinh hrep hrun hdec hZ hstep hop hstack hbytes =>
      pcontrol1_xi_fee_getter_of_memory c (caller := caller) hinh hrep hrun hdec hZ
        hstep hop hstack hbytes,
    pcontrol1_xi_quotes_pinned_fee,
    represents_pinnedExitFeeGetter,
    @exitAgrees_iff_zero_length_of_not_dataBranch,
    @exitAgrees_zero_length_operand_of_not_dataBranch,
    @exitAgrees_of_silent_of_not_dataBranch,
    @xi_observes_model_of_silent_of_not_dataBranch,
    @isRevert_false_of_dataBranch,
    @exitAgrees_of_silent_iff_not_dataBranch,
    @exit_op_eq_RETURN_of_dataBranch,
    @exitAgrees_iff_memory_bytes_of_dataBranch,
    @bytes_toByteArray,
    @bytes_readWithPadding_of_step_MSTORE,
    @memory_step_Push,
    @memory_Runs_Push,
    @bytes_readWithPadding_of_mstore_pushes_zero,
    @endpointAgrees_of_mstore_pushes_return_zero,
    @endpointAgrees_of_mstore_return_zero,
    @memory_mstore_append,
    @memory_step_MSTORE_append,
    @AppendStores.runs,
    @memory_AppendStores,
    @appendStores_two,
    @bytes_readWithPadding_of_appendStores,
    @endpointAgrees_of_mstores_return,
    @exitAgrees_of_mstores_return,
    @pcontrol1_xi_fee_getter_of_mstore,
    @pcontrol1_xi_fee_getter_of_mstore_zero,
    @pcontrol1_xi_fee_getter_of_mstore_pushes,
    Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent⟩

/-- The three registered parents at complete `Ξ`, together. Exactly three IDs,
the same three as `Eip8282.Audit.Guarantees.Id`. -/
theorem registered_parents_at_Xi :
    (type_of% psubmit1_xi_forall_parent) ∧
      (type_of% pdrain1_xi_forall_parent) ∧
      (type_of% pcontrol1_xi_forall_parent) :=
  ⟨psubmit1_xi_forall_parent, pdrain1_xi_forall_parent, pcontrol1_xi_forall_parent⟩

end Eip8282.Audit.XiTransport
