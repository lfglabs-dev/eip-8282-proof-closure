import Eip8282.Audit.Correspondence
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import EvmYul.EVM.Proof.Block

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

The exact-width equalities carry `μ₁.toNat < USize.size`, which is not
cosmetic: `USize.size` is `2 ^ System.Platform.numBits` and may be `2 ^ 32`, and
`readWithPadding` truncates its pad count through a machine word. The `≤`
directions are unconditional; `size_readWithPadding_of_lt_two_pow_32` is the
platform-independent corollary.

Closing what remains still needs a universal opcode-level proof over the pinned
runtimes. R4 does not attempt one. `A-ABSTRACT-TX` stays OPEN, and what stays
open is now precisely this: **nothing here proves the pinned runtimes reach any
particular exit instruction, nor what their memory holds when they do.** The
residual premise, verbatim, is

  `ExitAgrees op (haltData post.toMachineState op) (Model.step model mstep)`

equivalently `EndpointAgrees` via `endpointAgrees_iff_exitAgrees`. For P-DRAIN-1
and P-CONTROL-1 it is now a statement about a *specific* memory slice of a
*pinned* width (`exitAgrees_iff_memory_slice` + `XiWidthTransport`), refined to
per-digit equations for the fee quote and to per-record equations for the FIFO
window. For P-SUBMIT-1 the residual is gone on **every** branch, replaced by two
facts about the run itself — it exits on `REVERT`, with a zero length operand —
and `userCall_returnData_ne_nil_iff` certifies that those branches are all of
them bar the fee quote.

So what `A-ABSTRACT-TX` still buys, stated as narrowly as this module can state
it, is two byte-level facts about memory at the exit instruction — the 32-byte
fee quote and the encoded FIFO window — plus the fact that the runtimes reach an
exit instruction at all. It is no longer load-bearing for any branch that
publishes nothing.

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
      (type_of% Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent) :=
  ⟨fun kind caller calldata value => xiTransport kind (.user caller calldata value),
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
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
    Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent⟩

/-- **P-DRAIN-1**, transported to complete `Ξ`. -/
theorem pdrain1_xi_forall_parent :
    (∀ (kind : Kind) (calldataNonempty : Bool),
        XiTransport kind (.system calldataNonempty)) ∧
      (∀ kind : Kind, XiExitTransport kind) ∧
      (∀ kind : Kind, XiSliceTransport kind) ∧
      (∀ kind : Kind, XiWidthTransport kind) ∧
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
      (type_of% Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent) :=
  ⟨fun kind b => xiTransport kind (.system b),
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
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
    Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent⟩

/-- **P-CONTROL-1**, transported to complete `Ξ`. The control plane spans both
call classes — the fee quote is a user call, the excess/count update a system
call — so both instances are carried. -/
theorem pcontrol1_xi_forall_parent :
    (∀ (kind : Kind) (mstep : Model.Step), XiTransport kind mstep) ∧
      (∀ kind : Kind, XiExitTransport kind) ∧
      (∀ kind : Kind, XiSliceTransport kind) ∧
      (∀ kind : Kind, XiWidthTransport kind) ∧
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
      (type_of% Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent) :=
  ⟨fun kind mstep => xiTransport kind mstep,
    xiExitTransport,
    xiSliceTransport,
    xiWidthTransport,
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
    Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent⟩

/-- The three registered parents at complete `Ξ`, together. Exactly three IDs,
the same three as `Eip8282.Audit.Guarantees.Id`. -/
theorem registered_parents_at_Xi :
    (type_of% psubmit1_xi_forall_parent) ∧
      (type_of% pdrain1_xi_forall_parent) ∧
      (type_of% pcontrol1_xi_forall_parent) :=
  ⟨psubmit1_xi_forall_parent, pdrain1_xi_forall_parent, pcontrol1_xi_forall_parent⟩

end Eip8282.Audit.XiTransport
