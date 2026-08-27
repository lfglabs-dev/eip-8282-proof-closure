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

## What stays open

`EndpointAgrees` is the same explicit premise R2 and R3 carry, and it is the
same named OPEN assumption `A-ABSTRACT-TX`: that the terminal EVM observation
agrees with the abstract `Model.step` on *every* calldata/value/storage branch.
R4 does not discharge it and does not weaken it. What R4 changes is only where
the gap sits: it is now a statement about the endpoint of a complete `Ξ` call,
with the `X` ↔ `Ξ` layer closed beneath it.

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
  | error e => simp [Ξ, hX, observe]
  | ok r =>
    cases r with
    | success st o => simp [Ξ, hX, observe]
    | revert g' o => simp [Ξ, hX, observe]

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

/-- **The still-open leaf**, identical in shape to R2's and R3's and covered by
the existing `A-ABSTRACT-TX` ID: the terminal EVM observation agrees with the
abstract step. Proving it for every calldata/value/storage branch *is* the open
assumption. Naming it keeps a conditional composition from being read as the
missing universal opcode proof. -/
def EndpointAgrees (result : ExecutionResult EVM.State) (model : Outcome) : Prop :=
  observe (.ok result) = some (observeModel model)

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
and value. Not a finite trace. Not literal state equality — observation only. -/
def XiTransport (kind : Kind) (mstep : Model.Step) : Prop :=
  ∀ (c : XiCall kind) (model : Model.State)
    (rem gasCost : Nat) (trace : List Labelled)
    (exit mid post : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (out : ByteArray),
    Represents kind c.entry model →
    RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit →
    decodeAt exit = (op, arg) →
    Z (jumpdestsOf kind) op exit = .ok (mid, gasCost) →
    StepOk rem gasCost (op, arg) mid post →
    H post.toMachineState op = some out →
    EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model mstep) →
    observe c.result = some (observeModel (Model.step model mstep))

theorem xiTransport (kind : Kind) (mstep : Model.Step) : XiTransport kind mstep := by
  intro c model rem gasCost trace exit mid post op arg out _rep hrun hdec hZ hstep hH hend
  by_cases hop : op = .REVERT
  · rw [observe_result_revert c hrun hdec hZ hstep hH hop]
    simpa [EndpointAgrees, observe, hop] using hend
  · rw [observe_result_success c hrun hdec hZ hstep hH hop]
    simpa [EndpointAgrees, observe, hop] using hend

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
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hinh : inhibited model = true)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hend : EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model (.user caller calldata value))) :
    observe c.result = some { reverted := true, returnData := [] } := by
  rw [xiTransport kind (.user caller calldata value) c model rem gasCost trace
    exit mid post op arg out hrep hrun hdec hZ hstep hH hend]
  simp [Model.step, userCall, hinh]

/-- **P-DRAIN-1 at `Ξ`: the system call returns exactly the bounded FIFO
prefix.** A system message call succeeds and returns `concatReturned` of the
oldest `capOf kind` queued records — the FIFO window, capped, in order. -/
theorem pdrain1_xi_returns_fifo_prefix {kind : Kind} (c : XiCall kind)
    {model : Model.State} {calldataNonempty : Bool}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hend : EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model (.system calldataNonempty))) :
    observe c.result =
      some { reverted := false
             returnData := concatReturned (model.queue.take (capOf kind)) } := by
  rw [xiTransport kind (.system calldataNonempty) c model rem gasCost trace
    exit mid post op arg out hrep hrun hdec hZ hstep hH hend]
  simp [Model.step, systemCall, Represents.kind_eq hrep]

/-- **P-CONTROL-1 at `Ξ`: the fee getter quotes `currentFee`, read-only.** An
uninhibited predeploy answers an empty-calldata, zero-value user message call
with the 32-byte big-endian `currentFee` of the represented state — the exact
fee algebra the registered parent fixes, at the complete message call. -/
theorem pcontrol1_xi_fee_getter {kind : Kind} (c : XiCall kind)
    {model : Model.State} {caller : Address}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hinh : inhibited model = false)
    (hrep : Represents kind c.entry model)
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg))
    (hZ : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hend : EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model (.user caller [] 0))) :
    observe c.result =
      some { reverted := false, returnData := toBeBytes (currentFee model) 32 } := by
  rw [xiTransport kind (.user caller [] 0) c model rem gasCost trace
    exit mid post op arg out hrep hrun hdec hZ hstep hH hend]
  simp [Model.step, userCall, hinh]

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
      (type_of% Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent) :=
  ⟨fun kind caller calldata value => xiTransport kind (.user caller calldata value),
    Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent⟩

/-- **P-DRAIN-1**, transported to complete `Ξ`. -/
theorem pdrain1_xi_forall_parent :
    (∀ (kind : Kind) (calldataNonempty : Bool),
        XiTransport kind (.system calldataNonempty)) ∧
      (type_of% Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent) :=
  ⟨fun kind b => xiTransport kind (.system b),
    Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent⟩

/-- **P-CONTROL-1**, transported to complete `Ξ`. The control plane spans both
call classes — the fee quote is a user call, the excess/count update a system
call — so both instances are carried. -/
theorem pcontrol1_xi_forall_parent :
    (∀ (kind : Kind) (mstep : Model.Step), XiTransport kind mstep) ∧
      (type_of% Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent) :=
  ⟨fun kind mstep => xiTransport kind mstep,
    Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent⟩

/-- The three registered parents at complete `Ξ`, together. Exactly three IDs,
the same three as `Eip8282.Audit.Guarantees.Id`. -/
theorem registered_parents_at_Xi :
    (type_of% psubmit1_xi_forall_parent) ∧
      (type_of% pdrain1_xi_forall_parent) ∧
      (type_of% pcontrol1_xi_forall_parent) :=
  ⟨psubmit1_xi_forall_parent, pdrain1_xi_forall_parent, pcontrol1_xi_forall_parent⟩

end Eip8282.Audit.XiTransport
