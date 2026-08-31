import Eip8282.Audit.Correspondence
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import EvmYul.EVM.Proof.Block

/-!
# R3 — whole SYSTEM-call `Ξ` observational composition

`RunUntil` composes the complete non-halting prefix from the SYSTEM-call entry
to `RETURN` or `REVERT`; the terminating step then fixes the observation of
`EvmYul.EVM.X` at entry.  Status and return bytes are observed, rather than
claiming literal equality between EVM and model post-states.

R1's `Represents` lives only on draft PR #21, so this main-based module uses
the minimal relation needed by R3: the pinned predeploy account exists, has
the pinned runtime, and abstracts to the given model state.  It intentionally
does not duplicate R1's API or its proofs.

`EndpointAgrees` remains an explicit premise.  Proving it for every SYSTEM
calldata/storage path is the named OPEN `A-ABSTRACT-TX`; this module therefore
does not close that assumption or strengthen any registered parent.
-/

namespace Eip8282.Audit.SystemXiCorrespondence

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence (runtimeCode targetAddr)

/-- Minimal main-based R3 state relation, definitionally matching the core of
R1's draft `Represents`: only the pinned predeploy account is observed. -/
def Represents (kind : Kind) (world : EVM.State) (model : Model.State) : Prop :=
  ∃ acc : Account .EVM,
    world.accountMap.get? (targetAddr kind) = some acc ∧
      acc.code = runtimeCode kind ∧
      WellFormed kind acc.storage ∧
      model = toModel kind acc.storage acc.balance.toNat

structure Observation where
  reverted : Bool
  returnData : List Nat
  deriving DecidableEq, Repr

def bytes (data : ByteArray) : List Nat :=
  (List.range data.size).map fun i => (data.get! i).toNat

def observeΞ : Except EVM.ExecutionException (ExecutionResult EVM.State) →
    Option Observation
  | .ok (.success _ out) => some { reverted := false, returnData := bytes out }
  | .ok (.revert _ out) => some { reverted := true, returnData := bytes out }
  | .error _ => none

def observeModel : Outcome → Observation
  | .success _ out => { reverted := false, returnData := out }
  | .revert _ => { reverted := true, returnData := [] }

/-- Named open leaf of R3, covered by the existing `A-ABSTRACT-TX` ID. -/
def EndpointAgrees (result : ExecutionResult EVM.State) (model : Outcome) : Prop :=
  observeΞ (.ok result) = some (observeModel model)

theorem whole_system_call_success
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {entry exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun w => Halting w) validJumps fuel entry trace (rem + 1) exit)
    (hdecode : decodeAt exit = (op, arg))
    (hZ : Z validJumps op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hop : op ≠ .REVERT) :
    observeΞ (X fuel validJumps entry) =
      some { reverted := false, returnData := bytes out } := by
  rw [hrun.X_success hdecode hZ hstep hH hop]
  rfl

theorem whole_system_call_revert
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {entry exit mid post : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun w => Halting w) validJumps fuel entry trace (rem + 1) exit)
    (hdecode : decodeAt exit = (op, arg))
    (hZ : Z validJumps op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hop : op = .REVERT) :
    observeΞ (X fuel validJumps entry) =
      some { reverted := true, returnData := bytes out } := by
  rw [hrun.X_revert hdecode hZ hstep hH hop]
  rfl

/-- Whole SYSTEM-call correspondence, conditional exactly on the endpoint
observation still tracked as `A-ABSTRACT-TX`. -/
theorem whole_system_call_xi_correspondence
    {kind : Kind} {world exit mid post : EVM.State} {model : Model.State}
    {calldataNonempty : Bool}
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (_represents : Represents kind world model)
    (hrun : RunUntil (fun w => Halting w) validJumps fuel world trace (rem + 1) exit)
    (hdecode : decodeAt exit = (op, arg))
    (hZ : Z validJumps op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hendpoint : EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model (.system calldataNonempty))) :
    observeΞ (X fuel validJumps world) =
      some (observeModel (Model.step model (.system calldataNonempty))) := by
  by_cases hop : op = .REVERT
  · rw [whole_system_call_revert hrun hdecode hZ hstep hH hop]
    simpa [EndpointAgrees, observeΞ, hop] using hendpoint
  · rw [whole_system_call_success hrun hdecode hZ hstep hH hop]
    simpa [EndpointAgrees, observeΞ, hop] using hendpoint

/-- Exactly the three existing registered parents; R3 registers no new ID. -/
def RegisteredParents : Prop :=
  (type_of% Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent) ∧
  (type_of% Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent) ∧
  (type_of% Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent)

theorem registeredParents : RegisteredParents :=
  ⟨Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent,
    Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent,
    Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent⟩

/-- R3 carries the unchanged registered parents alongside the SYSTEM-call
observation. Their existing bytecode conjuncts and kill-lines are untouched. -/
theorem whole_system_call_registered_correspondence
    {kind : Kind} {world exit mid post : EVM.State} {model : Model.State}
    {calldataNonempty : Bool}
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (rep : Represents kind world model)
    (hrun : RunUntil (fun w => Halting w) validJumps fuel world trace (rem + 1) exit)
    (hdecode : decodeAt exit = (op, arg))
    (hZ : Z validJumps op exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (op, arg) mid post)
    (hH : H post.toMachineState op = some out)
    (hendpoint : EndpointAgrees
      (if op = .REVERT then .revert post.gasAvailable out else .success post out)
      (Model.step model (.system calldataNonempty))) :
    observeΞ (X fuel validJumps world) =
        some (observeModel (Model.step model (.system calldataNonempty))) ∧
      RegisteredParents :=
  ⟨whole_system_call_xi_correspondence rep hrun hdecode hZ hstep hH hendpoint,
    registeredParents⟩

end Eip8282.Audit.SystemXiCorrespondence
