import Eip8282.Audit.Represents
import EvmYul.EVM.Proof.Block

/-!
# R2 — whole user-call `X` composition

This module joins the F4a/F4d proof APIs to R1's `Represents` relation.  A
`RunUntil` starts at PC zero and ends immediately before `RETURN` or `REVERT`;
the corresponding terminating step then fixes the result of `X` at the entry.

The result compared with `Model.step` is an observation (status and return
bytes), not equality of EVM and model states.  `EndpointAgrees` is intentionally
an explicit premise: proving it for every calldata/value branch is precisely
the part of `A-ABSTRACT-TX` which is still open.  Thus R2 provides sound
whole-call composition without pretending to close the universal claim.
-/

namespace Eip8282.Audit.UserXiCorrespondence

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Represents

/-- What is externally visible at the call boundary.  Post-state equality is
deliberately absent. -/
structure Observation where
  reverted : Bool
  returnData : List Nat
  deriving DecidableEq, Repr

def bytes (b : ByteArray) : List Nat :=
  (List.range b.size).map fun i => (b.get! i).toNat

def observeX : Except EVM.ExecutionException (ExecutionResult EVM.State) →
    Option Observation
  | .ok (.success _ out) => some { reverted := false, returnData := bytes out }
  | .ok (.revert _ out) => some { reverted := true, returnData := bytes out }
  | .error _ => none

def observeModel : Outcome → Observation
  | .success _ out => { reverted := false, returnData := out }
  | .revert _ => { reverted := true, returnData := [] }

/-- The still-open leaf of R2: the terminal EVM observation agrees with the
abstract user step.  Keeping this named prevents a conditional composition
lemma from being mistaken for the missing universal opcode proof. -/
def EndpointAgrees (result : ExecutionResult EVM.State) (model : Outcome) : Prop :=
  observeX (.ok result) = some (observeModel model)

/-- F4d success composition, projected to observations. -/
theorem whole_user_call_success
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {entry exit mid post : EVM.State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun op => Halting op) validJumps fuel entry trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hw : w ≠ .REVERT) :
    observeX (X fuel validJumps entry) =
      some { reverted := false, returnData := bytes out } := by
  rw [hrun.X_success hdec hZ hstep hH hw]
  rfl

/-- F4d revert composition, projected to observations. -/
theorem whole_user_call_revert
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {entry exit mid post : EVM.State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun op => Halting op) validJumps fuel entry trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hw : w = .REVERT) :
    observeX (X fuel validJumps entry) =
      some { reverted := true, returnData := bytes out } := by
  rw [hrun.X_revert hdec hZ hstep hH hw]
  rfl

/-- **R2 correspondence theorem.** From an R1 world at entry, a whole proved
user call ending at `RETURN`/`REVERT`, and the explicit endpoint agreement
obligation, the entry-PC execution has the same observation as `Model.step`.

This is deliberately conditional while `A-ABSTRACT-TX` remains open. -/
theorem whole_user_call_xi_correspondence
    {kind : Kind} {world exit mid post : EVM.State} {model : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    {validJumps : Array UInt256} {fuel rem gasCost : Nat}
    {trace : List Labelled} {w : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (_rep : Represents kind world model)
    (hrun : RunUntil (fun op => Halting op) validJumps fuel world trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hend : (if w = .REVERT then
        { reverted := true, returnData := bytes out }
      else { reverted := false, returnData := bytes out }) =
        observeModel (Model.step model (.user caller calldata value))) :
    observeX (X fuel validJumps world) =
      some (observeModel (Model.step model (.user caller calldata value))) := by
  by_cases hw : w = .REVERT
  · rw [whole_user_call_revert hrun hdec hZ hstep hH hw]
    exact congrArg some (by simpa [hw] using hend)
  · rw [whole_user_call_success hrun hdec hZ hstep hH hw]
    exact congrArg some (by simpa [hw] using hend)

end Eip8282.Audit.UserXiCorrespondence
