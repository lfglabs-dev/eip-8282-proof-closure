import Eip8282.Audit.Represents
import Eip8282.Audit.XiTransport
import EvmYul.EVM.Proof.Block

/-!
# R2 — whole user-call `Ξ` composition

This module joins the F4a/F4d proof APIs to R1's `Represents` relation.  A
`RunUntil` starts at PC zero and ends immediately before `RETURN` or `REVERT`;
the corresponding terminating step then fixes the result of the code run at the
entry.  R4's `Eip8282.Audit.XiTransport` closes the remaining wrapper layer, so
the statement below is about `EvmYul.EVM.Ξ` — the complete message call an
EIP-8282 client makes — and not merely about `X`.

The observation reused here is R4's, so `X`-level and `Ξ`-level facts compose
without a translation step.  What is compared with `Model.step` is an
observation (status and return bytes), not equality of EVM and model states.

The endpoint premise is intentionally explicit: proving it for every
calldata/value branch is precisely the part of `A-ABSTRACT-TX` which is still
open.  R2 therefore provides sound whole-call composition without pretending to
close the universal claim, and it introduces no parent IDs.
-/

namespace Eip8282.Audit.UserXiCorrespondence

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model
open Eip8282.Audit.Correspondence
open Eip8282.Audit.XiTransport
  (observe observeModel bytes jumpdestsOf XiCall
   observe_result_success observe_result_revert)

/-- The abstract user step this module composes against. -/
abbrev userStep (caller : Address) (calldata : List Byte) (value : Wei) :
    Model.Step := .user caller calldata value

/-- The observation a terminating instruction fixes: `REVERT` flips the status
flag, every other halting instruction returns its bytes as success. -/
def terminalObservation (w : Operation .EVM) (out : ByteArray) :
    XiTransport.Observation :=
  if w = .REVERT then { reverted := true, returnData := bytes out }
  else { reverted := false, returnData := bytes out }

/-- F4d success composition at the complete `Ξ` call, projected to
observations. -/
theorem whole_user_call_success {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun op => Halting op) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z (jumpdestsOf kind) w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hw : w ≠ .REVERT) :
    observe c.result = some (terminalObservation w out) := by
  rw [observe_result_success c hrun hdec hZ hstep hH hw, terminalObservation,
    if_neg hw]

/-- F4d revert composition at the complete `Ξ` call, projected to
observations. -/
theorem whole_user_call_revert {kind : Kind} (c : XiCall kind)
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (hrun : RunUntil (fun op => Halting op) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z (jumpdestsOf kind) w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hw : w = .REVERT) :
    observe c.result = some (terminalObservation w out) := by
  rw [observe_result_revert c hrun hdec hZ hstep hH hw, terminalObservation,
    if_pos hw]

/-- **R2 correspondence theorem.** From an R1 `Represents` world at the machine
`Ξ` starts from, a whole proved run ending at `RETURN`/`REVERT`, and the
explicit endpoint obligation, the complete `Ξ` message call has the same
observation as `Model.step` on the corresponding user call.

`Ξ` here is the real entry point, including the wrapper and the jumpdest table
`Ξ` derives for itself from the pinned code — both closed unconditionally by
R4. What remains explicit is `hend`, which is the named OPEN `A-ABSTRACT-TX`;
this theorem does not discharge it and must not be read as closing it. -/
theorem whole_user_call_xi_correspondence
    {kind : Kind} {model : Model.State} (c : XiCall kind)
    {caller : Address} {calldata : List Byte} {value : Wei}
    {rem gasCost : Nat} {trace : List Labelled} {exit mid post : EVM.State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {out : ByteArray}
    (_rep : Eip8282.Audit.Represents.Represents kind c.entry model)
    (hrun : RunUntil (fun op => Halting op) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z (jumpdestsOf kind) w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some out)
    (hend : terminalObservation w out =
      observeModel (Model.step model (userStep caller calldata value))) :
    observe c.result =
      some (observeModel (Model.step model (userStep caller calldata value))) := by
  by_cases hw : w = .REVERT
  · rw [whole_user_call_revert c hrun hdec hZ hstep hH hw, hend]
  · rw [whole_user_call_success c hrun hdec hZ hstep hH hw, hend]

end Eip8282.Audit.UserXiCorrespondence
