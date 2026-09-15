import Eip8282.Audit.Integrator.RuntimeExecutionScope
import Eip8282.Audit.Integrator.Topics.Nested

/-! No actual Theta invocation occurs within either pinned runtime. Locations
include precompiles and zero-fuel calls, so the exclusion does not rely on
successful children or positive event counts. Collision INVALID also has no
successful Xi execution and no located Theta. -/
namespace Eip8282.Audit.Integrator.RuntimeThetaExclusion
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope NestedEvents
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem step_no_theta {n f : Nat} {child : ThetaArgs} {outer : StepArgs}
    {result : StepResult} {tree : EventTree} {path : EventTree.Address} {r : ThetaResult}
    (hop : outer.op ∈ allowedOps)
    (loc : ThetaAt (.step n outer) result tree path f child r) : False := by
  cases loc with
  | stepChild hc body loc =>
    have hn := selected_none (n := n) hop
    change selectedChild n outer = some _ at hc
    rw [hn] at hc
    cases hc

theorem x_no_theta {image : Image} {fuel f : Nat} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {child : ThetaArgs} {r : ThetaResult} (hat : At image pre)
    (loc : ThetaAt (.x fuel (D_J image.code ⟨0⟩) pre) result tree path f child r) : False := by
  induction fuel generalizing pre result tree path with
  | zero => cases loc
  | succ fuel ih =>
    cases loc with
    | xStepError hz hs loc => exact step_no_theta (opcode_allowed hat) loc
    | xNextChild hz hs hh ht loc => exact step_no_theta (opcode_allowed hat) loc
    | xNextTail hz hs hh ht loc => exact ih (accepted_next hat hz (sound hs) hh) loc
    | xHalt hz hs hh hn loc => exact step_no_theta (opcode_allowed hat) loc
    | xRevert hz hs hh hr loc => exact step_no_theta (opcode_allowed hat) loc

theorem xi_no_theta {image : Image} {fuel f : Nat} {outer : XiArgs}
    {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {child : ThetaArgs} {r : ThetaResult} (hc : outer.env.code = image.code)
    (loc : ThetaAt (.xi fuel outer) result tree path f child r) : False := by
  cases loc with
  | xi body inner =>
    have hj : outer.jumps = D_J image.code ⟨0⟩ := by
      change D_J outer.env.code ⟨0⟩ = _
      rw [hc]
    rw [hj] at inner
    exact x_no_theta (entry_at hc) inner

private theorem invalid_x_no_success {fuel : Nat} {outer : XiArgs}
    {post : EVM.State} {out : ByteArray} (hc : outer.env.code = ⟨#[0xfe]⟩)
    (hr : X fuel outer.jumps outer.entry = .ok (.success post out)) : False := by
  obtain ⟨_,_,op,arg,mid,_,_,hd,hz,_⟩ := SuccessInversion.success_step hr
  have hi : decodeAt outer.entry = (.INVALID,none) :=
    decodeAt_of_code_pc hc rfl (by decide +kernel)
  cases hi.symm.trans hd
  exact OrdinaryGas.accepted_valid hz rfl

theorem invalid_no_success {fuel : Nat} {outer : XiArgs}
    {published : Created × World × UInt256 × Substate} {out : ByteArray}
    (hc : outer.env.code = ⟨#[0xfe]⟩)
    (hr : (Request.xi fuel outer).eval = .ok (.success published out)) : False := by
  cases fuel with
  | zero => cases hr
  | succ fuel =>
    unfold Request.eval Ξ at hr
    change (do
      let r ← X fuel outer.jumps outer.entry
      match r with
      | .success st o => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) o)
      | .revert g o => Except.ok (ExecutionResult.revert g o)) = _ at hr
    cases he : X fuel outer.jumps outer.entry with
    | error err => simp only [he,Bind.bind,Except.bind] at hr; cases hr
    | ok result =>
      cases result with
      | revert g o => simp only [he,Bind.bind,Except.bind] at hr; cases hr
      | success post o => exact invalid_x_no_success hc he

theorem invalid_no_theta {fuel : Nat} {outer : XiArgs}
    {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (hc : outer.env.code = ⟨#[0xfe]⟩)
    (loc : ThetaAt (.xi fuel outer) result tree path f a r) : False :=
  NestedFunding.invalid_has_no_call hc loc

#print axioms x_no_theta
#print axioms xi_no_theta
#print axioms invalid_no_success
#print axioms invalid_no_theta
end Eip8282.Audit.Integrator.RuntimeThetaExclusion
