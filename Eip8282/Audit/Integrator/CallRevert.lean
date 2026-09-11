import Eip8282.Audit.Integrator.MessageCall
import Eip8282.Audit.Integrator.SuccessInversion

/-! Precise failure inversion at the actual Theta code boundary. Returned false
restores the complete pre-transfer journal, but may arise either from Xi REVERT
or a non-OutOfFuel exceptional halt. Evaluator OutOfFuel remains an error.
This does not classify precompile outcomes or assert source interpreter parity.
-/
namespace Eip8282.Audit.Integrator.CallRevert
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

/-- No successful Xi execution can be hidden inside returned Theta false. -/
theorem false_cases (c : MessageCall.Context)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,false,out)) :
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      (c.execution = .ok (.revert gas out) ∨
       ∃ e, c.execution = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
         gas = UInt256.ofNat 0 ∧ out = ByteArray.empty) := by
  obtain ⟨hw,hss,hcs⟩ := MessageCall.failure_restores_journal c created world gas substate out h
  refine ⟨hw,hss,hcs,?_⟩
  rw [MessageCall.result_eq_settle] at h
  cases he : c.execution with
  | error err =>
    by_cases hf : (err == ExecutionException.OutOfFuel) = true
    · simp [MessageCall.Context.settle,he,hf] at h
    · have hfalse : (err == ExecutionException.OutOfFuel) = false := by
        cases hb : (err == ExecutionException.OutOfFuel) <;> simp_all
      simp [MessageCall.Context.settle,he,hfalse] at h
      obtain ⟨_,_,hg,_,ho⟩ := h
      exact Or.inr ⟨err,rfl,hfalse,hg.symm,ho.symm⟩
  | ok result =>
    cases result with
    | revert g o =>
      simp only [MessageCall.Context.settle,he,Except.ok.injEq,Prod.mk.injEq] at h
      obtain ⟨_,_,hg,_,_,ho⟩ := h
      subst g
      subst o
      exact Or.inl rfl
    | success post data =>
      rcases post with ⟨cs,ws,gs,ss⟩
      simp [MessageCall.Context.settle,he] at h

/-- Actual Xi REVERT exposes the same X REVERT, gas and output. -/
theorem xi_revert_X {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind)
    {gas : UInt256} {out : ByteArray} (h : c.result = .ok (.revert gas out)) :
    X c.fuel (jumpdestsOf kind) c.entry = .ok (.revert gas out) := by
  unfold XiCall.result Ξ at h
  change (do
    let r ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
    match r with
    | .success st o => Except.ok (ExecutionResult.success
        (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _ at h
  rw [Xi_validJumps_eq c.code_pinned] at h
  cases hx : X c.fuel (jumpdestsOf kind) c.entry with
  | error err =>
    simp only [hx,Bind.bind,Except.bind] at h
    cases h
  | ok result =>
    cases result with
    | success final data =>
      simp only [hx,Bind.bind,Except.bind] at h
      cases h
    | revert g data =>
      simp only [hx,Bind.bind,Except.bind,Except.ok.injEq,ExecutionResult.revert.injEq] at h
      obtain ⟨hg,ho⟩ := h
      subst g
      subst data
      rfl

#print axioms false_cases
#print axioms xi_revert_X
end Eip8282.Audit.Integrator.CallRevert
