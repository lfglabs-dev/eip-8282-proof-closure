import Eip8282.Audit.Integrator.ReferenceRuntimeCompletion

/-! Uniqueness of a complete actual nonhalting instruction trace. This lets a
structural append path and a source-priced protected runtime certificate share
exactly one trace, without assuming equal lengths or supplying a second desired
instruction list. The result concerns the pinned evaluator's actual XRuns. -/
namespace Eip8282.Audit.Integrator.ReferenceTraceAgreement
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Blocked (vj : Array UInt256) (fuel : Nat) (pre : EVM.State) : Prop :=
  ∀ cost next, ¬ XStepAt vj (fuel-1) cost pre next

theorem blocked_of_stop {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    (decoded : decodeAt pre = (.STOP,none)) : Blocked vj fuel pre := by
  intro cost next h
  obtain ⟨mid,hz,hs,hh⟩ := h
  rw [decoded] at hh
  simp [H] at hh

theorem blocked_of_terminal {vj : Array UInt256} {fuel cost : Nat}
    {pre mid post : EVM.State} {out : ByteArray}
    (charged : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (step : StepOk (fuel-1) cost (decodeAt pre) mid post)
    (halted : H post.toMachineState (decodeAt pre).1 = some out) : Blocked vj fuel pre := by
  intro otherCost next h
  obtain ⟨otherMid,hz,hs,hh⟩ := h
  rw [charged] at hz
  obtain ⟨rfl,rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hz
  have he := Step.deterministic_ok step hs
  subst next
  rw [halted] at hh
  contradiction

theorem complete_unique {vj : Array UInt256} {fuel rem₁ rem₂ : Nat}
    {pre exit₁ exit₂ : EVM.State} {trace₁ trace₂ : List Labelled}
    (first : XRuns vj fuel pre trace₁ rem₁ exit₁)
    (second : XRuns vj fuel pre trace₂ rem₂ exit₂)
    (end₁ : Blocked vj rem₁ exit₁) (end₂ : Blocked vj rem₂ exit₂) :
    trace₁ = trace₂ ∧ rem₁ = rem₂ ∧ exit₁ = exit₂ := by
  induction first generalizing rem₂ exit₂ trace₂ with
  | refl fuel pre =>
    cases second with
    | refl => exact ⟨rfl,rfl,rfl⟩
    | cons step tail =>
      exact False.elim (end₁ _ _ (by simpa only [Nat.add_sub_cancel] using step))
  | @cons fuel gasCost rem pre mid post trace step tail ih =>
    cases second with
    | refl =>
      exact False.elim (end₂ _ _ (by simpa only [Nat.add_sub_cancel] using step))
    | cons otherStep otherTail =>
      obtain ⟨rfl,rfl⟩ := XStepAt.deterministic step otherStep
      obtain ⟨ht,hr,hp⟩ := ih otherTail end₁ end₂
      exact ⟨by rw [ht],hr,hp⟩

#print axioms blocked_of_stop
#print axioms blocked_of_terminal
#print axioms complete_unique
end Eip8282.Audit.Integrator.ReferenceTraceAgreement
