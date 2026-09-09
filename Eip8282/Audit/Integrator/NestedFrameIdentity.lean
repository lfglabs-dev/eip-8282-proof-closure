import Eip8282.Audit.Integrator.NestedFrameOccurrence

/-!
# Unique actual Xi identity at a structural frame path

The same path in the same actual nested certificate cannot denote different
Xi invocations. This includes all outcomes and preserves full execution inputs,
not only the code or target account. No frame list or global count is assumed.
-/
namespace Eip8282.Audit.Integrator.NestedEvents.XiAt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem identity {q : Request} {result₁ result₂ : q.Outcome} {tree₁ tree₂ : EventTree}
    {path : EventTree.Address} {f₁ f₂ : Nat} {a₁ a₂ : XiArgs} {r₁ r₂ : XiResult}
    (h₁ : XiAt q result₁ tree₁ path f₁ a₁ r₁)
    (h₂ : XiAt q result₂ tree₂ path f₂ a₂ r₂) :
    f₁ = f₂ ∧ a₁ = a₂ ∧ r₁ = r₂ := by
  induction h₁ generalizing tree₂ f₂ a₂ r₂ with
  | here body =>
      cases h₂ with
      | here body₂ => exact ⟨rfl, rfl, outcome_deterministic body body₂⟩
      | xi _ loc => exact False.elim (x_nonempty loc rfl)
  | xStepError hz hs loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          exact ih loc₂
      | xNextChild hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
  | xNextChild hz hs hh ht loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNextChild hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
      | xHalt hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
  | xNextTail hz hs hh ht loc ih =>
      cases h₂ with
      | xNextTail hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xHalt hz hs hh hn loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert _ _ _ hr₂ _ => exact False.elim (hn hr₂)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xHalt hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xRevert hz hs hh hr loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt _ _ _ hn₂ _ => exact False.elim (hn₂ hr)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xi body loc ih =>
      cases h₂ with
      | here => exact False.elim (x_nonempty loc rfl)
      | xi _ loc₂ => exact ih loc₂
  | thetaCode bytes hc body loc ih =>
      cases h₂ with
      | thetaCode _ hc₂ _ loc₂ =>
          cases ToExecute.Code.inj (hc.symm.trans hc₂)
          exact ih loc₂
  | lambdaInit bytes hp body loc ih =>
      cases h₂ with
      | lambdaInit _ hp₂ _ loc₂ =>
          cases Option.some.inj (hp.symm.trans hp₂)
          exact ih loc₂
  | stepChild hc body loc ih =>
      cases h₂ with
      | stepChild hc₂ _ loc₂ =>
          cases Option.some.inj (stepChild_unique hc hc₂)
          exact ih loc₂

#print axioms identity
end Eip8282.Audit.Integrator.NestedEvents.XiAt
