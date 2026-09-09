import Eip8282.Audit.Integrator.NestedEventCert

/-!
# Extract the unique complete nested event certificate

Every recursive certificate is obtained from a strictly smaller actual evaluator
fuel. Errors are ordinary outcomes of the same extraction and never authorize
discarding a selected child.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach SuccessInversion
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

private theorem extract_fuel (n : Nat) :
    ∀ q : Request, q.fuel = n → ∃ tree, Cert q q.eval tree := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro q hn
      cases q with
      | x fuel vj pre =>
          simp only [Request.fuel] at hn
          subst n
          cases fuel with
          | zero => exact ⟨.done, Cert.xZero vj pre⟩
          | succ fuel =>
              cases hz : Z vj (decodeAt pre).1 pre with
              | error err =>
                  change ∃ tree, Cert (.x (fuel+1) vj pre) (X (fuel+1) vj pre) tree
                  rw [X_succ_of_Z_error rfl hz]
                  exact ⟨.done, Cert.xGuardError hz⟩
              | ok charged =>
                  obtain ⟨mid,cost⟩ := charged
                  let a := StepArgs.ofGuard vj pre mid cost hz
                  obtain ⟨child,hs⟩ := ih fuel (by omega) (.step fuel a) rfl
                  cases he : (Request.step fuel a).eval with
                  | error err =>
                      rw [he] at hs
                      change ∃ tree, Cert (.x (fuel+1) vj pre) (X (fuel+1) vj pre) tree
                      rw [X_succ_of_step_error rfl hz he]
                      exact ⟨_, Cert.xStepError hz hs⟩
                  | ok post =>
                      rw [he] at hs
                      cases hh : H post.toMachineState (decodeAt pre).1 with
                      | none =>
                          obtain ⟨next,ht⟩ := ih fuel (by omega) (.x fuel vj post) rfl
                          change ∃ tree, Cert (.x (fuel+1) vj pre) (X (fuel+1) vj pre) tree
                          rw [X_succ_of_continue rfl hz he hh]
                          exact ⟨_, Cert.xNext hz hs hh ht⟩
                      | some out =>
                          by_cases hr : (decodeAt pre).1 = .REVERT
                          · change ∃ tree, Cert (.x (fuel+1) vj pre) (X (fuel+1) vj pre) tree
                            rw [X_succ_of_revert rfl hz he hh hr]
                            exact ⟨_, Cert.xRevert hz hs hh hr⟩
                          · change ∃ tree, Cert (.x (fuel+1) vj pre) (X (fuel+1) vj pre) tree
                            rw [X_succ_of_halt rfl hz he hh hr]
                            exact ⟨_, Cert.xHalt hz hs hh hr⟩
      | xi fuel a =>
          simp only [Request.fuel] at hn
          subst n
          cases fuel with
          | zero => exact ⟨.done, Cert.xiZero a⟩
          | succ fuel =>
              obtain ⟨tree,ht⟩ := ih fuel (by omega) (.x fuel a.jumps a.entry) rfl
              exact ⟨tree, Cert.xi ht⟩
      | theta fuel a =>
          simp only [Request.fuel] at hn
          subst n
          cases fuel with
          | zero => exact ⟨.done, Cert.thetaZero a⟩
          | succ fuel =>
              cases hc : a.code with
              | Precompiled target => exact ⟨.done, Cert.thetaPrecompile target hc⟩
              | Code bytes =>
                  obtain ⟨tree,ht⟩ := ih fuel (by omega) (.xi fuel (a.xiArgs bytes)) rfl
                  exact ⟨tree, Cert.thetaCode bytes hc ht⟩
      | lambda fuel a =>
          simp only [Request.fuel] at hn
          subst n
          cases fuel with
          | zero => exact ⟨.done, Cert.lambdaZero a⟩
          | succ fuel =>
              cases hp : a.preimage with
              | none => exact ⟨.done, Cert.lambdaNoPreimage hp⟩
              | some bytes =>
                  obtain ⟨tree,ht⟩ := ih fuel (by omega) (.xi fuel (a.xiArgs bytes)) rfl
                  exact ⟨tree, Cert.lambdaInit bytes hp ht⟩
      | step fuel a =>
          simp only [Request.fuel] at hn
          subst n
          cases hc : selectedChild fuel a with
          | none => exact ⟨.done, Cert.stepNone hc⟩
          | some child =>
              obtain ⟨tree,ht⟩ := ih child.fuel (stepChild_fuel hc) child rfl
              exact ⟨tree, Cert.stepChild hc ht⟩

/-- Every actual evaluator outcome has a complete nested tree. -/
theorem extract (q : Request) : ∃ tree, Cert q q.eval tree := extract_fuel q.fuel q rfl

/-- The pinned inputs fix the entire structural tree, not only its result. -/
theorem deterministic {q : Request} {r₁ r₂ : q.Outcome} {t₁ t₂ : EventTree}
    (h₁ : Cert q r₁ t₁) (h₂ : Cert q r₂ t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | xZero => cases h₂; rfl
  | xGuardError hz =>
      cases h₂ with
      | xGuardError => rfl
      | xStepError hz₂ _ => cases hz.symm.trans hz₂
      | xNext hz₂ _ _ _ => cases hz.symm.trans hz₂
      | xHalt hz₂ _ _ _ => cases hz.symm.trans hz₂
      | xRevert hz₂ _ _ _ => cases hz.symm.trans hz₂
  | xStepError hz hs ih =>
      cases h₂ with
      | xGuardError hz₂ => cases hz.symm.trans hz₂
      | xStepError hz₂ hs₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          exact congrArg (fun c => EventTree.step false c .done) (ih hs₂)
      | xNext hz₂ hs₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt hz₂ hs₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert hz₂ hs₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
  | xNext hz hs hh ht ihs iht =>
      cases h₂ with
      | xGuardError hz₂ => cases hz.symm.trans hz₂
      | xStepError hz₂ hs₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNext hz₂ hs₂ hh₂ ht₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          rw [ihs hs₂, iht ht₂]
      | xHalt hz₂ hs₂ hh₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ hh₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
  | xHalt hz hs hh hn ih =>
      cases h₂ with
      | xGuardError hz₂ => cases hz.symm.trans hz₂
      | xStepError hz₂ hs₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNext hz₂ hs₂ hh₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xHalt hz₂ hs₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          rw [ih hs₂]
      | xRevert _ _ _ hr₂ => exact False.elim (hn hr₂)
  | xRevert hz hs hh hr ih =>
      cases h₂ with
      | xGuardError hz₂ => cases hz.symm.trans hz₂
      | xStepError hz₂ hs₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNext hz₂ hs₂ hh₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xHalt _ _ _ hn₂ => exact False.elim (hn₂ hr)
      | xRevert hz₂ hs₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          rw [ih hs₂]
  | xiZero => cases h₂; rfl
  | xi body ih => cases h₂ with | xi body₂ => exact ih body₂
  | thetaZero => cases h₂; rfl
  | thetaPrecompile _ hc =>
      cases h₂ with
      | thetaPrecompile => rfl
      | thetaCode _ hc₂ _ => cases hc.symm.trans hc₂
  | thetaCode bytes hc body ih =>
      cases h₂ with
      | thetaPrecompile _ hc₂ => cases hc.symm.trans hc₂
      | thetaCode _ hc₂ body₂ =>
          cases ToExecute.Code.inj (hc.symm.trans hc₂)
          exact ih body₂
  | lambdaZero => cases h₂; rfl
  | lambdaNoPreimage hp =>
      cases h₂ with
      | lambdaNoPreimage => rfl
      | lambdaInit _ hp₂ _ => cases hp.symm.trans hp₂
  | lambdaInit bytes hp body ih =>
      cases h₂ with
      | lambdaNoPreimage hp₂ => cases hp.symm.trans hp₂
      | lambdaInit _ hp₂ body₂ =>
          cases Option.some.inj (hp.symm.trans hp₂)
          exact ih body₂
  | stepNone hc =>
      cases h₂ with
      | stepNone => rfl
      | stepChild hc₂ _ => cases stepChild_unique hc hc₂
  | stepChild hc body ih =>
      cases h₂ with
      | stepNone hc₂ => cases stepChild_unique hc hc₂
      | stepChild hc₂ body₂ =>
          cases Option.some.inj (stepChild_unique hc hc₂)
          exact ih body₂

#print axioms deterministic
#print axioms extract
end Eip8282.Audit.Integrator.NestedEvents
