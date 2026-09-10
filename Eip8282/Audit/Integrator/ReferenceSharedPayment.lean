import Eip8282.Audit.Integrator.ReferenceMeterPath

/-! Initial budgets for the literal source meter with reservoir-first state
charges and execution spill. No separate state reservoir is required: execution
must cover the execution budget, and the two pools together must cover both
budgets. Credits are observed only when their instruction executes. This is a
source-meter theorem, not an admitted transaction or Python execution theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceSharedPayment
open EvmYul ReferenceStorageGas ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem state_success (m : Meter) (amount futureExec futureState : Nat)
    (he : futureExec ≤ m.execution)
    (ht : amount+futureExec+futureState ≤ m.execution+m.reservoir) :
    ∃ post, chargeState m amount = some post ∧
      futureExec ≤ post.execution ∧ futureExec+futureState ≤ post.execution+post.reservoir := by
  unfold chargeState
  split
  · exact ⟨_,rfl,he,by dsimp; omega⟩
  · rw [if_pos (by omega)]
    exact ⟨_,rfl,by dsimp; omega,by dsimp; omega⟩

/-- The caller reserves the remaining execution work before this instruction.
If state payment spills, the remaining reservoir is zero and total funds protect
that same execution reserve. No future refund is borrowed. -/
theorem pay_success (event : Event) (m : Meter) (futureExec futureState : Nat)
    (he : executionBudget event+futureExec ≤ m.execution)
    (ht : executionBudget event+stateBudget event+futureExec+futureState ≤ m.execution+m.reservoir) :
    ∃ post, pay event m = some post ∧
      futureExec ≤ post.execution ∧ futureExec+futureState ≤ post.execution+post.reservoir := by
  cases event with
  | ordinary amount =>
    change amount+futureExec ≤ m.execution at he
    change amount+0+futureExec+futureState ≤ m.execution+m.reservoir at ht
    refine ⟨{m with execution := m.execution-amount},?_,?_,?_⟩
    · exact if_pos (by omega)
    · dsimp; omega
    · dsimp; omega
  | store warm original current new =>
    change 12100+futureExec ≤ m.execution at he
    change 12100+97920+futureExec+futureState ≤ m.execution+m.reservoir at ht
    obtain ⟨be,bs,sentry⟩ := charge_bounds warm original current new
    unfold pay storageCharge
    simp only [Bool.false_eq_true,↓reduceIte,sentry]
    rw [if_pos (by omega)]
    unfold creditState chargeExecution
    rw [if_pos (by dsimp; omega)]
    simp only [Option.bind_some]
    apply state_success
    · dsimp; omega
    · dsimp; omega

/-- Arbitrarily long finite event lists, funded at entry with actual split pools.
State charges may spill into execution gas; no artificial positive-reservoir
premise or iteration bound is introduced. -/
theorem payment (events : List Event) (m : Meter)
    (he : sumExec events ≤ m.execution)
    (ht : sumExec events+sumState events ≤ m.execution+m.reservoir) :
    ∃ post, run events m = some post := by
  induction events generalizing m with
  | nil => exact ⟨m,rfl⟩
  | cons event events ih =>
    have ex : sumExec (event::events) = executionBudget event+sumExec events := rfl
    have st : sumState (event::events) = stateBudget event+sumState events := rfl
    obtain ⟨middle,paid,me,mt⟩ := pay_success event m (sumExec events) (sumState events)
      (by omega) (by omega)
    obtain ⟨post,tail⟩ := ih middle me mt
    exact ⟨post,by simp only [run,paid,Option.bind_some,tail]⟩

#print axioms pay_success
#print axioms payment
end Eip8282.Audit.Integrator.ReferenceSharedPayment
