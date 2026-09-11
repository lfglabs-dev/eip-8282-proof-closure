import Eip8282.Audit.Integrator.ReferenceExecutionPotential

/-! Execution-potential conservation for the exact source CALL resource
sequence, including successful and failed children. The stipend is subtracted
from the parent's charged overhead exactly once. Actual source dispatch and
journal extraction remain distinct from this literal resource adapter. -/
namespace Eip8282.Audit.Integrator.ReferenceCallPotential
open EvmYul ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCallGrant ReferenceChildMeter ReferenceCallChildBoundary ReferenceExecutionPotential
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem execution_debit {pre : Meter} {post : ReferenceStorageGas.Meter} {amount : Nat}
    (h : ReferenceStorageGas.chargeExecution (core pre) amount = some post) :
    potential (update pre post)+amount = potential pre := by
  unfold ReferenceStorageGas.chargeExecution at h
  split at h
  · cases h
    simp only [update,core,potential] at *
    omega
  · contradiction

theorem state_preserves {pre : Meter} {post : ReferenceStorageGas.Meter} {amount : Nat}
    (h : ReferenceStorageGas.chargeState (core pre) amount = some post) :
    potential (update pre post) = potential pre := by
  unfold ReferenceStorageGas.chargeState at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      simp only [update,core,potential] at *
      omega
    · contradiction

theorem prepared_debit {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre charged : Meter}
    (h : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged) :
    potential charged+executionCost cold delegated delegationCold hasValue memoryCost = potential pre := by
  unfold prepare at h
  cases he : ReferenceStorageGas.chargeExecution (core pre)
      (executionCost cold delegated delegationCold hasValue memoryCost) with
  | none => simp only [he,Option.bind_none,Option.map_none] at h; contradiction
  | some middle =>
    simp only [he,Option.bind_some] at h
    cases hs : ReferenceStorageGas.chargeState middle (stateCost hasValue deadRecipient) with
    | none => simp only [hs,Option.map_none] at h; contradiction
    | some final =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst charged
      have hd := execution_debit he
      have hsame : core (update pre middle) = middle := by cases middle; rfl
      have hs' : ReferenceStorageGas.chargeState (core (update pre middle))
          (stateCost hasValue deadRecipient) = some final := by rw [hsame]; exact hs
      have hp := state_preserves hs'
      have hu : update (update pre middle) final = update pre final := rfl
      rw [hu] at hp
      omega

def overhead (cold delegated delegationCold hasValue : Bool) (memoryCost : Nat) : Nat :=
  executionCost cold delegated delegationCold hasValue memoryCost-stipend hasValue

theorem overhead_exact (cold delegated delegationCold hasValue : Bool) (memoryCost : Nat) :
    overhead cold delegated delegationCold hasValue memoryCost+stipend hasValue =
      executionCost cold delegated delegationCold hasValue memoryCost := by
  cases hasValue <;> simp only [overhead,executionCost,stipend,Bool.false_eq_true,↓reduceIte] <;> omega

private theorem refill_preserves (hasValue deadRecipient : Bool) (outcome : Outcome) (m : Meter) :
    potential (refill hasValue deadRecipient outcome m) = potential m := by
  unfold refill
  split
  · exact credit_preserves _ _
  · rfl

/-- This works for arbitrary signed net state use. The child work is bounded
by its execution potential before settlement; ancestor rollback cannot erase
that paid work. The finish receipt supplies the actual merge assertions. -/
theorem call_work {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost work : Nat} {pre charged child final : Meter}
    (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
    (requested : UInt256) (outcome : Outcome)
    (childWork : potential child+work ≤ potential (start (split hasValue requested charged)))
    (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
    potential final+work+overhead cold delegated delegationCold hasValue memoryCost ≤ potential pre := by
  have hp := prepared_debit prepared
  have hg := split_potential hasValue requested charged
  have ho := overhead_exact cold delegated delegationCold hasValue memoryCost
  have hs := settle_nonincrease outcome child
  have hi : potential (start (split hasValue requested charged)) =
      (split hasValue requested charged).childExecution := by simp [start,init,potential]
  unfold finish at finished
  cases hm : incorporate (split hasValue requested charged).parent (settle outcome child) (failed outcome) with
  | none => simp only [hm,Option.map_none] at finished; contradiction
  | some merged =>
    simp only [hm,Option.map_some,Option.some.injEq] at finished
    subst final
    have hmerge := incorporate_preserves hm
    rw [refill_preserves]
    omega

#print axioms execution_debit
#print axioms state_preserves
#print axioms prepared_debit
#print axioms overhead_exact
#print axioms call_work
end Eip8282.Audit.Integrator.ReferenceCallPotential
