import Eip8282.Audit.Integrator.ReferenceStorageGas

/-! Storage-set state charges and credits telescope on an actual value chain.
A set-then-clear cycle cannot create net state gas. This algebra must be applied
to the same slot's ordered writes; arbitrary unlinked event readings do not
supply that premise. Account lifecycle and nested rollback remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceStoragePotential
open EvmYul ReferenceStorageGas
set_option autoImplicit false

noncomputable def potential (original current : UInt256) : Int :=
  if original = ⟨0⟩ ∧ current ≠ ⟨0⟩ then 97920 else 0

theorem step (warm : Bool) (original current new : UInt256) :
    ((classify warm original current new).state : Int)-(classify warm original current new).stateRefund =
      potential original new-potential original current := by
  classical
  by_cases ho : original = ⟨0⟩
  · subst original
    by_cases hc : current = ⟨0⟩
    · subst current
      by_cases hn : new = ⟨0⟩
      · subst new; simp [classify,potential]
      · simp [classify,potential,hn,Ne.symm hn]
    · by_cases hn : new = ⟨0⟩
      · subst new; simp [classify,potential,hc,Ne.symm hc]
      · simp [classify,potential,hc,hn,Ne.symm hc,Ne.symm hn]
  · simp [classify,potential,ho]

def finalValue : UInt256 → List UInt256 → UInt256
  | current, [] => current
  | _, new::tail => finalValue new tail

def net : UInt256 → UInt256 → List UInt256 → Int
  | _, _, [] => 0
  | original, current, new::tail =>
    ((classify false original current new).state : Int)-(classify false original current new).stateRefund+
      net original new tail

/-- Arbitrary finite write sequences, with successive current values linked.
This is a per-slot signed state-gas balance, not a count of retained appends. -/
theorem telescope (original current : UInt256) (writes : List UInt256) :
    net original current writes = potential original (finalValue current writes)-potential original current := by
  induction writes generalizing current with
  | nil => simp [net,finalValue]
  | cons new tail ih =>
    simp only [net,finalValue,ih,step]
    omega

/-- A slot starting at its transaction-original value owes no initial state
credit. Net state-gas spending cannot become negative on its linked writes. -/
theorem from_original (original : UInt256) (writes : List UInt256) :
    0 ≤ net original original writes ∧ net original original writes ≤ 97920 := by
  classical
  rw [telescope]
  have hi : potential original original = 0 := by simp [potential]
  rw [hi]
  unfold potential
  split <;> omega

#print axioms step
#print axioms telescope
#print axioms from_original
end Eip8282.Audit.Integrator.ReferenceStoragePotential
