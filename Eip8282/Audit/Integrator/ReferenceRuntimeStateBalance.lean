import Eip8282.Audit.Integrator.ReferenceStorageFlow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-! Sum state-gas potential over the finite EVM address/word-key space.
No enumeration bound is imposed on execution. The finite sum is mathematical,
not an executable scan of storage or a claim of canonical source reachability.
Actual coupled actions derive all slot changes and their exact total charge. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceStorageFlow
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000

abbrev Slot := AccountAddress × Fin UInt256.size

-- Use a symbolic finite enumeration, avoiding reduction of the concrete
-- numeral Fin universes during kernel conversion. Membership remains universal.
noncomputable local instance symbolicSlots : Fintype Slot := Fintype.ofFinite Slot

noncomputable def totalPotential (p : Parent) (tx : Tx) : Int :=
  ∑ q : Slot, slotPotential p tx q.1 (UInt256.mk q.2).toByteArray

private theorem delta_sum {p : Parent} {v next : View} {w : Warm}
    {instr : Instruction} {event : Event} (price : Price p v w next instr.1 event) :
    (∑ q : Slot, keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray) = eventDelta event := by
  classical
  by_cases hs : instr.1 = .SSTORE
  · have same (q : Slot) : keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray =
        if q = (v.env.codeOwner,v.stack[0]!.val) then eventDelta event else 0 := by
      unfold keyDelta
      simp only [hs,true_and,ReferenceStorageView.key_injective.eq_iff]
      have he : (q.1 = v.env.codeOwner ∧ UInt256.mk q.2 = v.stack[0]!) ↔ q = (v.env.codeOwner,v.stack[0]!.val) := by
        constructor
        · rintro ⟨ha,hk⟩
          exact Prod.ext ha (congrArg UInt256.val hk)
        · intro hq
          subst q
          exact ⟨rfl,rfl⟩
      simp only [he]
    calc
      _ = ∑ q : Slot, (if q = (v.env.codeOwner,v.stack[0]!.val) then eventDelta event else 0) :=
        Finset.sum_congr rfl (fun q _ => same q)
      _ = _ := by simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,hn,rfl⟩ := price
    simp only [keyDelta,hs,false_and,if_false,eventDelta,Finset.sum_const_zero]

theorem action_balance {kind : Kind} {p : Parent} {instr : Instruction} {v next : View}
    {w : Warm} {event : Event} (action : ReferenceRuntimeAction.Action kind p instr v next)
    (price : Price p v w next instr.1 event) :
    eventDelta event = totalPotential p next.storage-totalPotential p v.storage := by
  classical
  calc
    eventDelta event = ∑ q : Slot, keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray := (delta_sum price).symm
    _ = ∑ q : Slot, (slotPotential p next.storage q.1 (UInt256.mk q.2).toByteArray-
        slotPotential p v.storage q.1 (UInt256.mk q.2).toByteArray) := by
      apply Finset.sum_congr rfl
      intro q _
      exact action_delta action price _ _
    _ = _ := Finset.sum_sub_distrib _ _

/-- The actual finite runtime supplies its exact signed state-charge balance.
Readings for an arbitrary unlinked event list would not prove this theorem. -/
theorem of_coupled {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events) :
    (events.map eventDelta).sum = totalPotential p finish.storage-totalPotential p v.storage := by
  induction h with
  | refl => simp only [List.map_nil,List.sum_nil,sub_self]
  | cons actual decoded related nextRelated warm created action readings price tail ih =>
    simp only [List.map_cons,List.sum_cons,action_balance action price]
    omega

/-- Exact empty storage/created/read projection of a fresh source TransactionState. -/
def emptyTx : Tx := {writes := fun _ _ => none, created := ∅, reads := ∅}

theorem empty_potential (p : Parent) : totalPotential p emptyTx = 0 := by
  classical
  unfold totalPotential
  apply Finset.sum_eq_zero
  intro q _
  simp [slotPotential,emptyTx,original,current,ReferenceStoragePotential.potential]

theorem nonnegative (p : Parent) (tx : Tx) : 0 ≤ totalPotential p tx := by
  classical
  apply Finset.sum_nonneg
  intro q _
  unfold slotPotential ReferenceStoragePotential.potential
  split <;> omega

/-- Fresh-transaction storage is a concrete sufficient initial case. This does
not assert that arbitrary nested frames start with empty transaction overlays. -/
theorem from_empty {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (initial : v.storage = emptyTx) : 0 ≤ (events.map eventDelta).sum := by
  rw [of_coupled h,initial,empty_potential,sub_zero]
  exact nonnegative p finish.storage

#print axioms action_balance
#print axioms of_coupled
#print axioms empty_potential
#print axioms nonnegative
#print axioms from_empty
end Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance
