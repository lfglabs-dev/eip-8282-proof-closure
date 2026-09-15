import Eip8282.Audit.Integrator.Topics.Reference3

/-! Refund provenance on actual linked storage writes. A fresh transaction
cannot start with an outstanding clear-slot refund. The literal source counter
is signed internally and converted to U256 at the top-level boundary; bounds
below are derived, not a silent clamp/modulo. Consumer: full gas settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedRefund
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

noncomputable def potential (original current : UInt256) : Int :=
  if original ≠ ⟨0⟩ ∧ current = ⟨0⟩ then 11616 else 0

theorem class_bounds (warm : Bool) (original current new : UInt256) :
    potential original new-potential original current ≤ (ReferenceStorageGas.classify warm original current new).refundDelta ∧
    (ReferenceStorageGas.classify warm original current new).refundDelta ≤ 21616 := by
  classical
  by_cases ho : original = ⟨0⟩ <;> by_cases hc : current = ⟨0⟩ <;> by_cases hn : new = ⟨0⟩ <;>
    by_cases he : current = new <;> by_cases hr : original = new <;>
    simp_all [potential,ReferenceStorageGas.classify] <;> omega

def delta : Event → Int
  | .ordinary _ => 0
  | .store warm original current new => (ReferenceStorageGas.classify warm original current new).refundDelta

noncomputable def slotPotential (p : Parent) (tx : Tx) (a : AccountAddress) (key : ByteArray) : Int :=
  potential (original p tx a key) (current p tx a key)

abbrev Slot := ReferenceRuntimeStateBalance.Slot
noncomputable local instance symbolicSlots : Fintype Slot := Fintype.ofFinite Slot
noncomputable def totalPotential (p : Parent) (tx : Tx) : Int :=
  ∑ q : Slot, slotPotential p tx q.1 (UInt256.mk q.2).toByteArray

noncomputable def keyDelta (instr : Instruction) (v : View) (event : Event) (a : AccountAddress) (key : ByteArray) : Int :=
  if instr.1 = .SSTORE ∧ a = v.env.codeOwner ∧ key = v.stack[0]!.toByteArray then delta event else 0

private theorem store_potential (p : Parent) (tx : Tx) (owner a : AccountAddress) (key value : UInt256) (query : ByteArray) :
    slotPotential p (ReferenceStorageStep.storeView tx owner key value) a query =
      if a = owner ∧ query = key.toByteArray then potential (original p tx a query) value else slotPotential p tx a query := by
  classical
  unfold slotPotential ReferenceStorageStep.storeView
  have same : original p (write (readTracked tx owner key.toByteArray) owner key.toByteArray value) a query = original p tx a query := rfl
  rw [same,write_read,tracked_read]
  split <;> rfl

private theorem action_lower {kind : Eip8282.Audit.Model.Kind} {p : Parent} {instr : Instruction} {v next : View} {w : Warm} {event : Event}
    (action : ReferenceRuntimeAction.Action kind p instr v next) (price : Price p v w next instr.1 event) (a : AccountAddress) (key : ByteArray) :
    slotPotential p next.storage a key-slotPotential p v.storage a key ≤ keyDelta instr v event a key := by
  classical
  cases action with
  | copy => simp [keyDelta,ReferenceCalldataCopy.copyAction,slotPotential]
  | log => simp [keyDelta,ReferenceLogView.logAction,slotPotential]
  | base action =>
    cases action with
    | pure hp =>
      have storage := ReferenceActionMetadata.pure_storage hp
      have hn : instr.1 ≠ .SSTORE := by
        intro he
        unfold ReferencePureAction.action at hp
        rw [he] at hp
        simp [ReferencePureAction.classify] at hp
      rw [storage]
      simp [keyDelta,hn]
    | @load v slot rest shape =>
      have same : slotPotential p (loadAction p v slot rest).storage a key = slotPotential p v.storage a key := rfl
      rw [same]
      simp [keyDelta]
    | word => simp [keyDelta,memoryAction,slotPotential]
    | byte => simp [keyDelta,memoryAction,slotPotential]
    | @store v slot value rest permission shape =>
      simp only [Price,if_true] at price
      obtain ⟨_,rfl⟩ := price
      change slotPotential p (ReferenceStorageStep.storeView v.storage v.env.codeOwner slot value) a key-_ ≤ keyDelta (.SSTORE,none) v _ a key
      rw [store_potential]
      simp only [keyDelta,shape,List.getElem!_cons_zero,true_and]
      by_cases same : a = v.env.codeOwner ∧ key = slot.toByteArray
      · rw [if_pos same,if_pos same]
        rcases same with ⟨rfl,rfl⟩
        simp only [delta,slotPotential,sourceReading,shape,List.getElem!_cons_zero,List.getElem!_cons_succ]
        exact (class_bounds _ _ _ _).1
      · rw [if_neg same,if_neg same]
        omega

private theorem delta_sum {p : Parent} {v next : View} {w : Warm} {instr : Instruction} {event : Event}
    (price : Price p v w next instr.1 event) :
    (∑ q : Slot, keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray) = delta event := by
  classical
  by_cases hs : instr.1 = .SSTORE
  · have same (q : Slot) : keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray =
        if q = (v.env.codeOwner,v.stack[0]!.val) then delta event else 0 := by
      unfold keyDelta
      simp only [hs,true_and,ReferenceStorageView.key_injective.eq_iff]
      have he : (q.1 = v.env.codeOwner ∧ UInt256.mk q.2 = v.stack[0]!) ↔ q = (v.env.codeOwner,v.stack[0]!.val) := by
        constructor
        · rintro ⟨ha,hk⟩; exact Prod.ext ha (congrArg UInt256.val hk)
        · intro hq; subst q; exact ⟨rfl,rfl⟩
      simp only [he]
    calc
      _ = ∑ q : Slot, (if q = (v.env.codeOwner,v.stack[0]!.val) then delta event else 0) := Finset.sum_congr rfl (fun q _ => same q)
      _ = _ := by simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,_,rfl⟩ := price
    simp only [keyDelta,hs,false_and,if_false,delta,Finset.sum_const_zero]

theorem action_balance {kind : Eip8282.Audit.Model.Kind} {p : Parent} {instr : Instruction} {v next : View} {w : Warm} {event : Event}
    (action : ReferenceRuntimeAction.Action kind p instr v next) (price : Price p v w next instr.1 event) :
    totalPotential p next.storage-totalPotential p v.storage ≤ delta event := by
  classical
  rw [←delta_sum price]
  unfold totalPotential
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro q _
  exact action_lower action price _ _

theorem source_balance {kind : Eip8282.Audit.Model.Kind} {p : Parent} {v finish : View} {w fw : Warm} {events : List Event}
    (actual : ReferenceSourceReplayTrace.Run kind p v w finish fw events) :
    totalPotential p finish.storage-totalPotential p v.storage ≤ (events.map delta).sum := by
  induction actual with
  | refl => simp
  | cons effect price stack tail ih =>
    have step := action_balance effect price
    simp only [List.map_cons,List.sum_cons]
    omega

theorem empty_potential (p : Parent) : totalPotential p ReferenceRuntimeStateBalance.emptyTx = 0 := by
  classical
  unfold totalPotential
  apply Finset.sum_eq_zero
  intro q _
  simp [slotPotential,ReferenceRuntimeStateBalance.emptyTx,original,current,potential]

theorem nonnegative (p : Parent) (tx : Tx) : 0 ≤ totalPotential p tx := by
  classical
  apply Finset.sum_nonneg
  intro q _
  unfold slotPotential potential
  split <;> omega

theorem delta_upper (events : List Event) : (events.map delta).sum ≤ 21616*events.length := by
  induction events with
  | nil => simp
  | cons event events ih =>
    have bound : delta event ≤ 21616 := by
      cases event with
      | ordinary => simp [delta]
      | store warm original current new => exact (class_bounds warm original current new).2
    simp only [List.map_cons,List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one]
    omega

#print axioms class_bounds
#print axioms action_balance
#print axioms source_balance
#print axioms empty_potential
#print axioms nonnegative
#print axioms delta_upper
end Eip8282.Audit.Integrator.ReferenceCheckedRefund
