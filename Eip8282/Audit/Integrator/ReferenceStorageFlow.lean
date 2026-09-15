import Eip8282.Audit.Integrator.Topics.ReferenceStorage
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime

/-! Same-slot state-gas accounting is derived from literal source view actions
on the actual coupled runtime. Query keys select precisely their own SSTORE
charges. This concerns internal execution; enclosing rollback is separate. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageFlow
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

noncomputable def slotPotential (p : Parent) (tx : Tx) (a : AccountAddress) (key : ByteArray) : Int :=
  ReferenceStoragePotential.potential (original p tx a key) (current p tx a key)

def eventDelta : Event → Int
  | .ordinary _ => 0
  | .store warm original current new =>
    ((ReferenceStorageGas.classify warm original current new).state : Int)-
      (ReferenceStorageGas.classify warm original current new).stateRefund

noncomputable def keyDelta (instr : Instruction) (v : View) (event : Event)
    (a : AccountAddress) (key : ByteArray) : Int :=
  if instr.1 = .SSTORE ∧ a = v.env.codeOwner ∧ key = v.stack[0]!.toByteArray then eventDelta event else 0

private theorem store_potential (p : Parent) (tx : Tx) (owner a : AccountAddress)
    (key value : UInt256) (query : ByteArray) :
    slotPotential p (ReferenceStorageStep.storeView tx owner key value) a query =
      if a = owner ∧ query = key.toByteArray then ReferenceStoragePotential.potential (original p tx a query) value
      else slotPotential p tx a query := by
  classical
  unfold slotPotential ReferenceStorageStep.storeView
  have ho : original p (write (readTracked tx owner key.toByteArray) owner key.toByteArray value) a query =
      original p tx a query := rfl
  rw [ho,write_read,tracked_read]
  split <;> rfl

/-- The exact charged class is tied to the actual key/current/new storage
reading, not to an arbitrary independently chosen Event stream. -/
theorem action_delta {kind : Kind} {p : Parent} {instr : Instruction} {v next : View}
    {w : Warm} {event : Event} (action : ReferenceRuntimeAction.Action kind p instr v next)
    (price : Price p v w next instr.1 event) (a : AccountAddress) (key : ByteArray) :
    keyDelta instr v event a key = slotPotential p next.storage a key-slotPotential p v.storage a key := by
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
      simp only [Price,↓reduceIte] at price
      obtain ⟨_,rfl⟩ := price
      change keyDelta (.SSTORE,none) v _ a key =
        slotPotential p (ReferenceStorageStep.storeView v.storage v.env.codeOwner slot value) a key-_
      rw [store_potential]
      simp only [keyDelta,shape,List.getElem!_cons_zero,true_and]
      by_cases he : a = v.env.codeOwner ∧ key = slot.toByteArray
      · rw [if_pos he,if_pos he]
        rcases he with ⟨rfl,rfl⟩
        simp only [eventDelta,sourceReading,shape,List.getElem!_cons_zero,List.getElem!_cons_succ]
        exact ReferenceStoragePotential.step _ _ _ _
      · rw [if_neg he,if_neg he]
        omega

/-- A charge certificate retains the exact ordered source actions and prices
used by its actual Coupled producer. Each event contributes once to this key. -/
inductive Charges (kind : Kind) (p : Parent) (a : AccountAddress) (key : ByteArray) :
    View → List Event → View → List Int → Prop where
  | nil (v : View) : Charges kind p a key v [] v []
  | cons {instr : Instruction} {v next finish : View} {w : Warm}
      {event : Event} {events : List Event} {amounts : List Int}
      (action : ReferenceRuntimeAction.Action kind p instr v next)
      (price : Price p v w next instr.1 event)
      (tail : Charges kind p a key next events finish amounts) :
      Charges kind p a key v (event::events) finish (keyDelta instr v event a key::amounts)

theorem charges_balance {kind : Kind} {p : Parent} {a : AccountAddress} {key : ByteArray}
    {v finish : View} {events : List Event} {amounts : List Int}
    (h : Charges kind p a key v events finish amounts) :
    amounts.length = events.length ∧
      amounts.sum = slotPotential p finish.storage a key-slotPotential p v.storage a key := by
  induction h with
  | nil => simp
  | cons action price tail ih =>
    constructor
    · simp only [List.length_cons,ih.1]
    · simp only [List.sum_cons,action_delta action price]
      omega

/-- The arbitrary finite actual runtime supplies the ordered charge certificate
and its telescoped same-slot balance, without assuming a value chain. -/
theorem of_coupled {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (a : AccountAddress) (key : ByteArray) :
    ∃ amounts, Charges kind p a key v events finish amounts ∧ amounts.length = events.length ∧
      amounts.sum = slotPotential p finish.storage a key-slotPotential p v.storage a key := by
  have existsCharges : ∃ amounts, Charges kind p a key v events finish amounts := by
    induction h with
    | refl => exact ⟨[],.nil _⟩
    | cons actual decoded related nextRelated warm created action readings price tail ih =>
      obtain ⟨amounts,hm⟩ := ih
      exact ⟨_,.cons action price hm⟩
  obtain ⟨amounts,hm⟩ := existsCharges
  exact ⟨amounts,hm,charges_balance hm⟩

#print axioms action_delta
#print axioms charges_balance
#print axioms of_coupled
end Eip8282.Audit.Integrator.ReferenceStorageFlow
