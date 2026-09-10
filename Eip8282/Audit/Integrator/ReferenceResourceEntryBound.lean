import Eip8282.Audit.Integrator.ReferenceExecutionLedger

/-! Potential bounds at nested entries of the literal resource ledger. This
relation retains actual ledger branches and grant equations, but is deliberately
NOT an occurrence identity: proofs are propositions, and no path uniqueness or
source frame coverage is asserted. Actual source tree extraction remains open.
No Selected premise, fixed internal cap, or net-state sign hypothesis occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceResourceEntryBound
open EvmYul
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCallGrant
open ReferenceChildMeter ReferenceCallChildBoundary ReferenceExecutionPotential
open ReferenceCallPotential ReferenceExecutionLedger
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual prior CALL charges cover the stipend before granting the child. -/
theorem call_entry {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre charged : Meter}
    (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
    (requested : UInt256) : potential (start (split hasValue requested charged)) ≤ potential pre := by
  have hp := prepared_debit prepared
  have hg := split_potential hasValue requested charged
  have ho := overhead_exact cold delegated delegationCold hasValue memoryCost
  have hi : potential (start (split hasValue requested charged)) =
      (split hasValue requested charged).childExecution := by simp [start,init,potential]
  omega

/-- State charging transfers between pools without creating execution potential. -/
theorem creation_entry {pre : Meter} {chargedCore : ReferenceStorageGas.Meter} {amount : Nat}
    (charged : ReferenceStorageGas.chargeState (core pre) amount = some chargedCore) :
    potential (start (creationSplit (update pre chargedCore))) ≤ potential pre := by
  have hp := state_preserves charged
  have hg := creation_potential (update pre chargedCore)
  omega

/-- A nested resource entry, with all surrounding ledger evidence retained.
This relation supports a numeric bound only; it does not identify unique nodes. -/
inductive EntryAt : Meter → Meter → Nat → Meter → Prop where
  | here {pre post : Meter} {work : Nat} (actual : Run pre post work) : EntryAt pre post work pre
  | left {pre mid post node : Meter} {first second : Nat}
      (head : EntryAt pre mid first node) (tail : Run mid post second) :
      EntryAt pre post (first+second) node
  | right {pre mid post node : Meter} {first second : Nat}
      (head : Run pre mid first) (tail : EntryAt mid post second node) :
      EntryAt pre post (first+second) node
  | call {pre charged child final node : Meter} {childWork : Nat}
      (cold delegated delegationCold hasValue deadRecipient : Bool) (memoryCost : Nat)
      (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
      (requested : UInt256) (outcome : Outcome)
      (body : EntryAt (start (split hasValue requested charged)) child childWork node)
      (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
      EntryAt pre final (overhead cold delegated delegationCold hasValue memoryCost+childWork) node
  | create {pre child final node : Meter} {chargedCore : ReferenceStorageGas.Meter} {childWork : Nat}
      (stateAmount : Nat) (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
      (outcome : Outcome) (newAccount : Bool)
      (body : EntryAt (start (creationSplit (update pre chargedCore))) child childWork node)
      (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
      EntryAt pre final childWork node

theorem EntryAt.sound_top {pre post node : Meter} {work : Nat} (h : EntryAt pre post work node) :
    Run pre post work := by
  induction h with
  | here actual => exact actual
  | left head tail ih => exact .trans ih tail
  | right head tail ih => exact .trans head ih
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact .call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome ih finished
  | create stateAmount charged outcome newAccount body finished ih =>
    exact .create stateAmount charged outcome newAccount ih finished

theorem EntryAt.potential_le {pre post node : Meter} {work : Nat} (h : EntryAt pre post work node) :
    potential node ≤ potential pre := by
  induction h with
  | here actual => exact Nat.le_refl _
  | left head tail ih => exact ih
  | right head tail ih =>
    have bound := bounded head
    omega
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact ih.trans (call_entry prepared requested)
  | create stateAmount charged outcome newAccount body finished ih =>
    exact ih.trans (creation_entry charged)

theorem EntryAt.cap {pre post node : Meter} {work cap : Nat} (h : EntryAt pre post work node)
    (bound : potential pre ≤ cap) : potential node ≤ cap := h.potential_le.trans bound

#print axioms call_entry
#print axioms creation_entry
#print axioms EntryAt.sound_top
#print axioms EntryAt.potential_le
#print axioms EntryAt.cap
end Eip8282.Audit.Integrator.ReferenceResourceEntryBound
