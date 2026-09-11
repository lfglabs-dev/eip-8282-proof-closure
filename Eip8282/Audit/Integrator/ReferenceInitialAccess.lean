import Eip8282.Audit.Integrator.ReferenceCheckpointCall
import Eip8282.Audit.Integrator.ReferenceStorageWarmth
import Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep

/-! Initial storage warmth from the represented transaction access list and
jump destinations from scanning the actual pinned code. EL0cc100eb fork.py
586-592 inserts each address/slot pair; interpreter.py162 copies that set and
221 scans resolved code. Byte serialization and Python/source extraction remain
explicit semantic boundaries. This proves the finite list/set producers, not
complete dispatch/delegation/gas construction. Consumers: initialized prepaid
terminal/EOF and failure APIs. -/
namespace Eip8282.Audit.Integrator.ReferenceInitialAccess
open EvmYul EvmYul.EVM
open ReferenceSourceReadings
open ReferenceCheckpointCall (call)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Exactly the pairs inserted by the access-list nested loop. -/
def keys (tx : RefundAccounting.Context) : List (AccountAddress × UInt256) := do
  let (a, slots) ← tx.transaction.getAccessList
  let k ← slots.toList
  pure (a,k)

def warmOfKeys (ks : List (AccountAddress × UInt256)) : Warm :=
  {p | p ∈ ks.map (fun (a,k) => (a,k.toByteArray))}

def warm (tx : RefundAccounting.Context) : Warm := warmOfKeys (keys tx)

private local instance : LawfulBEq UInt256 where
  eq_of_beq := by
    intro a b h
    cases a with | mk a =>
    cases b with | mk b =>
    exact congrArg UInt256.mk (beq_iff_eq.mp h)
  rfl := by
    intro a
    cases a with
    | mk v =>
      change (v == v) = true
      exact beq_self_eq_true v

private theorem word_compare (a b : UInt256) : compare a b = compare a.val b.val := by
  cases a with | mk a =>
    cases b with | mk b =>
      change (compare a b).then .eq = compare a b
      cases compare a b <;> rfl

private instance : Std.TransCmp Substate.storageKeysCmp := by
  unfold Substate.storageKeysCmp
  infer_instance

private instance : Std.LawfulBEqCmp Substate.storageKeysCmp where
  compare_eq_iff_beq := by
    intro a b
    change (compare a.1 b.1).then (compare a.2 b.2) = .eq ↔ (a == b) = true
    rw [word_compare]
    simp only [Ordering.then_eq_eq,Std.compare_eq_iff_eq,beq_iff_eq]
    constructor
    · rintro ⟨ha,hk⟩
      exact Prod.ext ha (congrArg UInt256.mk hk)
    · intro h
      subst b
      exact ⟨rfl,rfl⟩

theorem warm_member (ks : List (AccountAddress × UInt256)) (a : AccountAddress) (k : UInt256) :
    (a,k.toByteArray) ∈ warmOfKeys ks ↔ (a,k) ∈ ks := by
  simp only [warmOfKeys,Set.mem_setOf_eq,List.mem_map]
  constructor
  · rintro ⟨⟨b,q⟩,hq,he⟩
    simp only [Prod.mk.injEq,ReferenceStorageView.key_injective.eq_iff] at he
    rcases he with ⟨rfl,rfl⟩
    exact hq
  · intro h
    exact ⟨(a,k),h,rfl⟩

theorem access_contains (tx : RefundAccounting.Context) (a : AccountAddress) (k : UInt256) :
    tx.entrySubstate.accessedStorageKeys.contains (a,k) = true ↔ (a,k) ∈ keys tx := by
  change (Std.TreeSet.ofList (keys tx) Substate.storageKeysCmp).contains (a,k) = true ↔ _
  rw [Std.TreeSet.contains_ofList,List.contains_iff_mem]

theorem related (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (code : (call kind tx).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind)) :
    WarmRelated (warm tx) (CallBridge.codeCall (call kind tx) code 0).entry := by
  intro a k
  change (a,k.toByteArray) ∈ warmOfKeys (keys tx) ↔ tx.entrySubstate.accessedStorageKeys.contains (a,k) = true
  rw [warm_member,access_contains]

/-- Run the existing source-shaped scanner, rather than request a matching table. -/
def destinations (bytes : ByteArray) : List Nat :=
  (ReferenceDecodeSites.scan bytes bytes.size 0).filter (fun pc => bytes[pc]? == some 0x5b)

theorem scanned_context (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) :
    ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind)
      (destinations (call kind tx).code) := by
  have hc : (call kind tx).code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference (JournalInvariant.modelKind kind)) := by cases kind <;> rfl
  unfold ReferenceCheckedStackControlStep.DestinationContext
  rw [hc]
  unfold destinations
  rw [ReferenceDecodeSites.scan_eq_sites]
  rfl

#print axioms warm_member
#print axioms access_contains
#print axioms related
#print axioms scanned_context
end Eip8282.Audit.Integrator.ReferenceInitialAccess
