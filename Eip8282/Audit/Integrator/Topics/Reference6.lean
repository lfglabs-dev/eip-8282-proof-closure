import Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
import Eip8282.Audit.Integrator.Topics.ReferenceCheckpoint
import Eip8282.Audit.Integrator.Topics.ReferencePrepaid
import Eip8282.Audit.Integrator.ReferenceStorageWarmth

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceInitialAccess -/

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

end

section

/-! ## ReferenceInitializedFailure -/

/-! Same prepaid call consumers with initial storage warmth constructed from
the represented access list and destinations scanned from pinned code. Transfer
mode is the literal True used by source create_evm. This specializes the old
mode-parametric APIs without claiming full source constructor equivalence:
dispatch/delegation, actual meter, concrete Python extraction and canonical
admission remain open. Logs remain protected-owner observations; source transfer
LOG3 at SYSTEM_ADDRESS is outside that projection. No resource identity or
termination is inferred. -/
namespace Eip8282.Audit.Integrator.ReferenceInitializedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> rfl

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {parent : ReferenceStorageView.Parent} {partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel
      (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.storage)
      (ReferenceInitialAccess.warm transaction) pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : (call kind transaction).calldata.size < UInt256.size) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    let live := {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live (prepaid emptyHash accountsParent before transaction).2
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent restored (call kind transaction).world ∧
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle (prepaid emptyHash accountsParent before transaction).2.storage [] (ReferenceInitialAccess.warm transaction) (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = (prepaid emptyHash accountsParent before transaction).2.accounts.writes ∧
      restored.codeWrites = (prepaid emptyHash accountsParent before transaction).2.codeWrites ∧ restored.transient = (prepaid emptyHash accountsParent before transaction).2.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p (prepaid emptyHash accountsParent before transaction).2.storage address key := by
  exact ReferencePrepaidFailure.settled kind transaction history admission recipient nonblob emptyHash accountsParent before
    codeParent true (ReferenceInitialAccess.scanned_context kind transaction) loaded balances actual slots
    (ReferenceInitialAccess.related kind transaction (code kind transaction)) grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceInitializedFailure

end

section

/-! ## ReferenceInitializedGuarantees -/

/-! Same prepaid call consumers with initial storage warmth constructed from
the represented access list and destinations scanned from pinned code. Transfer
mode is the literal True used by source create_evm. This specializes the old
mode-parametric APIs without claiming full source constructor equivalence:
dispatch/delegation, actual meter, concrete Python extraction and canonical
admission remain open. Logs remain protected-owner observations; source transfer
LOG3 at SYSTEM_ADDRESS is outside that projection. No resource identity or
termination is inferred. -/
namespace Eip8282.Audit.Integrator.ReferenceInitializedGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)


private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> rfl

theorem terminal {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.storage) (ReferenceInitialAccess.warm transaction) pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2 with accounts := finalAccounts, storage := result.view.storage}
      kind (call kind transaction) parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  exact ReferencePrepaidGuarantees.terminal kind transaction history admission recipient nonblob emptyHash accountsParent before
    codeParent true (ReferenceInitialAccess.scanned_context kind transaction) actual loaded balances
    (Or.inl rfl) slots (ReferenceInitialAccess.related kind transaction (code kind transaction)) grant fit

theorem eof {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.storage) (ReferenceInitialAccess.warm transaction) pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2 with accounts := finalAccounts, storage := view.storage}
      kind (call kind transaction) parent events view true output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent true).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  exact ReferencePrepaidGuarantees.eof kind transaction history admission recipient nonblob emptyHash accountsParent before
    codeParent true (ReferenceInitialAccess.scanned_context kind transaction) actual loaded balances
    (Or.inl rfl) slots (ReferenceInitialAccess.related kind transaction (code kind transaction)) grant fit

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceInitializedGuarantees

end
