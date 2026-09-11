import Eip8282.Audit.Integrator.ReferenceInitializedFailure
import Eip8282.Audit.Integrator.ReferenceAllocatedEntry

/-! Same three-guarantee / failed-frame consumers from actual computed dispatch
read journal and source allocated meter. Selected source nonce/fee/floor checks
plus represented sender presence derive funding admission and calldata width.
Explicit intrinsic admission clauses justify every allocation subtraction.
The source constructor bridge remains scoped: represented nonblob call without
authorizations, pinned nondelegating code, protected-owner logs. No full Python
extraction, canonical admission/history, synthetic/source gas equality, global
ancestor commitment or guaranteed termination is claimed. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedFailure
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
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks transaction sender)
    (found : transaction.world.get? transaction.sender = some sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks transaction)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {parent : ReferenceStorageView.Parent} {partialWarm : Warm} {partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel
      (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.storage)
      (ReferenceInitialAccess.warm transaction) (ReferenceAllocatedEntry.meter transaction) = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    :
    ReferenceSourceDispatch.probe emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent
      (ReachableCalls.address kind) transaction.transaction.base.value =
      (.ready (ReachableCalls.runtime kind),fetched emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent (ReachableCalls.address kind)) ∧
    ReferenceAllocatedEntry.zeroBytes transaction.transaction.base.data ≤ transaction.transaction.base.data.size ∧
    ReferenceAllocatedEntry.intrinsic transaction+(ReferenceAllocatedEntry.meter transaction).execution+
      (ReferenceAllocatedEntry.meter transaction).reservoir = transaction.transaction.base.gasLimit.toNat ∧
    ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter transaction) ≤ 16777216 ∧
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    let live := {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts, storage := view.storage}
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
  have admitted := ReferenceAllocatedEntry.admission checks found nonblob
  have allocated := ReferenceAllocatedEntry.allocated transaction costs
  have dispatch := ReferenceAllocatedEntry.dispatched emptyHash accountsParent before transaction kind codeParent
    checks found nonblob balances loaded
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash accountsParent before transaction kind codeParent
    checks found nonblob balances loaded
  have bound : ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter transaction) ≤ 30000000 := by
    have cap := allocated.2.2
    omega
  rw [entered] at actual ⊢
  refine ⟨dispatch,allocated.1,allocated.2.1,allocated.2.2,?_⟩
  exact ReferenceInitializedFailure.settled kind transaction history admitted.1 recipient nonblob emptyHash accountsParent before
    codeParent loaded balances actual slots bound admitted.2

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceAllocatedFailure
