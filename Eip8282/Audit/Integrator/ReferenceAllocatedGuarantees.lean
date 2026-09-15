import Eip8282.Audit.Integrator.Topics.Reference6
import Eip8282.Audit.Integrator.Topics.ReferenceAllocated

/-! Same three-guarantee / failed-frame consumers from actual computed dispatch
read journal and source allocated meter. Selected source nonce/fee/floor checks
plus represented sender presence derive funding admission and calldata width.
Explicit intrinsic admission clauses justify every allocation subtraction.
The source constructor bridge remains scoped: represented nonblob call without
authorizations, pinned nondelegating code, protected-owner logs. No full Python
extraction, canonical admission/history, synthetic/source gas equality, global
ancestor commitment or guaranteed termination is claimed. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedGuarantees
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
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks transaction sender)
    (found : transaction.world.get? transaction.sender = some sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.storage) (ReferenceInitialAccess.warm transaction) (ReferenceAllocatedEntry.meter transaction) = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
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
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts, storage := result.view.storage}
      kind (call kind transaction) parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
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
  exact ReferenceInitializedGuarantees.terminal kind transaction history admitted.1 recipient nonblob emptyHash accountsParent before
    codeParent actual loaded balances slots bound admitted.2

theorem eof {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks transaction sender)
    (found : transaction.world.get? transaction.sender = some sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {finalWarm : Warm} {final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.storage) (ReferenceInitialAccess.warm transaction) (ReferenceAllocatedEntry.meter transaction) = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
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
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts, storage := view.storage}
      kind (call kind transaction) parent events view true output ∧ finalAccounts.writes = (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
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
  exact ReferenceInitializedGuarantees.eof kind transaction history admitted.1 recipient nonblob emptyHash accountsParent before
    codeParent actual loaded balances slots bound admitted.2

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceAllocatedGuarantees
