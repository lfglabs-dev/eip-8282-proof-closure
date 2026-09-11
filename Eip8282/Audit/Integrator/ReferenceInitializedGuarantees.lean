import Eip8282.Audit.Integrator.ReferencePrepaidGuarantees
import Eip8282.Audit.Integrator.ReferenceInitialAccess

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
