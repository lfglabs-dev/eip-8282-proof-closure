import Eip8282.Audit.Integrator.ReferencePrepaidFailure
import Eip8282.Audit.Integrator.ReferenceInitialAccess

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
