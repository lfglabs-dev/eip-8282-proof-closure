import Eip8282.Audit.Integrator.ReferenceAllocatedExecution

/-! Exhaustive same-run allocated-call certificate. No final outcome, successful
execution or abstract-model agreement is an input. The gas-potential fuel
producer yields an actual computed outcome; reachable-site coverage excludes
unsupported and continued results. Terminal/EOF supply the same three predicates
and source settled balances; exceptional failures supply exact local rollback.
All source/extraction/protocol domains of allocated-entry APIs remain explicit. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedTotal
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
open ReferenceTransferredFailure (fetched restore)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def Started {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) : Prop :=
    ReferenceSourceDispatch.probe emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2 codeParent
      (ReachableCalls.address kind) tx.transaction.base.value =
      (.ready (ReachableCalls.runtime kind),fetched emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2 codeParent (ReachableCalls.address kind)) ∧
    ReferenceAllocatedEntry.zeroBytes tx.transaction.base.data ≤ tx.transaction.base.data.size ∧
    ReferenceAllocatedEntry.intrinsic tx+(ReferenceAllocatedEntry.meter tx).execution+
      (ReferenceAllocatedEntry.meter tx).reservoir = tx.transaction.base.gasLimit.toNat ∧
    ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter tx) ≤ 16777216 ∧
    (prepaid emptyHash accountsParent before tx).1 = .ok () ∧
    TransactionEventBounds.request tx = .theta tx.fuel
      (TransactionEventBounds.message tx (ReachableCalls.address kind)) ∧
    (0 < tx.fuel → (call kind tx).result =
      (NestedEvents.Request.theta tx.fuel (TransactionEventBounds.message tx (ReachableCalls.address kind))).eval) ∧
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).1 = .ok ()

def Result {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (parent : ReferenceStorageView.Parent) (events : List ReferenceMeterPath.Event)
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)) : Outcome → Prop
  | .terminal result =>
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 with accounts := finalAccounts, storage := result.view.storage}
      kind (call kind tx) parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 with accounts := finalAccounts} (call kind tx).entryWorld
  | .eof view _finalWarm _final output =>
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 with accounts := finalAccounts, storage := view.storage}
      kind (call kind tx) parent events view true output ∧ finalAccounts.writes = (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 with accounts := finalAccounts} (call kind tx).entryWorld
  | .failed fault view partialWarm partialMeter output =>
    let live := {(ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live (prepaid emptyHash accountsParent before tx).2
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent restored (call kind tx).world ∧
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle (prepaid emptyHash accountsParent before tx).2.storage [] (ReferenceInitialAccess.warm tx) (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = (prepaid emptyHash accountsParent before tx).2.accounts.writes ∧
      restored.codeWrites = (prepaid emptyHash accountsParent before tx).2.codeWrites ∧ restored.transient = (prepaid emptyHash accountsParent before tx).2.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p (prepaid emptyHash accountsParent before tx).2.storage address key
  | .continued .. | .unsupported .. => False

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (recipient : tx.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks tx)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent before.accounts codeParent before.codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before tx.world)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray = SystemSpec.worldSlot tx.world (call kind tx).target q) :
    Started kind tx emptyHash accountsParent before codeParent ∧
    ∃ events result finalAccounts,
      ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent = some ((events,result),finalAccounts) ∧
      Result kind tx emptyHash accountsParent before codeParent parent events finalAccounts result := by
  have admitted := ReferenceAllocatedEntry.admission checks found nonblob
  have allocation := ReferenceAllocatedEntry.allocated tx costs
  have ready := ReferenceAllocatedExecution.prepared kind tx history checks found nonblob emptyHash accountsParent before codeParent parent loaded balances slots
  constructor
  · exact ⟨ReferenceAllocatedEntry.dispatched emptyHash accountsParent before tx kind codeParent checks found nonblob balances loaded,
      allocation.1,allocation.2.1,allocation.2.2,
      ReferenceSourcePrepaidCheckpoint.success emptyHash accountsParent before tx admitted.1 nonblob balances,
      ReferenceCheckpointCall.selected_request kind tx recipient,
      ReferenceCheckpointCall.call_result kind tx history admitted.1,ready.1⟩
  · obtain ⟨events,result,finalAccounts,actual,finalized⟩ := ReferenceAllocatedExecution.completed kind tx history checks found nonblob costs
      emptyHash accountsParent before codeParent parent loaded balances slots
    refine ⟨events,result,finalAccounts,actual,?_⟩
    cases result with
    | continued v w m e => exact False.elim finalized
    | unsupported tag v w m o => exact False.elim finalized
    | terminal result =>
      have h := ReferenceAllocatedGuarantees.terminal kind tx history checks found recipient nonblob costs emptyHash accountsParent before
        codeParent actual loaded balances slots
      exact h.2.2.2.2.2.2.2.2
    | eof view warm meter output =>
      have h := ReferenceAllocatedGuarantees.eof kind tx history checks found recipient nonblob costs emptyHash accountsParent before
        codeParent actual loaded balances slots
      exact h.2.2.2.2.2.2.2.2
    | failed fault view warm meter output =>
      have h := ReferenceAllocatedFailure.settled kind tx history checks found recipient nonblob costs emptyHash accountsParent before
        codeParent loaded balances actual slots
      exact h.2.2.2.2.2.2.2

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceAllocatedTotal
