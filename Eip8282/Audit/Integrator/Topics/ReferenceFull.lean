import Eip8282.Audit.Integrator.ReferenceAllocatedTotal
import Eip8282.Audit.Integrator.Topics.ReferenceCall
import Eip8282.Audit.Integrator.Topics.Reference2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceFullLogExecution -/

/-! Literal current-frame transfer logs at the allocated ordinary transaction
entry, followed by the same account-aware runtime. Signature-to-source Keccak
binding remains external. The actual entry success is derived by the consumer.
There are no inherited logs in this top-level transaction frame. -/
namespace Eip8282.Audit.Integrator.ReferenceFullLogExecution
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceCheckpointCall (call)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def emitted (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256) : List LogEntry :=
  ReferenceCallEntry.logs (call kind tx) true signature

def initial (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256) (storage : ReferenceStorageView.Tx) : View :=
  {ReferenceRuntimeView.initial (ReferenceAllocatedExecution.frame kind tx) storage with logs := emitted kind tx signature}

theorem fresh (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (storage : ReferenceStorageView.Tx) :
    (ReferenceRuntimeView.initial (ReferenceAllocatedExecution.frame kind tx) storage).logs = [] := rfl

theorem initial_eq (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256) (storage : ReferenceStorageView.Tx) :
    initial kind tx signature storage = ReferenceLogPrefixHandlers.view (emitted kind tx signature)
      (ReferenceRuntimeView.initial (ReferenceAllocatedExecution.frame kind tx) storage) := by
  simp only [initial,ReferenceLogPrefixHandlers.view,fresh,List.append_nil]

noncomputable def run {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (parent : ReferenceStorageView.Parent) :=
  ReferenceCheckedAccountEvaluator.eval accountsParent
    (ReferenceInitialAccess.destinations (call kind tx).code) parent ByteArray.empty (ReferenceAllocatedExecution.fuel tx)
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts
    (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage)
    (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx)

theorem transport {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent) :
    run kind tx signature emptyHash accountsParent before codeParent parent =
      (ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent).map
        (ReferenceLogPrefixEvaluation.evaluated (emitted kind tx signature)) := by
  unfold run ReferenceAllocatedExecution.run
  rw [initial_eq,ReferenceLogPrefixEvaluation.eval]

theorem extracted {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    {events : List ReferenceMeterPath.Event} {result : Outcome}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (actual : run kind tx signature emptyHash accountsParent before codeParent parent = some ((events,result),finalAccounts)) :
    ∃ finish finalWarm final,
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) parent
        (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage)
        (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx) finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind tx).code)
        (ReferenceAccountLookup.peek accountsParent (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts (ReachableCalls.address kind)).isSome
        parent finish finalWarm final ByteArray.empty = result ∧ ReferenceCheckedEvaluator.Ended result := by
  have context := ReferenceInitialAccess.scanned_context kind tx
  have stack : (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage).stack.length ≤ 1024 := by simp [initial,ReferenceRuntimeView.initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage) rfl
  have checked := (ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned).1
  exact ReferenceCheckedEvaluator.extract context checked

#print axioms fresh
#print axioms initial_eq
#print axioms transport
#print axioms extracted
end Eip8282.Audit.Integrator.ReferenceFullLogExecution

end

section

/-! ## ReferenceFullLogTotal -/

/-! Same full-frame execution, same source gas events, and the three allocated
claims, with the emitted transfer LOG3 included before runtime LOG0s. Neither
an endpoint nor successful execution is assumed. The computed full trace
supplies settlement warmth; caught failure and REVERT discard the whole local
log contribution. Parent eligibility is not ancestor or canonical commitment.
The old synthetic replay gas is still distinct from this actual source meter.
-/
namespace Eip8282.Audit.Integrator.ReferenceFullLogTotal
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceCheckpointCall (call)
open ReferenceFullLogExecution (emitted initial run)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
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
    ReferenceAllocatedTotal.Started kind tx emptyHash accountsParent before codeParent ∧
    ∃ events core finalAccounts finish finalWarm final,
      ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent = some ((events,core),finalAccounts) ∧
      ReferenceAllocatedTotal.Result kind tx emptyHash accountsParent before codeParent parent events finalAccounts core ∧
      run kind tx signature emptyHash accountsParent before codeParent parent =
        some ((events,ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core),finalAccounts) ∧
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) parent
        (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage)
        (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx) finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind tx).code)
        (ReferenceAccountLookup.peek accountsParent (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts (ReachableCalls.address kind)).isSome
        parent finish finalWarm final ByteArray.empty = ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core ∧
      ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm
        (ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core) =
        ReferenceLogPrefixSettlement.boundary (emitted kind tx signature)
          (ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm core) ∧
      ReferenceTransferLogs.project (ReachableCalls.address kind) (emitted kind tx signature) = [] := by
  obtain ⟨started,events,core,finalAccounts,actual,claims⟩ := ReferenceAllocatedTotal.verified kind tx history checks found recipient nonblob costs
    emptyHash accountsParent before codeParent parent loaded balances slots
  have full : run kind tx signature emptyHash accountsParent before codeParent parent =
      some ((events,ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core),finalAccounts) := by
    rw [ReferenceFullLogExecution.transport,actual]
    rfl
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceFullLogExecution.extracted kind tx signature emptyHash accountsParent before codeParent parent full
  exact ⟨started,events,core,finalAccounts,finish,finalWarm,final,actual,claims,full,trace,last,
    ReferenceLogPrefixSettlement.settled ..,ReferenceCallEntry.protected_logs kind (call kind tx) true signature⟩

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceFullLogTotal

end
