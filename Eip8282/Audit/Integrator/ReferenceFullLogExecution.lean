import Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement
import Eip8282.Audit.Integrator.ReferenceAllocatedTotal
import Eip8282.Audit.Integrator.ReferenceCallEntry

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
