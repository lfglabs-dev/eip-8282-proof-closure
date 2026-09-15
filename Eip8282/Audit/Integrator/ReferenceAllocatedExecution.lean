import Eip8282.Audit.Integrator.ReferenceAllocatedGuarantees
import Eip8282.Audit.Integrator.Topics.ReferenceAllocated
import Eip8282.Audit.Integrator.Topics.Reference2

/-! Concrete allocated entry supplies finite computational completion and
exhaustive supported outcomes. It is not unconditional EVM success: revert and
resource failure remain real outcomes. Consumer: one exhaustive allocated-call
certificate composing the previous same-outcome guarantee/rollback results. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedExecution
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback
open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem code (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) :
    (call kind tx).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> rfl

def frame (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) :=
  CallBridge.codeCall (call kind tx) (code kind tx) 0

def fuel (tx : RefundAccounting.Context) : Nat :=
  ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter tx)+1

noncomputable def run {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (parent : ReferenceStorageView.Parent) :=
  ReferenceCheckedAccountEvaluator.eval accountsParent
    (ReferenceInitialAccess.destinations (call kind tx).code) parent ByteArray.empty (fuel tx)
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts
    (initial (frame kind tx) (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage)
    (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx)

theorem prepared {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent before.accounts codeParent before.codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before tx.world)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray = SystemSpec.worldSlot tx.world (call kind tx).target q) :
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).1 = .ok () ∧
    ReferenceStorageView.Related parent (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage (frame kind tx).entry.toState ∧
    SystemSpec.HasOwner (frame kind tx).entry.toState := by
  have admission := (ReferenceAllocatedEntry.admission checks found nonblob).1
  have facts := ReferenceCheckpointCall.domain kind tx history admission
  have source := ReferenceSourcePrepaidCheckpoint.bindings emptyHash accountsParent before tx kind codeParent parent admission nonblob balances loaded slots
  have ready := ReferenceSourcePreparedBounds.prepared (call kind tx) (show ReleaseCandidate.CallInput kind (call kind tx) from ⟨rfl,rfl,rfl⟩)
    facts.2.2.2 emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2 codeParent true parent
    source.2.1 source.2.2.1 facts.2.2.1 source.2.2.2
  rw [ReferenceAllocatedEntry.entered_eq emptyHash accountsParent before tx kind codeParent checks found nonblob balances loaded]
  exact ⟨ready.1,ready.2,TransferFrame.pinned_codeCall_hasOwner (call kind tx)
    (ReferenceCheckpointCall.pinned kind tx history admission) (code kind tx) 0⟩

/-- The gas potential determines sufficient computational fuel. No supplied
successful/final outcome or 256-iteration limit is needed. -/
theorem completed {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks tx)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent before.accounts codeParent before.codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before tx.world)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray = SystemSpec.worldSlot tx.world (call kind tx).target q) :
    ∃ events result finalAccounts,
      run kind tx emptyHash accountsParent before codeParent parent = some ((events,result),finalAccounts) ∧
      ReferenceSupportedOutcome.Finalized result := by
  have ready := prepared kind tx history checks found nonblob emptyHash accountsParent before codeParent parent loaded balances slots
  have admitted := ReferenceAllocatedEntry.admission checks found nonblob
  have allocation := ReferenceAllocatedEntry.allocated tx costs
  have cap : ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter tx) ≤ 30000000 := by omega
  have context := ReferenceInitialAccess.scanned_context kind tx
  have stack : (initial (frame kind tx) (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (frame kind tx) (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage) rfl
  have sufficient := ReferenceCheckedAccountEvaluator.sufficient (accountsParent := accountsParent)
    (accounts := (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts)
    (parent := parent) (output := ByteArray.empty) (warm := ReferenceInitialAccess.warm tx)
    context stack aligned (show ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter tx) < fuel tx from Nat.lt_succ_self _)
  change run kind tx emptyHash accountsParent before codeParent parent ≠ none at sufficient
  cases actual : run kind tx emptyHash accountsParent before codeParent parent with
  | none => exact False.elim (sufficient actual)
  | some pair =>
    rcases pair with ⟨⟨events,result⟩,finalAccounts⟩
    refine ⟨events,result,finalAccounts,rfl,?_⟩
    exact ReferenceSupportedOutcome.account_evaluated (frame kind tx) context actual ready.2.1 ready.2.2
      (ReferenceInitialAccess.related kind tx (code kind tx)) cap admitted.2

#print axioms prepared
#print axioms completed
end Eip8282.Audit.Integrator.ReferenceAllocatedExecution
