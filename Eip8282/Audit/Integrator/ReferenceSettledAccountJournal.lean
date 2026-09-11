import Eip8282.Audit.Integrator.ReferenceFullGasTotal

/-! Account/code/transient settlement uses the same receipt error as storage
settlement. The source execution does not modify account writes in these pinned
runtimes. Balances and protected code hash below are derived from actual entry
and the actual evaluator, not assumed at a post-execution checkpoint. -/
namespace Eip8282.Audit.Integrator.ReferenceSettledAccountJournal
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding
open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def journal {Hash : Type} (snapshot entered : Tx Hash)
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) : Tx Hash :=
  let live := {entered with accounts := finalAccounts}
  let accountsSettled := if receipt.error.isNone then live else ReferenceTransferredFailure.restore live snapshot
  {accountsSettled with storage := receipt.storage}

theorem storage {Hash : Type} (snapshot entered : Tx Hash)
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) :
    (journal snapshot entered finalAccounts receipt).storage = receipt.storage := rfl

theorem balances {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (snapshot entered : Tx Hash) (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) (beforeWorld entryWorld : AccountMap .EVM)
    (beforeRelated : BalancesRelated emptyHash parent snapshot beforeWorld)
    (entryRelated : BalancesRelated emptyHash parent entered entryWorld)
    (writes : finalAccounts.writes = entered.accounts.writes) :
    BalancesRelated emptyHash parent (journal snapshot entered finalAccounts receipt)
      (if receipt.error.isNone then entryWorld else beforeWorld) := by
  unfold journal
  dsimp only
  split
  · exact ReferenceSourceBalanceOutcome.same_writes emptyHash parent entered _ entryWorld entryRelated writes
  · exact ReferenceSourceBalanceOutcome.same_writes emptyHash parent snapshot _ beforeWorld beforeRelated rfl

theorem hash {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (snapshot entered : Tx Hash) (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) (address : AccountAddress)
    (writes : finalAccounts.writes = entered.accounts.writes)
    (same : hashAt emptyHash parent entered address = hashAt emptyHash parent snapshot address) :
    hashAt emptyHash parent (journal snapshot entered finalAccounts receipt) address =
      hashAt emptyHash parent snapshot address := by
  unfold journal
  dsimp only
  split
  · unfold hashAt account ReferenceAccountLookup.peek
    rw [writes]
    exact same
  · rfl

theorem derived {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender) (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (accountsParent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent before.accounts codeParent before.codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (related : BalancesRelated emptyHash accountsParent before tx.world)
    {events core finalAccounts}
    (actual : ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent = some ((events,core),finalAccounts))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) :
    (∀ a, (account emptyHash accountsParent
      (journal (prepaid emptyHash accountsParent before tx).2
        (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts receipt) a).balance.toNat ≤
      TransferFunding.worldFunds tx.checkpoint) ∧
    hashAt emptyHash accountsParent
      (journal (prepaid emptyHash accountsParent before tx).2
        (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts receipt)
        (ReachableCalls.address kind) ≠ emptyHash := by
  have admission := (ReferenceAllocatedEntry.admission checks found nonblob).1
  have domain := ReferenceCheckpointCall.domain kind tx history admission
  have paid := ReferenceSourcePrepaidCheckpoint.balances emptyHash accountsParent before tx admission nonblob related
  have entryEq := ReferenceAllocatedEntry.entered_eq emptyHash accountsParent before tx kind codeParent checks found nonblob related loaded
  have entryBalances : BalancesRelated emptyHash accountsParent
      (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 (call kind tx).entryWorld := by
    rw [entryEq]
    exact ReferenceSourceBalanceTransport.enter_balances emptyHash accountsParent
      (ReferenceTransferredFailure.fetched emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2 codeParent (call kind tx).target)
      (call kind tx) true paid domain.2.2.1 domain.2.2.2 (Or.inl rfl)
  have writes := ReferenceCheckedAccountEvaluator.writes actual
  have current := balances emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts receipt
    tx.checkpoint (call kind tx).entryWorld paid entryBalances writes
  have entryFunds := TransferFunding.entry_funds_le (call kind tx) domain.2.2.1
  refine ⟨?_,?_⟩
  · intro a
    rw [current a]
    split
    · exact (TransferFunding.balance_le_funds _ a).trans entryFunds
    · exact TransferFunding.balance_le_funds _ a
  · have loadedPaid := (ReferenceSourcePrepaidCheckpoint.loaded emptyHash accountsParent before tx codeParent
      (ReachableCalls.address kind) admission nonblob related).trans loaded
    have notEmpty : (call kind tx).code ≠ ByteArray.empty := by
      change ReachableCalls.runtime kind ≠ ByteArray.empty
      cases kind <;> decide
    have original := ReferenceSourceValueTransfer.loaded_nonempty_hash emptyHash accountsParent
      (prepaid emptyHash accountsParent before tx).2 codeParent (ReachableCalls.address kind) loadedPaid notEmpty
    rw [hash emptyHash accountsParent _ _ finalAccounts receipt _ writes]
    · exact original
    · rw [entryEq]
      exact ReferenceSourceValueTransfer.enter_hash emptyHash accountsParent _ _ _ _ _ _

#print axioms storage
#print axioms balances
#print axioms hash
#print axioms derived
end Eip8282.Audit.Integrator.ReferenceSettledAccountJournal
