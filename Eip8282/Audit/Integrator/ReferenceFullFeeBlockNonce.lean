import Eip8282.Audit.Integrator.ReferenceOrdinaryBlockNonce

/-! All three existing conditional claims, same execution/receipt/full logs/gas
and fee finalization, now with the final account nonce projection and checked
sender U64 conversion. Added domain: the initially observed source sender
nonce equals the old admitted sender nonce. This is a representation condition,
not a final-state or successful incorporation assumption. Other account payload
bindings and full block incorporation remain outside this theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceFullFeeBlockNonce
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
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray = SystemSpec.worldSlot tx.world (call kind tx).target q)
    (fresh : before.storage = ReferenceRuntimeStateBalance.emptyTx)
    (sourceNonce : (ReferenceSourceValueTransfer.account emptyHash accountsParent before tx.sender).nonce = sender.nonce.toNat) :
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
      ReferenceTransferLogs.project (ReachableCalls.address kind) (emitted kind tx signature) = [] ∧
      ∃ receipt, ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm
          (ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core) = .returned receipt ∧
        ReferenceTransactionSettlement.Facts tx.transaction.base.gasLimit.toNat (ReferenceAdmissionExtraction.calldataFloor tx.transaction tx.sender)
          (ReferenceTransactionGas.allocate tx.transaction.base.gasLimit.toNat (ReferenceAllocatedEntry.intrinsic tx)).reservoir receipt.meter ∧
        ReferenceSourceFeeFinalization.Result emptyHash accountsParent
          (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2
          (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2
          finalAccounts tx receipt parent kind ∧
        let finished := (ReferenceSourceFeeFinalization.finish emptyHash accountsParent
          (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2
          (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts tx receipt).2
        (∀ a, (ReferenceSourceValueTransfer.account emptyHash accountsParent finished a).nonce =
          (ReferenceSourceValueTransfer.account emptyHash accountsParent before a).nonce + (if a = tx.sender then 1 else 0)) ∧
        ReferenceOrdinaryBlockNonce.checkedNonce
          (ReferenceSourceValueTransfer.account emptyHash accountsParent finished tx.sender).nonce =
          some (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)) ∧
        (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)).toNat = tx.transaction.base.nonce.toNat+1 := by
  obtain ⟨started,events,core,finalAccounts,finish,finalWarm,final,actual,claims,full,trace,last,logs,projection,receipt,settled,facts,fees⟩ :=
    ReferenceFullFeeTotal.verified kind tx signature history checks found recipient nonblob costs emptyHash accountsParent before codeParent parent loaded balances slots fresh
  have nonces := ReferenceOrdinaryBlockNonce.actual kind tx checks found nonblob emptyHash accountsParent before codeParent parent loaded balances actual receipt
  have converted := ReferenceOrdinaryBlockNonce.admitted_nonce emptyHash accountsParent before tx checks sourceNonce
  refine ⟨started,events,core,finalAccounts,finish,finalWarm,final,actual,claims,full,trace,last,logs,projection,receipt,settled,facts,fees,nonces,?_,converted.2⟩
  rw [nonces tx.sender,if_pos rfl]
  exact converted.1

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceFullFeeBlockNonce
