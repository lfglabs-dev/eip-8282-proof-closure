import Eip8282.Audit.Integrator.ReferenceFullFeeBlockNonce

/-! Account writes and code hashes of the actual fee-finalized journal.
Consumer: ordinary block account enumeration and BAL incorporation. Finite
support is derived from the actual evaluator and initial journal, including
frame rollback and ordered credits. It is not an append-occurrence count. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccounts
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem modify_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256) (outside : address ≠ key) :
    (modifyBalance emptyHash parent tx key balance).accounts.writes address = tx.accounts.writes address := by
  unfold modifyBalance
  dsimp only
  split <;> simp only [writeAccount,if_neg outside,ReferenceAccountLookup.tracked]

private theorem paid_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender address : AccountAddress) (executionFee blobFee : Nat) (outside : address ≠ sender) :
    (ReferenceSourcePrepayment.pay emptyHash parent tx sender executionFee blobFee).2.accounts.writes address = tx.accounts.writes address := by
  unfold ReferenceSourcePrepayment.pay
  dsimp only
  split
  · split
    · rw [modify_outside _ _ _ _ _ _ outside,ReferenceSourcePrepayment.increment_form]
      simp only [writeAccount,if_neg outside]
      rfl
    · rw [ReferenceSourcePrepayment.increment_form]
      simp only [writeAccount,if_neg outside]
      rfl
  · rw [ReferenceSourcePrepayment.increment_form]
    simp only [writeAccount,if_neg outside]
    rfl

private theorem move_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256)
    (senderNe : address ≠ sender) (recipientNe : address ≠ recipient) :
    (move emptyHash parent tx sender recipient value).2.accounts.writes address = tx.accounts.writes address := by
  unfold move
  dsimp only
  split
  · split
    · rw [modify_outside _ _ _ _ _ _ recipientNe]
      change (modifyBalance emptyHash parent _ sender _).accounts.writes address = _
      rw [modify_outside _ _ _ _ _ _ senderNe]
      rfl
    · change (modifyBalance emptyHash parent _ sender _).accounts.writes address = _
      rw [modify_outside _ _ _ _ _ _ senderNe]
      rfl
  · rfl

private theorem enter_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) (transfer : Bool)
    (senderNe : address ≠ sender) (recipientNe : address ≠ recipient) :
    (enter emptyHash parent tx sender recipient value transfer).2.accounts.writes address = tx.accounts.writes address := by
  unfold enter
  split
  · exact move_outside emptyHash parent tx sender recipient address value senderNe recipientNe
  · rfl

private theorem credit_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256) (outside : address ≠ key) :
    (ReferenceSourceFeeCredit.credit emptyHash parent tx key amount).2.accounts.writes address = tx.accounts.writes address := by
  unfold ReferenceSourceFeeCredit.credit
  dsimp only
  split
  · rw [modify_outside _ _ _ _ _ _ outside]
    rfl
  · rfl

private theorem fees_outside {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (payer beneficiary address : AccountAddress) (price base : Nat)
    (gas : ReferenceTransactionGas.Settlement) (payerNe : address ≠ payer) (beneficiaryNe : address ≠ beneficiary) :
    (ReferenceSourceFeeDisbursement.run emptyHash parent tx payer beneficiary price base gas).2.accounts.writes address =
      tx.accounts.writes address := by
  unfold ReferenceSourceFeeDisbursement.run
  dsimp only
  split
  · split
    · split
      · exact credit_outside _ _ _ _ _ _ payerNe
      · split
        · split <;> rw [credit_outside _ _ _ _ _ _ beneficiaryNe,credit_outside _ _ _ _ _ _ payerNe]
        · exact credit_outside _ _ _ _ _ _ payerNe
    · rfl
  · rfl

/-- Both fee credits preserve all code hashes, including zero-value cleanup. -/
theorem fees_hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (payer beneficiary address : AccountAddress) (price base : Nat)
    (gas : ReferenceTransactionGas.Settlement) :
    hashAt emptyHash parent (ReferenceSourceFeeDisbursement.run emptyHash parent tx payer beneficiary price base gas).2 address =
      hashAt emptyHash parent tx address := by
  unfold ReferenceSourceFeeDisbursement.run
  dsimp only
  split
  · split
    · split
      · exact ReferenceSourceFeeCredit.hash _ _ _ _ _ _
      · split
        · split <;> rw [ReferenceSourceFeeCredit.hash,ReferenceSourceFeeCredit.hash]
        · exact ReferenceSourceFeeCredit.hash _ _ _ _ _ _
    · rfl
  · rfl

theorem fees_code {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (payer beneficiary : AccountAddress) (price base : Nat)
    (gas : ReferenceTransactionGas.Settlement) :
    (ReferenceSourceFeeDisbursement.run emptyHash parent tx payer beneficiary price base gas).2.codeWrites = tx.codeWrites := by
  unfold ReferenceSourceFeeDisbursement.run
  dsimp only
  split
  · split
    · split
      · exact (ReferenceSourceFeeCredit.fields _ _ _ _ _).1
      · split
        · split <;> rw [(ReferenceSourceFeeCredit.fields _ _ _ _ _).1,(ReferenceSourceFeeCredit.fields _ _ _ _ _).1]
        · exact (ReferenceSourceFeeCredit.fields _ _ _ _ _).1
    · rfl
  · rfl

theorem outside {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (storageParent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites
      (ReferenceCheckpointCall.call kind tx).target).1 = .ok (ReferenceCheckpointCall.call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash parent before tx.world)
    {events core finalAccounts}
    (execution : ReferenceAllocatedExecution.run kind tx emptyHash parent before codeParent storageParent = some ((events,core),finalAccounts))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) (address : AccountAddress) (senderNe : address ≠ tx.sender)
    (targetNe : address ≠ ReachableCalls.address kind) (beneficiaryNe : address ≠ tx.header.beneficiary) :
    (ReferenceSourceFeeFinalization.finish emptyHash parent
      (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 finalAccounts tx receipt).2.accounts.writes address =
      before.accounts.writes address := by
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash parent before tx kind codeParent checks found nonblob balances loaded
  have writes := ReferenceCheckedAccountEvaluator.writes execution
  have paid := paid_outside emptyHash parent before tx.sender address (ReferenceSourcePrepaidCheckpoint.executionFee tx) 0 senderNe
  have entryWrite : (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2.accounts.writes address = before.accounts.writes address := by
    rw [entered]
    unfold ReferenceTransferredFailure.entry
    exact (enter_outside emptyHash parent _ (ReferenceCheckpointCall.call kind tx).caller
      (ReferenceCheckpointCall.call kind tx).target address _ true senderNe targetNe).trans paid
  unfold ReferenceSourceFeeFinalization.finish
  rw [fees_outside _ _ _ _ _ _ _ _ _ senderNe beneficiaryNe]
  unfold ReferenceSettledAccountJournal.journal
  dsimp only
  split
  · rw [writes]
    exact entryWrite
  · exact paid

theorem hash {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (storageParent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites
      (ReferenceCheckpointCall.call kind tx).target).1 = .ok (ReferenceCheckpointCall.call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash parent before tx.world)
    {events core finalAccounts}
    (execution : ReferenceAllocatedExecution.run kind tx emptyHash parent before codeParent storageParent = some ((events,core),finalAccounts))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) (address : AccountAddress) :
    hashAt emptyHash parent (ReferenceSourceFeeFinalization.finish emptyHash parent
      (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 finalAccounts tx receipt).2 address =
      hashAt emptyHash parent before address := by
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash parent before tx kind codeParent checks found nonblob balances loaded
  have writes := ReferenceCheckedAccountEvaluator.writes execution
  have admitted := (ReferenceAllocatedEntry.admission checks found nonblob).1
  have funded := ReferenceSourcePrepaidCheckpoint.funded emptyHash parent before tx admitted nonblob balances
  unfold ReferenceSourceFeeFinalization.finish
  rw [fees_hash,ReferenceSettledAccountJournal.hash _ _ _ _ _ _ _ writes]
  · exact ReferenceSourcePrepayment.successful_hash emptyHash parent before tx.sender address _ 0 funded
  · rw [entered]
    exact enter_hash emptyHash parent _ _ _ address _ _

theorem code {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (storageParent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites
      (ReferenceCheckpointCall.call kind tx).target).1 = .ok (ReferenceCheckpointCall.call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash parent before tx.world)
    {events core finalAccounts}
    (execution : ReferenceAllocatedExecution.run kind tx emptyHash parent before codeParent storageParent = some ((events,core),finalAccounts))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) :
    (ReferenceSourceFeeFinalization.finish emptyHash parent
      (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 finalAccounts tx receipt).2.codeWrites = before.codeWrites := by
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash parent before tx kind codeParent checks found nonblob balances loaded
  have paid := (ReferenceSourcePrepaidCheckpoint.fields emptyHash parent before tx).2.1
  unfold ReferenceSourceFeeFinalization.finish
  rw [fees_code]
  unfold ReferenceSettledAccountJournal.journal
  dsimp only
  split
  · rw [entered]
    exact (enter_code emptyHash parent _ _ _ _ _).trans paid
  · exact paid

#print axioms fees_code
#print axioms code
#print axioms fees_hash
#print axioms outside
#print axioms hash
end Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccounts
