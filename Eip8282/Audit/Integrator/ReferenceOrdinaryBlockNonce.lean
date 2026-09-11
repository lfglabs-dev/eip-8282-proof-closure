import Eip8282.Audit.Integrator.ReferenceFullFeeTotal

/-! Nonce projection of the same ordinary source journal, consumed by
ReferenceFullFeeBlockNonce.verified and subsequent block account incorporation.
The new initial source nonce observation is distinct from balance correspondence.
No final nonce bound or successful block incorporation is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryBlockNonce
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem account_write {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (value : Option (ReferenceSourceValueTransfer.Account Hash)) :
    account emptyHash parent (writeAccount tx key value) address =
      if address = key then value.getD (empty emptyHash) else account emptyHash parent tx address := by
  classical
  by_cases same : address = key <;> simp [account,writeAccount,ReferenceAccountLookup.peek,same]

theorem modify {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256) :
    (account emptyHash parent (modifyBalance emptyHash parent tx key balance) address).nonce =
      (account emptyHash parent tx address).nonce := by
  classical
  unfold modifyBalance
  dsimp only
  split
  · rename_i deleted
    rw [account_write]
    by_cases same : address = key
    · subst address
      simpa only [if_true,Option.getD_none,empty] using deleted.1.symm
    · simp only [if_neg same]
      rfl
  · rw [account_write]
    by_cases same : address = key <;> simp only [same,if_true,if_false,Option.getD_some]
    rfl

/-- Includes both partially executed transfer errors, and aliases. -/
theorem transfer {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) :
    (account emptyHash parent (move emptyHash parent tx sender recipient value).2 address).nonce =
      (account emptyHash parent tx address).nonce := by
  unfold move
  dsimp only
  split
  · split
    · dsimp only
      rw [modify]
      change (account emptyHash parent (modifyBalance emptyHash parent _ sender _) address).nonce = _
      rw [modify]
      rfl
    · dsimp only
      change (account emptyHash parent (modifyBalance emptyHash parent _ sender _) address).nonce = _
      rw [modify]
      rfl
  · rfl

theorem entry {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool) :
    (account emptyHash parent (enter emptyHash parent tx sender recipient value shouldTransfer).2 address).nonce =
      (account emptyHash parent tx address).nonce := by
  unfold enter
  split
  · exact transfer emptyHash parent tx sender recipient address value
  · rfl

theorem credit {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256) :
    (account emptyHash parent (ReferenceSourceFeeCredit.credit emptyHash parent tx key amount).2 address).nonce =
      (account emptyHash parent tx address).nonce := by
  unfold ReferenceSourceFeeCredit.credit
  dsimp only
  split
  · rw [modify]
    rfl
  · rfl

/-- Ordered credits preserve nonce on success and on every partial error. -/
theorem disbursement {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (payer beneficiary address : AccountAddress) (price base : Nat)
    (gas : ReferenceTransactionGas.Settlement) :
    (account emptyHash parent (ReferenceSourceFeeDisbursement.run emptyHash parent tx payer beneficiary price base gas).2 address).nonce =
      (account emptyHash parent tx address).nonce := by
  unfold ReferenceSourceFeeDisbursement.run
  dsimp only
  split
  · split
    · split
      · exact credit emptyHash parent tx payer address _
      · split
        · split <;> rw [credit,credit]
        · exact credit emptyHash parent tx payer address _
    · rfl
  · rfl

/-- Settlement chooses the prepaid checkpoint on frame failure, so it does
not undo the transaction nonce increment. Runtime writes are obtained from
the very evaluator whose receipt is consumed, not an arbitrary final journal. -/
theorem actual {Hash Error : Type} [DecidableEq Hash]
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
    (account emptyHash parent (ReferenceSourceFeeFinalization.finish emptyHash parent
      (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 finalAccounts tx receipt).2 address).nonce =
      (account emptyHash parent before address).nonce + (if address = tx.sender then 1 else 0) := by
  have admitted := (ReferenceAllocatedEntry.admission checks found nonblob).1
  have funded := ReferenceSourcePrepaidCheckpoint.funded emptyHash parent before tx admitted nonblob balances
  have paid := (ReferenceSourcePrepayment.successful_account emptyHash parent before tx.sender address _ 0 funded).2
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash parent before tx kind codeParent checks found nonblob balances loaded
  have writes := ReferenceCheckedAccountEvaluator.writes execution
  unfold ReferenceSourceFeeFinalization.finish
  rw [disbursement]
  have settled : (account emptyHash parent (ReferenceSettledAccountJournal.journal
      (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 finalAccounts receipt) address).nonce =
      (account emptyHash parent (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash parent before tx).2 address).nonce := by
    unfold ReferenceSettledAccountJournal.journal
    dsimp only
    split
    · have same : account emptyHash parent
          { (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 with
            accounts := finalAccounts, storage := receipt.storage } address =
        account emptyHash parent (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2 address := by
        unfold account ReferenceAccountLookup.peek
        rw [writes]
      rw [same,entered]
      exact entry emptyHash parent _ _ _ address _ _
    · rfl
  rw [settled]
  change (account emptyHash parent (ReferenceSourcePrepayment.pay emptyHash parent before tx.sender _ 0).2 address).nonce = _
  rw [paid]
  split <;> simp_all only [Nat.add_zero]

/-- Source BAL uses a checked U64 constructor, not modular coercion. -/
def checkedNonce (n : Nat) : Option UInt64 :=
  if n < 2^64 then some (UInt64.ofNat n) else none

/-- Independent before-state source observation supplies the nonce omitted
by balance-only correspondence. Admission supplies the actual numeric bound. -/
theorem admitted_nonce {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (before : Tx Hash) (tx : RefundAccounting.Context) {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (sourceNonce : (account emptyHash parent before tx.sender).nonce = sender.nonce.toNat) :
    checkedNonce ((account emptyHash parent before tx.sender).nonce+1) =
      some (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)) ∧
    (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)).toNat = tx.transaction.base.nonce.toNat+1 := by
  have bound := checks.nonceOverflow
  have fits : tx.transaction.base.nonce.toNat+1 < 2^64 := by omega
  rw [sourceNonce,checks.nonceMatch]
  constructor
  · simp only [checkedNonce,if_pos fits]
  · exact Nat.mod_eq_of_lt fits

#print axioms modify
#print axioms transfer
#print axioms entry
#print axioms credit
#print axioms disbursement
#print axioms actual
#print axioms admitted_nonce
end Eip8282.Audit.Integrator.ReferenceOrdinaryBlockNonce
