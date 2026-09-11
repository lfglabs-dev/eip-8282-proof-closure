import Eip8282.Audit.Integrator.ReferenceSettledAccountJournal
import Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement
import Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts

/-! Actual source gas and account journal now meet at ordered fee disbursement.
The initial history/prepayment budget derives every balance/amount overflow
guard. No post-state affordability or fee-disbursement success is an input.
The statement preserves protected slots and gives all account balance changes,
including payer=beneficiary. This is not canonical source history extraction. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeFinalization
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
open ReferenceSettledAccountJournal (journal)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def gas (tx : RefundAccounting.Context) (receipt : ReferenceCheckedFrameOutcome.Receipt) :=
  ReferenceTransactionSettlement.calculation tx.transaction.base.gasLimit.toNat
    (ReferenceAdmissionExtraction.calldataFloor tx.transaction tx.sender)
    (ReferenceTransactionGas.allocate tx.transaction.base.gasLimit.toNat (ReferenceAllocatedEntry.intrinsic tx)).reservoir receipt.meter

noncomputable def finish {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (snapshot entered : Tx Hash) (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (tx : RefundAccounting.Context) (receipt : ReferenceCheckedFrameOutcome.Receipt) :=
  ReferenceSourceFeeDisbursement.run emptyHash parent (journal snapshot entered finalAccounts receipt)
    tx.sender tx.header.beneficiary tx.effectivePrice.toNat tx.baseFee (gas tx receipt)

structure Result {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (snapshot entered : Tx Hash) (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (tx : RefundAccounting.Context) (receipt : ReferenceCheckedFrameOutcome.Receipt)
    (storageParent : ReferenceStorageView.Parent) (kind : ReachableCalls.Contract) : Prop where
  success : (finish emptyHash parent snapshot entered finalAccounts tx receipt).1 = .ok ()
  balances : ∀ a, (account emptyHash parent (finish emptyHash parent snapshot entered finalAccounts tx receipt).2 a).balance.toNat =
    (account emptyHash parent (journal snapshot entered finalAccounts receipt) a).balance.toNat +
      (if a = tx.sender then (gas tx receipt).gasLeft*tx.effectivePrice.toNat else 0) +
      (if a = tx.header.beneficiary then (gas tx receipt).gasUsed*(tx.effectivePrice.toNat-tx.baseFee) else 0)
  protected_storage : ∀ slot, ReferenceStorageView.current storageParent
    (finish emptyHash parent snapshot entered finalAccounts tx receipt).2.storage (ReachableCalls.address kind) slot =
    ReferenceStorageView.current storageParent receipt.storage (ReachableCalls.address kind) slot
  fee_partition : (gas tx receipt).gasLeft*tx.effectivePrice.toNat +
    (gas tx receipt).gasUsed*(tx.effectivePrice.toNat-tx.baseFee) +
    (gas tx receipt).gasUsed*tx.baseFee = tx.transaction.base.gasLimit.toNat*tx.effectivePrice.toNat

theorem actual {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM} (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender) (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (emptyHash : Hash) (accountsParent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent before.accounts codeParent before.codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (related : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before tx.world)
    {events core finalAccounts}
    (execution : ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent = some ((events,core),finalAccounts))
    (receipt : ReferenceCheckedFrameOutcome.Receipt)
    (facts : ReferenceTransactionSettlement.Facts tx.transaction.base.gasLimit.toNat
      (ReferenceAdmissionExtraction.calldataFloor tx.transaction tx.sender)
      (ReferenceTransactionGas.allocate tx.transaction.base.gasLimit.toNat (ReferenceAllocatedEntry.intrinsic tx)).reservoir receipt.meter) :
    Result emptyHash accountsParent (prepaid emptyHash accountsParent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts tx receipt parent kind := by
  have ordered := ReferenceSourceFeeAmounts.price_base tx checks.baseCovered
  have amounts := ReferenceSourceFeeAmounts.actual facts tx.effectivePrice.toNat tx.baseFee ordered
  have derived := ReferenceSettledAccountJournal.derived kind tx history checks found nonblob emptyHash accountsParent before codeParent parent loaded related execution receipt
  have admission := (ReferenceAllocatedEntry.admission checks found nonblob).1
  have debit := TransactionFunding.checkpoint_debit tx admission
  have funds := FundingHistory.trace_funds (ProtocolCreditEnvelope.ledger_bound history.ledger).1
  have total := funds.trans_lt (LedgerCreditSafety.genesis_budget history.ledger history.counts)
  have payout : TransferFunding.worldFunds tx.checkpoint + (gas tx receipt).gasLeft*tx.effectivePrice.toNat +
      (gas tx receipt).gasUsed*(tx.effectivePrice.toNat-tx.baseFee) < UInt256.size := by
    have a := amounts.2
    change (gas tx receipt).gasLeft*tx.effectivePrice.toNat + (gas tx receipt).gasUsed*(tx.effectivePrice.toNat-tx.baseFee) ≤ _ at a
    unfold TransactionFunding.upfront at debit
    omega
  have paid := ReferenceSourceFeeDisbursement.funded emptyHash accountsParent
    (journal (prepaid emptyHash accountsParent before tx).2 (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts receipt)
    tx.sender tx.header.beneficiary tx.effectivePrice.toNat tx.baseFee (TransferFunding.worldFunds tx.checkpoint) (gas tx receipt) ordered derived.1 payout
  refine ⟨paid.1,paid.2,?_,amounts.1⟩
  intro slot
  exact ReferenceSourceFeeDisbursement.protected_storage emptyHash accountsParent _ tx.sender tx.header.beneficiary
    (ReachableCalls.address kind) tx.effectivePrice.toNat tx.baseFee (gas tx receipt) derived.2 parent slot

#print axioms actual
end Eip8282.Audit.Integrator.ReferenceSourceFeeFinalization
