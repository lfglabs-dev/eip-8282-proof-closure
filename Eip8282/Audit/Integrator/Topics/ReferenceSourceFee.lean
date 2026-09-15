import Eip8282.Audit.Integrator.ReferenceSettledAccountJournal
import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.ReferenceTransactionSettlement

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSourceFeeAmounts -/

/-! Source fee subtraction and the exact refund/tip/burn partition. Source gas
settlement supplies the same gas-used/left pair; no old replay gas is used.
Admission supplies price/base ordering and the prepayment supplies its budget.
The burn is an accounting residual, not an extra balance credit. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts
open EvmYul EvmYul.EVM
open ReferenceAdmissionExtraction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem dynamic_base (cap priority : UInt256) (base : Nat) (fits : base ≤ cap.toNat) :
    base ≤ (min priority (cap-UInt256.ofNat base)+UInt256.ofNat base).toNat := by
  have bn : (UInt256.ofNat base).toNat = base := Nat.mod_eq_of_lt (fits.trans_lt cap.val.isLt)
  have sn : (cap-UInt256.ofNat base).toNat = cap.toNat-base := by
    rw [Eip8282.Audit.EntryReach.toNat_sub_of_le _ _ (by rw [bn]; exact fits),bn]
  have mn : (min priority (cap-UInt256.ofNat base)).toNat ≤ cap.toNat-base := by
    change (if priority ≤ cap-UInt256.ofNat base then priority else cap-UInt256.ofNat base).toNat ≤ _
    split
    · rename_i h
      change priority.toNat ≤ (cap-UInt256.ofNat base).toNat at h
      rwa [sn] at h
    · exact sn.le
  have capFit : cap.toNat < UInt256.size := cap.val.isLt
  rw [Eip8282.Audit.EntryReach.toNat_add_of_lt _ _ (by rw [bn]; omega),bn]
  omega

theorem price_base (tx : RefundAccounting.Context) (base : tx.baseFee ≤ feeCap tx.transaction) :
    tx.baseFee ≤ tx.effectivePrice.toNat := by
  obtain ⟨fuel,world,baseFee,header,genesis,blocks,transaction,sender⟩ := tx
  cases transaction with
  | legacy t => exact base
  | access t => exact base
  | dynamic t => exact dynamic_base t.maxFeePerGas t.maxPriorityFeePerGas baseFee base
  | blob t => exact dynamic_base t.maxFeePerGas t.maxPriorityFeePerGas baseFee base

theorem partition (gas : ReferenceTransactionGas.Settlement) (limit price base : Nat)
    (conserved : gas.gasUsed+gas.gasLeft = limit) (ordered : base ≤ price) :
    gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = limit*price ∧
    gas.gasLeft*price + gas.gasUsed*(price-base) ≤ limit*price := by
  have eq : gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = limit*price := by
    rw [Nat.add_assoc,← Nat.mul_add,Nat.sub_add_cancel ordered,← Nat.add_mul,Nat.add_comm gas.gasLeft,conserved]
  exact ⟨eq,by omega⟩

theorem actual {txGas floor grant : Nat} {meter : ReferenceMeterRollback.Meter}
    (facts : ReferenceTransactionSettlement.Facts txGas floor grant meter)
    (price base : Nat) (ordered : base ≤ price) :
    let gas := ReferenceTransactionSettlement.calculation txGas floor grant meter
    gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = txGas*price ∧
    gas.gasLeft*price + gas.gasUsed*(price-base) ≤ txGas*price :=
  partition _ _ _ _ facts.sender_conservation ordered

#print axioms price_base
#print axioms partition
#print axioms actual
end Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts

end

section

/-! ## ReferenceSourceFeeCredit -/

/-! Literal create_ether / modify_state credit, including zero credits, source
checked U256 addition and read effects preceding overflow. This is consumed by
the ordered source fee disbursement, not an external funding-history credit. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeCredit
open EvmYul ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

noncomputable def credit {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (address : AccountAddress) (amount : UInt256) :
    Except Unit Unit × Tx Hash :=
  let old := account emptyHash parent tx address
  let read := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts address}
  if old.balance.toNat + amount.toNat < UInt256.size then
    (.ok (),modifyBalance emptyHash parent read address
      (UInt256.ofNat (old.balance.toNat + amount.toNat)))
  else (.error (),read)

theorem successful {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key : AccountAddress) (amount : UInt256)
    (fits : (account emptyHash parent tx key).balance.toNat + amount.toNat < UInt256.size) :
    (credit emptyHash parent tx key amount).1 = .ok () ∧
    ∀ address, (account emptyHash parent (credit emptyHash parent tx key amount).2 address).balance.toNat =
      (account emptyHash parent tx address).balance.toNat + (if address = key then amount.toNat else 0) := by
  unfold credit
  rw [if_pos fits]
  refine ⟨rfl,?_⟩
  intro address
  rw [ReferenceSourceTransferFunding.modify_balance]
  by_cases same : address = key
  · subst address
    simp only [if_true]
    change (_ % UInt256.size) = _
    exact Nat.mod_eq_of_lt fits
  · simp only [if_neg same,Nat.add_zero]
    rfl

theorem hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256) :
    hashAt emptyHash parent (credit emptyHash parent tx key amount).2 address = hashAt emptyHash parent tx address := by
  unfold credit
  dsimp only
  split
  · rw [modify_hash]
    rfl
  · rfl

theorem protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (credit emptyHash parent tx key amount).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold credit
  dsimp only
  split
  · exact modify_protected_storage emptyHash parent
      {tx with accounts := ReferenceAccountLookup.tracked tx.accounts key}
      key address _ nonempty storageParent slot
  · rfl

theorem fields {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key : AccountAddress) (amount : UInt256) :
    (credit emptyHash parent tx key amount).2.codeWrites = tx.codeWrites ∧
    (credit emptyHash parent tx key amount).2.transient = tx.transient ∧
    (credit emptyHash parent tx key amount).2.accounts.reads = insert key tx.accounts.reads := by
  unfold credit
  dsimp only
  split
  · unfold modifyBalance
    dsimp only
    split <;> simp [writeAccount,ReferenceAccountLookup.tracked]
  · exact ⟨rfl,rfl,rfl⟩

#print axioms successful
#print axioms hash
#print axioms protected_storage
#print axioms fields
end Eip8282.Audit.Integrator.ReferenceSourceFeeCredit

end

section

/-! ## ReferenceSourceFeeDisbursement -/

/-! Pinned fork.py997-1006: calculate refund and priority, then convert/credit
payer, then convert/credit beneficiary. Errors retain completed reads/credits.
Zero payments are not skipped. Equal payer/beneficiary addresses are supported.
The budget theorem is consumed by same-frame finalization, with its budget
derived from the prepayment/history producer. No post-balance premise. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement
open EvmYul ReferenceSourceValueTransfer ReferenceSourceFeeCredit
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Error where
  | priorityUnderflow | refundAmountOverflow | refundCreditOverflow
  | tipAmountOverflow | tipCreditOverflow

noncomputable def run {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary : AccountAddress)
    (price base : Nat) (gas : ReferenceTransactionGas.Settlement) : Except Error Unit × Tx Hash :=
  let refundAmount := gas.gasLeft * price
  if base ≤ price then
    let tipAmount := gas.gasUsed * (price-base)
    if refundAmount < UInt256.size then
      let refunded := credit emptyHash parent tx payer (UInt256.ofNat refundAmount)
      match refunded.1 with
      | .error _ => (.error .refundCreditOverflow,refunded.2)
      | .ok _ =>
        if tipAmount < UInt256.size then
          let tipped := credit emptyHash parent refunded.2 beneficiary (UInt256.ofNat tipAmount)
          match tipped.1 with
          | .error _ => (.error .tipCreditOverflow,tipped.2)
          | .ok _ => (.ok (),tipped.2)
        else (.error .tipAmountOverflow,refunded.2)
    else (.error .refundAmountOverflow,tx)
  else (.error .priorityUnderflow,tx)

theorem funded {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary : AccountAddress)
    (price base budget : Nat) (gas : ReferenceTransactionGas.Settlement)
    (baseFits : base ≤ price)
    (balances : ∀ a, (account emptyHash parent tx a).balance.toNat ≤ budget)
    (funds : budget + gas.gasLeft*price + gas.gasUsed*(price-base) < UInt256.size) :
    (run emptyHash parent tx payer beneficiary price base gas).1 = .ok () ∧
    ∀ a, (account emptyHash parent (run emptyHash parent tx payer beneficiary price base gas).2 a).balance.toNat =
      (account emptyHash parent tx a).balance.toNat +
        (if a = payer then gas.gasLeft*price else 0) +
        (if a = beneficiary then gas.gasUsed*(price-base) else 0) := by
  have refundFit : gas.gasLeft*price < UInt256.size := by omega
  have tipFit : gas.gasUsed*(price-base) < UInt256.size := by omega
  have refundNat : (UInt256.ofNat (gas.gasLeft*price)).toNat = gas.gasLeft*price := Nat.mod_eq_of_lt refundFit
  have tipNat : (UInt256.ofNat (gas.gasUsed*(price-base))).toNat = gas.gasUsed*(price-base) := Nat.mod_eq_of_lt tipFit
  have first := successful emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price)) (by rw [refundNat]; have h := balances payer; omega)
  have second := successful emptyHash parent (credit emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price))).2 beneficiary
    (UInt256.ofNat (gas.gasUsed*(price-base))) (by
      rw [first.2 beneficiary,refundNat,tipNat]
      have h := balances beneficiary
      split <;> omega)
  unfold run
  dsimp only
  rw [if_pos baseFits,if_pos refundFit,first.1]
  dsimp only
  rw [if_pos tipFit,second.1]
  refine ⟨rfl,?_⟩
  intro a
  rw [second.2 a,first.2 a,refundNat,tipNat]

/-- Protected code storage survives zero-credit cleanup as well as all partial
errors. This property is available even outside the funded-success domain. -/
theorem protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary address : AccountAddress)
    (price base : Nat) (gas : ReferenceTransactionGas.Settlement)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (run emptyHash parent tx payer beneficiary price base gas).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold run
  dsimp only
  split
  · split
    · split
      · exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
      · split
        · have next : hashAt emptyHash parent (credit emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price))).2 address ≠ emptyHash := by rwa [ReferenceSourceFeeCredit.hash]
          split <;> rw [ReferenceSourceFeeCredit.protected_storage emptyHash parent _ beneficiary address _ next storageParent slot]
          all_goals exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
        · exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
    · rfl
  · rfl

#print axioms funded
#print axioms protected_storage
end Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement

end

section

/-! ## ReferenceSourceFeeFinalization -/

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

end
