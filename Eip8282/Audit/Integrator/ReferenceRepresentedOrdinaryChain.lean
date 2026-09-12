import Eip8282.Audit.Integrator.ReferenceFullFeeBlockTotal
import Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce

/-! Derived (represented-parent) consumers of the ordinary-transaction chain.

Sibling consumers next to the existing ones at each of the four levels
(`admitted_nonce`, `FullFeeBlockNonce.verified`, `FullFeeBlockReceipt.verified`,
`FullFeeBlockTotal.verified`). Each derived form specializes the abstract source
accounts parent to `representedParent codeHash tx.world` and internally derives
the ad-hoc `sourceNonce` (and, where present, `balances`) premise via the
representation lemmas from `ReferenceRepresentedSourceNonce`
(`sourceNonce_of_represented` and `BalancesRelated_of_represented_freshAll`).

The existing consumers (`ReferenceOrdinaryBlockNonce.admitted_nonce`,
`ReferenceFullFeeBlockNonce.verified`, `ReferenceFullFeeBlockReceipt.verified`,
`ReferenceFullFeeBlockTotal.verified`) remain unchanged. Callers keep the choice
of the abstract-parent form or the represented-parent form.

**Domain of the derived consumers**: the caller commits to
`accountsParent = representedParent codeHash tx.world` (the source accounts
overlay is literally the represented image of the pinned pre-transaction
world). Under this domain, the read-nonce equality and the balance-only
coherence are automatic; the derived forms replace those two ad-hoc premises
with the single structural equality.

Public consumer signatures are preserved. This module supplies alternative
derivations, not replacements. -/
namespace Eip8282.Audit.Integrator.ReferenceRepresentedOrdinaryChain

open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer (Account Tx account empty)
open ReferenceSourceTransferFunding (representedParent BalancesRelated)
open ReferenceRepresentedSourceNonce
  (sourceNonce_of_represented BalancesRelated_of_represented_freshAll)
open ReferenceCheckpointCall (call)
open ReferenceCheckedSystemEntry (before)
open ReferenceOrdinaryBlockSettlement (Block)

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Derived `ReferenceOrdinaryBlockNonce.admitted_nonce`: takes the
    represented-parent specialization and derives the `sourceNonce` premise
    from `found` + a pointwise fresh accounts journal at `tx.sender`. -/
theorem admitted_nonce_of_represented {Hash : Type}
    (codeHash : ByteArray → Hash) (emptyHash : Hash)
    (before : Tx Hash) (tx : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (freshAccountsAt : before.accounts.writes tx.sender = none) :
    ReferenceOrdinaryBlockNonce.checkedNonce
        ((account emptyHash (representedParent codeHash tx.world) before tx.sender).nonce+1) =
      some (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)) ∧
    (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)).toNat =
      tx.transaction.base.nonce.toNat+1 :=
  ReferenceOrdinaryBlockNonce.admitted_nonce emptyHash
    (representedParent codeHash tx.world) before tx checks
    (sourceNonce_of_represented codeHash tx.world before emptyHash tx.sender sender
      freshAccountsAt found)

#print axioms admitted_nonce_of_represented

/-- Derived `ReferenceFullFeeBlockNonce.verified`: specializes the accounts
    parent to `representedParent codeHash tx.world`, derives `balances` from
    globally-fresh accounts, derives `sourceNonce` from `found` + pointwise
    freshness, and forwards to the abstract-parent `verified`. -/
theorem FullFeeBlockNonce_verified_of_represented
    {deposit exit : TransactionAppendBudget.Receipt}
    {Hash Error : Type} [DecidableEq Hash]
    (codeHash : ByteArray → Hash)
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (recipient : tx.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks tx)
    (emptyHash : Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash
      (representedParent codeHash tx.world) before.accounts codeParent before.codeWrites
      (call kind tx).target).1 = .ok (call kind tx).code)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray =
      SystemSpec.worldSlot tx.world (call kind tx).target q)
    (fresh : before.storage = ReferenceRuntimeStateBalance.emptyTx)
    (freshAccounts : before.accounts.writes = fun _ => none) :
    ReferenceAllocatedTotal.Started kind tx emptyHash (representedParent codeHash tx.world) before codeParent ∧
    ∃ events core finalAccounts finish finalWarm final,
      ReferenceAllocatedExecution.run kind tx emptyHash (representedParent codeHash tx.world) before codeParent parent = some ((events,core),finalAccounts) ∧
      ReferenceAllocatedTotal.Result kind tx emptyHash (representedParent codeHash tx.world) before codeParent parent events finalAccounts core ∧
      ReferenceFullLogExecution.run kind tx signature emptyHash (representedParent codeHash tx.world) before codeParent parent =
        some ((events,ReferenceLogPrefixHandlers.outcome (ReferenceFullLogExecution.emitted kind tx signature) core),finalAccounts) ∧
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) parent
        (ReferenceFullLogExecution.initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash (representedParent codeHash tx.world) before tx kind codeParent).2.storage)
        (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx) finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind tx).code)
        (ReferenceAccountLookup.peek (representedParent codeHash tx.world) (ReferenceAllocatedEntry.entered emptyHash (representedParent codeHash tx.world) before tx kind codeParent).2.accounts (ReachableCalls.address kind)).isSome
        parent finish finalWarm final ByteArray.empty = ReferenceLogPrefixHandlers.outcome (ReferenceFullLogExecution.emitted kind tx signature) core ∧
      ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash (representedParent codeHash tx.world) before tx).2.storage [] finalWarm
        (ReferenceLogPrefixHandlers.outcome (ReferenceFullLogExecution.emitted kind tx signature) core) =
        ReferenceLogPrefixSettlement.boundary (ReferenceFullLogExecution.emitted kind tx signature)
          (ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash (representedParent codeHash tx.world) before tx).2.storage [] finalWarm core) ∧
      ReferenceTransferLogs.project (ReachableCalls.address kind) (ReferenceFullLogExecution.emitted kind tx signature) = [] ∧
      ∃ receipt, ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash (representedParent codeHash tx.world) before tx).2.storage [] finalWarm
          (ReferenceLogPrefixHandlers.outcome (ReferenceFullLogExecution.emitted kind tx signature) core) = .returned receipt ∧
        ReferenceTransactionSettlement.Facts tx.transaction.base.gasLimit.toNat (ReferenceAdmissionExtraction.calldataFloor tx.transaction tx.sender)
          (ReferenceTransactionGas.allocate tx.transaction.base.gasLimit.toNat (ReferenceAllocatedEntry.intrinsic tx)).reservoir receipt.meter ∧
        ReferenceSourceFeeFinalization.Result emptyHash (representedParent codeHash tx.world)
          (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash (representedParent codeHash tx.world) before tx).2
          (ReferenceAllocatedEntry.entered emptyHash (representedParent codeHash tx.world) before tx kind codeParent).2
          finalAccounts tx receipt parent kind ∧
        let finished := (ReferenceSourceFeeFinalization.finish emptyHash (representedParent codeHash tx.world)
          (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash (representedParent codeHash tx.world) before tx).2
          (ReferenceAllocatedEntry.entered emptyHash (representedParent codeHash tx.world) before tx kind codeParent).2 finalAccounts tx receipt).2
        (∀ a, (ReferenceSourceValueTransfer.account emptyHash (representedParent codeHash tx.world) finished a).nonce =
          (ReferenceSourceValueTransfer.account emptyHash (representedParent codeHash tx.world) before a).nonce + (if a = tx.sender then 1 else 0)) ∧
        ReferenceOrdinaryBlockNonce.checkedNonce
          (ReferenceSourceValueTransfer.account emptyHash (representedParent codeHash tx.world) finished tx.sender).nonce =
          some (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)) ∧
        (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)).toNat = tx.transaction.base.nonce.toNat+1 :=
  ReferenceFullFeeBlockNonce.verified kind tx signature history checks found recipient nonblob costs
    emptyHash (representedParent codeHash tx.world) before codeParent parent loaded
    (BalancesRelated_of_represented_freshAll codeHash tx.world before emptyHash freshAccounts)
    slots fresh
    (sourceNonce_of_represented codeHash tx.world before emptyHash tx.sender sender
      (by rw [freshAccounts]) found)

#print axioms FullFeeBlockNonce_verified_of_represented

/-- Derived `ReferenceFullFeeBlockReceipt.verified`: same specialization
    pattern; produces the `Certificate` witness at the represented parent. -/
theorem FullFeeBlockReceipt_verified_of_represented
    {deposit exit : TransactionAppendBudget.Receipt}
    {Hash Error : Type} [DecidableEq Hash]
    (codeHash : ByteArray → Hash)
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (recipient : tx.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks tx)
    (emptyHash : Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash
      (representedParent codeHash tx.world) before.accounts codeParent before.codeWrites
      (call kind tx).target).1 = .ok (call kind tx).code)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind tx).target q.toByteArray =
      SystemSpec.worldSlot tx.world (call kind tx).target q)
    (fresh : before.storage = ReferenceRuntimeStateBalance.emptyTx)
    (freshAccounts : before.accounts.writes = fun _ => none)
    (freshCode : before.codeWrites = fun _ => none) :
    Nonempty (ReferenceFullFeeBlockReceipt.Certificate kind tx signature emptyHash
      (representedParent codeHash tx.world) before codeParent parent) :=
  ReferenceFullFeeBlockReceipt.verified kind tx signature history checks found recipient nonblob costs
    emptyHash (representedParent codeHash tx.world) before codeParent parent loaded
    (BalancesRelated_of_represented_freshAll codeHash tx.world before emptyHash freshAccounts)
    slots fresh
    (sourceNonce_of_represented codeHash tx.world before emptyHash tx.sender sender
      (by rw [freshAccounts]) found)
    freshAccounts freshCode

#print axioms FullFeeBlockReceipt_verified_of_represented

/-- Derived `ReferenceFullFeeBlockTotal.verified`: top-level public consumer
    with the represented-parent specialization on `block.accounts`. Discharges
    the two ad-hoc premises `balances` and `sourceNonce` internally. -/
theorem FullFeeBlockTotal_verified_of_represented
    {deposit exit : TransactionAppendBudget.Receipt}
    {Hash Error : Type} [DecidableEq Hash]
    (codeHash : ByteArray → Hash)
    (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) (signature : UInt256)
    (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender)
    (recipient : tx.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks tx)
    (emptyHash : Hash) (block : Block Hash Error)
    (represented : block.accounts = representedParent codeHash tx.world)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash block.accounts
      (before Hash).accounts block.code (before Hash).codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (slots : ∀ q, ReferenceStorageView.current block.storage (before Hash).storage (call kind tx).target q.toByteArray =
      SystemSpec.worldSlot tx.world (call kind tx).target q) :
    ∃ (cert : ReferenceFullFeeBlockReceipt.Certificate kind tx signature emptyHash block.accounts (before Hash) block.code block.storage)
      (final : Block Hash Error),
      ReferenceOrdinaryBlockSettlement.incorporate emptyHash block (ReachableCalls.address kind)
        (ReferenceOrdinaryBlockSettlement.settled cert) (ReferenceFullFeeBlockReceipt.addresses kind tx) cert.keys =
        some (final,before Hash) ∧
      final.builder.storage.index = block.builder.storage.index ∧
      final.accounts = ReferenceOrdinaryBlockSettlement.commitAccounts block.accounts (ReferenceOrdinaryBlockSettlement.settled cert) ∧
      final.code = block.code ∧
      final.storage = ReferenceStorageView.commit block.storage (ReferenceOrdinaryBlockSettlement.settled cert).storage ∧
      final.accountReads = block.accountReads ∪ (ReferenceOrdinaryBlockSettlement.settled cert).accounts.reads ∧
      final.storageReads = block.storageReads ∪ (ReferenceOrdinaryBlockSettlement.settled cert).storage.reads ∧
      (∀ a, ((ReferenceAccountLookup.parentRead final.accounts a).getD (ReferenceSourceValueTransfer.empty emptyHash)) =
        ReferenceSourceValueTransfer.account emptyHash block.accounts (ReferenceOrdinaryBlockSettlement.settled cert) a) ∧
      (∀ (q : UInt256), ReferenceStorageView.parentRead final.storage (ReachableCalls.address kind) q.toByteArray =
        ReferenceStorageView.current block.storage cert.receipt.storage (ReachableCalls.address kind) q.toByteArray) ∧
      (∀ a k, a ≠ ReachableCalls.address kind → ReferenceStorageView.parentRead final.storage a k =
        ReferenceStorageView.parentRead block.storage a k) ∧
      ((ReferenceOrdinaryBlockAccess.entries (ReferenceOrdinaryBlockSettlement.settled cert).accounts (ReferenceFullFeeBlockReceipt.addresses kind tx)).map Prod.fst).Nodup ∧
      (∀ pair ∈ ReferenceOrdinaryBlockAccess.entries (ReferenceOrdinaryBlockSettlement.settled cert).accounts (ReferenceFullFeeBlockReceipt.addresses kind tx),
        (ReferenceOrdinaryBlockSettlement.settled cert).accounts.writes pair.1 = some pair.2) ∧
      (∀ a value, (ReferenceOrdinaryBlockSettlement.settled cert).accounts.writes a = some value →
        (a,value) ∈ ReferenceOrdinaryBlockAccess.entries (ReferenceOrdinaryBlockSettlement.settled cert).accounts (ReferenceFullFeeBlockReceipt.addresses kind tx)) ∧
      ((ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (ReferenceOrdinaryBlockSettlement.settled cert).storage cert.keys).map Prod.fst).Nodup ∧
      (∀ pair ∈ ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (ReferenceOrdinaryBlockSettlement.settled cert).storage cert.keys,
        (ReferenceOrdinaryBlockSettlement.settled cert).storage.writes (ReachableCalls.address kind) pair.1 = some pair.2) ∧
      (∀ a k value, (ReferenceOrdinaryBlockSettlement.settled cert).storage.writes a k = some value → a = ReachableCalls.address kind ∧
        (k,value) ∈ ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (ReferenceOrdinaryBlockSettlement.settled cert).storage cert.keys) := by
  have balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash block.accounts (before Hash) tx.world := by
    rw [represented]
    exact BalancesRelated_of_represented_freshAll codeHash tx.world (before Hash) emptyHash rfl
  have sourceNonce :
      (ReferenceSourceValueTransfer.account emptyHash block.accounts (before Hash) tx.sender).nonce =
        sender.nonce.toNat := by
    rw [represented]
    exact sourceNonce_of_represented codeHash tx.world (before Hash) emptyHash tx.sender sender rfl found
  exact ReferenceFullFeeBlockTotal.verified kind tx signature history checks found recipient
    nonblob costs emptyHash block loaded balances slots sourceNonce

#print axioms FullFeeBlockTotal_verified_of_represented

end Eip8282.Audit.Integrator.ReferenceRepresentedOrdinaryChain
