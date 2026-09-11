import Eip8282.Audit.Integrator.ReferenceOrdinaryBlockSettlement

/-! Ordinary transactions: all three conditional runtime claims, actual full
logs/rollback/meter and ordered fee credits, then the SAME final source journal
incorporated into the block. The initial transaction journal is constructed
fresh. Source sender nonce correspondence is an explicit initial domain addition
beyond balance-only FullFeeTotal; final support/conversions/merge are derived.
No canonical History producer, complete transaction admission, global account-map
representation, next-transaction History or final block BAL validation is claimed.
Synthetic replay resources remain distinct from actual source gas. -/
namespace Eip8282.Audit.Integrator.ReferenceFullFeeBlockTotal
open EvmYul EvmYul.EVM
open ReferenceCheckpointCall (call)
open ReferenceCheckedSystemEntry (before)
open ReferenceFullFeeBlockReceipt
open ReferenceOrdinaryBlockSettlement
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
    (emptyHash : Hash) (block : Block Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash block.accounts
      (before Hash).accounts block.code (before Hash).codeWrites (call kind tx).target).1 = .ok (call kind tx).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash block.accounts (before Hash) tx.world)
    (slots : ∀ q, ReferenceStorageView.current block.storage (before Hash).storage (call kind tx).target q.toByteArray =
      SystemSpec.worldSlot tx.world (call kind tx).target q)
    (sourceNonce : (ReferenceSourceValueTransfer.account emptyHash block.accounts (before Hash) tx.sender).nonce = sender.nonce.toNat) :
    ∃ (cert : Certificate kind tx signature emptyHash block.accounts (before Hash) block.code block.storage)
      (final : Block Hash Error),
      incorporate emptyHash block (ReachableCalls.address kind) (settled cert) (addresses kind tx) cert.keys =
        some (final,before Hash) ∧
      final.builder.storage.index = block.builder.storage.index ∧
      final.accounts = commitAccounts block.accounts (settled cert) ∧
      final.code = block.code ∧
      final.storage = ReferenceStorageView.commit block.storage (settled cert).storage ∧
      final.accountReads = block.accountReads ∪ (settled cert).accounts.reads ∧
      final.storageReads = block.storageReads ∪ (settled cert).storage.reads ∧
      (∀ a, ((ReferenceAccountLookup.parentRead final.accounts a).getD (ReferenceSourceValueTransfer.empty emptyHash)) =
        ReferenceSourceValueTransfer.account emptyHash block.accounts (settled cert) a) ∧
      (∀ (q : UInt256), ReferenceStorageView.parentRead final.storage (ReachableCalls.address kind) q.toByteArray =
        ReferenceStorageView.current block.storage cert.receipt.storage (ReachableCalls.address kind) q.toByteArray) ∧
      (∀ a k, a ≠ ReachableCalls.address kind → ReferenceStorageView.parentRead final.storage a k =
        ReferenceStorageView.parentRead block.storage a k) ∧
      ((ReferenceOrdinaryBlockAccess.entries (settled cert).accounts (addresses kind tx)).map Prod.fst).Nodup ∧
      (∀ pair ∈ ReferenceOrdinaryBlockAccess.entries (settled cert).accounts (addresses kind tx),
        (settled cert).accounts.writes pair.1 = some pair.2) ∧
      (∀ a value, (settled cert).accounts.writes a = some value →
        (a,value) ∈ ReferenceOrdinaryBlockAccess.entries (settled cert).accounts (addresses kind tx)) ∧
      ((ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (settled cert).storage cert.keys).map Prod.fst).Nodup ∧
      (∀ pair ∈ ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (settled cert).storage cert.keys,
        (settled cert).storage.writes (ReachableCalls.address kind) pair.1 = some pair.2) ∧
      (∀ a k value, (settled cert).storage.writes a k = some value → a = ReachableCalls.address kind ∧
        (k,value) ∈ ReferenceSystemBlockAccess.entries (ReachableCalls.address kind) (settled cert).storage cert.keys) := by
  obtain ⟨cert⟩ := ReferenceFullFeeBlockReceipt.verified kind tx signature history checks found recipient nonblob costs
    emptyHash block.accounts (before Hash) block.code block.storage loaded balances slots rfl sourceNonce rfl rfl
  obtain ⟨builder,incorporated,index⟩ := ReferenceOrdinaryBlockSettlement.incorporated block cert
  let final := merged block (settled cert) builder
  have storageComplete := ReferenceOrdinaryBlockStorage.complete cert.writes
  refine ⟨cert,final,incorporated,index,rfl,?_,rfl,rfl,rfl,?_,?_,?_,
    ReferenceOrdinaryBlockAccess.entries_unique _ _,ReferenceOrdinaryBlockAccess.entries_sound _ _,
    ReferenceOrdinaryBlockSettlement.entries_complete cert,storageComplete⟩
  · change commitCode block.code (settled cert) = block.code
    have code := cert.code
    change (settled cert).codeWrites = fun _ => none at code
    simp only [commitCode,code,Option.orElse_none]
  · intro a
    exact commit_read emptyHash block.accounts (settled cert) a
  · intro q
    change ReferenceStorageView.parentRead (ReferenceStorageView.commit block.storage (settled cert).storage) _ _ = _
    rw [ReferenceStorageView.commit_read]
    exact cert.fees.protected_storage q.toByteArray
  · intro a k foreign
    change ReferenceStorageView.parentRead (ReferenceStorageView.commit block.storage (settled cert).storage) a k = _
    rw [ReferenceStorageView.commit_read]
    have absent : (settled cert).storage.writes a k = none := by
      cases h : (settled cert).storage.writes a k with
      | none => rfl
      | some value => exact False.elim (foreign (cert.writes a k value h).1)
    simp only [ReferenceStorageView.current,absent,Option.getD_none]

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceFullFeeBlockTotal
