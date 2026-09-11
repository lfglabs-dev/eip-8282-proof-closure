import Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccess

/-! A single actual ordinary computation supplies all three conditional
claims, its exact frame receipt, fee-finalized account/storage journal, finite
write support, unchanged hashes and checked sender nonce. Initial account/code
write overlays are fresh; nonce correspondence is explicitly additional to the
balance-only domain. Consumer: ReferenceFullFeeBlockTotal.verified. -/
namespace Eip8282.Audit.Integrator.ReferenceFullFeeBlockReceipt
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceCheckpointCall (call)
open ReferenceFullLogExecution (emitted initial run)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

noncomputable def journal {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (tx : RefundAccounting.Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (before : ReferenceSourceValueTransfer.Tx Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt) :=
  (ReferenceSourceFeeFinalization.finish emptyHash accountsParent
    (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts tx receipt).2

def addresses (kind : ReachableCalls.Contract) (tx : RefundAccounting.Context) : List AccountAddress :=
  [tx.sender,ReachableCalls.address kind,tx.header.beneficiary]

structure Certificate {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (tx : RefundAccounting.Context) (signature : UInt256) (emptyHash : Hash)
    (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent) where
  events : List ReferenceMeterPath.Event
  core : Outcome
  finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)
  finish : View
  finalWarm : Warm
  final : ReferenceMeterRollback.Meter
  receipt : ReferenceCheckedFrameOutcome.Receipt
  keys : List UInt256
  started : ReferenceAllocatedTotal.Started kind tx emptyHash accountsParent before codeParent
  actual : ReferenceAllocatedExecution.run kind tx emptyHash accountsParent before codeParent parent = some ((events,core),finalAccounts)
  claims : ReferenceAllocatedTotal.Result kind tx emptyHash accountsParent before codeParent parent events finalAccounts core
  full : run kind tx signature emptyHash accountsParent before codeParent parent =
    some ((events,ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core),finalAccounts)
  trace : ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) parent
    (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage)
    (ReferenceInitialAccess.warm tx) (ReferenceAllocatedEntry.meter tx) finish finalWarm final events
  last : ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind tx).code)
    (ReferenceAccountLookup.peek accountsParent (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.accounts (ReachableCalls.address kind)).isSome
    parent finish finalWarm final ByteArray.empty = ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core
  logSettlement : ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm
      (ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core) =
    ReferenceLogPrefixSettlement.boundary (emitted kind tx signature)
      (ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm core)
  transferLogProjection : ReferenceTransferLogs.project (ReachableCalls.address kind) (emitted kind tx signature) = []
  settled : ReferenceCheckedFrameOutcome.settle (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage [] finalWarm
    (ReferenceLogPrefixHandlers.outcome (emitted kind tx signature) core) = .returned receipt
  resources : ReferenceTransactionSettlement.Facts tx.transaction.base.gasLimit.toNat (ReferenceAdmissionExtraction.calldataFloor tx.transaction tx.sender)
    (ReferenceTransactionGas.allocate tx.transaction.base.gasLimit.toNat (ReferenceAllocatedEntry.intrinsic tx)).reservoir receipt.meter
  fees : ReferenceSourceFeeFinalization.Result emptyHash accountsParent
    (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2
    (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts tx receipt parent kind
  nonces : ∀ a, (ReferenceSourceValueTransfer.account emptyHash accountsParent (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt) a).nonce =
    (ReferenceSourceValueTransfer.account emptyHash accountsParent before a).nonce + (if a = tx.sender then 1 else 0)
  senderNonce : ReferenceOrdinaryBlockNonce.checkedNonce
    (ReferenceSourceValueTransfer.account emptyHash accountsParent (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt) tx.sender).nonce =
      some (UInt64.ofNat (tx.transaction.base.nonce.toNat+1))
  nonceExact : (UInt64.ofNat (tx.transaction.base.nonce.toNat+1)).toNat = tx.transaction.base.nonce.toNat+1
  accountSupport : ∀ a, a ∉ addresses kind tx →
    (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt).accounts.writes a = none
  hashes : ∀ a, ReferenceSourceValueTransfer.hashAt emptyHash accountsParent (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt) a =
    ((ReferenceAccountLookup.parentRead accountsParent a).getD (ReferenceSourceValueTransfer.empty emptyHash)).codeHash
  code : (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt).codeWrites = fun _ => none
  writes : ReferenceOrdinaryBlockStorage.Writes (ReachableCalls.address kind)
    (journal kind tx emptyHash accountsParent before codeParent finalAccounts receipt).storage keys
  beforeAccounts : before.accounts.writes = fun _ => none

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
    (sourceNonce : (ReferenceSourceValueTransfer.account emptyHash accountsParent before tx.sender).nonce = sender.nonce.toNat)
    (freshAccounts : before.accounts.writes = fun _ => none) (freshCode : before.codeWrites = fun _ => none) :
    Nonempty (Certificate kind tx signature emptyHash accountsParent before codeParent parent) := by
  obtain ⟨started,events,core,finalAccounts,finish,finalWarm,final,actual,claims,full,trace,last,logs,projection,receipt,settled,facts,fees,nonces,senderNonce,nonceExact⟩ :=
    ReferenceFullFeeBlockNonce.verified kind tx signature history checks found recipient nonblob costs emptyHash accountsParent before codeParent parent loaded balances slots fresh sourceNonce
  have stack : (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage).stack.length ≤ 1024 := by
    simp [ReferenceFullLogExecution.initial,ReferenceRuntimeView.initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned
    (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage) rfl
  have initialFresh : (initial kind tx signature (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2.storage).storage = ReferenceRuntimeStateBalance.emptyTx :=
    ReferenceFreshStorageEntry.allocated emptyHash accountsParent before tx kind codeParent fresh
  have snapshotFresh : (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2.storage.writes = fun _ _ => none := by
    rw [(ReferenceSourcePrepaidCheckpoint.fields emptyHash accountsParent before tx).1,fresh]
    rfl
  obtain ⟨keys,support⟩ := ReferenceOrdinaryBlockStorage.receipt trace stack aligned initialFresh snapshotFresh last settled
  have finalSupport := ReferenceOrdinaryBlockStorage.fees emptyHash accountsParent
    (ReferenceSettledAccountJournal.journal (ReferenceSourcePrepaidCheckpoint.prepaid emptyHash accountsParent before tx).2
      (ReferenceAllocatedEntry.entered emptyHash accountsParent before tx kind codeParent).2 finalAccounts receipt)
    tx.sender tx.header.beneficiary tx.effectivePrice.toNat tx.baseFee (ReferenceSourceFeeFinalization.gas tx receipt) support
  refine ⟨⟨events,core,finalAccounts,finish,finalWarm,final,receipt,keys,started,actual,claims,full,trace,last,logs,projection,settled,facts,fees,
    nonces,senderNonce,nonceExact,?_,?_,?_,finalSupport,freshAccounts⟩⟩
  · intro a outside
    have apart : a ≠ tx.sender ∧ a ≠ ReachableCalls.address kind ∧ a ≠ tx.header.beneficiary := by
      simpa only [addresses,List.mem_cons,List.not_mem_nil,or_false,not_or] using outside
    unfold journal
    rw [ReferenceOrdinaryBlockAccounts.outside kind tx checks found nonblob emptyHash accountsParent before codeParent parent loaded balances actual receipt a apart.1 apart.2.1 apart.2.2,freshAccounts]
  · intro a
    unfold journal
    rw [ReferenceOrdinaryBlockAccounts.hash kind tx checks found nonblob emptyHash accountsParent before codeParent parent loaded balances actual receipt a]
    unfold ReferenceSourceValueTransfer.hashAt ReferenceSourceValueTransfer.account ReferenceAccountLookup.peek
    rw [freshAccounts]
    rfl
  · exact (ReferenceOrdinaryBlockAccounts.code kind tx checks found nonblob emptyHash accountsParent before codeParent parent loaded balances actual receipt).trans freshCode

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceFullFeeBlockReceipt
