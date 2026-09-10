import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
import Eip8282.Audit.Integrator.ReferenceTransferredFailure

/-! Source entry producer factored at the numeric bound actually consumed.
ReferenceCheckpointGuarantees derives this bound from the history BEFORE the
transaction and its literal prepayment, avoiding an artificial intermediate
History assumption. The earlier history-based public entry is unchanged. -/
namespace Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem prepared {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (input : ReleaseCandidate.CallInput kind c)
    (total : TransferFunding.worldFunds c.world < UInt256.size)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceStorageView.Related parent (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage
      (CallBridge.codeCall c (code input) 0).entry.toState := by
  let start := fetched emptyHash accountsParent before codeParent c.target
  have startBalances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent start c.world := balances
  refine ⟨ReferenceSourceTransferFunding.enter_success emptyHash accountsParent start c shouldTransfer startBalances funded total,?_⟩
  have fetchedLoad : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      start.accounts codeParent start.codeWrites c.target).1 = .ok c.code := loaded
  have nonempty : c.code ≠ ByteArray.empty := by
    rw [code input]
    cases kind <;> decide +kernel
  have hashNonempty := ReferenceSourceValueTransfer.loaded_nonempty_hash emptyHash accountsParent start codeParent c.target fetchedLoad nonempty
  intro q
  change ReferenceStorageView.current parent (ReferenceSourceValueTransfer.enter emptyHash accountsParent start c.caller c.target c.value shouldTransfer).2.storage c.target q.toByteArray = _
  rw [ReferenceSourceValueTransfer.enter_protected_storage emptyHash accountsParent start c.caller c.target c.target c.value shouldTransfer hashNonempty]
  exact (slots q).trans (TransferFrame.codeCall_storage c (code input) 0 q).symm

#print axioms prepared
end Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds
