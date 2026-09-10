import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
import Eip8282.Audit.Integrator.ReferenceTransferredFailure

/-! Common entry producer for successful and failed protected calls. The same
before-transfer code, slots and balances derive transfer admission and runtime
slots. No post-transfer condition is assumed. Python context construction and
pre-state representation are separate application obligations. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedEntry
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem prepared {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
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
  refine ⟨ReferenceSourceTransferFunding.after_history emptyHash accountsParent start c shouldTransfer history startBalances funded,?_⟩
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
end Eip8282.Audit.Integrator.ReferenceSourceFundedEntry
