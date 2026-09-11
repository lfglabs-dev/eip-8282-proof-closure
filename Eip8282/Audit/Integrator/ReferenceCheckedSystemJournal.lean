import Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution
import Eip8282.Audit.Integrator.ReferenceSettledAccountJournal

/-! SYSTEM has no value movement or fee credits. Its actual runtime preserves
account writes; settlement retains live reads and uses the same receipt's
storage. Full source account observations are unchanged for every outcome,
without asserting full account equality between source and replay semantics. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer ReferenceCheckedSystemEntry
open ReferenceSettledAccountJournal (journal)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem unchanged {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (emptyHash : Hash)
    (accountsParent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt)
    (writes : finalAccounts.writes = (entered kind c emptyHash accountsParent codeParent).2.accounts.writes) :
    let settled := journal (before Hash) (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
    settled.accounts.writes = (before Hash).accounts.writes ∧
    settled.accounts.reads = finalAccounts.reads ∧
    settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
    settled.storage = receipt.storage ∧
    ∀ a, account emptyHash accountsParent settled a = account emptyHash accountsParent (before Hash) a := by
  have entryEq := (ready kind c emptyHash accountsParent codeParent loaded).2
  rw [entryEq] at writes ⊢
  have beforeWrites : finalAccounts.writes = (before Hash).accounts.writes := writes
  dsimp only
  unfold journal
  dsimp only
  split
  · refine ⟨beforeWrites,rfl,rfl,rfl,rfl,?_⟩
    intro a
    unfold account ReferenceAccountLookup.peek
    rw [beforeWrites]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩

#print axioms unchanged
end Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal
