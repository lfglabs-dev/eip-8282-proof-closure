import Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry

/-! Actual mandatory SYSTEM evaluation with computational fuel derived from
its source gas potential. This produces a supported completed local outcome;
it does not equate computational completion with successful EVM execution.
The extracted final dispatch, journal and events feed SystemTotal directly. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def fuel (kind : ReachableCalls.Contract) (c : Context) := ReferenceExecutionPotential.potential (meter kind c)+1

noncomputable def run {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) :=
  ReferenceCheckedAccountEvaluator.eval accountsParent
    (ReferenceInitialAccess.destinations (call kind c).code) (storageParent c) ByteArray.empty (fuel kind c)
    (entered kind c emptyHash accountsParent codeParent).2.accounts
    (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)

theorem computed {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ events result finalAccounts,
      run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts) ∧
      ReferenceSupportedOutcome.Finalized result := by
  obtain ⟨slots,owner,warm,context⟩ := bindings kind c history emptyHash accountsParent codeParent loaded
  have stack : (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) rfl
  have enough : run kind c emptyHash accountsParent codeParent ≠ none :=
    ReferenceCheckedAccountEvaluator.sufficient context stack aligned (Nat.lt_succ_self _)
  cases actual : run kind c emptyHash accountsParent codeParent with
  | none => exact False.elim (enough actual)
  | some pair =>
    rcases pair with ⟨⟨events,result⟩,finalAccounts⟩
    refine ⟨events,result,finalAccounts,rfl,?_⟩
    exact ReferenceSupportedOutcome.account_evaluated (xi kind c) context actual slots owner warm
      (by rw [(constructed kind c history).2.2.2]) (by change 0 < UInt256.size; decide)

theorem extracted {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    {events result finalAccounts}
    (actual : run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts)) :
    ∃ finish finalWarm final,
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) (storageParent c)
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (storageParent c) finish finalWarm final ByteArray.empty = result ∧
      finalAccounts.writes = (entered kind c emptyHash accountsParent codeParent).2.accounts.writes := by
  obtain ⟨_,_,_,context⟩ := bindings kind c history emptyHash accountsParent codeParent loaded
  have erased := ReferenceCheckedAccountEvaluator.evaluated context actual
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context erased.1
  exact ⟨finish,finalWarm,final,trace,last,erased.2⟩

#print axioms computed
#print axioms extracted
end Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution
