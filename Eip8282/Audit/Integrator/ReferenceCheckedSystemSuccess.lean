import Eip8282.Audit.Integrator.ReferenceCheckedSystemWhole
import Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal

/-! Mandatory SYSTEM success is derived from the existing source-paid trace
and identified with the same computed account evaluator used by SystemTotal.
No independent successful endpoint is assumed. The initialized History/code
load domain and audited source semantics remain explicit. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemSuccess
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem erased {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ events ended, ReferenceCheckedEvaluator.eval (ReferenceInitialAccess.destinations (call kind c).code) true
      (storageParent c) ByteArray.empty (ReferenceCheckedSystemExecution.fuel kind c)
      (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c) =
        some (events,.terminal ended) ∧ ended.halt = .returned := by
  have installed := (ReleaseCandidate.invariants history).2.2.2 kind |>.1
  let sourceXi := ProtocolSystemDispatchExtraction.xi kind c.world c.genesis c.blocks c.header c.baseFee 8502 ByteArray.empty installed
  obtain ⟨h,whole⟩ := ProtocolSystemDispatchExtraction.source_whole kind c.world c.genesis c.blocks c.header c.baseFee 8502 (by decide) installed
  have sameView : initial sourceXi (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).state =
      initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage := by
    rw [(ready kind c emptyHash accountsParent codeParent loaded).2]
    unfold sourceXi ProtocolSystemDispatchExtraction.xi initial xi CallBridge.codeCall
    dsimp only
    have frameEq : ProtocolSystemDispatchExtraction.frame
        (ProtocolSystemDispatchExtraction.unchecked (ReachableCalls.address kind) ByteArray.empty c.baseFee)
        c.world c.genesis c.blocks c.header (8502+1) = call kind c := (constructed kind c history).1
    rw [frameEq]
    rfl
  have sameMeter : ProtocolSystemDispatchExtraction.meter (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee) =
      ReferenceMeterBoundary.core (meter kind c) := rfl
  have atEntry : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime (JournalInvariant.modelKind kind)) sourceXi.entry := by
    cases kind with
    | deposit => exact ⟨sourceXi.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    | exit => exact ⟨sourceXi.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  have context := (bindings kind c history emptyHash accountsParent codeParent loaded).2.2.2
  rw [sameMeter] at whole
  obtain ⟨events,ended,actual,halt,_⟩ := ReferenceCheckedSystemWhole.evaluated whole atEntry context
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  rw [sameView] at actual
  exact ⟨events,ended,actual,halt⟩

theorem owner {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (emptyHash : Hash)
    (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts
      (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).env.codeOwner).isSome = true := by
  have emptyWrites : ∀ a, (entered kind c emptyHash accountsParent codeParent).2.accounts.writes a = none := by
    rw [(ready kind c emptyHash accountsParent codeParent loaded).2]; intro a; rfl
  exact ReferenceCodeAccountPresence.fresh_system_owner ReferenceSourceValueTransfer.Account.codeHash emptyHash
    accountsParent (before Hash).accounts (entered kind c emptyHash accountsParent codeParent).2.accounts
    (fun _ => rfl) emptyWrites codeParent (before Hash).codeWrites (ReachableCalls.address kind) loaded
    (by cases kind <;> decide +kernel)

/-- The account-aware computation itself succeeds. Pairing two unrelated runs
is avoided by exact evaluator projection and deterministic result equality. -/
theorem execution {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ events ended finalAccounts,
      ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,.terminal ended),finalAccounts) ∧
      ended.halt = .returned := by
  obtain ⟨events,result,finalAccounts,actual,_⟩ := ReferenceCheckedSystemExecution.computed kind c history emptyHash accountsParent codeParent loaded
  obtain ⟨paidEvents,ended,paidRun,halt⟩ := erased kind c history emptyHash accountsParent codeParent loaded
  have context := (bindings kind c history emptyHash accountsParent codeParent loaded).2.2.2
  have same := (ReferenceCheckedAccountEvaluator.evaluated context actual (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)).1
  rw [owner kind c emptyHash accountsParent codeParent loaded] at same
  have identical := Option.some.inj (same.symm.trans paidRun)
  cases identical
  exact ⟨events,ended,finalAccounts,actual,halt⟩

#print axioms erased
#print axioms owner
#print axioms execution
end Eip8282.Audit.Integrator.ReferenceCheckedSystemSuccess
