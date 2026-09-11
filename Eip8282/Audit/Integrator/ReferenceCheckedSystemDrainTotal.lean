import Eip8282.Audit.Integrator.ReferenceCheckedSystemSuccess

/-! Successful mandatory SYSTEM drain on the same checked execution and
complete local settlement. This strengthens SystemTotal's exhaustive safety
without a new entry premise: Whole's existing resource producer now supplies
actual evaluator success. Canonical block incorporation and applicability of
History/source transcriptions remain separate obligations. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemDrainTotal
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceSettledAccountJournal (journal)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ProtocolSystemDispatchExtraction.frame (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee)
      c.world c.genesis c.blocks c.header 8503 = call kind c ∧
    (∀ signature, ReferenceCallEntry.logs (call kind c) true signature = []) ∧
    (entered kind c emptyHash accountsParent codeParent).1 = .ok () ∧
    ∃ events ended finalAccounts finish finalWarm final receipt,
      ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,.terminal ended),finalAccounts) ∧
      ReferenceCheckedSystemOutcome.Claims kind c events (.terminal ended) ∧
      ended.halt = .returned ∧
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) (storageParent c)
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (storageParent c) finish finalWarm final ByteArray.empty = .terminal ended ∧
      ReferenceCheckedFrameOutcome.settle (before Hash).storage [] finalWarm (.terminal ended) = .returned receipt ∧
      ReferenceSystemOutputMeter.Facts (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).stateGasReservoir receipt.meter ∧
      receipt.error = none ∧ receipt.storage = ended.view.storage ∧ receipt.output = ended.output ∧
      receipt.meter = ended.meter ∧ receipt.logsForParent = ended.view.logs ∧
      let settled := journal (before Hash) (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
      settled.accounts.writes = (before Hash).accounts.writes ∧
      settled.accounts.reads = finalAccounts.reads ∧
      settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
      settled.storage = receipt.storage ∧
      ∀ a, ReferenceSourceValueTransfer.account emptyHash accountsParent settled a =
        ReferenceSourceValueTransfer.account emptyHash accountsParent (before Hash) a := by
  obtain ⟨frame,logs,entry,events,outcome,finalAccounts,finish,finalWarm,final,receipt,
    actual,claims,trace,last,settled,fields,journalFacts⟩ :=
    ReferenceCheckedSystemTotal.verified kind c history emptyHash accountsParent codeParent loaded
  obtain ⟨paidEvents,ended,paidAccounts,paidRun,halt⟩ :=
    ReferenceCheckedSystemSuccess.execution kind c history emptyHash accountsParent codeParent loaded
  have identical := Option.some.inj (actual.symm.trans paidRun)
  cases identical
  have receiptEq : receipt = ReferenceCheckedFrameOutcome.success [] ended.view finalWarm ended.meter ended.output := by
    simp only [ReferenceCheckedFrameOutcome.settle,halt,
      show ReferenceCheckedTerminalStep.Halt.returned ≠ .reverted by decide,if_false,
      ReferenceCheckedFrameOutcome.Boundary.returned.injEq] at settled
    exact settled.symm
  refine ⟨frame,logs,entry,events,ended,finalAccounts,finish,finalWarm,final,receipt,
    actual,claims,halt,trace,last,settled,fields,?_,?_,?_,?_,?_,journalFacts⟩
  all_goals simp [receiptEq,ReferenceCheckedFrameOutcome.success]

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceCheckedSystemDrainTotal
