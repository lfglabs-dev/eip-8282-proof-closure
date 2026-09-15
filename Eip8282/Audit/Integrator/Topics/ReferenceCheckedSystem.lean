import Eip8282.Audit.Integrator.Topics.ReferenceCheckedSystem2
import Eip8282.Audit.Integrator.Topics.ReferenceSystem3

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckedSystemTotal -/

/-! One exhaustive checked mandatory SYSTEM computation, three predicates,
complete local receipt/journal settlement and top-level gas conversions.
Initialized history, represented block storage and actual pinned source code
read are the domain. No outcome/trace/post-state premise is supplied. Successful
drain within source resources is established by the stronger SystemDrainTotal;
this safety theorem preserves failures rather than silently assuming success. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal
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
    ∃ events result finalAccounts finish finalWarm final receipt,
      ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts) ∧
      ReferenceCheckedSystemOutcome.Claims kind c events result ∧
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) (storageParent c)
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (storageParent c) finish finalWarm final ByteArray.empty = result ∧
      ReferenceCheckedFrameOutcome.settle (before Hash).storage [] finalWarm result = .returned receipt ∧
      ReferenceSystemOutputMeter.Facts (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).stateGasReservoir receipt.meter ∧
      let settled := journal (before Hash) (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
      settled.accounts.writes = (before Hash).accounts.writes ∧
      settled.accounts.reads = finalAccounts.reads ∧
      settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
      settled.storage = receipt.storage ∧
      ∀ a, ReferenceSourceValueTransfer.account emptyHash accountsParent settled a =
        ReferenceSourceValueTransfer.account emptyHash accountsParent (before Hash) a := by
  have inputs := constructed kind c history
  have ready := (ReferenceCheckedSystemEntry.ready kind c emptyHash accountsParent codeParent loaded).2
  refine ⟨inputs.1,inputs.2.2.1,by rw [ready],?_⟩
  obtain ⟨events,result,finalAccounts,actual,supported⟩ := ReferenceCheckedSystemExecution.computed kind c history emptyHash accountsParent codeParent loaded
  obtain ⟨finish,finalWarm,final,trace,last,writes⟩ := ReferenceCheckedSystemExecution.extracted kind c history emptyHash accountsParent codeParent loaded actual
  have claims := (ReferenceCheckedSystemOutcome.proved kind c history emptyHash accountsParent codeParent loaded actual supported finalWarm).1
  have fresh : (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).storage = ReferenceRuntimeStateBalance.emptyTx := by rw [ready]; rfl
  obtain ⟨receipt,settled,fields⟩ := ReferenceSystemOutputReceipt.settled trace
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl) fresh rfl rfl inputs.2.2.2.le last claims (before Hash).storage
  exact ⟨events,result,finalAccounts,finish,finalWarm,final,receipt,actual,claims,trace,last,settled,fields,
    ReferenceCheckedSystemJournal.unchanged kind c emptyHash accountsParent codeParent loaded finalAccounts receipt writes⟩

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal

end

section

/-! ## ReferenceCheckedSystemWhole -/

/-! Whole's paid actual SYSTEM trace is one successful checked computation.
The result's output, storage and logs are those of that same trace. Source
meter potential supplies computational budget; replay gas is never substituted.
Consumer: mandatory SYSTEM success from source_whole and constructed entry. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemWhole
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceSystemSourcePayment ReferenceExecutionPotential
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem evaluated {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : SystemExecutionResources.Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {warm : Warm} {meter : Meter} {destinations : List Nat}
    (whole : Whole parent created h v warm (core meter))
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ∃ events ended,
      ReferenceCheckedEvaluator.eval destinations true parent ByteArray.empty (potential meter+1) v warm meter =
        some (events,.terminal ended) ∧
      ended.halt = .returned ∧ ended.output = h.output ∧
      ReferenceStorageView.Related parent ended.view.storage h.finalState.toState ∧
      ended.view.logs = ProtectedLogFrame.project h.finalState.executionEnv.codeOwner h.finalState.substate := by
  obtain ⟨prefixEvents,events,finalCore,finish,finalWarm,off,len,rest,coupled,related,warmRelated,createdEq,
    decoded,shape,result,outputEq,costEq,eventEq,paid,execution,reservoir,lastWarm⟩ := whole
  subst events
  have fullPaid : runFull (prefixEvents++[.ordinary (terminalCost finish off len)]) meter =
      some (update meter finalCore) := by simp only [runFull,paid,Option.map_some]
  rw [ReferenceCheckedRuntimeTrace.runFull_append] at fullPaid
  obtain ⟨lastMeter,prefixPaid,returnPaid⟩ := Option.bind_eq_some_iff.mp fullPaid
  obtain ⟨trace,continuation⟩ := ReferenceCheckedSystemTraceForward.coupled coupled site context aligned prefixPaid
  have lengthBound := trace.length_bound stack aligned
  have lastAligned : ReferenceActionMemoryBounds.Aligned finish := by
    unfold ReferenceActionMemoryBounds.Aligned
    rw [words_related related]
    exact related.memory.size
  have enough : prefixEvents.length ≤ potential meter := by omega
  obtain ⟨budget,budgetEq⟩ := Nat.exists_eq_add_of_le enough
  have terminal := ReferenceCheckedSystemReturn.evaluated (destinations := destinations) (parent := parent) (warm := finalWarm) decoded shape lastAligned returnPaid budget ByteArray.empty
  have actual := continuation (budget+1) ByteArray.empty
  rw [terminal] at actual
  have budgetFit : prefixEvents.length+(budget+1) = potential meter+1 := by omega
  rw [budgetFit] at actual
  simp only [Option.map_some,List.append_nil] at actual
  exact ⟨prefixEvents,ReferenceCheckedSystemReturn.result finish off len rest (update meter finalCore),
    actual,rfl,outputEq.symm,result.storage,result.logs⟩

#print axioms evaluated
end Eip8282.Audit.Integrator.ReferenceCheckedSystemWhole

end

section

/-! ## ReferenceCheckedSystemSuccess -/

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

end

section

/-! ## ReferenceCheckedSystemDrainTotal -/

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

end
