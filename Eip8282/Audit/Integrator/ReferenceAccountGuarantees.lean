import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator
import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Concrete consumers of account-aware checked evaluation. All three
observations use its same computed terminal/EOF; owner presence is obtained
from the layered account lookup rather than an independent Bool. Installed
old owner/invariants remain derived from the actual initialized history.
This does not identify the layered source account payloads with the old World,
source frame snapshots, or Ethereum history. Replay resources remain synthetic.
-/
namespace Eip8282.Audit.Integrator.ReferenceAccountGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

/-- Computed terminal from the same transferred entry consumes the derived
history domain. No assumed old success, old trace, owner, queue, safe fee input
or 2^128 budget is required. Source grant and storage/warm bindings are explicit. -/
theorem terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel accounts
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some ((events,.terminal result),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    ReferenceCheckedTheta.Completed kind c parent events result.view
      (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = accounts.writes := by
  have stack : (initial (CallBridge.codeCall c (code pinned) 0) tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (CallBridge.codeCall c (code pinned) 0) tx) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  exact ⟨ReleaseCandidate.checked_terminal history pinned context checked slots warmRelated grant fit,writes⟩

/-- Genuine computed EOF is covered by the same history-derived predicates. -/
theorem eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel accounts
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    output = ByteArray.empty ∧ ReferenceCheckedTheta.Completed kind c parent events view true output ∧ finalAccounts.writes = accounts.writes := by
  have stack : (initial (CallBridge.codeCall c (code pinned) 0) tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (CallBridge.codeCall c (code pinned) 0) tx) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  obtain ⟨empty,observed⟩ := ReleaseCandidate.checked_eof history pinned context checked slots warmRelated grant fit
  exact ⟨empty,observed,writes⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceAccountGuarantees
