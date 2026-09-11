import Eip8282.Audit.Integrator.ReferenceSourceCompletedBalances

/-! Same three guarantees and source settled balances of the very same replay
receipt world. The computed runtime endpoint and source transfer are shared;
old-runtime balance preservation closes the post-world connection. The additional
transfer-mode condition scopes these stronger exports, not earlier guarantees.
Full Python frame extraction, source gas and ancestor settlement remain open. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

theorem terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
      kind c parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have original := ReferenceSourceFundedGuarantees.terminal history pinned emptyHash accountsParent before codeParent shouldTransfer
    context actual loaded balances funded slots warmRelated grant fit
  have sameBalances := ReferenceSourceBalanceOutcome.evaluated emptyHash accountsParent before codeParent c shouldTransfer
    history balances funded mode actual
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
    (ReleaseCandidate.installed_call history pinned) original.2.1 balances sameBalances
  exact ⟨original.1,completed,original.2.2,sameBalances⟩

theorem eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
      kind c parent events view true output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have original := ReferenceSourceFundedGuarantees.eof history pinned emptyHash accountsParent before codeParent shouldTransfer
    context actual loaded balances funded slots warmRelated grant fit
  have sameBalances := ReferenceSourceBalanceOutcome.evaluated emptyHash accountsParent before codeParent c shouldTransfer
    history balances funded mode actual
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    (ReleaseCandidate.installed_call history pinned) original.2.2.1 balances sameBalances
  exact ⟨original.1,original.2.1,completed,original.2.2.2,sameBalances⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees
