import Eip8282.Audit.Integrator.ReferenceSourceFundedEntry
import Eip8282.Audit.Integrator.ReferenceAccountGuarantees

/-! All three same-outcome checked guarantee consumers now start before source
value transfer. Initialized funding plus initial balance correspondence derives
transfer success; code/slot preservation derives runtime slots. The output
still uses the explicit synthetic replay/old-world observation boundary of
ReferenceCheckedTheta.Completed; source gas and canonical Ethereum are not
identified with those receipts. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees
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
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceCheckedTheta.Completed kind c parent events result.view
      (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes := by
  have ready := ReferenceSourceFundedEntry.prepared c history pinned emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots
  exact ⟨ready.1,ReferenceAccountGuarantees.terminal history pinned context actual ready.2 warmRelated grant fit⟩

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
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceCheckedTheta.Completed kind c parent events view true output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes := by
  have ready := ReferenceSourceFundedEntry.prepared c history pinned emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots
  exact ⟨ready.1,ReferenceAccountGuarantees.eof history pinned context actual ready.2 warmRelated grant fit⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees
