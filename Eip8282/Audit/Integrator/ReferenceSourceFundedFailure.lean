import Eip8282.Audit.Integrator.ReferenceSourceFundedEntry
import Eip8282.Audit.Integrator.ReferenceTransferredFailure

/-! Source transfer admission is derived before applying the same failed
runtime/snapshot consumer. The independent inputs are pre-transfer balance
read correspondence and sender funding, not transfer success, recipient fit,
chosen wealth maximum or failure post-state. Full source frame/world bindings
and canonical admission remain open. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code input) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code input) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    let live := {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live before
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle before.storage [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = before.accounts.writes ∧
      restored.codeWrites = before.codeWrites ∧ restored.transient = before.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p before.storage address key := by
  have entered := (ReferenceSourceFundedEntry.prepared c history input emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots).1
  exact ReferenceTransferredFailure.settled c history input emptyHash accountsParent before codeParent shouldTransfer
    context loaded entered actual slots warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceSourceFundedFailure
