import Eip8282.Audit.Integrator.ReferenceDerivedFailure
import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Existing initialized history derives the old entry owner needed by the
PC replay proof. The same source account-aware failure then derives its catch
classification and projected rollback/meter/log settlement. No independent
owner Bool, old HasOwner, caught-fault or desired postcondition is supplied.
This is not yet full source/old-world equality or source transaction closure;
account payloads, value transfer and actual saved frame identity stay open.
-/
namespace Eip8282.Audit.Integrator.ReferenceHistoryFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Account Hash Error : Type} [DecidableEq Hash] {kind : Contract}
    (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (codeWrites : Hash → Option ByteArray)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm partialWarm : Warm} {pre partialMeter : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx Account}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites
      c.target).1 = .ok c.code)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites c.target).2
      (initial (CallBridge.codeCall c (code input) 0) tx) warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code input) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code input) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle tx [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage.created = view.storage.created ∧ receipt.storage.reads = view.storage.reads ∧
      ∀ p address key, ReferenceStorageView.current p receipt.storage address key =
        ReferenceStorageView.current p tx address key := by
  exact ReferenceDerivedFailure.settled (CallBridge.codeCall c (code input) 0)
    codeHash emptyHash accountsParent accounts codeParent codeWrites context loaded actual slots
    (TransferFrame.pinned_codeCall_hasOwner c (ReleaseCandidate.installed_call history input) (code input) 0)
    warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceHistoryFailure
