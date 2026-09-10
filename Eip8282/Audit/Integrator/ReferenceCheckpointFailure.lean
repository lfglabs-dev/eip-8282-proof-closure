import Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome
import Eip8282.Audit.Integrator.ReferenceCheckpointCall
import Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds
import Eip8282.Audit.Integrator.ReferencePinnedFailure

/-! Same failed computed frame, now at the actual admitted transaction's
checkpoint. The initialized history is before prepayment. Caller funding,
installed owner and transfer success are derived; the exact saved snapshot
restores its pre-transfer balances and four write components. Source frame,
admission compatibility, gas and ancestor bindings remain explicit limits. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckpointFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

open ReferenceCheckpointCall (call)
private theorem input (kind : Contract) (transaction : RefundAccounting.Context) :
    ReleaseCandidate.CallInput kind (call kind transaction) := ⟨rfl,rfl,rfl⟩
private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> rfl

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before (call kind transaction).world)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot (call kind transaction).world (call kind transaction).target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall (call kind transaction) (code kind transaction) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : (call kind transaction).calldata.size < UInt256.size) :
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    let live := {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live before
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent restored (call kind transaction).world ∧
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
  have facts := ReferenceCheckpointCall.domain kind transaction history admission
  have pinned := ReferenceCheckpointCall.pinned kind transaction history admission
  have ready := ReferenceSourcePreparedBounds.prepared (call kind transaction) (input kind transaction) facts.2.2.2
    emptyHash accountsParent before codeParent shouldTransfer parent loaded balances facts.2.2.1 slots
  refine ⟨ReferenceCheckpointCall.selected_request kind transaction recipient,
    ReferenceCheckpointCall.call_result kind transaction history admission,
    ReferenceSourceBalanceOutcome.restored emptyHash accountsParent _ before (call kind transaction).world balances, ?_⟩
  exact ReferencePinnedFailure.settled (call kind transaction) pinned emptyHash accountsParent before codeParent shouldTransfer
    context loaded ready.1 actual slots warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceCheckpointFailure
