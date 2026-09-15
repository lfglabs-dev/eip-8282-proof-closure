import Eip8282.Audit.Integrator.CallOwnerCoherence
import Eip8282.Audit.Integrator.ReferencePinnedFailure
import Eip8282.Audit.Integrator.Topics.ReferenceSource
import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.Topics.Transaction2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckpointCall -/

/-! Initialized history is needed before the admitted transaction, not invented
at its post-prepayment checkpoint. The actual checkpoint and selected message
supply the call's invariant, funding, installed code and world bound. The old
admission/transaction semantics remain explicit; Amsterdam field extraction and
blob/type4 compatibility are not claimed by these producers. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckpointCall
open EvmYul EvmYul.EVM
open ReachableCalls (Contract address runtime)
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def call (kind : Contract) (tx : RefundAccounting.Context) : MessageCall.Context :=
  (TransactionEventBounds.message tx (address kind)).context (tx.fuel-1) (runtime kind)

/-- Domain facts follow the same literal balance/nonce debit checkpoint. -/
theorem domain {deposit exit : TransactionAppendBudget.Receipt} (kind : Contract)
    (tx : RefundAccounting.Context) (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : Account .EVM} (admission : TransactionFunding.Admission tx sender) :
    JournalInvariant.Invariant kind (ActualJournalHistory.work history.receipts) (call kind tx).world ∧
    ActualJournalHistory.work history.receipts < 2^128 ∧
    (call kind tx).value.toNat ≤ TransferFunding.worldBalance (call kind tx).world (call kind tx).caller ∧
    TransferFunding.worldFunds (call kind tx).world < UInt256.size := by
  have initial := ReleaseCandidate.invariants history
  have current := JournalInvariant.frame (initial.2.2.2 kind)
    (TransactionJournalEdges.checkpoint_frame tx admission (address kind))
  have total := FundingHistory.trace_funds (ProtocolCreditEnvelope.ledger_bound history.ledger).1
  have beforeBound := total.trans_lt (LedgerCreditSafety.genesis_budget history.ledger history.counts)
  have debit := TransactionFunding.checkpoint_debit tx admission
  refine ⟨current,initial.2.2.1,TransactionFunding.checkpoint_funded tx admission,?_⟩
  change TransferFunding.worldFunds tx.checkpoint < UInt256.size
  omega

theorem pinned {deposit exit : TransactionAppendBudget.Receipt} (kind : Contract)
    (tx : RefundAccounting.Context) (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : Account .EVM} (admission : TransactionFunding.Admission tx sender) :
    ReachableCalls.PinnedCall kind (call kind tx) := by
  obtain ⟨account,found,code⟩ := (domain kind tx history admission).1.1
  exact ⟨rfl,rfl,⟨account,found,code⟩,rfl⟩

theorem selected_code {deposit exit : TransactionAppendBudget.Receipt} (kind : Contract)
    (tx : RefundAccounting.Context) (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : Account .EVM} (admission : TransactionFunding.Admission tx sender) :
    toExecute .EVM tx.checkpoint (address kind) = .Code (runtime kind) :=
  CallOwnerCoherence.installed_toExecute (domain kind tx history admission).1.1

/-- Actual transaction recipient selects this message request, rather than
an arbitrary call on a separately assumed intermediate history. -/
theorem selected_request (kind : Contract) (tx : RefundAccounting.Context)
    (recipient : tx.transaction.base.recipient = some (address kind)) :
    TransactionEventBounds.request tx = .theta tx.fuel (TransactionEventBounds.message tx (address kind)) := by
  simp only [TransactionEventBounds.request,recipient]

/-- This context's original resource result is the actual selected Theta.
Later source guarantee receipts still state explicitly when they use replay gas. -/
theorem call_result {deposit exit : TransactionAppendBudget.Receipt} (kind : Contract)
    (tx : RefundAccounting.Context) (history : ReleaseCandidate.History deposit exit tx.world)
    {sender : Account .EVM} (admission : TransactionFunding.Admission tx sender)
    (fuel : 0 < tx.fuel) :
    (call kind tx).result = (Request.theta tx.fuel (TransactionEventBounds.message tx (address kind))).eval := by
  unfold Request.eval TransactionEventBounds.message
  rw [selected_code kind tx history admission]
  change Θ (tx.fuel-1+1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [Nat.sub_add_cancel (by omega)]
  rfl

#print axioms domain
#print axioms pinned
#print axioms selected_code
#print axioms selected_request
#print axioms call_result
end Eip8282.Audit.Integrator.ReferenceCheckpointCall

end

section

/-! ## ReferenceCheckpointFailure -/

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

end
