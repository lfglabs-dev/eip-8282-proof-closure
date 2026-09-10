import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.TransactionJournalEdges
import Eip8282.Audit.Integrator.CallOwnerCoherence

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
