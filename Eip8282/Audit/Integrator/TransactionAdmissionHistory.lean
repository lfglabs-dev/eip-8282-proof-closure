import Eip8282.Audit.Integrator.TransactionCalldataAdmission
import Eip8282.Audit.Integrator.TransactionCommittedEffects

/-! Intrinsic admission feeds the existing actual journal-history constructor
and committed-effect consumer. Calldata fit is derived, not another arbitrary
history premise. Funding, full validator extraction and execution resources
remain explicit; the existing admission structure and trace are unchanged. -/
namespace Eip8282.Audit.Integrator.TransactionAdmissionHistory
open EvmYul EvmYul.EVM
open NestedEvents
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address)
open JournalInvariant (Invariant modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem append {initial before : World} {receipts : List Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (r : Receipt) (linked : r.call.world = before) (account : Account .EVM)
    (funded : TransactionFunding.Admission r.call account)
    (intrinsic : intrinsicGas r.call.transaction ≤ r.call.transaction.base.gasLimit.toNat)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel) :
    ActualJournalHistory.Trace initial (receipts++[r]) credits r.world :=
  ActualJournalHistory.Trace.transaction history r linked account funded
    (TransactionCalldataAdmission.calldata_fit r.call.transaction intrinsic) resources

/-- Committed occurrences, physical queue and logs use the same real receipt.
The root calldata gate now follows from intrinsic admission; nested sizes
continue to follow the actual word-sized call arguments. -/
theorem receipt_effects {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (funded : TransactionFunding.Admission r.call account)
    (intrinsic : intrinsicGas r.call.transaction ≤ r.call.transaction.base.gasLimit.toNat)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (invariant : Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128)
    (queue : JournalPathQueues.Queue kind)
    (represented : QueueInvariant.Represents (modelKind kind)
      (SystemSpec.worldSlot r.call.world (address kind)) queue) :
    TransactionCommittedEffects.Effects kind r queue :=
  TransactionCommittedEffects.receipt_effects r history funded funds
    (TransactionCalldataAdmission.calldata_fit r.call.transaction intrinsic)
    resources invariant bound queue represented

#print axioms append
#print axioms receipt_effects
end Eip8282.Audit.Integrator.TransactionAdmissionHistory
