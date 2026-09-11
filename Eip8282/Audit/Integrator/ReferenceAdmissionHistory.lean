import Eip8282.Audit.Integrator.ReferenceCalldataAdmission
import Eip8282.Audit.Integrator.TransactionCommittedEffects

/-! Source calldata-floor admission feeds the existing actual history and
committed-effect consumers directly. It is not converted into the different
pinned intrinsicGas gate. Source transaction/state/execution and full validator
extraction are still required to identify these inputs with Ethereum. -/
namespace Eip8282.Audit.Integrator.ReferenceAdmissionHistory
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
    {recipientExecution accessTokens : Nat}
    (floorGate : ReferenceCalldataAdmission.Gate r.call.transaction.base.data.size recipientExecution accessTokens)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel) :
    ActualJournalHistory.Trace initial (receipts++[r]) credits r.world :=
  ActualJournalHistory.Trace.transaction history r linked account funded
    (ReferenceCalldataAdmission.data_fit r.call.transaction.base.data floorGate) resources

theorem receipt_effects {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (funded : TransactionFunding.Admission r.call account)
    {recipientExecution accessTokens : Nat}
    (floorGate : ReferenceCalldataAdmission.Gate r.call.transaction.base.data.size recipientExecution accessTokens)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (invariant : Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128)
    (queue : JournalPathQueues.Queue kind)
    (represented : QueueInvariant.Represents (modelKind kind)
      (SystemSpec.worldSlot r.call.world (address kind)) queue) :
    TransactionCommittedEffects.Effects kind r queue :=
  TransactionCommittedEffects.receipt_effects r history funded funds
    (ReferenceCalldataAdmission.data_fit r.call.transaction.base.data floorGate)
    resources invariant bound queue represented

#print axioms append
#print axioms receipt_effects
end Eip8282.Audit.Integrator.ReferenceAdmissionHistory
