import Eip8282.Audit.Integrator.Topics.Protocol
import Eip8282.Audit.Integrator.FactoryHistoryGuarantees

/-! Compose the proposed empty SYSTEM pair after exact real factory deployment
and one linked funded history. Both pre-call invariants and the numerical work
bound are derived; the canonical ledger/deployment/dispatch producers and policy
decision remain explicit. A conditional sequence does not adopt a fork. -/
namespace Eip8282.Audit.Integrator.FactorySystemSequence
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open TransactionAppendBudget (Receipt BlockReceipt)
open FactoryHistoryGuarantees (Inputs)
open JournalInvariant (Invariant)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Neither a queue invariant nor a convenient wealth/work ceiling is supplied
at SYSTEM entry. Actual deployment, history, ledger and block receipts produce
them, and the same two constructed SYSTEM transitions extend that history. -/
theorem from_genesis_both (deposit exit : Receipt) (dep : Inputs .deposit deposit.call)
    (ext : Inputs .exit exit.call) (linked : exit.call.world = deposit.world)
    {before : AccountMap .EVM} {baseCredits credits pow withdrawals migrations : Nat}
    {receipts : List Receipt}
    (prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world)
    (history : ActualJournalHistory.Trace exit.world receipts credits before)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations
      (baseCredits+credits) before)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    (genesis : BlockHeader) (processed : ProcessedBlocks) (header : BlockHeader)
    (gasPrice : UInt256) (fuel : Nat) (resources : 8503 ≤ fuel) :
    deposit.success = true ∧ exit.success = true ∧
    ∃ after, ∃ pair : ProtocolSystemSequence.EmptyPair before after genesis processed header gasPrice fuel,
      ActualJournalHistory.Trace exit.world receipts credits after ∧
      (∀ kind, Invariant kind (ActualJournalHistory.work receipts) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  have creditBudget := LedgerCreditSafety.genesis_budget ledger counts
  obtain ⟨hd,he,seedFunds,seedInv⟩ := FactoryHistoryGuarantees.two_seeds deposit exit dep ext linked prior (by omega)
  have funds := (GenesisWorldFunding.funding_budget ledger counts).2
  have workBound := ActualJournalHistory.work_lt_of_blocks receipts blocks listed slots
  have beforeInv : ∀ kind, Invariant kind (ActualJournalHistory.work receipts) before :=
    fun kind => ActualJournalHistory.preserves history seedFunds (seedInv kind) funds workBound
  obtain ⟨after,pair,extended,finalInv,depGuards,extGuards⟩ :=
    ProtocolSystemSequence.extends_history genesis processed header gasPrice fuel history
      (fun _ => ActualJournalHistory.work receipts) beforeInv (fun _ => workBound) resources
  exact ⟨hd,he,after,pair,extended,finalInv,depGuards,extGuards⟩

#print axioms from_genesis_both
end Eip8282.Audit.Integrator.FactorySystemSequence
