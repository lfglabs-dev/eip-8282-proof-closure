import Eip8282.Audit.Integrator.TransactionCommittedEffects
import Eip8282.Audit.Integrator.GenesisWorldFunding
import Eip8282.Audit.Integrator.JournalCommittedCardinality

/-! Initialized-history composition with the physical prequeue derived from
the actual preceding states. The concrete genesis-loader ledger discharges the
numerical funding premise. Canonical deployment, protocol ledger extraction,
admission, block/slot transport and Ethereum semantic correspondence are still
required external producers; these conditional theorems do not adopt a fork. -/
namespace Eip8282.Audit.Integrator.HistoryCommittedGuarantees
open EvmYul EvmYul.EVM
open NestedEvents TransactionCommittedEffects
open TransactionAppendBudget (Receipt BlockReceipt)
open ReachableCalls (Contract address)
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem represented_queue {kind : Contract} {budget : Nat} {world : World}
    (hi : JournalInvariant.Invariant kind budget world) :
    ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot world (address kind)) queue := by
  cases kind with
  | deposit =>
    obtain ⟨_,_,queue,represented⟩ := hi.2
    exact ⟨queue,represented⟩
  | exit =>
    obtain ⟨_,_,queue,represented,_⟩ := hi.2
    exact ⟨queue,represented⟩

/-- This counts committed submission events, not the final queue length:
SYSTEM drains may remove records whose append event has already committed. -/
theorem exact_log_count {kind : Contract} {r : Receipt} {queue : JournalPathQueues.Queue kind}
    (effects : Effects kind r queue) :
    (ProtectedLogFrame.project (address kind) r.substate).length =
      JournalRetainedWork.count kind (TransactionEventBounds.request r.call)
        (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r) := by
  obtain ⟨os,_,paths,_,_,logs,_⟩ := effects
  have count := JournalCommittedCardinality.emitted_length os paths
  have he : os.map (·.path) = (JournalRetainedCalls.retainedList kind
      (TransactionEventBounds.request r.call) (TransactionEventBounds.request r.call).eval
      (TransactionAppendBudget.tree r)).map ([]++·) := by simpa using paths
  rw [JournalCommittedLogs.emitted_replay os he] at count
  rw [logs]
  exact count

/-- The caller supplies neither a queue nor a per-transaction invariant.
Both are extracted from the actual initialized prefix at this list position. -/
theorem composed {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : ActualJournalHistory.Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r ∧
      (ProtectedLogFrame.project (address kind) r.substate).length =
        JournalRetainedWork.count kind (TransactionEventBounds.request r.call)
          (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r) := by
  have bound := ActualJournalHistory.work_lt_of_blocks receipts blocks listed slots
  obtain ⟨pc,hpc,prior,_⟩ := ActualHistoryCalls.transaction_prefix history atIndex
  have hw := ActualHistoryCalls.position_work atIndex
  have hf : TransferFunding.worldFunds genesis+(baseCredits+pc) < FundedDomain.fundingCeiling := by omega
  have hi := ActualJournalHistory.preserves prior seedFunds seed hf (by omega)
  obtain ⟨queue,represented⟩ := represented_queue hi
  obtain ⟨effects,localGuards⟩ :=
    TransactionCommittedEffects.history_guarantees history seedFunds seed funds bound atIndex queue represented
  exact ⟨queue,represented,effects,localGuards,exact_log_count effects⟩

/-- The complete constructed genesis world and a same-credit protocol ledger
supply the funding envelope. Counts still require canonical protocol producers;
this does not assume a convenient bound on the caller's wealth. -/
theorem from_genesis_ledger {kind : Contract} {initial final : World}
    {baseCredits credits pow withdrawals migrations : Nat} {receipts : List Receipt}
    (history : ActualJournalHistory.Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace GenesisFundingWorld.world baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations
      (baseCredits+credits) final)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r ∧
      (ProtectedLogFrame.project (address kind) r.substate).length =
        JournalRetainedWork.count kind (TransactionEventBounds.request r.call)
          (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r) :=
  composed history seedFunds seed (GenesisWorldFunding.funding_budget ledger counts).2 blocks listed slots atIndex

#print axioms exact_log_count
#print axioms represented_queue
#print axioms composed
#print axioms from_genesis_ledger
end Eip8282.Audit.Integrator.HistoryCommittedGuarantees
