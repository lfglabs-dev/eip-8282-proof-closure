import Eip8282.Audit.Integrator.JournalCommittedLogs
import Eip8282.Audit.Integrator.TransactionRetainedQueues
import Eip8282.Audit.Integrator.JournalRetainedWork

/-! One actual transaction receipt supplies the same canonical surviving call
IDs, chosen queue replay, final protected logs and gas bound. The initialized
history supplies all three local guarantee observations at every actual nested
call, including calls later rolled back. Protocol/seed/admission producers
remain explicit; this does not declare Ethereum context closure. -/
namespace Eip8282.Audit.Integrator.TransactionCommittedEffects
open EvmYul EvmYul.EVM
open NestedEvents JournalExecution JournalWorldPaths JournalRetainedCalls JournalCommittedLogs
open RefundAccounting
open TransactionEventBounds (request)
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address runtime)
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem provisional_logs {kind : Contract} (c : Context) {tree : EventTree}
    (hp : DoneLogs kind (request c) (request c).eval tree [] (request c) (request c).eval tree)
    {world : World} {gas : UInt256} {ss : Substate} {status : Bool}
    (hr : c.provisional = .ok (world,gas,ss,status)) :
    ProtectedLogFrame.project (address kind) ss =
      emitted kind (request c) (request c).eval tree [] (request c) (request c).eval tree := by
  rcases TransactionJournalEdges.provisional_cases c hr with ⟨ht,target,created,out,he⟩ |
    ⟨target,ht,created,out,he⟩
  · unfold request at hp ⊢
    rw [ht] at hp ⊢
    have h := hp target created world gas ss status out he
    exact h
  · unfold request at hp ⊢
    rw [ht] at hp ⊢
    have h := hp created world gas ss status out he
    exact h

theorem result_logs {kind : Contract} (c : Context) {tree : EventTree}
    (hp : DoneLogs kind (request c) (request c).eval tree [] (request c) (request c).eval tree)
    {world : World} {ss : Substate} {status : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,status,used)) :
    ProtectedLogFrame.project (address kind) ss =
      emitted kind (request c) (request c).eval tree [] (request c) (request c).eval tree := by
  cases he : c.provisional with
  | error err => rw [TransactionFunding.result_equation,he] at hr; cases hr
  | ok result =>
    obtain ⟨pw,remaining,a,z⟩ := result
    exact (ProtectedLogFrame.transaction_projection c (address kind) he hr).trans (provisional_logs c hp he)

def Effects (kind : Contract) (r : Receipt) (queue : JournalPathQueues.Queue kind) : Prop :=
  ∃ os : List (Occurrence kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)),
    JournalWorldPaths.Path kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)
      os r.call.world r.world ∧
    os.map (·.path) = retainedList kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r) ∧
    (os.map (·.path)).Nodup ∧
    Represents (modelKind kind) (worldSlot r.world (address kind)) (JournalPathQueues.replay os queue) ∧
    ProtectedLogFrame.project (address kind) r.substate = os.flatMap contribution ∧
    JournalRetainedWork.count kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r) ≤ r.used.toNat

/-- Both final observables use the identical occurrence list of the same
actual receipt. No log postcondition or per-call invariant is an input. -/
theorem receipt_effects {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (ha : TransactionFunding.Admission r.call account)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (fit : r.call.transaction.base.data.size < UInt256.size)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (hi : JournalInvariant.Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128)
    (queue : JournalPathQueues.Queue kind)
    (represented : Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue) :
    Effects kind r queue := by
  have cert := TransactionAppendBudget.tree_cert r
  have ready := TransactionJournal.ready r.call ha hi
  have adequate := TransactionJournal.adequate r.call resources
  have inputs := NestedProtectedJournal.inputs_from_history r.call history ha funds
    (TransactionJournal.data_fit r.call fit) (TransactionAppendBudget.tree r)
  obtain ⟨os,path,exactList,nodup,replay⟩ := TransactionRetainedQueues.receipt_replay r history ha funds
    fit resources hi bound queue represented
  have logs := result_logs r.call (JournalCommittedLogs.extract cert budget bound ready (inputs_every inputs) adequate) r.executed
  have he : os.map (·.path) = (retainedList kind (request r.call) (request r.call).eval
      (TransactionAppendBudget.tree r)).map ([]++·) := by simpa using exactList
  rw [emitted_replay os he] at logs
  exact ⟨os,path,exactList,nodup,replay,logs,
    JournalRetainedWork.transaction_count_le_used kind r.call r.executed cert budget bound ready inputs adequate⟩

/-- Observations cover every actual protected call, whether or not its
ancestor eventually commits. The separate Effects list selects survival. -/
def LocalGuarantees (kind : Contract) (receipt : Receipt) : Prop :=
  ∀ path fuel a created world gas ss status out,
    ThetaAt (request receipt.call) (request receipt.call).eval (TransactionAppendBudget.tree receipt)
      path (fuel+1) a (.ok (created,world,gas,ss,status,out)) →
    a.target = address kind →
    NestedProtectedJournal.Observed kind (a.context fuel (runtime kind)) created world ss status out

/-- Arbitrary actual history positions compose queue, committed logs, work
and the three guarantee observations from a single initial seed. -/
theorem history_guarantees {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : ActualJournalHistory.Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (bound : ActualJournalHistory.work receipts < 2^128)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r)
    (queue : JournalPathQueues.Queue kind)
    (represented : Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue) :
    Effects kind r queue ∧ LocalGuarantees kind r := by
  obtain ⟨pc,hpc,prior,account,ha,fit,resources⟩ := ActualHistoryCalls.transaction_prefix history atIndex
  have hw := ActualHistoryCalls.position_work atIndex
  have hf : TransferFunding.worldFunds genesis+(baseCredits+pc) < FundedDomain.fundingCeiling := by omega
  have hi := ActualJournalHistory.preserves prior seedFunds seed hf (by omega)
  refine ⟨receipt_effects r (ActualJournalHistory.funding prior seedFunds) ha hf fit resources hi
    (by exact lt_of_le_of_lt hw bound) queue represented,?_⟩
  intro path fuel a created world gas ss status out loc ht
  exact (ActualHistoryCalls.observed history seedFunds seed funds bound atIndex loc ht rfl).choose_spec.2.2

theorem history_in_blocks {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : ActualJournalHistory.Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (blocks : List TransactionAppendBudget.BlockReceipt)
    (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r)
    (queue : JournalPathQueues.Queue kind)
    (represented : Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue) :
    Effects kind r queue ∧ LocalGuarantees kind r :=
  history_guarantees history seedFunds seed funds
    (ActualJournalHistory.work_lt_of_blocks receipts blocks listed slots) atIndex queue represented

#print axioms provisional_logs
#print axioms result_logs
#print axioms receipt_effects
#print axioms history_guarantees
#print axioms history_in_blocks
end Eip8282.Audit.Integrator.TransactionCommittedEffects
