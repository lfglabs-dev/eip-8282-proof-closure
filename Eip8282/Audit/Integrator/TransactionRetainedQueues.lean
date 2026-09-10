import Eip8282.Audit.Integrator.JournalRetainedPaths
import Eip8282.Audit.Integrator.JournalPathQueues
import Eip8282.Audit.Integrator.ActualHistoryCalls

/-! Actual transaction queue replay uses exactly the independently specified
surviving protected-call addresses, once each in execution order. Calls that
return false are retained atomic no-ops; this list is not a count of committed
submissions. Log survival and reference-protocol transport are separate. -/
namespace Eip8282.Audit.Integrator.TransactionRetainedQueues
open EvmYul EvmYul.EVM
open NestedEvents JournalWorldPaths JournalExecution RefundAccounting
open JournalRetainedPaths JournalRetainedCalls
open TransactionEventBounds (request)
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address)
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem provisional_path {kind : Contract} (c : Context) {tree : EventTree}
    (hp : ExactDone kind (request c) (request c).eval tree [] (request c) (request c).eval tree)
    {world : World} {gas : UInt256} {ss : Substate} {status : Bool}
    (hr : c.provisional = .ok (world,gas,ss,status)) :
    ExactReaches kind (request c) (request c).eval tree [] (request c) (request c).eval tree c.checkpoint world := by
  rcases TransactionJournalEdges.provisional_cases c hr with ⟨ht,target,created,out,he⟩ |
    ⟨target,ht,created,out,he⟩
  · unfold request at hp ⊢
    rw [ht] at hp ⊢
    exact hp target created world gas ss status out he
  · unfold request at hp ⊢
    rw [ht] at hp ⊢
    exact hp created world gas ss status out he

/-- Literal Υ finalization transports the same actual root path. Its cleanup
frame uses the deletion exclusion proved for that root's actual result. -/
theorem result_path {kind : Contract} (c : Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account) {tree : EventTree} {budget : Nat}
    (hp : ExactDone kind (request c) (request c).eval tree [] (request c) (request c).eval tree)
    (hj : Done kind budget (request c) (request c).eval)
    {world : World} {ss : Substate} {status : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,status,used)) :
    ExactReaches kind (request c) (request c).eval tree [] (request c) (request c).eval tree c.world world := by
  rw [TransactionFunding.result_equation] at hr
  cases he : c.provisional with
  | error err => simp only [he,Bind.bind,Except.bind] at hr; cases hr
  | ok result =>
    obtain ⟨pw,remaining,a,z⟩ := result
    have invocation := provisional_path c hp he
    have journal := TransactionJournal.provisional c hj he
    have cleanup := TransactionJournalEdges.settled_codeAt_frame c pw remaining a journal.1.1 journal.2
    have entry := TransactionJournalEdges.checkpoint_frame c ha (address kind)
    simp only [he,Bind.bind,Except.bind,pure,Except.pure] at hr
    cases hr
    obtain ⟨occurrences,path,exactList⟩ := invocation
    refine ⟨occurrences,?_,exactList⟩
    simpa only [List.nil_append, List.append_nil] using
      (JournalWorldPaths.Path.trans (.frame entry) (JournalWorldPaths.Path.trans path (.frame cleanup)))

/-- No path or queue postcondition is assumed: the exact receipt supplies its
actual tree, full recursive path and final represented replay. -/
theorem receipt_replay {kind : Contract} {genesis : World} {credits budget : Nat}
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
    ∃ occurrences : List (Occurrence kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)),
      Path kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)
        occurrences r.call.world r.world ∧
      occurrences.map (·.path) = retainedList kind (request r.call) (request r.call).eval
        (TransactionAppendBudget.tree r) ∧
      (occurrences.map (·.path)).Nodup ∧
      Represents (modelKind kind) (worldSlot r.world (address kind)) (JournalPathQueues.replay occurrences queue) := by
  have cert := TransactionAppendBudget.tree_cert r
  have ready := TransactionJournal.ready r.call ha hi
  have adequate := TransactionJournal.adequate r.call resources
  have inputs := NestedProtectedJournal.inputs_from_history r.call history ha funds
    (TransactionJournal.data_fit r.call fit) (TransactionAppendBudget.tree r)
  have paths := JournalRetainedPaths.extract cert budget bound ready (inputs_every inputs) adequate
  have journal := (JournalCheckpoints.from_resources cert adequate budget bound ready inputs).1
  obtain ⟨occurrences,path,exactList⟩ := result_path r.call ha paths journal r.executed
  have he : occurrences.map (·.path) = retainedList kind (request r.call) (request r.call).eval
      (TransactionAppendBudget.tree r) := by simpa using exactList
  exact ⟨occurrences,path,he,by rw [he]; exact retainedList_nodup _ _ _ _,
    JournalPathQueues.represented_replay cert adequate budget bound ready inputs path queue represented⟩

/-- Every actual transaction position obtains this committed-world queue
replay from the initialized history, including final failed status. -/
theorem history_replay {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : ActualJournalHistory.Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (bound : ActualJournalHistory.work receipts < 2^128)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r)
    (queue : JournalPathQueues.Queue kind)
    (represented : Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue) :
    ∃ occurrences : List (Occurrence kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)),
      Path kind (request r.call) (request r.call).eval (TransactionAppendBudget.tree r)
        occurrences r.call.world r.world ∧
      occurrences.map (·.path) = retainedList kind (request r.call) (request r.call).eval
        (TransactionAppendBudget.tree r) ∧
      (occurrences.map (·.path)).Nodup ∧
      Represents (modelKind kind) (worldSlot r.world (address kind)) (JournalPathQueues.replay occurrences queue) := by
  obtain ⟨pc,hpc,prior,account,ha,fit,resources⟩ := ActualHistoryCalls.transaction_prefix history atIndex
  have hw := ActualHistoryCalls.position_work atIndex
  have hf : TransferFunding.worldFunds genesis+(baseCredits+pc) < FundedDomain.fundingCeiling := by omega
  have hi := ActualJournalHistory.preserves prior seedFunds seed hf (by omega)
  exact receipt_replay r (ActualJournalHistory.funding prior seedFunds) ha hf fit resources hi
    (by exact lt_of_le_of_lt hw bound) queue represented

#print axioms provisional_path
#print axioms result_path
#print axioms receipt_replay
#print axioms history_replay
end Eip8282.Audit.Integrator.TransactionRetainedQueues
