import Eip8282.Audit.Integrator.ActualHistoryCalls
import Eip8282.Audit.Integrator.Topics.Factory
import Eip8282.Audit.Integrator.JournalPathQueues
import Eip8282.Audit.Integrator.TransactionCommittedEffects
import Eip8282.Audit.Integrator.Topics.Transaction3
import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.TransactionJournal

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## TransactionCalldataAdmission -/

/-! Actual pinned intrinsic-gas admission bounds transaction calldata.
EvmYul/EVM/Gas.lean intrinsicGas charges a natural4 or16 per data byte.
This does not silently add intrinsic admission to TransactionFunding.Admission;
the protocol/executable transaction validator must supply the explicit gate.
-/
namespace Eip8282.Audit.Integrator.TransactionCalldataAdmission
open EvmYul EvmYul.EVM
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def byteCost (acc : Nat) (b : UInt8) : Nat := acc + if b == 0 then 4 else 16

private theorem loop_bound (data : ByteArray) (i j acc : Nat) (h : j+i ≤ data.size) :
    acc+4*i ≤ ByteArray.foldlM.loop (m := Id) (fun a b => pure (byteCost a b))
      data data.size (Nat.le_refl _) i j acc := by
  induction i generalizing j acc with
  | zero =>
    rw [ByteArray.foldlM.loop]
    split <;> exact Nat.le_refl _
  | succ i ih =>
    have hj : j < data.size := by omega
    rw [ByteArray.foldlM.loop,dif_pos hj]
    change acc+4*(i+1) ≤ ByteArray.foldlM.loop (m := Id) (fun a b => pure (byteCost a b))
      data data.size (Nat.le_refl _) i (j+1) (byteCost acc data[j])
    have ht := ih (j+1) (byteCost acc data[j]) (by omega)
    have hb : acc+4 ≤ byteCost acc data[j] := by
      unfold byteCost
      split <;> omega
    omega

theorem data_cost (data : ByteArray) : 4*data.size ≤ data.foldl byteCost 0 := by
  have h := loop_bound data data.size 0 0 (by omega)
  simpa only [ByteArray.foldl,ByteArray.foldlM,dif_pos (Nat.le_refl data.size),
    Nat.sub_zero,Id.run,Nat.zero_add] using h

theorem intrinsic_bound (t : Transaction) : 4*t.base.data.size ≤ intrinsicGas t := by
  have h := data_cost t.base.data
  change 4*t.base.data.size ≤ t.base.data.foldl
    (fun acc b => acc + if b == 0 then GasConstants.Gtxdatazero else GasConstants.Gtxdatanonzero) 0 at h
  unfold intrinsicGas
  dsimp only
  omega

theorem calldata_fit (t : Transaction) (admitted : intrinsicGas t ≤ t.base.gasLimit.toNat) :
    t.base.data.size < UInt256.size := by
  have h := intrinsic_bound t
  have hw := t.base.gasLimit.val.isLt
  change t.base.gasLimit.toNat < UInt256.size at hw
  omega

#print axioms data_cost
#print axioms intrinsic_bound
#print axioms calldata_fit
end Eip8282.Audit.Integrator.TransactionCalldataAdmission

end

section

/-! ## TransactionAdmissionHistory -/

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

end

section

/-! ## TransactionFactoryEntry -/

/-! Actual admitted transaction checkpoint and selected factory message call.
Positive Theta fuel, installed code and actual recipient are explicit. No
initializer success or post-transaction invariant is assumed. -/
namespace Eip8282.Audit.Integrator.TransactionFactoryEntry
open EvmYul EvmYul.EVM
open NestedEvents FactoryRuntimeEntry TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def call (c : RefundAccounting.Context) : MessageCall.Context :=
  (TransactionEventBounds.message c factoryAddress).context (c.fuel-1) FactoryRuntimeEntry.runtime

theorem call_fuel (c : RefundAccounting.Context) (n : Nat) (hf : c.fuel = n+1) :
    (call c).fuel = n := by change c.fuel-1 = n; omega

theorem checkpoint_factory (c : RefundAccounting.Context) (sender old : Account .EVM)
    (ha : TransactionFunding.Admission c sender)
    (hi : c.world.get? factoryAddress = some old) (hne : c.sender ≠ factoryAddress) :
    c.checkpoint.get? factoryAddress = some old := by
  rw [TransactionFunding.checkpoint_eq c ha]
  have he := Std.TreeMap.getElem?_insert (t := c.world) (k := c.sender)
    (a := factoryAddress) (v := TransactionFunding.debited c sender)
  change (c.world.insert c.sender (TransactionFunding.debited c sender)).get? factoryAddress = _ at he
  rw [he]
  simp only [Std.LawfulEqOrd.compare_eq_iff_eq,hne,if_false]
  exact hi

theorem selected_code (c : RefundAccounting.Context) (sender old : Account .EVM)
    (ha : TransactionFunding.Admission c sender)
    (hi : c.world.get? factoryAddress = some old) (hne : c.sender ≠ factoryAddress)
    (hc : old.code = FactoryRuntimeEntry.runtime) :
    toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime :=
  FactoryCallEntry.installed_toExecute c.checkpoint old (checkpoint_factory c sender old ha hi hne) hc

theorem call_funding (c : RefundAccounting.Context) (sender : Account .EVM)
    (ha : TransactionFunding.Admission c sender) :
    (call c).value.toNat ≤ worldBalance (call c).world (call c).caller ∧
      worldFunds (call c).world ≤ worldFunds c.world := by
  refine ⟨TransactionFunding.checkpoint_funded c ha,?_⟩
  have h := TransactionFunding.checkpoint_debit c ha
  change worldFunds c.checkpoint ≤ worldFunds c.world
  omega

theorem call_world_bound (c : RefundAccounting.Context) (sender : Account .EVM)
    (ha : TransactionFunding.Admission c sender) (hw : worldFunds c.world < UInt256.size) :
    worldFunds (call c).world < UInt256.size := (call_funding c sender ha).2.trans_lt hw

/-- The context result is the exact Theta selected by the transaction, including
all returned statuses and errors. Its inner fuel is one below outer Theta fuel. -/
theorem call_result (c : RefundAccounting.Context) (hf : 0 < c.fuel)
    (hc : toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime) :
    (call c).result = (Request.theta c.fuel (TransactionEventBounds.message c factoryAddress)).eval := by
  unfold Request.eval TransactionEventBounds.message
  rw [hc]
  change Θ (c.fuel-1+1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [Nat.sub_add_cancel (by omega)]
  rfl

theorem provisional_of_call (c : RefundAccounting.Context) (hf : 0 < c.fuel)
    (hc : toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime)
    (ht : c.transaction.base.recipient = some factoryAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) (success : Bool) (out : ByteArray)
    (hr : (call c).result = .ok (created,world,gas,ss,success,out)) :
    c.provisional = .ok (world,gas,ss,success) := by
  rw [call_result c hf hc] at hr
  unfold RefundAccounting.Context.provisional
  rw [ht]
  change Θ c.fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at hr
  dsimp only [TransactionEventBounds.message] at hr
  simp only
  rw [hr]

#print axioms call_fuel
#print axioms checkpoint_factory
#print axioms selected_code
#print axioms call_funding
#print axioms call_world_bound
#print axioms call_result
#print axioms provisional_of_call
end Eip8282.Audit.Integrator.TransactionFactoryEntry

end

section

/-! ## TransactionQueuePaths -/

/-! Actual Υ commits a queue-world path extracted from its own evaluator.
Checkpoint debit and final settlement are frames. The chosen physical queue is
therefore the replay of actual retained protected calls; ancestor rollback is
handled by extraction. Completeness and uniqueness of the retained occurrence
list, and committed log survival, remain stronger separate obligations. -/
namespace Eip8282.Audit.Integrator.TransactionQueuePaths
open EvmYul EvmYul.EVM
open NestedEvents JournalWorldPaths JournalExecution RefundAccounting
open TransactionEventBounds (request)
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address)
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem provisional_path {kind : Contract} (c : Context) {tree : EventTree}
    (hp : DonePath kind (request c) (request c).eval tree (request c) (request c).eval)
    {world : World} {gas : UInt256} {ss : Substate} {status : Bool}
    (hr : c.provisional = .ok (world,gas,ss,status)) :
    Reaches kind (request c) (request c).eval tree c.checkpoint world := by
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
    (hp : DonePath kind (request c) (request c).eval tree (request c) (request c).eval)
    (hj : Done kind budget (request c) (request c).eval)
    {world : World} {ss : Substate} {status : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,status,used)) :
    Reaches kind (request c) (request c).eval tree c.world world := by
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
    exact (Reaches.frame entry).trans (invocation.trans (Reaches.frame cleanup))

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
      Represents (modelKind kind) (worldSlot r.world (address kind)) (JournalPathQueues.replay occurrences queue) := by
  have cert := TransactionAppendBudget.tree_cert r
  have ready := TransactionJournal.ready r.call ha hi
  have adequate := TransactionJournal.adequate r.call resources
  have inputs := NestedProtectedJournal.inputs_from_history r.call history ha funds
    (TransactionJournal.data_fit r.call fit) (TransactionAppendBudget.tree r)
  have paths := JournalWorldPaths.extract cert budget bound ready (inputs_every inputs) adequate
  have journal := (JournalCheckpoints.from_resources cert adequate budget bound ready inputs).1
  obtain ⟨occurrences,path⟩ := result_path r.call ha paths journal r.executed
  exact ⟨occurrences,path,JournalPathQueues.represented_replay cert adequate budget bound ready inputs path queue represented⟩

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
end Eip8282.Audit.Integrator.TransactionQueuePaths

end
