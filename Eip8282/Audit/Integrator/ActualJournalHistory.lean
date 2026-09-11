import Eip8282.Audit.Integrator.TransactionJournal
import Eip8282.Audit.Integrator.SystemJournal

/-!
# Linked actual transaction, canonical SYSTEM, transfer and external-credit histories

The history contains actual receipts and independent input admission/resources.
It contains no intermediate queue, invariant or assumed postcondition. The same
ordered transaction receipts determine the executed-work bound. Failed status
and ancestor rollback remain inside those actual receipts. External credits
are literal balance operations, with provenance still a protocol obligation.
-/
namespace Eip8282.Audit.Integrator.ActualJournalHistory
open EvmYul EvmYul.EVM
open NestedEvents
open ReachableCalls (Contract Transition address runtime)
open TransactionAppendBudget (Receipt BlockReceipt)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def work (receipts : List Receipt) : Nat :=
  (receipts.map NestedJournalBudget.events).sum

theorem work_append (receipts : List Receipt) (r : Receipt) :
    work (receipts++[r]) = work receipts + NestedJournalBudget.events r := by
  simp [work]

/-- The system constructor is restricted to either actual canonical runtime.
An arbitrary SYSTEM call is not silently treated as a zero-work journal edge. -/
inductive Trace (initial : World) : List Receipt → Nat → World → Prop where
  | initial : Trace initial [] 0 initial
  | transaction {receipts : List Receipt} {credits : Nat} {before : World}
      (prior : Trace initial receipts credits before) (r : Receipt)
      (linked : r.call.world = before) (account : Account .EVM)
      (admission : TransactionFunding.Admission r.call account)
      (fit : r.call.transaction.base.data.size < UInt256.size)
      (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel) :
      Trace initial (receipts++[r]) credits r.world
  | system {receipts : List Receipt} {credits : Nat} {before after : World}
      (prior : Trace initial receipts credits before) {selector : Contract}
      (t : Transition selector before after)
      (sender : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr)
      (zero : t.call.value = ⟨0⟩) (fit : t.call.calldata.size < UInt256.size) :
      Trace initial receipts credits after
  | transfer {receipts : List Receipt} {credits : Nat} {before : World}
      (prior : Trace initial receipts credits before)
      (sender recipient : AccountAddress) (amount : UInt256)
      (funded : amount.toNat ≤ TransferFunding.worldBalance before sender) :
      Trace initial receipts credits (ProtocolTransfer.transfer before sender recipient amount)
  | credit {receipts : List Receipt} {credits : Nat} {before : World}
      (prior : Trace initial receipts credits before)
      (recipient : AccountAddress) (amount : UInt256) :
      Trace initial receipts (credits+amount.toNat) (before.increaseBalance .EVM recipient amount)

/-- Funding is extracted from the very same world transitions, optionally
starting from a separately identified genesis-to-initialization funding trace. -/
theorem funding {genesis initial world : World} {baseCredits credits : Nat}
    {receipts : List Receipt} (h : Trace initial receipts credits world)
    (seed : FundingHistory.Trace genesis baseCredits initial) :
    FundingHistory.Trace genesis (baseCredits+credits) world := by
  induction h with
  | initial => simpa only [Nat.add_zero] using seed
  | transaction prior r linked account admission fit resources ih =>
    have step := FundingHistory.Step.transaction r.call account admission r.executed
    rw [linked] at step
    simpa only [Nat.add_zero] using FundingHistory.Trace.next ih step
  | system prior t sender zero fit ih =>
    have step := FundingHistory.Step.system t.call sender zero t.executed
    rw [t.pre] at step
    simpa only [Nat.add_zero] using FundingHistory.Trace.next ih step
  | transfer prior sender recipient amount funded ih =>
    simpa only [Nat.add_zero] using
      FundingHistory.Trace.next ih (FundingHistory.Step.transfer _ sender recipient amount funded)
  | credit prior recipient amount ih =>
    simpa only [Nat.add_assoc] using
      FundingHistory.Trace.next ih (FundingHistory.Step.credit _ recipient amount)

/-- Precise work-budget variant of complete Υ journal preservation, on the
canonical tree selected for this exact receipt. -/
theorem transaction_step {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (ha : TransactionFunding.Admission r.call account)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (fit : r.call.transaction.base.data.size < UInt256.size)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (hi : JournalInvariant.Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128) :
    JournalInvariant.Invariant kind (budget+NestedJournalBudget.events r) r.world := by
  have cert := TransactionAppendBudget.tree_cert r
  have inputs := NestedProtectedJournal.inputs_from_history r.call history ha funds
    (TransactionJournal.data_fit r.call fit) (TransactionAppendBudget.tree r)
  have done_ := (JournalCheckpoints.from_resources cert (TransactionJournal.adequate r.call resources)
    budget bound (TransactionJournal.ready r.call ha hi) inputs).1
  exact (TransactionJournal.settled r.call done_ r.executed).1

/-- Every intermediate queue/control/code invariant is derived from the one
initial journal, actual transitions and nonnegative credit/work prefixes. -/
theorem preserves {kind : Contract} {genesis initial world : World} {baseCredits credits : Nat}
    {receipts : List Receipt} (h : Trace initial receipts credits world)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial) :
    TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling →
    work receipts < 2^128 → JournalInvariant.Invariant kind (work receipts) world := by
  induction h with
  | initial =>
    intro funds bound
    exact seed
  | @transaction receipts credits before prior r linked account admission fit resources ih =>
    intro funds bound
    rw [work_append] at bound ⊢
    have priorInv := ih funds (by omega)
    have hf := funding prior seedFunds
    have priorInvCall : JournalInvariant.Invariant kind (work receipts) r.call.world := by rw [linked]; exact priorInv
    have hf' : FundingHistory.Trace genesis (baseCredits+credits) r.call.world := by rw [linked]; exact hf
    exact transaction_step r hf' admission funds fit resources priorInvCall bound
  | system prior t sender zero fit ih =>
    intro funds bound
    exact SystemJournal.preserves t sender zero fit bound (ih funds bound)
  | transfer prior sender recipient amount funded ih =>
    intro funds bound
    exact JournalInvariant.frame (ih funds bound)
      (ProtocolTransfer.frame _ sender recipient (address kind) amount)
  | credit prior recipient amount ih =>
    intro funds bound
    exact JournalInvariant.frame (ih (by omega) bound)
      (FinalizationWorldFrame.credit_frame _ recipient (address kind) amount)

/-- The resource envelope applies to the same ordered receipt list as the
linked world history. List positions retain repeated equal invocations. -/
theorem work_lt_of_blocks (receipts : List Receipt) (blocks : List BlockReceipt)
    (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup) : work receipts < 2^128 := by
  rw [listed]
  have he : ∀ xs : List BlockReceipt, work (xs.flatMap (fun b => b.receipts)) =
      (xs.map (fun b => (b.receipts.map NestedJournalBudget.events).sum)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b bs ih => simpa only [List.flatMap_cons,work,List.map_append,List.sum_append,
        List.map_cons,List.sum_cons] using congrArg (fun n => work b.receipts+n) ih
  rw [he]
  exact NestedJournalBudget.history_lt blocks slots

/-- This closes the internal initialized-history induction. Deployment,
credit provenance/ceiling and canonical reference block admission remain
explicit inputs, not consequences claimed by the typed history itself. -/
theorem initialized_history {kind : Contract} {genesis initial world : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (h : Trace initial receipts credits world)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup) :
    JournalInvariant.Invariant kind (work receipts) world ∧
      FundingHistory.Trace genesis (baseCredits+credits) world :=
  ⟨preserves h seedFunds seed funds (work_lt_of_blocks receipts blocks listed slots), funding h seedFunds⟩

#print axioms funding
#print axioms transaction_step
#print axioms preserves
#print axioms work_lt_of_blocks
#print axioms initialized_history
end Eip8282.Audit.Integrator.ActualJournalHistory
