import Eip8282.Audit.Integrator.FactoryHistoryGuarantees

/-!
# Supply and executed-work assumptions

The supply bound concerns the actual world at every transaction entry, not
lifetime issuance and not just the final world. Admission and the nested
funding proof derive the bounds at inner calls. Work is the conservative
marked-LOG0 count of the actual execution trees, including rolled-back work.
Neither assumption contains a fee, storage or queue invariant.
-/
namespace Eip8282.Audit.Integrator.ResourceAssumptions
open EvmYul EvmYul.EVM NestedEvents
open ReachableCalls (Contract address)
open TransactionAppendBudget (Receipt)
open TransactionCommittedEffects
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- 10^50 ETH, expressed in wei. -/
def supplyLimit : Nat := 10^68

theorem supply_units : supplyLimit = 10^50 * 10^18 := by decide

theorem supply_below_fee_boundary : supplyLimit < FundedDomain.fundingCeiling := by
  decide +kernel

theorem supply_fits_word : supplyLimit < UInt256.size := by decide

/-- Circulating funds at each actual transaction input. Nested checkpoints
are handled by the execution funding proof, not additional assumed bounds. -/
def SupplyBound (receipts : List Receipt) : Prop :=
  ∀ r ∈ receipts, TransferFunding.worldFunds r.call.world < supplyLimit

/-- Derive state invariants from initialization, linked admitted execution,
transaction-entry supply and total executed work. External credits may exceed
this bound over the lifetime if burns keep each transaction entry below it. -/
theorem preserves {kind : Contract} {initial final : World} {receipts : List Receipt}
    {credits : Nat} (history : ActualJournalHistory.Trace initial receipts credits final)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (supply : SupplyBound receipts) (work : ActualJournalHistory.work receipts < 2^128) :
    JournalInvariant.Invariant kind (ActualJournalHistory.work receipts) final := by
  induction history with
  | initial => exact seed
  | @transaction receipts credits before prior r linked account admission fit resources ih =>
    have previousSupply : SupplyBound receipts := by
      intro x hx
      exact supply x (List.mem_append_left _ hx)
    have currentSupply := supply r (List.mem_append_right _ (by simp))
    rw [ActualJournalHistory.work_append] at work ⊢
    have previous := ih previousSupply (by omega)
    have atCall : JournalInvariant.Invariant kind (ActualJournalHistory.work receipts) r.call.world := by
      rw [linked]
      exact previous
    exact ActualJournalHistory.transaction_step r FundingHistory.Trace.initial admission
      (by simpa using currentSupply.trans supply_below_fee_boundary) fit resources atCall work
  | system prior t sender zero fit ih =>
    exact SystemJournal.preserves t sender zero fit work (ih supply work)
  | transfer prior sender recipient amount funded ih =>
    exact JournalInvariant.frame (ih supply work)
      (ProtocolTransfer.frame _ sender recipient (address kind) amount)
  | credit prior recipient amount ih =>
    exact JournalInvariant.frame (ih supply work)
      (FinalizationWorldFrame.credit_frame _ recipient (address kind) amount)

/-- The formula and counter/physical-queue conditions are conclusions of the
history theorem. Enabled safety includes the inhibitor case. -/
theorem domains {kind : Contract} {initial final : World} {receipts : List Receipt}
    {credits : Nat} (history : ActualJournalHistory.Trace initial receipts credits final)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (supply : SupplyBound receipts) (work : ActualJournalHistory.work receipts < 2^128) :
    AccountedState.Bounded (ActualJournalHistory.work receipts) (worldSlot final (address kind)) ∧
    FundedDomain.EnabledSafe (match kind with | .deposit => 8 | .exit => 2)
      (worldSlot final (address kind)) ∧
    ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot final (address kind)) queue := by
  have hi := preserves history seed supply work
  obtain ⟨queue,represented⟩ := HistoryCommittedGuarantees.represented_queue hi
  cases kind with
  | deposit => exact ⟨hi.2.1,hi.2.2.1,queue,represented⟩
  | exit => exact ⟨hi.2.1,hi.2.2.1,queue,represented⟩

/-- A next completed plain call, including an independently scheduled SYSTEM
call, consumes the derived domains directly. Its actual receipt and input
width remain explicit; scheduling and success are not promised. -/
theorem completed_call {kind : Contract} {initial before after : World}
    {receipts : List Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (supply : SupplyBound receipts) (work : ActualJournalHistory.work receipts < 2^128)
    (call : ReachableCalls.Transition kind before after)
    (fit : call.call.calldata.size < UInt256.size) :
    NestedProtectedJournal.Observed kind call.call call.created after call.substate
      call.success call.output :=
  JournalGuarantees.completed call (preserves history seed supply work) work fit

/-- All three guarantees and the represented physical queue at any actual
transaction position. No numeric fee or per-call storage domain is a premise. -/
theorem guarantees {kind : Contract} {initial final : World} {receipts : List Receipt}
    {credits : Nat} (history : ActualJournalHistory.Trace initial receipts credits final)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (supply : SupplyBound receipts) (work : ActualJournalHistory.work receipts < 2^128)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r := by
  obtain ⟨pc,_,prior,account,admission,fit,resources⟩ :=
    ActualHistoryCalls.transaction_prefix history atIndex
  have prefixSupply : SupplyBound (receipts.take i) := by
    intro x hx
    exact supply x (List.mem_of_mem_take hx)
  have positionWork := ActualHistoryCalls.position_work atIndex
  have hi := preserves prior seed prefixSupply (by omega)
  have funds : TransferFunding.worldFunds r.call.world + 0 < FundedDomain.fundingCeiling := by
    have member : r ∈ receipts := List.mem_of_getElem? atIndex
    simpa using (supply r member).trans supply_below_fee_boundary
  obtain ⟨queue,represented⟩ := HistoryCommittedGuarantees.represented_queue hi
  refine ⟨queue,represented,receipt_effects r FundingHistory.Trace.initial admission funds fit resources hi
    (lt_of_le_of_lt positionWork work) queue represented,?_⟩
  intro path fuel a created world gas ss status out loc ht
  exact (TransactionJournal.observed r.call FundingHistory.Trace.initial admission funds fit resources hi
    (TransactionAppendBudget.tree_cert r) (lt_of_le_of_lt positionWork work) loc ht rfl).choose_spec.2.2

/-- The verified factory transaction produces the seed; the consumer supplies
no initial queue or safe-fee invariant. Factory/address/admission/resource
inputs remain explicit and are not a claim of canonical installation. -/
theorem from_deployment {kind : Contract} (deployment : Receipt)
    (inputs : FactoryHistoryGuarantees.Inputs kind deployment.call)
    (deploymentSupply : TransferFunding.worldFunds deployment.call.world < supplyLimit)
    {final : World} {receipts : List Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace deployment.world receipts credits final)
    (supply : SupplyBound receipts) (work : ActualJournalHistory.work receipts < 2^128)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    deployment.success = true ∧ ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r := by
  obtain ⟨success,seed,_,_,_⟩ := FactoryHistoryGuarantees.deployment_seed deployment inputs
    (deploymentSupply.trans supply_fits_word)
  exact ⟨success,guarantees history seed supply work atIndex⟩

#print axioms supply_units
#print axioms supply_below_fee_boundary
#print axioms supply_fits_word
#print axioms preserves
#print axioms domains
#print axioms completed_call
#print axioms guarantees
#print axioms from_deployment
end Eip8282.Audit.Integrator.ResourceAssumptions
