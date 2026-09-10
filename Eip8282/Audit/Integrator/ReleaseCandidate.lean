import Eip8282.Audit.Integrator.FactoryHistoryGuarantees
import Eip8282.Audit.Integrator.FactorySystemSequence
import Eip8282.Audit.Integrator.ReferenceCheckedTheta
import Eip8282.Audit.Integrator.ReferenceCheckedPrefix

/-! Release composition for the three existing guarantee IDs.
The domain contains actual pinned-semantic deployment/history inputs and
independent ledger/resource restrictions, never the desired postcondition.
Ethereum satisfaction of that domain is NOT asserted. In particular the old
scalar-gas receipts and their admission are not Amsterdam dual-pool receipts.
The checked adapter changes only replay resources and does not identify its
complete account world or gas with Python execution.
-/
namespace Eip8282.Audit.Integrator.ReleaseCandidate
open EvmYul EvmYul.EVM
open NestedEvents
open ReachableCalls (Contract PinnedCall Transition address)
open JournalInvariant (Invariant modelKind)
open TransactionAppendBudget (Receipt BlockReceipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Explicit finite-history domain. All accounting counters index actual
literal transitions; the separate ledger supplies a same-total credit bound.
It need not be the identical sequence and is not advertised as canonical
provenance. No invariant, safe numerator, no-wrap, call-success or queue is an
input. Factory installation/address hash and Ethereum applicability are
external semantic/deployment conditions, not conclusions of this structure. -/
structure History (deposit exit : Receipt) (before : World) where
  depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call
  exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call
  linked : exit.call.world = deposit.world
  baseCredits : Nat
  credits : Nat
  pow : Nat
  withdrawals : Nat
  migrations : Nat
  receipts : List Receipt
  prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world
  actual : ActualJournalHistory.Trace exit.world receipts credits before
  ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations
    (baseCredits+credits) before
  counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations
  blocks : List BlockReceipt
  listed : receipts = blocks.flatMap (fun b => b.receipts)
  slots : (blocks.map (fun b => b.slot)).Nodup

/-- Independently chosen call inputs. Installed target/code existence is
produced from history, rather than required again at the public call API. -/
structure CallInput (kind : Contract) (c : MessageCall.Context) : Prop where
  target : c.target = address kind
  code : c.code = ReachableCalls.runtime kind
  ordinaryValue : c.apparentValue = c.value

/-- Exact initialization and the complete actual prefix derive both current
invariants and the structural budget. No per-call safety premise remains. -/
theorem invariants {deposit exit : Receipt} {before : World}
    (h : History deposit exit before) :
    deposit.success = true ∧ exit.success = true ∧
    ActualJournalHistory.work h.receipts < 2^128 ∧
    ∀ kind, Invariant kind (ActualJournalHistory.work h.receipts) before := by
  have funds := LedgerCreditSafety.genesis_budget h.ledger h.counts
  obtain ⟨hd,he,seedFunds,seedInv⟩ := FactoryHistoryGuarantees.two_seeds
    deposit exit h.depositInputs h.exitInputs h.linked h.prior (by omega)
  have bound := ActualJournalHistory.work_lt_of_blocks h.receipts h.blocks h.listed h.slots
  exact ⟨hd,he,bound,fun kind => ActualJournalHistory.preserves h.actual seedFunds
    (seedInv kind) (GenesisWorldFunding.funding_budget h.ledger h.counts).2 bound⟩

/-- The actual initialized history supplies the installed-code witness. -/
theorem installed_call {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : History deposit exit c.world) (input : CallInput kind c) : PinnedCall kind c := by
  obtain ⟨account,found,code⟩ := ((invariants history).2.2.2 kind).1
  refine ⟨input.target,input.code,⟨account,?_,code.trans input.code.symm⟩,input.ordinaryValue⟩
  simpa only [input.target] using found

/-- Primary release theorem at the next real pinned Theta call. All three
predicates share one pre-world, complete receipt, output, logs and settlement.
It includes returned failures; it does not assume the call succeeds. -/
theorem call {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (h : History deposit exit c.world) (pinned : CallInput kind c)
    (fit : c.calldata.size < UInt256.size)
    {created : Std.TreeSet AccountAddress compare} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {output : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,output)) :
    NestedProtectedJournal.Observed kind c created world substate success output := by
  let t : Transition kind c.world world := ⟨c,installed_call h pinned,rfl,created,gas,substate,success,output,actual⟩
  exact JournalGuarantees.completed t ((invariants h).2.2.2 kind) (invariants h).2.2.1 fit

/-- One history domain composes every past transaction's exact retained
queue/log effects and all nested local guarantees with the next actual call.
Executed work and retained effects remain distinct predicates. -/
theorem composed {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : History deposit exit c.world) (input : CallInput kind c)
    (fit : c.calldata.size < UInt256.size)
    {created : Std.TreeSet AccountAddress compare} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {output : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,output)) :
    NestedProtectedJournal.Observed kind c created world substate success output ∧
    (∀ (i : Nat) (r : Receipt), history.receipts[i]? = some r →
      ∀ k, ∃ queue : JournalPathQueues.Queue k,
        QueueInvariant.Represents (modelKind k)
          (SystemSpec.worldSlot r.call.world (address k)) queue ∧
        TransactionCommittedEffects.Effects k r queue ∧
        TransactionCommittedEffects.LocalGuarantees k r ∧
        (ProtectedLogFrame.project (address k) r.substate).length =
          JournalRetainedWork.count k (TransactionEventBounds.request r.call)
            (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r)) := by
  refine ⟨call history input fit actual, ?_⟩
  intro i r atIndex
  exact (FactoryHistoryGuarantees.from_genesis_both deposit exit
    history.depositInputs history.exitInputs history.linked history.prior history.actual
    history.ledger history.counts history.blocks history.listed history.slots atIndex).2.2

/-- The mathematical fee agreement domain is a derived pre-state fact at
both targets, including immediately after any admitted history edge. -/
theorem enabled_numerator {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (h : History deposit exit c.world) (pinned : CallInput kind c)
    (enabled : SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0) ≠ Eip8282.Audit.EntryReach.INH) :
    SuccessfulUser.numerator c (DirectAdmission.target (modelKind kind)) ≤ 2892 := by
  have hi := (invariants h).2.2.2 kind
  have target := pinned.target
  cases kind with
  | deposit =>
    obtain ⟨_,_,safe,_⟩ := hi
    have hs := safe.resolve_left (by simpa only [target] using enabled)
    simpa only [SuccessfulUser.numerator,target,DirectAdmission.target,modelKind,ControlSpec.feeInputNat] using hs
  | exit =>
    obtain ⟨_,_,safe,_⟩ := hi
    have hs := safe.resolve_left (by simpa only [target] using enabled)
    simpa only [SuccessfulUser.numerator,target,DirectAdmission.target,modelKind,ControlSpec.feeInputNat] using hs

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

/-- Computed terminal from the same transferred entry consumes the derived
history domain. No assumed old success, old trace, owner, queue, safe fee input
or 2^128 budget is required. Source grant and storage/warm bindings are explicit. -/
theorem checked_terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : History deposit exit c.world) (pinned : CallInput kind c)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    ReferenceCheckedTheta.Completed kind c parent events result.view
      (decide (result.halt ≠ .reverted)) result.output :=
  ReferenceCheckedTheta.terminal (installed_call history pinned) context actual slots warmRelated grant
    ((invariants history).2.2.2 kind) (invariants history).2.2.1 fit

/-- Genuine computed EOF is covered by the same history-derived predicates. -/
theorem checked_eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : History deposit exit c.world) (pinned : CallInput kind c)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some (events,.eof view finalWarm final output))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    output = ByteArray.empty ∧ ReferenceCheckedTheta.Completed kind c parent events view true output :=
  ReferenceCheckedTheta.eof (installed_call history pinned) context actual slots warmRelated grant
    ((invariants history).2.2.2 kind) (invariants history).2.2.1 fit

#print axioms invariants
#print axioms installed_call
#print axioms call
#print axioms composed
#print axioms enabled_numerator
#print axioms checked_terminal
#print axioms checked_eof
end Eip8282.Audit.Integrator.ReleaseCandidate
