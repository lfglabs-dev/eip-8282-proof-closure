import Eip8282.Audit.Integrator.Topics.ReferenceCheckedSystem2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSystemOutputMeter -/

/-! Checked fields of process_top_level's SYSTEM TransactionOutput. The same
trace derives the signed-refund U256 conversion and tx_state_gas_used assertion.
No ordinary transaction settlement, gas fee or block charge is invented. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemOutputMeter
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def Valid (grant : Nat) (m : Meter) : Prop := m.baseline ≤ grant ∧ 0 ≤ m.refund ∧ m.refund < UInt256.size

structure Facts (grant : Nat) (m : Meter) : Prop where
  net_checked : checkedNetUsed grant m = some (netUsed grant m)
  refund_checked : ReferenceRefundCounter.checked m.refund = some (UInt256.ofNat m.refund.toNat)
  refund_exact : ((UInt256.ofNat m.refund.toNat).toNat : Int) = m.refund

theorem facts {grant : Nat} {m : Meter} (valid : Valid grant m) : Facts grant m := by
  refine ⟨if_pos valid.1,if_pos valid.2,?_⟩
  have fit : m.refund.toNat < UInt256.size := by have h := valid.2; omega
  change ((m.refund.toNat % UInt256.size : Nat) : Int) = m.refund
  rw [Nat.mod_eq_of_lt fit]
  exact Int.toNat_of_nonneg valid.2.1

theorem fresh_paid {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {pre middle final : Meter} {events : List Event} {amount grant : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w pre finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (initialRefund : pre.refund = 0) (initialBaseline : pre.baseline = grant)
    (maximum : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (terminal : runFull [.ordinary amount] middle = some final) :
    Valid grant final ∧ Valid grant (restore final) := by
  obtain ⟨source,paid,_⟩ := actual.extract stack aligned
  have lower := ReferenceCheckedRefund.source_balance source
  rw [fresh,ReferenceCheckedRefund.empty_potential,sub_zero] at lower
  have nonnegative := ReferenceCheckedRefund.nonnegative p finish.storage
  have upper := ReferenceCheckedRefund.delta_upper events
  have counter := ReferenceRefundCounter.full_refund paid
  rw [initialRefund,zero_add] at counter
  have last := ReferenceRefundCounter.full_refund terminal
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ReferenceCheckedRefund.delta,add_zero] at last
  have length := actual.length_bound stack aligned
  have numeric : (21616*30000000 : Int) < UInt256.size := by decide +kernel
  have metadata := (ReferenceCheckedStateGas.terminal_balance actual stack aligned terminal grant).2.2.1
  have baseline : final.baseline = grant := metadata.trans initialBaseline
  constructor
  · exact ⟨baseline.le,by omega,by omega⟩
  · exact ⟨baseline.le,by simp [restore],by change (0 : Int) < UInt256.size; decide⟩

#print axioms facts
#print axioms fresh_paid
#print axioms ReferenceOutcomeGas.terminal_paid
end Eip8282.Audit.Integrator.ReferenceSystemOutputMeter

end

section

/-! ## ReferenceSystemOutputReceipt -/

/-! Construct the receipt and top-level checked output fields together. The
same final dispatcher supplies its partial or terminal meter; no source output
conversion or host-exception success is assumed by the public SYSTEM consumer. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemOutputReceipt
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary ReferenceMeterPath
open ReferenceCheckedDispatch ReferenceCheckedFrameOutcome ReferenceSystemOutputMeter
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem settled {kind : ReachableCalls.Contract} {c : ReferenceCheckedSystemEntry.Context}
    {p : ReferenceStorageView.Parent} {v finish : View} {w fw : Warm} {pre middle : Meter} {events : List Event} {grant : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) p v w pre finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (initialRefund : pre.refund = 0) (initialBaseline : pre.baseline = grant)
    (maximum : ReferenceExecutionPotential.potential pre ≤ 30000000)
    {d : List Nat} {owner : Bool} {output : ByteArray} {result : Outcome}
    (last : ReferenceCheckedDispatch.run d owner p finish fw middle output = result)
    (claims : ReferenceCheckedSystemOutcome.Claims kind c events result)
    (snapshot : ReferenceStorageView.Tx) :
    ∃ receipt, settle snapshot [] fw result = .returned receipt ∧ Facts grant receipt.meter := by
  cases result with
  | continued view warm meter event => exact False.elim claims
  | unsupported tag view warm meter out => exact False.elim claims
  | terminal result =>
    obtain ⟨_,handler,_⟩ := ReferenceCheckedDispatchTerminal.terminal last
    obtain ⟨amount,paid⟩ := ReferenceOutcomeGas.terminal_paid handler
    have valid := fresh_paid actual stack aligned fresh initialRefund initialBaseline maximum paid
    by_cases reverted : result.halt = .reverted
    · refine ⟨failure snapshot result.view fw (restore result.meter) result.output .reverted,?_,facts valid.2⟩
      simp only [settle,reverted,if_true,ReferenceChildMeter.settle]
    · refine ⟨success [] result.view fw result.meter result.output,?_,facts valid.1⟩
      simp only [settle,if_neg reverted]
  | eof post postWarm postMeter out =>
    have same := ReferenceCheckedEOF.fields last
    have paid : runFull [.ordinary 0] middle = some middle := by
      simp [runFull,ReferenceMeterPath.run,pay,ReferenceStorageGas.chargeExecution,core,update]
    refine ⟨success [] post postWarm postMeter out,rfl,?_⟩
    change Facts grant postMeter
    rw [←same.2.2.1]
    exact facts (fresh_paid actual stack aligned fresh initialRefund initialBaseline maximum paid).1
  | failed fault post postWarm postMeter out =>
    have paid := (actual.extract stack aligned).2.1
    have prior := (ReferenceMeterBoundary.accounting paid grant).2.2.1
    have fields := ReferenceMeterMetadata.dispatch d owner p finish fw middle output
    rw [last] at fields
    have baseline : postMeter.baseline = grant := fields.1.trans (prior.trans initialBaseline)
    have caught : ReferenceCheckedFaultClass.caught fault = true := claims
    refine ⟨failure snapshot post postWarm (ReferenceChildMeter.settle .exceptional postMeter) ByteArray.empty (.exceptional fault),?_,?_⟩
    · simp only [settle,caught,if_true]
    · apply facts
      exact ⟨baseline.le,by change (0 : Int) ≤ 0; omega,by change (0 : Int) < UInt256.size; decide⟩

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceSystemOutputReceipt

end
