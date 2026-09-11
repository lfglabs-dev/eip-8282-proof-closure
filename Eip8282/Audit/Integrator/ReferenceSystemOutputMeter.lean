import Eip8282.Audit.Integrator.ReferenceCheckedSystemOutcome

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
