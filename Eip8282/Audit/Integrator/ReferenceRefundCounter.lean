import Eip8282.Audit.Integrator.ReferenceCheckedRefund

/-! Source refund-counter arithmetic and checked U256 construction are bound
to the same linked runtime and its actual meter, not a supplied valid refund.
Consumer: full-frame transaction gas settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceRefundCounter
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceCheckedRefund (delta)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem execution_refund {m post : ReferenceStorageGas.Meter} {amount : Nat}
    (actual : ReferenceStorageGas.chargeExecution m amount = some post) : post.refund = m.refund := by
  unfold ReferenceStorageGas.chargeExecution at actual
  split at actual
  · cases actual; rfl
  · contradiction

private theorem state_refund {m post : ReferenceStorageGas.Meter} {amount : Nat}
    (actual : ReferenceStorageGas.chargeState m amount = some post) : post.refund = m.refund := by
  unfold ReferenceStorageGas.chargeState at actual
  split at actual
  · cases actual; rfl
  · split at actual
    · cases actual; rfl
    · contradiction

theorem pay_refund {event : Event} {m post : ReferenceStorageGas.Meter}
    (actual : pay event m = some post) : post.refund = m.refund+delta event := by
  cases event with
  | ordinary amount => simpa only [delta,add_zero] using execution_refund actual
  | store warm original current new =>
    change ReferenceStorageGas.storageCharge false warm original current new m = some post at actual
    unfold ReferenceStorageGas.storageCharge at actual
    simp only [Bool.false_eq_true,if_false] at actual
    split at actual
    · obtain ⟨mid,charged,stored⟩ := Option.bind_eq_some_iff.mp actual
      have first := execution_refund charged
      have second := state_refund stored
      exact second.trans first
    · contradiction

theorem run_refund {events : List Event} {m post : ReferenceStorageGas.Meter}
    (actual : ReferenceMeterPath.run events m = some post) : post.refund = m.refund+(events.map delta).sum := by
  induction events generalizing m with
  | nil => cases actual; simp
  | cons event events ih =>
    change (pay event m).bind (ReferenceMeterPath.run events) = some post at actual
    obtain ⟨mid,charged,tail⟩ := Option.bind_eq_some_iff.mp actual
    have first := pay_refund charged
    have rest := ih tail
    simp only [List.map_cons,List.sum_cons]
    omega

theorem full_refund {events : List Event} {m post : ReferenceMeterRollback.Meter}
    (actual : ReferenceMeterBoundary.runFull events m = some post) : post.refund = m.refund+(events.map delta).sum := by
  unfold ReferenceMeterBoundary.runFull at actual
  obtain ⟨last,paid,same⟩ := Option.map_eq_some_iff.mp actual
  cases same
  exact run_refund paid

def checked (refund : Int) : Option UInt256 :=
  if 0 ≤ refund ∧ refund < UInt256.size then some (UInt256.ofNat refund.toNat) else none

theorem fresh_prefix {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {final : ReferenceMeterRollback.Meter} {events : List Event} {txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx) :
    0 ≤ final.refund ∧ final.refund ≤ 21616*events.length ∧ final.refund < UInt256.size := by
  obtain ⟨source,paid,_⟩ := actual.extract stack aligned
  have lower := ReferenceCheckedRefund.source_balance source
  rw [fresh,ReferenceCheckedRefund.empty_potential,sub_zero] at lower
  have nonnegative := ReferenceCheckedRefund.nonnegative p finish.storage
  have upper := ReferenceCheckedRefund.delta_upper events
  have counter := full_refund paid
  have length := actual.length_bound stack aligned
  have maximum : ReferenceExecutionPotential.potential (ReferenceTransactionWork.initial txGas intrinsic) ≤ 16777216 := by
    simp only [ReferenceTransactionWork.initial,ReferenceChildMeter.init,ReferenceExecutionPotential.potential,ReferenceTransactionGas.allocate,Nat.add_zero]
    omega
  have numeric : (21616*16777216 : Int) < UInt256.size := by decide +kernel
  simp only [ReferenceTransactionWork.initial,ReferenceChildMeter.init,zero_add] at counter
  exact ⟨by omega,by omega,by omega⟩

theorem fresh_terminal {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle final : ReferenceMeterRollback.Meter} {events : List Event} {amount txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (terminal : ReferenceMeterBoundary.runFull [.ordinary amount] middle = some final) :
    0 ≤ final.refund ∧ final.refund < UInt256.size ∧
    checked final.refund = some (UInt256.ofNat final.refund.toNat) ∧
    ((UInt256.ofNat final.refund.toNat).toNat : Int) = final.refund := by
  have bounds := fresh_prefix actual stack aligned fresh
  have counter := full_refund terminal
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,delta,add_zero] at counter
  have nonnegative : 0 ≤ final.refund := by omega
  have fit : final.refund < UInt256.size := by omega
  refine ⟨nonnegative,fit,if_pos ⟨nonnegative,fit⟩,?_⟩
  have natFit : final.refund.toNat < UInt256.size := by omega
  change ((final.refund.toNat % UInt256.size : Nat) : Int) = final.refund
  rw [Nat.mod_eq_of_lt natFit]
  exact Int.toNat_of_nonneg nonnegative

#print axioms pay_refund
#print axioms run_refund
#print axioms full_refund
#print axioms fresh_prefix
#print axioms fresh_terminal
end Eip8282.Audit.Integrator.ReferenceRefundCounter
