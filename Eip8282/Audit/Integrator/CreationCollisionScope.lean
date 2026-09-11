import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.RuntimeThetaExclusion

/-! Actual creation at an installed protected runtime selects collision INVALID.
The computed address remains explicit; neither preimage validity nor sufficient
fuel is needed for the code-selection or exclusion conclusions. -/
namespace Eip8282.Audit.Integrator.CreationCollisionScope
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem runtime_size_positive (kind : ReachableCalls.Contract) :
    0 < (ReachableCalls.runtime kind).size := by
  cases kind <;> decide +kernel

theorem context_collision {kind : ReachableCalls.Contract} (c : CreationSettlement.Context)
    (bytes : ByteArray) (hc : JournalInvariant.CodeAt kind c.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind) :
    c.collision (CreationSettlement.address bytes) = true := by
  obtain ⟨old,ho,hcode⟩ := hc
  have he : c.existing (CreationSettlement.address bytes) = old := by
    unfold CreationSettlement.Context.existing
    rw [Std.TreeMap.getD_eq_getD_getElem?]
    change (c.world.get? (CreationSettlement.address bytes)).getD default = old
    rw [ha,ho]
    rfl
  have hn : old.code.size ≠ 0 := by
    rw [hcode]
    exact Nat.ne_of_gt (runtime_size_positive kind)
  have hd : decide (old.code.size ≠ 0) = true := decide_eq_true hn
  simp only [CreationSettlement.Context.collision, he, hd, Bool.or_true, Bool.true_or]

theorem selected_invalid {kind : ReachableCalls.Contract} (a : LambdaArgs)
    (bytes : ByteArray) (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind) :
    (a.xiArgs bytes).env.code = ⟨#[0xfe]⟩ := by
  have hcollision := context_collision (a.context 0) bytes hc ha
  change (a.context 0).selectedCode (CreationSettlement.address bytes) = _
  simp only [CreationSettlement.Context.selectedCode, hcollision, ↓reduceIte]

theorem no_theta {kind : ReachableCalls.Contract} {a : LambdaArgs} {bytes : ByteArray}
    (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind)
    {fuel f : Nat} {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {child : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (.xi fuel (a.xiArgs bytes)) result tree path f child r) : False :=
  RuntimeThetaExclusion.invalid_no_theta (selected_invalid a bytes hc ha) loc

theorem no_success {kind : ReachableCalls.Contract} {a : LambdaArgs} {bytes : ByteArray}
    (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind)
    {fuel : Nat} {published : Created × World × UInt256 × Substate} {out : ByteArray}
    (hr : (Request.xi fuel (a.xiArgs bytes)).eval = .ok (.success published out)) : False :=
  RuntimeThetaExclusion.invalid_no_success (selected_invalid a bytes hc ha) hr

#print axioms context_collision
#print axioms selected_invalid
#print axioms no_theta
#print axioms no_success
end Eip8282.Audit.Integrator.CreationCollisionScope
