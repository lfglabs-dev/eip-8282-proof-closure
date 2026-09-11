import Eip8282.Audit.Integrator.ReferenceRuntimeView

/-! Actual STOP terminal observations. The source control_flow.stop only clears
running and leaves the view unchanged. Actual output is empty; identification
with the source frame's initially empty output belongs to frame initialization.
No running-PC increment, memory growth, write permission or stack shape occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceStopView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceRuntimeView
set_option autoImplicit false

theorem terminal {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hz : Z vj .STOP pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.STOP,none) mid post)
    (related : Related parent v pre) :
    Related parent v post ∧ H post.toMachineState .STOP = some ByteArray.empty := by
  obtain rfl := Z_ok_state hz
  change EVM.step (fuel+1) gasCost (some (.STOP,none)) (zMid pre .STOP) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := Eip8282.Audit.SymExec.step_STOP (stepPre gasCost (zMid pre .STOP))
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  exact ⟨⟨related.env,related.pc,related.stack,
    ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩,
    related.storage,related.logs,related.owner⟩,rfl⟩

#print axioms terminal
end Eip8282.Audit.Integrator.ReferenceStopView
