import Eip8282.Audit.Integrator.ReferenceRuntimeReverse
import Eip8282.Audit.Integrator.ReferenceReplayAdmission
import Eip8282.Audit.Integrator.ReferenceReplayMemoryCost

/-! Actual guarded replay of a successful protected running action. Source
post stack and input expansion bounds remain explicit producers; old Z and raw
effects are constructed. The source event supplies a conservative synthetic
budget, not an equality between source and old execution charges. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReplay
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction ReferenceRuntimeReadings ReferenceExecutionLedger
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem step {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} (fuel : Nat)
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : Action kind parent (decodeAt pre) v next)
    (postbounded : next.stack.length ≤ 1024)
    (host : 32*MachineState.M (words v) (RuntimeMemoryMonotone.span pre (decodeAt pre).1).1
      (RuntimeMemoryMonotone.span pre (decodeAt pre).1).2 < 2^System.Platform.numBits)
    (budget : C' pre (decodeAt pre).1+memoryExpansionCost pre (decodeAt pre).1+2301 ≤ pre.gasAvailable.toNat) :
    ∃ post,
      Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre =
        .ok (zMid pre (decodeAt pre).1,C' pre (decodeAt pre).1) ∧
      StepOk (fuel+1) (C' pre (decodeAt pre).1) (decodeAt pre) (zMid pre (decodeAt pre).1) post ∧
      Related parent next post := by
  have hz := ReferenceReplayAdmission.z related site effect postbounded budget
  let charged := stepPre (C' pre (decodeAt pre).1) (zMid pre (decodeAt pre).1)
  have hr : Related parent v charged := ReferenceRuntimeView.charged related _ _
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) charged := site
  have decoded : decodeAt charged = decodeAt pre := rfl
  obtain ⟨post,raw,nextRelated⟩ := ReferenceRuntimeReverse.raw hr hat decoded effect host
  have allowed := RuntimeExecutionScope.opcode_allowed site
  have excludes := RuntimeOpcodeScope.allowed_excludes _ allowed
  have ordinary : OrdinaryGas.Ordinary (decodeAt pre).1 := ⟨excludes.2.1,excludes.2.2.1⟩
  refine ⟨post,hz,?_,nextRelated⟩
  change EVM.step (fuel+1) _ (some (decodeAt pre)) _ = _
  rw [OrdinaryGas.dispatch ordinary]
  exact raw

/-- A source price on the same action funds an actually accepted old step.
The exact natural old debit is returned alongside the complete effect view. -/
theorem priced_step {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {warm : ReferenceSourceReadings.Warm} {event : ReferenceMeterPath.Event}
    (fuel : Nat) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : Action kind parent (decodeAt pre) v next)
    (postbounded : next.stack.length ≤ 1024)
    (host : 32*MachineState.M (words v) (RuntimeMemoryMonotone.span pre (decodeAt pre).1).1
      (RuntimeMemoryMonotone.span pre (decodeAt pre).1).2 < 2^System.Platform.numBits)
    (price : Price parent v warm next (decodeAt pre).1 event)
    (budget : 222*eventWork event+2301 ≤ pre.gasAvailable.toNat) :
    ∃ post,
      Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre =
        .ok (zMid pre (decodeAt pre).1,C' pre (decodeAt pre).1) ∧
      StepOk (fuel+1) (C' pre (decodeAt pre).1) (decodeAt pre) (zMid pre (decodeAt pre).1) post ∧
      Related parent next post ∧
      post.gasAvailable.toNat+memoryExpansionCost pre (decodeAt pre).1+C' pre (decodeAt pre).1 = pre.gasAvailable.toNat ∧
      memoryExpansionCost pre (decodeAt pre).1+C' pre (decodeAt pre).1 ≤ 222*eventWork event := by
  have allowed := RuntimeExecutionScope.opcode_allowed site
  obtain ⟨rawPost,raw,rawRelated⟩ := ReferenceRuntimeReverse.raw related site rfl effect host
  have cost := ReferenceReplayMemoryCost.total_ratio allowed related rawRelated raw price
  obtain ⟨post,hz,hs,postRelated⟩ := step fuel related site effect postbounded host (by omega)
  have excludes := RuntimeOpcodeScope.allowed_excludes _ allowed
  have debit := OrdinaryGas.accepted_step_debit ⟨excludes.2.1,excludes.2.2.1⟩ hz hs
  exact ⟨post,hz,hs,postRelated,debit,by omega⟩

#print axioms step
#print axioms priced_step
end Eip8282.Audit.Integrator.ReferenceRuntimeReplay
