import Eip8282.Audit.Integrator.ReferencePureReverseComplete
import Eip8282.Audit.Integrator.ReferenceStorageReverse
import Eip8282.Audit.Integrator.ReferenceMemoryReverse
import Eip8282.Audit.Integrator.ReferenceCopyLogReverse
import Eip8282.Audit.Integrator.ReferenceRuntimeAction

/-! Compose all running protected-runtime raw effects in the reverse direction.
Successful source-shaped Action supplies its result; the pinned raw result is
constructed. The host premise concerns input-derived expansion, never a chosen
post-state. Source extraction and guarded resource replay remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {instr : Instruction}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = instr)
    (effect : Action kind parent instr v next)
    (host : 32*MachineState.M (words v) (RuntimeMemoryMonotone.span pre instr.1).1
      (RuntimeMemoryMonotone.span pre instr.1).2 < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step instr.1 instr.2 pre = .ok post ∧ Related parent next post := by
  cases effect with
  | base base =>
    cases base with
    | pure effect =>
      rw [←decoded] at effect ⊢
      exact ReferencePureReverseComplete.raw related site effect
    | load shape => exact ReferenceStorageReverse.load related site shape
    | store permission shape => exact ReferenceStorageReverse.store related site shape
    | word shape =>
      apply ReferenceMemoryReverse.mstore related site shape
      simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero] using host
    | byte shape =>
      apply ReferenceMemoryReverse.mstore8 related site shape
      simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero] using host
  | copy shape =>
    apply ReferenceCopyLogReverse.copy related site shape
    simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero,
      List.getElem!_cons_succ] using host
  | log permission shape =>
    apply ReferenceCopyLogReverse.log related site shape
    simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero,
      List.getElem!_cons_succ] using host

#print axioms raw
end Eip8282.Audit.Integrator.ReferenceRuntimeReverse
