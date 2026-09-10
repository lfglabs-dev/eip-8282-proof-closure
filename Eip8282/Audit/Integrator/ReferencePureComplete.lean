import Eip8282.Audit.Integrator.ReferencePureEnvironment
import Eip8282.Audit.Integrator.ReferencePureControl

/-! All supported pure families on one actual accepted step. Actual decoder
operands and post-state are preserved through the common running-view relation. -/
namespace Eip8282.Audit.Integrator.ReferencePureComplete
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem family {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Pure) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (opcode p,arg) mid post)
    (cdfit : v.env.calldata.size < UInt256.size) :
    ∃ next, action kind (opcode p,arg) v = some next ∧ Related parent next post := by
  cases p
  all_goals first
    | exact ReferencePureAction.binary _ h hat decoded hz hs
    | exact ReferencePureEnvironment.accepted _ (by trivial) h hat decoded hz hs (fun _ => cdfit)
    | exact ReferencePureControl.accepted _ (by trivial) h hat decoded hz hs

theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (supported : Supported (decodeAt pre).1)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (decodeAt pre) mid post)
    (cdfit : v.env.calldata.size < UInt256.size) :
    ∃ next, action kind (decodeAt pre) v = some next ∧ Related parent next post := by
  obtain ⟨p,hp⟩ := supported
  have hd : decodeAt pre = (opcode p,(decodeAt pre).2) := by
    apply Prod.ext
    · exact hp.symm
    · rfl
  have hz' : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost) := by
    simpa only [hat.1,hp] using hz
  have hs' : StepOk (fuel+1) cost (opcode p,(decodeAt pre).2) mid post := by
    rw [hd] at hs
    exact hs
  obtain ⟨next,ha,hr⟩ := family p h hat hd hz' hs' cdfit
  exact ⟨next,by rw [hd]; exact ha,hr⟩

#print axioms family
#print axioms accepted
end Eip8282.Audit.Integrator.ReferencePureComplete
