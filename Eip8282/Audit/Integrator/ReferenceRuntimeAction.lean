import Eip8282.Audit.Integrator.ReferenceSystemAction
import Eip8282.Audit.Integrator.ReferenceCalldataCopy
import Eip8282.Audit.Integrator.ReferenceLogView

/-! All nonhalting instructions actually reachable in the two pinned runtimes.
Write permission is derived only at admitted SSTORE/LOG0; static fee getters
and other read-only successful paths require no global writable-context premise.
Whole user-path resource production and terminal rollback are separate layers. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

inductive Action (kind : Kind) (parent : ReferenceStorageView.Parent) : Instruction → View → View → Prop where
  | base {instr : Instruction} {v next : View} :
      ReferenceSystemAction.Action kind parent instr v next → Action kind parent instr v next
  | copy {v : View} {dest source len : UInt256} {rest : Stack UInt256} :
      v.stack = dest::source::len::rest → Action kind parent (.CALLDATACOPY,none) v
        (ReferenceCalldataCopy.copyAction v dest source len rest)
  | log {v : View} {off len : UInt256} {rest : Stack UInt256} :
      v.env.perm = true → v.stack = off::len::rest → Action kind parent (.LOG0,none) v
        (ReferenceLogView.logAction v off len rest)

private theorem store_permission {vj : Array UInt256} {pre mid : EVM.State} {gasCost : Nat}
    (hz : Z vj .SSTORE pre = .ok (mid,gasCost)) : pre.executionEnv.perm = true := by
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 8 replace hz := elim_guard hz
  have hn := elim_guard_not hz
  cases hp : pre.executionEnv.perm <;> simp [hp,W] at hn ⊢

private theorem base_step {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (related : Related parent v pre) (ha : SystemPathBudget.Allowed (decodeAt pre).1)
    (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ next, ReferenceSystemAction.Action kind parent (decodeAt pre) v next ∧ Related parent next post := by
  rcases ReferenceSystemAction.cases_of_nonhalting ha hh with hp | hp | hp | hp | hp
  · obtain ⟨next,ha,hr⟩ := ReferencePureComplete.accepted related hat hp hz hs cdfit
    exact ⟨next,.pure ha,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SLOAD hp rfl
    obtain ⟨key,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sload hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .load hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SSTORE hp rfl
    have permission : v.env.perm = true := by
      rw [related.env]
      exact store_permission (by simpa only [hd] using hz)
    obtain ⟨key,value,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sstore hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .store permission hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .word hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE8 hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore8 hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .byte hstack,hr⟩

/-- Actual runtime scope supplies opcode membership. No user/SYSTEM classifier
or global permission, desired action, operand shape or next view is supplied. -/
theorem step {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (related : Related parent v pre) (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ next, Action kind parent (decodeAt pre) v next ∧ Related parent next post := by
  by_cases hcopy : (decodeAt pre).1 = .CALLDATACOPY
  · have hd := ReferenceDecodeShape.fixed pre .CALLDATACOPY hcopy rfl
    obtain ⟨dest,source,len,rest,_,hshape,hr⟩ := ReferenceCalldataCopy.accepted hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .copy hshape,hr⟩
  · by_cases hlog : (decodeAt pre).1 = .LOG0
    · have hd := ReferenceDecodeShape.fixed pre .LOG0 hlog rfl
      obtain ⟨off,len,rest,_,hshape,hpermission,hr⟩ := ReferenceLogView.accepted hat hd hz hs related capacity host
      exact ⟨_,by rw [hd]; exact .log hpermission hshape,hr⟩
    · obtain ⟨next,ha,hr⟩ := base_step hat hz hs hh related
        ⟨RuntimeExecutionScope.opcode_allowed hat,hlog,hcopy⟩ cdfit capacity host
      exact ⟨next,.base ha,hr⟩

#print axioms step
end Eip8282.Audit.Integrator.ReferenceRuntimeAction
