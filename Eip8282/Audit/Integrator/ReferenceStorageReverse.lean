import Eip8282.Audit.Integrator.ReferenceStorageViewAction

/-! Reverse raw storage effects. The actual existing owner rules out the old
absent-owner SSTORE no-op. Source execution, permission/gas admission and warm
or original-storage correspondence remain separate; no old step is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem pc_fit {kind : Kind} {pre : EVM.State}
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre) :
    pre.pc.toNat+1 < UInt256.size := by
  have := ReferenceRuntimeSites.pc_fit site
  omega

theorem load {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {key : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = key::rest) :
    ∃ post, EvmYul.step (τ := .EVM) .SLOAD none pre = .ok post ∧
      Related parent (loadAction parent v key rest) post := by
  have stack : pre.stack = key::rest := related.stack.symm.trans shape
  let post := ({pre with toState := (pre.toState.sload key).1} : EVM.State).replaceStackAndIncrPC
    ((pre.toState.sload key).2::rest)
  have raw : EvmYul.step (τ := .EVM) .SLOAD none pre = .ok post := by
    obtain ⟨sh,pc,stk,ex⟩ := pre
    simp only at stack
    subst stack
    rfl
  refine ⟨post,raw,related.env,?_,?_,?_,?_,related.logs,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ (pc_fit site)]
    rfl
  · change ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray::rest =
      slotW pre.toState key::rest
    rw [related.env,related.storage key]
  · exact ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩
  · intro q
    exact related.storage q

theorem store {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {key value : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = key::value::rest) :
    ∃ post, EvmYul.step (τ := .EVM) .SSTORE none pre = .ok post ∧
      Related parent (storeAction v key value rest) post := by
  have stack : pre.stack = key::value::rest := related.stack.symm.trans shape
  let post := ({pre with toState := pre.toState.sstore key value} : EVM.State).replaceStackAndIncrPC rest
  refine ⟨post,step_SSTORE stack,?_,?_,rfl,?_,?_,?_,?_⟩
  · exact related.env.trans (executionEnv_sstore _ _ _).symm
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ (pc_fit site)]
    rfl
  · exact ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩
  · change ReferenceStorageView.Related parent
      (ReferenceStorageStep.storeView v.storage v.env.codeOwner key value) (pre.toState.sstore key value)
    rw [related.env]
    exact ReferenceStorageView.write_transport parent
      (ReferenceStorageView.readTracked v.storage pre.executionEnv.codeOwner key.toByteArray)
      pre.toState related.storage related.owner key value
  · change v.logs = ProtectedLogFrame.project
      (pre.toState.sstore key value).executionEnv.codeOwner (pre.toState.sstore key value).substate
    simpa only [ProtectedLogFrame.project,executionEnv_sstore,AppendSpec.logs_sstore] using related.logs
  · exact SystemSpec.owner_sstore related.owner key value

#print axioms load
#print axioms store
end Eip8282.Audit.Integrator.ReferenceStorageReverse
