import Eip8282.Audit.Integrator.ReferenceRuntimeView
import Eip8282.Audit.Integrator.ReferenceAcceptedStack

/-! Produce complete source-shaped storage actions from actual accepted runtime
steps. The pop operands, natural PC bound and post-view relation are derived.
These local action constructors are not a Python execution semantics; original
storage, warmth/refunds, source account validity and charged replay stay separate.
The retained log projection includes every topic and payload at the owner. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageViewAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem memory_frame {pre post : EVM.State} {memory : ByteArray}
    (hf : ReferenceStorageStep.Frame pre post)
    (hm : ReferenceMemoryOperations.Related pre.toMachineState memory) :
    ReferenceMemoryOperations.Related post.toMachineState memory := by
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hf.memory,hf.activeWords]
    exact hm.coherent
  · rw [hf.activeWords]
    exact hm.size
  · rw [hf.memory]
    exact hm.bytes

private theorem natural_pc {kind : Kind} {pre post : EVM.State}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hf : ReferenceStorageStep.Frame pre post) : post.pc.toNat = pre.pc.toNat+1 := by
  have hfit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  rw [hf.pc,toNat_add_of_lt _ _ hfit]
  rfl

private theorem logs_frame {pre post : EVM.State} {logs : List LogEntry}
    (hf : ReferenceStorageStep.Frame pre post)
    (hl : logs = ProtectedLogFrame.project pre.executionEnv.codeOwner pre.substate) :
    logs = ProtectedLogFrame.project post.executionEnv.codeOwner post.substate := by
  simpa only [ProtectedLogFrame.project,hf.executionEnv,hf.logs] using hl

/-- The actual accepted stack supplies the source load key and remainder. -/
theorem sload {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hdecode : decodeAt pre = (.SLOAD,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre) :
    ∃ key rest, pre.stack.pop = some (rest,key) ∧ v.stack = key::rest ∧
      Related parent (loadAction parent v key rest) post := by
  rw [hdecode] at hz hs
  obtain ⟨rest,key,hshape,hpop⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
  obtain ⟨hstorage,howner,hstack,hframe,_⟩ := ReferenceStorageStep.sload hz hs
    parent v.storage related.storage related.owner hpop
  refine ⟨key,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨related.env.trans hframe.executionEnv.symm,?_,?_,
    memory_frame hframe related.memory,?_,logs_frame hframe related.logs,howner⟩
  · change v.pc+1 = post.pc.toNat
    rw [related.pc,natural_pc hat hframe]
  · change ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray::rest = post.stack
    rw [related.env,hstack]
  · change ReferenceStorageView.Related parent
      (ReferenceStorageView.readTracked v.storage v.env.codeOwner key.toByteArray) post.toState
    rw [related.env]
    exact hstorage

/-- Key and value are produced from actual Z admission. The literal action's
post storage, memory, logs, environment and PC are all proved related. -/
theorem sstore {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hdecode : decodeAt pre = (.SSTORE,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre) :
    ∃ key value rest, pre.stack.pop2 = some (rest,key,value) ∧
      v.stack = key::value::rest ∧ Related parent (storeAction v key value rest) post := by
  rw [hdecode] at hz hs
  obtain ⟨rest,key,value,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  obtain ⟨hstorage,howner,hstack,hframe⟩ := ReferenceStorageStep.sstore hz hs
    parent v.storage related.storage related.owner hpop
  refine ⟨key,value,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨related.env.trans hframe.executionEnv.symm,?_,hstack.symm,
    memory_frame hframe related.memory,?_,logs_frame hframe related.logs,howner⟩
  · change v.pc+1 = post.pc.toNat
    rw [related.pc,natural_pc hat hframe]
  · change ReferenceStorageView.Related parent
      (ReferenceStorageStep.storeView v.storage v.env.codeOwner key value) post.toState
    rw [related.env]
    exact hstorage

#print axioms sload
#print axioms sstore
end Eip8282.Audit.Integrator.ReferenceStorageViewAction
