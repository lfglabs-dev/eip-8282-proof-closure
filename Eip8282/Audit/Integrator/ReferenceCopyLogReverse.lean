import Eip8282.Audit.Integrator.ReferenceCalldataCopy
import Eip8282.Audit.Integrator.ReferenceLogView

/-! Reverse raw COPY/LOG0 effects from actual input operands, with a host bound
on computed memory expansion. No successful old step or post-state is assumed.
Source charging order and failed/static executions require separate extraction. -/
namespace Eip8282.Audit.Integrator.ReferenceCopyLogReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceLogView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem expanded {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (ReferenceReturnView.returnMemory v off len) := by
  have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    rw [related.memory.size,words_related related]
    omega
  have hext := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hmem,hex]
    have hc := related.memory.coherent
    change pre.memory.size ≤ 32*pre.activeWords.toNat at hc
    omega
  · rw [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

theorem copy {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {dest source len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = dest::source::len::rest)
    (host : 32*MachineState.M (words v) dest.toNat len.toNat < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .CALLDATACOPY none pre = .ok post ∧
      Related parent (ReferenceCalldataCopy.copyAction v dest source len rest) post := by
  have stack : pre.stack = dest::source::len::rest := related.stack.symm.trans shape
  let post := ({pre with toSharedState := pre.toSharedState.calldatacopy dest source len} : EVM.State).replaceStackAndIncrPC rest
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  have hhost : 32*MachineState.M pre.activeWords.toNat dest.toNat len.toNat < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  have hm := ReferenceCopyMemory.copy_related pre.toMachineState v.memory pre.executionEnv.calldata
    dest source len related.memory _ (Nat.le_refl _) hhost
  refine ⟨post,step_CALLDATACOPY stack,related.env,?_,rfl,?_,related.storage,related.logs,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change ReferenceMemoryOperations.Related _ (ReferenceCopyMemory.copyMemory v.memory v.env.calldata
      dest.toNat source.toNat len.toNat (32*MachineState.M (words v) dest.toNat len.toNat))
    rw [related.env,words_related related]
    exact hm

theorem log {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = off::len::rest)
    (host : 32*MachineState.M (words v) off.toNat len.toNat < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .LOG0 none pre = .ok post ∧
      Related parent (logAction v off len rest) post := by
  have stack : pre.stack = off::len::rest := related.stack.symm.trans shape
  let post := ({pre with toSharedState := SharedState.logOp off len #[] pre.toSharedState} : EVM.State).replaceStackAndIncrPC rest
  have raw := step_LOG0 stack
  have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat :=
    toNat_ofNat_lit _ (RuntimeMemoryMonotone.expansion_fit pre.activeWords off len)
  have hhost : 32*MachineState.M pre.activeWords.toNat off.toNat len.toNat < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hh : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hbytes : pre.memory.readWithPadding off.toNat len.toNat = ReferenceReturnView.output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  refine ⟨post,raw,related.env,?_,rfl,expanded related rfl hex,related.storage,?_,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change v.logs++[entry v off len] = ProtectedLogFrame.project pre.executionEnv.codeOwner
      {pre.substate with
        logSeries := pre.substate.logSeries.push ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩}
    rw [ProtectedLogFrame.push_self pre.executionEnv.codeOwner pre.substate
      ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩ rfl,
      ← related.logs,hbytes]
    rw [entry,related.env]

#print axioms copy
#print axioms log
end Eip8282.Audit.Integrator.ReferenceCopyLogReverse
