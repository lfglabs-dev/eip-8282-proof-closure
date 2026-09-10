import Eip8282.Audit.Integrator.ReferenceMemoryViewAction

/-! Raw inverse MSTORE/MSTORE8 effects from actual input operands. The only
capacity premise is a host bound on the computed input expansion; no post-state
or old admission is assumed. The source ledger must supply that host bound. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem assemble {p : ReferenceStorageView.Parent} {v : View} {pre post : EVM.State}
    {off : UInt256} {data : ByteArray} {rest : Stack UInt256} (h : Related p v pre)
    (he : post.executionEnv = pre.executionEnv) (hp : post.pc = pre.pc+UInt256.ofNat 1)
    (hf : pre.pc.toNat+1 < UInt256.size) (hst : post.stack = rest)
    (ha : post.accountMap = pre.accountMap) (hss : post.substate = pre.substate)
    (hm : ReferenceMemoryOperations.Related post.toMachineState
      (ReferenceMemoryOperations.splice v.memory off.toNat data (32*post.activeWords.toNat)))
    (hw : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat data.size) :
    Related p (memoryAction v off data rest) post := by
  refine ⟨h.env.trans he.symm,?_,hst.symm,?_,?_,?_,?_⟩
  · change v.pc+1 = post.pc.toNat
    rw [h.pc,hp,toNat_add_of_lt _ _ (by exact hf)]
    rfl
  · change ReferenceMemoryOperations.Related post.toMachineState
      (ReferenceMemoryOperations.splice v.memory off.toNat data (32*MachineState.M (words v) off.toNat data.size))
    rw [words_related h,← hw]
    exact hm
  · intro key
    have ht := h.storage key
    simpa only [memoryAction, slotW,EvmYul.State.sload,EvmYul.State.lookupAccount,he,ha] using ht
  · change v.logs = ProtectedLogFrame.project post.executionEnv.codeOwner post.substate
    rw [he,hss]
    exact h.logs
  · obtain ⟨a,hao⟩ := h.owner
    exact ⟨a,by rw [he,ha]; exact hao⟩

theorem mstore {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {off value : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = off::value::rest)
    (host : 32*MachineState.M (words v) off.toNat 32 < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .MSTORE none pre = .ok post ∧
      Related parent (memoryAction v off value.toByteArray rest) post := by
  have stack : pre.stack = off::value::rest := related.stack.symm.trans shape
  let cap := MachineState.M pre.activeWords.toNat off.toNat 32
  have word : cap < UInt256.size := RuntimeMemoryMonotone.expansion_fit_nat _ _ _
    pre.activeWords.val.isLt off.val.isLt (by decide +kernel)
  have bounds := ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat 32
  have hhost : 32*cap < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  let post := ({pre with toMachineState := pre.toMachineState.mstore off value} : EVM.State).replaceStackAndIncrPC rest
  have raw : EvmYul.step (τ := .EVM) .MSTORE none pre = .ok post := by
    change EVM.binaryMachineStateOp MachineState.mstore pre = _
    simp only [EVM.binaryMachineStateOp,stack,Stack.pop2]
    rfl
  have hm := ReferenceMemoryOperations.mstore pre.toMachineState v.memory off value cap
    related.memory bounds.1 (bounds.2 (by decide)) word hhost
  have hw : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat value.toByteArray.size := by
    change (UInt256.ofNat cap).toNat = _
    rw [toNat_ofNat_lit _ word]
    simp only [UInt256.size_toByteArray]; rfl
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  exact ⟨post,raw,assemble related rfl rfl fit rfl rfl rfl hm hw⟩

theorem mstore8 {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {off value : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = off::value::rest)
    (host : 32*MachineState.M (words v) off.toNat 1 < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .MSTORE8 none pre = .ok post ∧
      Related parent (memoryAction v off (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) rest) post := by
  have stack : pre.stack = off::value::rest := related.stack.symm.trans shape
  let cap := MachineState.M pre.activeWords.toNat off.toNat 1
  have word : cap < UInt256.size := RuntimeMemoryMonotone.expansion_fit_nat _ _ _
    pre.activeWords.val.isLt off.val.isLt (by decide +kernel)
  have bounds := ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat 1
  have hhost : 32*cap < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  let post := ({pre with toMachineState := pre.toMachineState.mstore8 off value} : EVM.State).replaceStackAndIncrPC rest
  have raw : EvmYul.step (τ := .EVM) .MSTORE8 none pre = .ok post := by
    change EVM.binaryMachineStateOp MachineState.mstore8 pre = _
    simp only [EVM.binaryMachineStateOp,stack,Stack.pop2]
    rfl
  have hm := ReferenceMemoryOperations.mstore8 pre.toMachineState v.memory off value cap
    related.memory bounds.1 (bounds.2 (by decide)) word hhost
  have hw : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).size := by
    change (UInt256.ofNat cap).toNat = _
    rw [toNat_ofNat_lit _ word]
    rfl
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  exact ⟨post,raw,assemble related rfl rfl fit rfl rfl rfl hm hw⟩

#print axioms mstore
#print axioms mstore8
end Eip8282.Audit.Integrator.ReferenceMemoryReverse
