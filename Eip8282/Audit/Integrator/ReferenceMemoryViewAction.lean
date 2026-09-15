import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Whole running-view transport for actual MSTORE and MSTORE8. The action's
capacity is computed from input view/operands. Operand shape and positive access
span are derived from actual Z/step; only a final capacity/host bound is local.
The complete SYSTEM trace supplies that capacity at each edge. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryViewAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem cap_word (cap : Nat) (host : 32*cap < 2^System.Platform.numBits) : cap < UInt256.size := by
  have hs : 2^64 < UInt256.size := by decide +kernel
  rcases System.Platform.numBits_eq with h | h <;> rw [h] at host <;> omega

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

theorem mstore {kind : Kind} {p : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hd : decodeAt pre = (.MSTORE,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (h : Related p v pre) (hc : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off value rest, v.stack = off::value::rest ∧
      Related p (memoryAction v off value.toByteArray rest) post := by
  have hz' : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) .MSTORE pre = .ok (mid,gasCost) := by simpa only [hd] using hz
  have hs' : StepOk (fuel+1) gasCost (.MSTORE,none) mid post := by simpa only [hd] using hs
  obtain ⟨rest,off,value,hstack,hpop⟩ := ReferenceAcceptedStack.pop2 hz' (by decide)
  have hb := RuntimeMemoryMonotone.accepted hat hz hs
  have hspan : off.toNat+32 ≤ 32*cap := by
    have hh := hb.2
    simp only [hd,RuntimeMemoryMonotone.span,hstack,List.getElem!_cons_zero] at hh
    have := hh (by decide)
    omega
  obtain ⟨hm,hst,ha,hss⟩ := ReferenceMemoryStep.mstore hz' hs' v.memory h.memory rest off value hpop cap
    (hb.1.trans hc) hspan (cap_word cap host) host
  have hword := RuntimeMemoryCharges.accepted_expansion hat hz hs
  have hw : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat value.toByteArray.size := by
    simpa [hd,RuntimeMemoryMonotone.span,hstack,UInt256.size_toByteArray] using hword
  have hehp : post.executionEnv = pre.executionEnv ∧ post.pc = pre.pc+UInt256.ofNat 1 := by
    obtain rfl := Z_ok_state hz'
    have known := EvmYul.EVM.Proof.step_MSTORE fuel gasCost (zMid pre .MSTORE) rest off value hpop
    have same := Except.ok.inj (hs'.symm.trans known)
    subst post
    exact ⟨rfl,rfl⟩
  have hf : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  exact ⟨off,value,rest,h.stack.trans hstack,assemble h hehp.1 hehp.2 hf hst ha hss hm hw⟩

theorem mstore8 {kind : Kind} {p : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hd : decodeAt pre = (.MSTORE8,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (h : Related p v pre) (hc : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off value rest, v.stack = off::value::rest ∧
      Related p (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest) post := by
  have hz' : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) .MSTORE8 pre = .ok (mid,gasCost) := by simpa only [hd] using hz
  have hs' : StepOk (fuel+1) gasCost (.MSTORE8,none) mid post := by simpa only [hd] using hs
  obtain ⟨rest,off,value,hstack,hpop⟩ := ReferenceAcceptedStack.pop2 hz' (by decide)
  have hb := RuntimeMemoryMonotone.accepted hat hz hs
  have hspan : off.toNat+1 ≤ 32*cap := by
    have hh := hb.2
    simp only [hd,RuntimeMemoryMonotone.span,hstack,List.getElem!_cons_zero] at hh
    have := hh (by decide)
    omega
  obtain ⟨hm,hst,ha,hss⟩ := ReferenceMemoryStep.mstore8 hz' hs' v.memory h.memory rest off value hpop cap
    (hb.1.trans hc) hspan (cap_word cap host) host
  have hword := RuntimeMemoryCharges.accepted_expansion hat hz hs
  have hw : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat
      (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).size := by
    change post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat 1
    simpa [hd,RuntimeMemoryMonotone.span,hstack] using hword
  have hehp : post.executionEnv = pre.executionEnv ∧ post.pc = pre.pc+UInt256.ofNat 1 := by
    obtain rfl := Z_ok_state hz'
    have known := EvmYul.EVM.Proof.step_MSTORE8 fuel gasCost (zMid pre .MSTORE8) rest off value hpop
    have same := Except.ok.inj (hs'.symm.trans known)
    subst post
    exact ⟨rfl,rfl⟩
  have hf : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  exact ⟨off,value,rest,h.stack.trans hstack,assemble h hehp.1 hehp.2 hf hst ha hss hm hw⟩

#print axioms mstore
#print axioms mstore8
end Eip8282.Audit.Integrator.ReferenceMemoryViewAction
