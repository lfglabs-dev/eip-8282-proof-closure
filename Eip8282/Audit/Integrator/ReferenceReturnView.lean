import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Terminal RETURN view from the actual accepted step. Operand witnesses and
padding bounds are produced internally, with no source-offset restriction.
The literal source output and eager extension retain current storage and all
owner-address logs. No terminal PC comparison or Python execution is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceReturnView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def output (v : View) (off len : UInt256) : ByteArray :=
  ReferenceMemoryView.buffer v.memory off.toNat len.toNat

def returnMemory (v : View) (off len : UInt256) : ByteArray :=
  ReferenceMemoryOperations.extend v.memory (32*MachineState.M (words v) off.toNat len.toNat)

/-- Terminal observations deliberately have no running-PC component. -/
structure Result (parent : ReferenceStorageView.Parent) (v : View)
    (off len : UInt256) (rest : Stack UInt256) (post : EVM.State) : Prop where
  returned : post.H_return = output v off len
  stack : post.stack = rest
  env : v.env = post.executionEnv
  storage : ReferenceStorageView.Related parent v.storage post.toState
  owner : SystemSpec.HasOwner post.toState
  logs : v.logs = ProtectedLogFrame.project post.executionEnv.codeOwner post.substate
  memory : ReferenceMemoryOperations.Related post.toMachineState (returnMemory v off len)

private theorem return_frame {vj : Array UInt256} {pre mid post : EVM.State}
    {fuel gasCost : Nat} {off len : UInt256} {rest : Stack UInt256}
    (hz : Z vj .RETURN pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.RETURN,none) mid post)
    (operands : pre.stack.pop2 = some (rest,off,len)) :
    post.toState = pre.toState ∧ post.memory = pre.memory := by
  obtain rfl := Z_ok_state hz
  have known := EvmYul.EVM.Proof.step_RETURN fuel gasCost (zMid pre .RETURN) rest off len operands
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  exact ⟨rfl,rfl⟩

private theorem expanded_memory {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (returnMemory v off len) := by
  have hmono := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
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
  · rw [returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

/-- Actual Z supplies both operands. The final capacity supplies the padding
bound; the source offset may be any UInt256, including when length is zero. -/
theorem terminal {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hz : Z vj .RETURN pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.RETURN,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post := by
  obtain ⟨rest,off,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  have hex := RuntimeMemoryCharges.return_expansion hz hs hpop
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hp : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds
        pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      rw [← hex] at hb
      omega
  obtain ⟨hout,hstack,_,_⟩ := ReferenceMemoryStep.return_output hz hs
    v.memory related.memory rest off len hpop hlen
  obtain ⟨hstate,hmem⟩ := return_frame hz hs hpop
  have henv := congrArg EvmYul.State.executionEnv hstate
  have hsub := congrArg EvmYul.State.substate hstate
  refine ⟨off,len,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨hout,hstack,related.env.trans henv.symm,?_,?_,?_,expanded_memory related hmem hex⟩
  · rw [hstate]
    exact related.storage
  · rw [hstate]
    exact related.owner
  · rw [henv,hsub]
    exact related.logs

/-- An actual H observation identifies the output of the same terminal step. -/
theorem halted {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat} {out : ByteArray}
    (hz : Z vj .RETURN pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.RETURN,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits)
    (hh : H post.toMachineState .RETURN = some out) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post ∧ out = output v off len := by
  obtain ⟨off,len,rest,hpop,hshape,hr⟩ := terminal hz hs related capacity host
  have ho : post.H_return = out := Option.some.inj hh
  exact ⟨off,len,rest,hpop,hshape,hr,ho.symm.trans hr.returned⟩

#print axioms terminal
#print axioms halted
end Eip8282.Audit.Integrator.ReferenceReturnView
