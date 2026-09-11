import Eip8282.Audit.Integrator.ReferenceReturnSlice
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Actual internal REVERT terminal view. The pinned Amsterdam system.py
revert body expands memory and returns its slice before raising Revert.
Source: audit/receipts/direct-reference-memory-control-sources-20260910.json,
EL0cc100eb190b64b23baba72dac0165652eaec252 system.py SHA256
37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890.
This successful primitive-step observation does not assert that the enclosing
Theta commits this world or logs; wrapper rollback is a separate theorem.
Source gas/failure ordering and executable Python interpretation remain separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceRevertView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open ReferenceRuntimeView ReferenceReturnView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

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

/-- Actual admission supplies operands; final capacity supplies host bounds.
No runtime-site or source-offset restriction is needed. -/
theorem terminal {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hz : Z vj .REVERT pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.REVERT,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post := by
  obtain ⟨rest,off,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  obtain rfl := Z_ok_state hz
  have raw : EvmYul.step (τ := .EVM) .REVERT none
      (stepPre gasCost (zMid pre .REVERT)) = .ok post := by
    change EVM.step (fuel+1) gasCost (some (.REVERT,none)) _ = .ok post at hs
    rw [OrdinaryGas.dispatch (by decide)] at hs
    exact hs
  have hex := RuntimeMemoryCharges.raw_expansion (by decide : Operation.REVERT ∈ RuntimeOpcodeScope.allowedOps) raw
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat
    pre.stack[0]!.toNat pre.stack[1]!.toNat at hex
  rw [hshape] at hex
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat at hex
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hp : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds
        pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      rw [← hex] at hb
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hout : pre.memory.readWithPadding off.toNat len.toNat = output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have known := Eip8282.Audit.SymExec.step_REVERT
    (s := stepPre gasCost (zMid pre .REVERT)) hshape
  have same := Except.ok.inj (raw.symm.trans known)
  subst post
  refine ⟨off,len,rest,hpop,related.stack.trans hshape,?_⟩
  exact ⟨hout,rfl,related.env,related.storage,related.owner,related.logs,
    expanded_memory related rfl hex⟩

/-- Actual H identifies this internal terminal's output, including the exact
unpadded slice of the computed source memory. This is not a commit theorem. -/
theorem halted {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat} {out : ByteArray}
    (hz : Z vj .REVERT pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.REVERT,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits)
    (hh : H post.toMachineState .REVERT = some out) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post ∧
      out = output v off len ∧ out = (returnMemory v off len).extract off.toNat (off.toNat+len.toNat) := by
  obtain ⟨off,len,rest,hpop,hshape,hr⟩ := terminal hz hs related capacity host
  have ho : post.H_return = out := Option.some.inj hh
  have he := ho.symm.trans hr.returned
  exact ⟨off,len,rest,hpop,hshape,hr,he,
    he.trans (ReferenceReturnSlice.output_eq_extract related off len)⟩

#print axioms terminal
#print axioms halted
end Eip8282.Audit.Integrator.ReferenceRevertView
