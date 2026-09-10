import Eip8282.Audit.Integrator.ReferenceCopyMemory
import Eip8282.Audit.Integrator.ReferenceRuntimeView
import Eip8282.Audit.Integrator.ReferenceAcceptedStack
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Actual accepted CALLDATACOPY constructs a source-shaped view update.
Cached Amsterdam EL0cc100eb190b64b23baba72dac0165652eaec252
vm/instructions/environment.py:206-243 SHA256
8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657:
pop destination/source/length, charge, extend, buffer_read, memory_write.
This proves the local effect on the running view, not Python execution or its
base/per-word gas charge. User-path capacity production remains separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceCalldataCopy
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def copyAction (v : View) (dest source len : UInt256) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1
    stack := rest
    memory := ReferenceCopyMemory.copyMemory v.memory v.env.calldata
      dest.toNat source.toNat len.toNat (32*MachineState.M (words v) dest.toNat len.toNat)}

/-- Actual admission supplies all operands. The only local resource premise is
an endpoint cap fitting the host; there is no source-offset bound or predicted
post memory/storage/log relation. Zero length permits every destination. -/
theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.CALLDATACOPY,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ dest source len rest, pre.stack.pop3 = some (rest,dest,source,len) ∧
      v.stack = dest::source::len::rest ∧ Related parent (copyAction v dest source len rest) post := by
  have hex := RuntimeMemoryCharges.accepted_expansion hat hz hs
  rw [decoded] at hz hs hex
  obtain ⟨rest,dest,source,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop3 hz (by decide)
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat
    pre.stack[0]!.toNat pre.stack[2]!.toNat at hex
  rw [hshape] at hex
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat dest.toNat len.toNat at hex
  rw [hex] at capacity
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  obtain rfl := Z_ok_state hz
  change EVM.step (fuel+1) gasCost (some (.CALLDATACOPY,none)) (zMid pre .CALLDATACOPY) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := step_CALLDATACOPY (s := stepPre gasCost (zMid pre .CALLDATACOPY)) hshape
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  have hm := ReferenceCopyMemory.copy_related (stepPre gasCost (zMid pre .CALLDATACOPY)).toMachineState
    v.memory pre.executionEnv.calldata dest source len
    (charged related .CALLDATACOPY gasCost).memory cap capacity host
  refine ⟨dest,source,len,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨related.env,?_,rfl,?_,related.storage,related.logs,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change ReferenceMemoryOperations.Related _ (ReferenceCopyMemory.copyMemory v.memory v.env.calldata
      dest.toNat source.toNat len.toNat (32*MachineState.M (words v) dest.toNat len.toNat))
    rw [related.env,words_related related]
    exact hm

#print axioms accepted
end Eip8282.Audit.Integrator.ReferenceCalldataCopy
