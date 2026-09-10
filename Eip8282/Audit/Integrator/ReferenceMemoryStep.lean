import Eip8282.Audit.Integrator.ReferenceMemoryOperations
import EvmYul.EVM.Proof.MemoryStep
import EvmYul.EVM.Proof.Block

/-! Memory relation along actual accepted EVM opcodes. Z and step gas updates
are retained, and the observed post-state is the actual supplied step result.
Source instruction interpretation and resource sufficiency remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryStep
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceMemoryOperations
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem charged_relation (pre : EVM.State) (op : Operation .EVM) (cost : Nat)
    (reference : ByteArray) (h : Related pre.toMachineState reference) :
    Related (stepPre cost (zMid pre op)).toMachineState reference :=
  ⟨h.coherent,h.size,h.bytes⟩

theorem mstore {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .MSTORE pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.MSTORE,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off value : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,value)) (cap : Nat)
    (active : pre.activeWords.toNat ≤ cap) (span : off.toNat+32 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related post.toMachineState (splice reference off.toNat value.toByteArray (32*post.activeWords.toNat)) ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_MSTORE fuel cost (zMid pre .MSTORE) rest off value operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.mstore _ reference off value cap
    (charged_relation pre .MSTORE cost reference related) active span word host,rfl,rfl,rfl⟩

theorem mstore8 {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .MSTORE8 pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.MSTORE8,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off value : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,value)) (cap : Nat)
    (active : pre.activeWords.toNat ≤ cap) (span : off.toNat+1 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related post.toMachineState
      (splice reference off.toNat ⟨#[UInt8.ofNat value.toNat]⟩ (32*post.activeWords.toNat)) ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_MSTORE8 fuel cost (zMid pre .MSTORE8) rest off value operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.mstore8 _ reference off value cap
    (charged_relation pre .MSTORE8 cost reference related) active span word host,rfl,rfl,rfl⟩

theorem return_output {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .RETURN pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.RETURN,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off len : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,len))
    (host : len.toNat < 2^System.Platform.numBits) :
    post.H_return = ReferenceMemoryView.buffer reference off.toNat len.toNat ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_RETURN fuel cost (zMid pre .RETURN) rest off len operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.return_output _ reference off len
    (charged_relation pre .RETURN cost reference related) host,rfl,rfl,rfl⟩

#print axioms mstore
#print axioms mstore8
#print axioms return_output
end Eip8282.Audit.Integrator.ReferenceMemoryStep
