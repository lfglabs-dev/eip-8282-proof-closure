import Eip8282.Audit.Integrator.ActualAppendGas
import Eip8282.Audit.Integrator.OrdinaryGas

/-! Every valid nonhalting opcode has positive literal base/dynamic cost.
No stack-validity or positive-cost premise is assumed. Accepted Z identifies
the actual charged cost; H=None identifies a nonhalting continuation. -/
namespace Eip8282.Audit.Integrator.OpcodeCostPositive
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open InstructionGasGroups GasConstants
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem access_positive (a : AccountAddress) (s : Substate) : 0 < Caccess a s := by
  unfold Caccess
  split <;> decide

private theorem call_positive (t r : AccountAddress) (v g : UInt256)
    (w : AccountMap .EVM) (m : MachineState) (s : Substate) :
    0 < Ccall t r v g w m s := by
  have hp := access_positive t s
  unfold Ccall Cextra
  omega

private theorem sstore_positive (s : EVM.State) : 0 < Csstore s := by
  unfold Csstore
  dsimp only
  split <;> split
  all_goals simp only [Gwarmaccess,Gcoldsload,Gsset,Gsreset]
  all_goals repeat first | omega | split

theorem opcode_cost_positive (pre : EVM.State) (op : Operation .EVM)
    (valid : op ≠ .INVALID) (nonhalt : Halting op = false) : 0 < C' pre op := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (valid rfl)
    | (simp [Halting] at nonhalt; done)
    | exact sstore_positive pre
    | exact call_positive _ _ _ _ _ _ _
    | skip
  all_goals simp +decide only [C', ↓reduceIte]
  all_goals first
    | exact access_positive _ _
    | exact Nat.add_pos_left (access_positive _ _) _
    | skip
  all_goals simp only [Csload,Gwarmaccess,Gcoldsload,Gexp,Gexpbyte,
    Gcopy,Glog,Glogdata,Glogtopic,Gcreate,Gkeccak256,Gkeccak256word,
    Gverylow]
  all_goals first | omega | (split <;> omega)

/-- Actual H=None cannot be one of the four halting opcode constructors. -/
theorem nonhalting_of_H_none (post : MachineState) (op : Operation .EVM)
    (h : H post op = none) : Halting op = false := by
  exact H_eq_none_iff.mp h

/-- Z acceptance supplies validity and the exact dynamic cost at mid-state. -/
theorem accepted_nonhalting_cost {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} {post : MachineState}
    (hz : Z vj op pre = .ok (mid,cost)) (hn : H post op = none) : 0 < cost := by
  rw [(ActualAppendGas.accepted_gas hz).2.2.2]
  exact opcode_cost_positive mid op (OrdinaryGas.accepted_valid hz) (nonhalting_of_H_none post op hn)

#print axioms opcode_cost_positive
#print axioms nonhalting_of_H_none
#print axioms accepted_nonhalting_cost
end Eip8282.Audit.Integrator.OpcodeCostPositive
