import Eip8282.Audit.EntryReach.Path

/-! Immediate shape follows from the actual decoder, including its EOF/invalid
STOP default. No independently supplied well-shaped instruction is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceDecodeShape
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem no_argument (pre : EVM.State) (hw : argOnNBytesOfInstr (decodeAt pre).1 = 0) :
    decodeAt pre = ((decodeAt pre).1,none) := by
  unfold decodeAt decode at hw ⊢
  cases h : pre.toState.executionEnv.code.get? pre.pc.toNat >>= parseInstr with
  | none => rfl
  | some op =>
    rw [h] at hw
    dsimp only [Bind.bind,Option.bind,Option.getD] at hw ⊢
    simp [hw]

theorem argument_width (pre : EVM.State) (value : UInt256) (width : Nat)
    (ha : (decodeAt pre).2 = some (value,width)) :
    width = argOnNBytesOfInstr (decodeAt pre).1 := by
  unfold decodeAt decode at ha ⊢
  cases h : pre.toState.executionEnv.code.get? pre.pc.toNat >>= parseInstr with
  | none => rw [h] at ha; cases ha
  | some op =>
    rw [h] at ha
    dsimp only [Bind.bind,Option.bind,Option.getD] at ha ⊢
    split at ha
    · cases ha
    · exact (Prod.mk.inj (Option.some.inj ha)).2.symm

theorem fixed (pre : EVM.State) (op : Operation .EVM)
    (hop : (decodeAt pre).1 = op) (hw : argOnNBytesOfInstr op = 0) :
    decodeAt pre = (op,none) := by
  have hn := no_argument pre (by rw [hop]; exact hw)
  simpa only [hop] using hn

#print axioms no_argument
#print axioms argument_width
#print axioms fixed
end Eip8282.Audit.Integrator.ReferenceDecodeShape
