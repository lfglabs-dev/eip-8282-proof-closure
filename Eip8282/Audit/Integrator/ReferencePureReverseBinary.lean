import Eip8282.Audit.Integrator.ReferencePureAction

/-! Reverse raw arithmetic effects on the fixed protected runtimes. Operands
come from successful source-shaped actions, not old admission. This does not
identify gas meters or assert extraction from the Python interpreter. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseBinary
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (b : ReferenceWordOps.Binary) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (ReferenceWordOps.opcode b,arg))
    (effect : action kind (ReferenceWordOps.opcode b,arg) v = some next) :
    ∃ post, EvmYul.step (ReferenceWordOps.opcode b) arg pre = .ok post ∧
      Related parent next post := by
  have fit := ReferenceRuntimeSites.pc_fit site
  rw [decoded] at fit
  have width : argOnNBytesOfInstr (ReferenceWordOps.opcode b) = 0 := by cases b <;> rfl
  have fit1 : pre.pc.toNat+1 < UInt256.size := by simpa [width] using fit
  change (classify (opcode (.binary b))).bind _ = _ at effect
  rw [classify_opcode] at effect
  simp only [Option.bind_some] at effect
  cases shape : v.stack with
  | nil => simp [familyAction,shape] at effect
  | cons x tail =>
    cases tail with
    | nil => simp [familyAction,shape] at effect
    | cons y rest =>
      have stack : pre.stack = x::y::rest := related.stack.symm.trans shape
      simp only [familyAction,shape] at effect
      cases effect
      exact ⟨_,binary_raw b arg pre x y rest stack,related_advance related _ 1 fit1⟩

#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseBinary
