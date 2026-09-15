import Eip8282.Audit.Integrator.ReferenceWordOps
import Eip8282.Audit.Execution.Words

/-! Successful source-shaped PUSH/POP/JUMP stack and running-PC effects.
Cached EL0cc vm/instructions/stack.py:29-83 and control_flow.py:48-102.
PUSH immediate value/width correspondence and jump-table correspondence must
come from exact-image decoding; arbitrary truncated-PUSH parity is false.
Actual Z acceptance supplies jump validity. Gas/error flow and terminal PCs
are not equated. DUP/SWAP source-index transport remains outside this module.
-/
namespace Eip8282.Audit.Integrator.ReferenceControlOps
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Running PC conversion, with the actual word-width bound explicit. -/
theorem next_pc (s : EVM.State) (stack : Stack UInt256) (width : Nat)
    (fit : s.pc.toNat+width < UInt256.size) :
    (s.replaceStackAndIncrPC stack width).pc.toNat = s.pc.toNat+width := by
  have hw : width < UInt256.size := by omega
  have he : (UInt256.ofNat width).toNat = width := toNat_ofNat_lit width hw
  change (s.pc+UInt256.ofNat width).toNat = _
  rw [toNat_add_of_lt _ _ (by rw [he]; exact fit),he]

theorem push_zero (s : EVM.State) (fit : s.pc.toNat+1 < UInt256.size) :
    EvmYul.step (τ := .EVM) .PUSH0 none s =
      .ok (s.replaceStackAndIncrPC (⟨0⟩::s.stack)) ∧
    (s.replaceStackAndIncrPC (⟨0⟩::s.stack)).pc.toNat = s.pc.toNat+1 :=
  ⟨rfl,next_pc s _ 1 fit⟩

/-- Covers PUSH1 through PUSH32 with exact operation width; the decoder must
supply the actual immediate word from a complete source span. -/
theorem push (op : Operation.POp) (s : EVM.State) (value : UInt256)
    (hn : op ≠ .PUSH0)
    (fit : s.pc.toNat+(argOnNBytesOfInstr (.Push op)+1) < UInt256.size) :
    EvmYul.step (.Push op) (some (value,argOnNBytesOfInstr (.Push op))) s =
      .ok (s.replaceStackAndIncrPC (value::s.stack) (argOnNBytesOfInstr (.Push op)+1)) ∧
    (s.replaceStackAndIncrPC (value::s.stack) (argOnNBytesOfInstr (.Push op)+1)).pc.toNat =
      s.pc.toNat+(argOnNBytesOfInstr (.Push op)+1) := by
  constructor
  · cases op <;> first | contradiction | rfl
  · exact next_pc s _ _ fit

theorem pop (s : EVM.State) (x : UInt256) (rest : Stack UInt256)
    (hs : s.stack=x::rest) (fit : s.pc.toNat+1 < UInt256.size) :
    EvmYul.step (τ := .EVM) .POP none s = .ok (s.replaceStackAndIncrPC rest) ∧
      (s.replaceStackAndIncrPC rest).pc.toNat = s.pc.toNat+1 := by
  constructor
  · obtain ⟨sh,pc,stk,ex⟩ := s
    simp only at hs
    subst stk
    rfl
  · exact next_pc s rest 1 fit

theorem accepted_jump {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    {dest : UInt256} (hd : pre.stack[0]? = some dest)
    (hj : op = .JUMP ∨ (op = .JUMPI ∧ pre.stack[1]? ≠ some ⟨0⟩)) : dest ∈ vj := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at hz
  replace hz := elim_guard hz
  replace hz := elim_guard hz
  replace hz := elim_guard hz
  replace hz := elim_guard hz
  have hJ := elim_guard_not hz
  replace hz := elim_guard hz
  have hI := elim_guard_not hz
  have hn : X.notIn pre.stack[0]? vj = false := by
    rcases hj with he | ⟨he,hne⟩
    · by_contra hf
      exact hJ ⟨he, by cases hv : X.notIn pre.stack[0]? vj <;> simp_all⟩
    · by_contra hf
      exact hI ⟨he, hne, by cases hv : X.notIn pre.stack[0]? vj <;> simp_all⟩
  have hc : vj.contains dest = true := by simpa [X.notIn, X.belongs, hd] using hn
  obtain ⟨w, hw, hb⟩ := Array.contains_iff_exists_mem_beq.mp hc
  have he : w = dest := by
    cases w with
    | mk w =>
      cases dest with
      | mk d =>
        change (d == w) = true at hb
        exact congrArg UInt256.mk (eq_of_beq hb).symm
  exact he ▸ hw


/-- Jump membership follows actual Z, not a proposed post-PC premise. -/
theorem jump {vj : Array UInt256} {s mid : EVM.State} {cost : Nat}
    (hz : Z vj .JUMP s = .ok (mid,cost)) (dest : UInt256) (rest : Stack UInt256)
    (hs : s.stack=dest::rest) :
    dest ∈ vj ∧ EvmYul.step (τ := .EVM) .JUMP none s = .ok {s with pc:=dest,stack:=rest} := by
  constructor
  · exact accepted_jump hz (by rw [hs]; rfl) (Or.inl rfl)
  · exact pureStep_sound (by decide) (by simp only [pureStep,hs])

theorem jumpi_taken {vj : Array UInt256} {s mid : EVM.State} {cost : Nat}
    (hz : Z vj .JUMPI s = .ok (mid,cost)) (dest cond : UInt256) (rest : Stack UInt256)
    (hs : s.stack=dest::cond::rest) (hn : cond ≠ ⟨0⟩) :
    dest ∈ vj ∧ EvmYul.step (τ := .EVM) .JUMPI none s = .ok {s with pc:=dest,stack:=rest} := by
  constructor
  · apply accepted_jump hz (by rw [hs]; rfl)
    exact Or.inr ⟨rfl,by simpa [hs] using hn⟩
  · exact step_JUMPI_taken hs hn

/-- An untaken conditional jump does not require its destination to be valid. -/
theorem jumpi_zero {vj : Array UInt256} {s mid : EVM.State} {cost : Nat}
    (_hz : Z vj .JUMPI s = .ok (mid,cost)) (dest : UInt256) (rest : Stack UInt256)
    (hs : s.stack=dest::⟨0⟩::rest) (fit : s.pc.toNat+1 < UInt256.size) :
    EvmYul.step (τ := .EVM) .JUMPI none s =
      .ok {s with pc:=s.pc+⟨1⟩,stack:=rest} ∧
    (s.pc+⟨1⟩).toNat = s.pc.toNat+1 :=
  ⟨step_JUMPI_untaken hs rfl,next_pc s rest 1 fit⟩

/-- Python end-pop/end-push versus pinned head-pop/head-push. -/
theorem python_push_pop (base : List UInt256) (x : UInt256) :
    ReferenceWordOps.fromPython (base++[x]) = x::ReferenceWordOps.fromPython base := by
  simp [ReferenceWordOps.fromPython,List.reverse_append]

#print axioms next_pc
#print axioms push_zero
#print axioms push
#print axioms pop
#print axioms accepted_jump
#print axioms jump
#print axioms jumpi_taken
#print axioms jumpi_zero
#print axioms python_push_pop
end Eip8282.Audit.Integrator.ReferenceControlOps
