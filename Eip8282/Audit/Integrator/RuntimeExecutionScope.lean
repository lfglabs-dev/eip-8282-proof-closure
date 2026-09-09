import Eip8282.Audit.Integrator.RuntimeOpcodeScope
import Eip8282.Audit.Integrator.NestedFrameOccurrence
import Eip8282.Audit.Integrator.OrdinaryGas

/-!
Actual execution preserves the finite instruction sites of the pinned runtimes.
Jump destinations come from accepted Z; fallthrough widths come from decode.
The result includes every evaluator outcome, including proof-fuel exhaustion.
-/
namespace Eip8282.Audit.Integrator.RuntimeExecutionScope
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach Eip8282.Audit.Jumpdests
open Eip8282.Audit.Bytecode RuntimeOpcodeScope NestedEvents
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

structure Image where
  code : ByteArray
  sites : List Nat
  checked : ∀ pc ∈ sites, SiteOK code sites pc
  jumps : ∀ pc ∈ D_J code ⟨0⟩, pc.toNat ∈ sites
  eof : opcodeAt code code.size = none
  entry : 0 ∈ sites

def deposit : Image where
  code := depositRuntime
  sites := depositSites
  checked := deposit_checked
  jumps := fun _ h => (deposit_jump_scope h).1
  eof := by decide +kernel
  entry := by decide

def exit : Image where
  code := exitRuntime
  sites := exitSites
  checked := exit_checked
  jumps := fun _ h => (exit_jump_scope h).1
  eof := by decide +kernel
  entry := by decide

/-- The only additional site is the decoder's actual STOP default at EOF. -/
def At (image : Image) (pre : EVM.State) : Prop :=
  pre.executionEnv.code = image.code ∧
    (pre.pc.toNat ∈ image.sites ∨ pre.pc.toNat = image.code.size)

private theorem word_roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with
  | mk v =>
      apply congrArg UInt256.mk
      apply Fin.ext
      exact Nat.mod_eq_of_lt v.isLt

private theorem allowed_all : ∀ op ∈ allowedOps, op ∈ allOps := by decide +kernel

private theorem decode_at (pre : EVM.State) :
    decodeAt pre = (opcodeAt pre.executionEnv.code pre.pc.toNat).getD (.STOP, none) := by
  simp only [decodeAt, opcodeAt, word_roundtrip]

theorem opcode_allowed {image : Image} {pre : EVM.State} (h : At image pre) :
    (decodeAt pre).1 ∈ allowedOps := by
  rw [decode_at, h.1]
  rcases h.2 with hs | he
  · have hc := (image.checked _ hs).2
    cases hd : opcodeAt image.code pre.pc.toNat with
    | none => simp only [hd] at hc
    | some i =>
        simp only [hd] at hc
        simpa only [hd, Option.getD_some] using hc.1
  · simp only [he, image.eof, Option.getD_none]
    decide

theorem selected_none {n : Nat} {a : StepArgs} (hop : a.op ∈ allowedOps) :
    selectedChild n a = none := by
  have ha := allowed_all a.op hop
  cases n with
  | zero => rfl
  | succ n =>
    generalize ho : a.op = op at ha ⊢
    all_ops_cases ha <;> simp only [selectedChild, ho]

private theorem raw_pc {op : Operation .EVM} (hop : op ∈ allowedOps)
    {arg : Option (UInt256 × Nat)}
    (hw : ∀ v n, arg = some (v,n) → n = argOnNBytesOfInstr op)
    {pre post : EVM.State} (hs : EvmYul.step op arg pre = .ok post)
    (hh : H post.toMachineState op = none) :
    post.pc = pre.pc + UInt256.ofNat (argOnNBytesOfInstr op + 1) ∨
      (pre.stack[0]? = some post.pc ∧
        (op = .JUMP ∨ (op = .JUMPI ∧ pre.stack[1]? ≠ some ⟨0⟩))) := by
  have ha := allowed_all op hop
  rcases List.mem_append.mp ha with hb | he
  · by_cases hj : op = .JUMP
    · subst op
      obtain ⟨sh, pc, stk, ex⟩ := pre
      cases stk with
      | nil => cases hs
      | cons d stk => cases hs; exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inl (pc_step hb hj hw hs)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (simp [H] at hh)
      | skip
    all_goals
      obtain ⟨sh, pc, stk, ex⟩ := pre
      rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      all_goals first
        | (cases hs; exact Or.inl rfl)
        | skip
    all_goals
      cases hs
    all_goals
      split
      · right
        refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
        intro he
        have hb : b = ⟨0⟩ := Option.some.inj he
        have hn := bne_zero_false b hb
        exact Bool.false_ne_true (hn.symm.trans ‹(b != ⟨0⟩) = true›)
      · exact Or.inl rfl

private theorem accepted_jump {vj : Array UInt256} {op : Operation .EVM}
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

private theorem next_word (pc : UInt256) (op : Operation .EVM) :
    pc + UInt256.ofNat (argOnNBytesOfInstr op + 1) = N pc op := by
  conv_lhs => rw [← word_roundtrip pc]
  conv_rhs => rw [← word_roundtrip pc]
  change UInt256.ofNat pc.toNat + UInt256.ofNat (argOnNBytesOfInstr op + 1) =
    (UInt256.ofNat pc.toNat + UInt256.ofNat 1) + UInt256.ofNat (argOnNBytesOfInstr op)
  rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat]
  congr 1
  omega

theorem accepted_environment {image : Image} {pre mid post : EVM.State}
    {fuel cost : Nat} {vj : Array UInt256} (hat : At image pre)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : EVM.step fuel cost (some (decodeAt pre)) mid = .ok post) :
    post.executionEnv = pre.executionEnv := by
  have hop := opcode_allowed hat
  have ho := allowed_excludes _ hop
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    rw [OrdinaryGas.dispatch ⟨ho.2.1, ho.2.2.1⟩] at hs
    have he := executionEnv_step (allowed_all _ hop) hs
    rw [Z_ok_state hz] at he
    exact he

/-- Actual accepted, nonhalting steps preserve sites. No path certificate or
per-instruction boundary premise is supplied by the caller. -/
theorem accepted_next {image : Image} {pre mid post : EVM.State}
    {fuel cost : Nat} (hat : At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : EVM.step fuel cost (some (decodeAt pre)) mid = .ok post)
    (hh : H post.toMachineState (decodeAt pre).1 = none) : At image post := by
  have henv := accepted_environment hat hz hs
  refine ⟨(congrArg (fun e => e.code) henv).trans hat.1, ?_⟩
  rcases hat.2 with hsite | heof
  · have hc := image.checked _ hsite
    have hd : decodeAt pre =
        (opcodeAt image.code pre.pc.toNat).getD (.STOP, none) := by
      rw [decode_at, hat.1]
    cases he : opcodeAt image.code pre.pc.toNat with
    | none => simp only [SiteOK, he] at hc; exact False.elim hc.2
    | some i =>
      have hi : decodeAt pre = i := by simpa only [he, Option.getD_some] using hd
      have hall := opcode_allowed hat
      have ho := allowed_excludes _ hall
      have hw : ∀ v n, (decodeAt pre).2 = some (v,n) →
          n = argOnNBytesOfInstr (decodeAt pre).1 := by
        rw [hi]
        exact arg_width_of_opcodeAt he
      cases fuel with
      | zero => cases hs
      | succ fuel =>
        rw [OrdinaryGas.dispatch ⟨ho.2.1, ho.2.2.1⟩] at hs
        have hp := raw_pc hall hw hs hh
        rw [Z_ok_state hz] at hp
        change post.pc = pre.pc + UInt256.ofNat (argOnNBytesOfInstr (decodeAt pre).1 + 1) ∨
          (pre.stack[0]? = some post.pc ∧ ((decodeAt pre).1 = .JUMP ∨
            ((decodeAt pre).1 = .JUMPI ∧ pre.stack[1]? ≠ some ⟨0⟩))) at hp
        rcases hp with hp | ⟨hstack,hjump⟩
        · have hn := hc.2
          simp only [he] at hn
          have hpc : post.pc.toNat = nextPC pre.pc.toNat i.1 := by
            rw [hp, next_word, hi]
            simp only [nextPC, word_roundtrip]
          rw [hpc]
          exact hn.2
        · exact Or.inl (image.jumps _ (accepted_jump hz hstack hjump))
  · have hd : (decodeAt pre).1 = .STOP := by
      rw [decode_at, hat.1, heof, image.eof]
      rfl
    simp [hd, H] at hh

theorem step_tree_done {n : Nat} {a : StepArgs} {result : StepResult} {tree : EventTree}
    (hop : a.op ∈ allowedOps) (h : Cert (.step n a) result tree) : tree = .done := by
  cases h with
  | stepNone => rfl
  | stepChild hc body =>
      have hn := selected_none (n := n) hop
      change selectedChild n a = some _ at hc
      rw [hn] at hc
      cases hc

/-- A tree with no selected child, retaining its local markers at all outcomes. -/
inductive Local : EventTree → Prop
  | done : Local .done
  | next {marked : Bool} {tail : EventTree} : Local tail → Local (.step marked .done tail)

theorem cert_local {image : Image} {fuel : Nat} {pre : EVM.State}
    {result : XResult} {tree : EventTree} (hat : At image pre)
    (hc : Cert (.x fuel (D_J image.code ⟨0⟩) pre) result tree) : Local tree := by
  induction fuel generalizing pre result tree with
  | zero => cases hc; exact .done
  | succ fuel ih =>
      cases hc with
      | xGuardError => exact .done
      | xStepError hz hs =>
          have hd := step_tree_done (a := StepArgs.ofGuard _ _ _ _ hz) (opcode_allowed hat) hs
          rw [hd]
          exact .next .done
      | xNext hz hs hh ht =>
          have hd := step_tree_done (a := StepArgs.ofGuard _ _ _ _ hz) (opcode_allowed hat) hs
          have hp := accepted_next hat hz (sound hs) hh
          rw [hd]
          exact .next (ih hp ht)
      | xHalt hz hs hh hn =>
          have hd := step_tree_done (a := StepArgs.ofGuard _ _ _ _ hz) (opcode_allowed hat) hs
          rw [hd]
          exact .next .done
      | xRevert hz hs hh hr =>
          have hd := step_tree_done (a := StepArgs.ofGuard _ _ _ _ hz) (opcode_allowed hat) hs
          rw [hd]
          exact .next .done

private theorem step_no_xi {n f : Nat} {child : XiArgs} {outer : StepArgs}
    {result : StepResult} {tree : EventTree} {path : EventTree.Address} {r : XiResult}
    (hop : outer.op ∈ allowedOps)
    (loc : XiAt (.step n outer) result tree path f child r) : False := by
  cases loc with
  | stepChild hc body loc =>
      have hn := selected_none (n := n) hop
      change selectedChild n outer = some _ at hc
      rw [hn] at hc
      cases hc

/-- No actual descendant Xi invocation occurs, even one with zero events. -/
theorem x_no_xi {image : Image} {fuel f : Nat} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {child : XiArgs} {r : XiResult} (hat : At image pre)
    (loc : XiAt (.x fuel (D_J image.code ⟨0⟩) pre) result tree path f child r) : False := by
  induction fuel generalizing pre result tree path with
  | zero => cases loc
  | succ fuel ih =>
      cases loc with
      | xStepError hz hs loc => exact step_no_xi (opcode_allowed hat) loc
      | xNextChild hz hs hh ht loc => exact step_no_xi (opcode_allowed hat) loc
      | xNextTail hz hs hh ht loc => exact ih (accepted_next hat hz (sound hs) hh) loc
      | xHalt hz hs hh hn loc => exact step_no_xi (opcode_allowed hat) loc
      | xRevert hz hs hh hr loc => exact step_no_xi (opcode_allowed hat) loc

theorem entry_at {image : Image} {a : XiArgs} (hc : a.env.code = image.code) :
    At image a.entry := ⟨hc, Or.inl image.entry⟩

/-- At an actual pinned runtime entry the only located Xi frame is the entry
itself. This includes successful, reverted, and exceptional outcomes. -/
theorem xi_only_self {image : Image} {fuel f : Nat} {a child : XiArgs}
    {result r : XiResult} {tree : EventTree} {path : EventTree.Address}
    (hc : a.env.code = image.code)
    (loc : XiAt (.xi fuel a) result tree path f child r) :
    path = [] ∧ f = fuel ∧ child = a ∧ r = result := by
  cases loc with
  | here => exact ⟨rfl,rfl,rfl,rfl⟩
  | xi body loc =>
      have hj : a.jumps = D_J image.code ⟨0⟩ := by
        change D_J a.env.code ⟨0⟩ = _
        rw [hc]
      rw [hj] at loc
      exact False.elim (x_no_xi (entry_at hc) loc)

#print axioms opcode_allowed
#print axioms selected_none
#print axioms accepted_environment
#print axioms accepted_next
#print axioms cert_local
#print axioms x_no_xi
#print axioms xi_only_self
end Eip8282.Audit.Integrator.RuntimeExecutionScope
