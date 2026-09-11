import Eip8282.Audit.Integrator.RuntimeMemoryMonotone
import EvmYul.EVM.Proof.MemoryStep

/-! Source-formula memory cost differences along the actual pinned XRuns.
The history is constructed from the run, not supplied as a desired charge
certificate. This does not assert that a reference interpreter charged these
amounts: it evaluates the source cost formula on actual pinned capacities. -/
namespace Eip8282.Audit.Integrator.RuntimeMemoryCharges
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope
open RuntimeMemoryMonotone (span Bounds expansion_fit expansion_fit_nat)
open ReferenceMemoryCapacity (cost cost_mono)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Repeated literal RETURN/REVERT expansion has the same high-water mark. -/
theorem expansion_idempotent (aw off len : Nat) :
    MachineState.M (MachineState.M aw off len) off len = MachineState.M aw off len := by
  cases len <;> simp [MachineState.M]

private theorem raw_dup (n : Nat) {pre post : EVM.State}
    (hs : EvmYul.dup n pre = .ok post) : post.activeWords = pre.activeWords := by
  unfold EvmYul.dup at hs
  dsimp only at hs
  split at hs
  · cases hs; rfl
  · cases hs

private theorem raw_swap (n : Nat) {pre post : EVM.State}
    (hs : EvmYul.swap n pre = .ok post) : post.activeWords = pre.activeWords := by
  unfold EvmYul.swap at hs
  dsimp only at hs
  split at hs
  · cases hs; rfl
  · cases hs

private theorem raw_fixed {op : Operation .EVM} (hop : op ∈ allowedOps)
    (hc : op ≠ .CALLDATACOPY) (hm : op ≠ .MSTORE) (hm8 : op ≠ .MSTORE8)
    (hl : op ≠ .LOG0) (hr : op ≠ .RETURN) (hv : op ≠ .REVERT)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (hs : EvmYul.step op arg pre = .ok post) :
    post.activeWords = pre.activeWords ∧ span pre op = (0,0) := by
  simp only [allowedOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hc rfl)
    | exact False.elim (hm rfl)
    | exact False.elim (hm8 rfl)
    | exact False.elim (hl rfl)
    | exact False.elim (hr rfl)
    | exact False.elim (hv rfl)
    | exact ⟨raw_dup _ hs, rfl⟩
    | exact ⟨raw_swap _ hs, rfl⟩
    | skip
  all_goals
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z, tail⟩⟩⟩
    all_goals cases hs <;> exact ⟨rfl,rfl⟩

/-- Exact active-word metadata for the same actual raw runtime instruction. -/
theorem raw_expansion {op : Operation .EVM} (hop : op ∈ allowedOps)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (hs : EvmYul.step op arg pre = .ok post) : post.activeWords.toNat =
      MachineState.M pre.activeWords.toNat (span pre op).1 (span pre op).2 := by
  by_cases hc : op = .CALLDATACOPY
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨src, _ | ⟨len, tail⟩⟩⟩
    all_goals first | (cases hs; exact toNat_ofNat_lit _ (expansion_fit sh.activeWords off len)) | cases hs
  by_cases hm : op = .MSTORE
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨value, tail⟩⟩
    all_goals first | (cases hs; exact toNat_ofNat_lit _ (expansion_fit_nat sh.activeWords.toNat off.toNat 32 sh.activeWords.val.isLt off.val.isLt (by decide +kernel))) | cases hs
  by_cases hm8 : op = .MSTORE8
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨value, tail⟩⟩
    all_goals first | (cases hs; exact toNat_ofNat_lit _ (expansion_fit_nat sh.activeWords.toNat off.toNat 1 sh.activeWords.val.isLt off.val.isLt (by decide +kernel))) | cases hs
  by_cases hl : op = .LOG0
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    all_goals first | (cases hs; exact toNat_ofNat_lit _ (expansion_fit sh.activeWords off len)) | cases hs
  by_cases hr : op = .RETURN
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    all_goals first | (cases hs; exact toNat_ofNat_lit _ (expansion_fit sh.activeWords off len)) | cases hs
  by_cases hv : op = .REVERT
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    · cases hs
    · cases hs
    · cases hs
      have h₁ := toNat_ofNat_lit _ (expansion_fit sh.activeWords off len)
      have h₂ := toNat_ofNat_lit _ (expansion_fit
        (UInt256.ofNat (MachineState.M sh.activeWords.toNat off.toNat len.toNat)) off len)
      change (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M sh.activeWords.toNat off.toNat len.toNat)).toNat
        off.toNat len.toNat)).toNat = _
      rw [h₂,h₁]
      exact expansion_idempotent _ _ _
  obtain ⟨he,hspan⟩ := raw_fixed hop hc hm hm8 hl hr hv hs
  simp only [he,hspan,MachineState.M]

/-- Actual charged-dispatch metadata, with the same decoded operands. -/
theorem accepted_expansion {image : Image} {pre mid post : EVM.State}
    {fuel gasCost : Nat} {vj : Array UInt256} (hat : At image pre)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : EVM.step fuel gasCost (some (decodeAt pre)) mid = .ok post) :
    post.activeWords.toNat = MachineState.M pre.activeWords.toNat
      (span pre (decodeAt pre).1).1 (span pre (decodeAt pre).1).2 := by
  have hop := opcode_allowed hat
  have ho := allowed_excludes _ hop
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    rw [OrdinaryGas.dispatch ⟨ho.2.1,ho.2.2.1⟩] at hs
    have he := raw_expansion hop hs
    rw [Z_ok_state hz] at he
    exact he

/-- Every summand is attached to an actual edge and its intermediate state. -/
inductive TraceCharges (vj : Array UInt256) :
    Nat → EVM.State → List Labelled → Nat → EVM.State → Nat → Prop where
  | refl (fuel : Nat) (pre : EVM.State) : TraceCharges vj fuel pre [] fuel pre 0
  | cons {fuel gasCost rem total : Nat} {pre mid post : EVM.State} {trace : List Labelled}
      (step : XStepAt vj fuel gasCost pre mid)
      (tail : TraceCharges vj fuel mid trace rem post total) :
      TraceCharges vj (fuel+1) pre ((fuel,gasCost,decodeAt pre)::trace) rem post
        ((cost mid.activeWords.toNat - cost pre.activeWords.toNat) + total)

theorem TraceCharges.erase {vj : Array UInt256} {fuel rem total : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (h : TraceCharges vj fuel pre trace rem post total) :
    XRuns vj fuel pre trace rem post := by
  induction h with
  | refl => exact .refl _ _
  | cons step _ ih => exact .cons step ih

/-- Even the annotation itself requires only the actual run. -/
theorem of_runs {vj : Array UInt256} {fuel rem : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (hr : XRuns vj fuel pre trace rem post) :
    ∃ total, TraceCharges vj fuel pre trace rem post total := by
  induction hr with
  | refl => exact ⟨0,.refl _ _⟩
  | cons step _ ih =>
    obtain ⟨total,ht⟩ := ih
    exact ⟨_,.cons step ht⟩

/-- Actual accepted runtime steps justify subtraction without truncation. -/
theorem TraceCharges.telescopes {image : Image} {fuel rem total : Nat}
    {pre post : EVM.State} {trace : List Labelled} (hat : At image pre)
    (hc : TraceCharges (D_J image.code ⟨0⟩) fuel pre trace rem post total) :
    total + cost pre.activeWords.toNat = cost post.activeWords.toNat := by
  revert hat
  induction hc with
  | refl => intro _; simp
  | cons step _ ih =>
    intro hat
    obtain ⟨mid,hz,hs,hh⟩ := step
    have hnext := accepted_next hat hz hs hh
    have hcost := cost_mono (RuntimeMemoryMonotone.accepted hat hz hs).1
    have hend := ih hnext
    omega

/-- The public producer takes no independently supplied charge history. -/
theorem from_runs {image : Image} {fuel rem : Nat}
    {pre post : EVM.State} {trace : List Labelled} (hat : At image pre)
    (hr : XRuns (D_J image.code ⟨0⟩) fuel pre trace rem post) :
    ∃ total, TraceCharges (D_J image.code ⟨0⟩) fuel pre trace rem post total ∧
      total + cost pre.activeWords.toNat = cost post.activeWords.toNat := by
  obtain ⟨total,hc⟩ := of_runs hr
  exact ⟨total,hc,hc.telescopes hat⟩

/-- Any finite run: the final capacity bounds the entire memory-cost sum. -/
theorem bounded_from_runs {image : Image} {fuel rem cap : Nat}
    {pre post : EVM.State} {trace : List Labelled} (hat : At image pre)
    (hr : XRuns (D_J image.code ⟨0⟩) fuel pre trace rem post)
    (hcap : post.activeWords.toNat ≤ cap) :
    ∃ total, TraceCharges (D_J image.code ⟨0⟩) fuel pre trace rem post total ∧
      total + cost pre.activeWords.toNat = cost post.activeWords.toNat ∧
      total ≤ cost cap - cost pre.activeWords.toNat ∧ total ≤ cost cap := by
  obtain ⟨total,hc,he⟩ := from_runs hat hr
  have hb := cost_mono hcap
  exact ⟨total,hc,he,by omega,by omega⟩

/-- Actual terminal RETURN updates M using its actual popped operands. -/
theorem return_expansion {vj : Array UInt256} {pre mid post : EVM.State}
    {fuel gasCost : Nat} {rest : Stack UInt256} {off len : UInt256}
    (hz : Z vj .RETURN pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.RETURN,none) mid post)
    (operands : pre.stack.pop2 = some (rest,off,len)) :
    post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat := by
  obtain rfl := Z_ok_state hz
  have known := EvmYul.EVM.Proof.step_RETURN fuel gasCost (zMid pre .RETURN) rest off len operands
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  exact toNat_ofNat_lit _ (RuntimeMemoryMonotone.expansion_fit pre.activeWords off len)

/-- The terminal's operand bound comes from the same SYSTEM RETURN witness. -/
theorem return_capacity {vj : Array UInt256} {pre mid post : EVM.State}
    {fuel gasCost cap : Nat} {rest : Stack UInt256} {off len : UInt256}
    (hz : Z vj .RETURN pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.RETURN,none) mid post)
    (operands : pre.stack.pop2 = some (rest,off,len))
    (active : pre.activeWords.toNat ≤ cap)
    (span : len.toNat = 0 ∨ off.toNat + len.toNat ≤ 32*cap) :
    pre.activeWords.toNat ≤ post.activeWords.toNat ∧ post.activeWords.toNat ≤ cap := by
  rw [return_expansion hz hs operands]
  exact ⟨(ReferenceMemoryCapacity.expansion_bounds _ _ _).1,
    ReferenceMemoryCapacity.expansion_le _ _ _ cap active span⟩

#print axioms raw_expansion
#print axioms accepted_expansion
#print axioms of_runs
#print axioms TraceCharges.telescopes
#print axioms from_runs
#print axioms bounded_from_runs
#print axioms return_expansion
#print axioms return_capacity
end Eip8282.Audit.Integrator.RuntimeMemoryCharges
