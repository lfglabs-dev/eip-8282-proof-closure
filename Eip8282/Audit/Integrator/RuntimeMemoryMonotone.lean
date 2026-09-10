import Eip8282.Audit.Integrator.RuntimeExecutionScope
import Eip8282.Audit.Integrator.ReferenceMemoryCapacity

/-! Actual pinned-runtime memory high-water marks. The conversion of M to a
word cannot wrap for word-sized operands, without any assumed memory cap.
Physical host allocation and reference-interpreter correspondence are separate.
XRuns contains nonhalting edges; `accepted` also includes RETURN and REVERT. -/
namespace Eip8282.Audit.Integrator.RuntimeMemoryMonotone
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Actual memory operands; a zero length performs no memory access. -/
def span (pre : EVM.State) (op : Operation .EVM) : Nat × Nat :=
  match op with
  | .CALLDATACOPY => (pre.stack[0]!.toNat, pre.stack[2]!.toNat)
  | .MSTORE => (pre.stack[0]!.toNat, 32)
  | .MSTORE8 => (pre.stack[0]!.toNat, 1)
  | .LOG0 | .RETURN | .REVERT => (pre.stack[0]!.toNat, pre.stack[1]!.toNat)
  | _ => (0, 0)

theorem expansion_fit_nat (aw off len : Nat)
    (ha : aw < UInt256.size) (ho : off < UInt256.size) (hl : len < UInt256.size) :
    MachineState.M aw off len < UInt256.size := by
  have hsize : 32 ≤ UInt256.size := by decide +kernel
  cases len with
  | zero => exact ha
  | succ len => simp only [MachineState.M]; omega

theorem expansion_fit (aw off len : UInt256) :
    MachineState.M aw.toNat off.toNat len.toNat < UInt256.size :=
  expansion_fit_nat _ _ _ aw.val.isLt off.val.isLt len.val.isLt

/-- Both conclusions concern the actual word conversion, not unbounded M. -/
theorem expansion (aw off : UInt256) (len : Nat) (hl : len < UInt256.size) :
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len)).toNat ∧
    (0 < len → off.toNat + len ≤
      32 * (UInt256.ofNat (MachineState.M aw.toNat off.toNat len)).toNat) := by
  rw [toNat_ofNat_lit _ (expansion_fit_nat aw.toNat off.toNat len aw.val.isLt off.val.isLt hl)]
  exact ReferenceMemoryCapacity.expansion_bounds _ _ _

def Bounds (pre post : EVM.State) (op : Operation .EVM) : Prop :=
  pre.activeWords.toNat ≤ post.activeWords.toNat ∧
  (0 < (span pre op).2 → (span pre op).1 + (span pre op).2 ≤ 32*post.activeWords.toNat)

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

/-- Literal raw instruction metadata, including terminal operations. -/
theorem raw_bounds {op : Operation .EVM} (hop : op ∈ allowedOps)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (hs : EvmYul.step op arg pre = .ok post) : Bounds pre post op := by
  by_cases hc : op = .CALLDATACOPY
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨src, _ | ⟨len, tail⟩⟩⟩
    all_goals first | (cases hs; exact expansion sh.activeWords off len.toNat len.val.isLt) | cases hs
  by_cases hm : op = .MSTORE
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨value, tail⟩⟩
    all_goals first | (cases hs; exact expansion sh.activeWords off 32 (by decide +kernel)) | cases hs
  by_cases hm8 : op = .MSTORE8
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨value, tail⟩⟩
    all_goals first | (cases hs; exact expansion sh.activeWords off 1 (by decide +kernel)) | cases hs
  by_cases hl : op = .LOG0
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    all_goals first | (cases hs; exact expansion sh.activeWords off len.toNat len.val.isLt) | cases hs
  by_cases hr : op = .RETURN
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    all_goals first | (cases hs; exact expansion sh.activeWords off len.toNat len.val.isLt) | cases hs
  by_cases hv : op = .REVERT
  · subst op
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases stk with _ | ⟨off, _ | ⟨len, tail⟩⟩
    · cases hs
    · cases hs
    · cases hs
      have h₁ := expansion sh.activeWords off len.toNat len.val.isLt
      have h₂ := expansion (UInt256.ofNat (MachineState.M sh.activeWords.toNat off.toNat len.toNat))
        off len.toNat len.val.isLt
      exact ⟨h₁.1.trans h₂.1, h₂.2⟩
  obtain ⟨he,hspan⟩ := raw_fixed hop hc hm hm8 hl hr hv hs
  simp only [Bounds, he, hspan, Nat.lt_irrefl, false_implies, and_true, le_refl]

/-- Actual Z plus dispatcher; no assumed capacity or access bound. -/
theorem accepted {image : Image} {pre mid post : EVM.State}
    {fuel cost : Nat} {vj : Array UInt256} (hat : At image pre)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : EVM.step fuel cost (some (decodeAt pre)) mid = .ok post) :
    Bounds pre post (decodeAt pre).1 := by
  have hop := opcode_allowed hat
  have ho := allowed_excludes _ hop
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    rw [OrdinaryGas.dispatch ⟨ho.2.1,ho.2.2.1⟩] at hs
    have hb := raw_bounds hop hs
    rw [Z_ok_state hz] at hb
    exact hb

/-- The same actual nonhalting run transports both code sites and capacity. -/
theorem runs {image : Image} {fuel rem : Nat} {pre post : EVM.State}
    {trace : List Labelled} (hat : At image pre)
    (hr : XRuns (D_J image.code ⟨0⟩) fuel pre trace rem post) :
    At image post ∧ pre.activeWords.toNat ≤ post.activeWords.toNat := by
  revert hat
  induction hr with
  | refl => intro hat; exact ⟨hat, Nat.le_refl _⟩
  | cons step tail ih =>
    intro hat
    obtain ⟨mid,hz,hs,hh⟩ := step
    have hn := accepted_next hat hz hs hh
    have hb := accepted hat hz hs
    have ht := ih hn
    exact ⟨ht.1,hb.1.trans ht.2⟩

/-- A real prefix, edge, and suffix expose an arbitrary intermediate access.
Only the final state's capacity is bounded. -/
theorem suffix_bounds {image : Image} {fuel edgeFuel cost rem : Nat}
    {start pre post finish : EVM.State} {beforeTrace afterTrace : List Labelled} {cap : Nat}
    (hat : At image start)
    (hp : XRuns (D_J image.code ⟨0⟩) fuel start beforeTrace (edgeFuel+1) pre)
    (he : XStepAt (D_J image.code ⟨0⟩) edgeFuel cost pre post)
    (ht : XRuns (D_J image.code ⟨0⟩) edgeFuel post afterTrace rem finish)
    (hcap : finish.activeWords.toNat ≤ cap) :
    pre.activeWords.toNat ≤ cap ∧ post.activeWords.toNat ≤ cap ∧
    (0 < (span pre (decodeAt pre).1).2 →
      (span pre (decodeAt pre).1).1 + (span pre (decodeAt pre).1).2 ≤ 32*cap) := by
  have hpre := (runs hat hp).1
  obtain ⟨mid,hz,hs,hh⟩ := he
  have hb := accepted hpre hz hs
  have hpost := accepted_next hpre hz hs hh
  have hend := (runs hpost ht).2.trans hcap
  refine ⟨hb.1.trans hend,hend,fun hpos => ?_⟩
  exact (hb.2 hpos).trans (Nat.mul_le_mul_left 32 hend)

#print axioms expansion_fit
#print axioms raw_bounds
#print axioms accepted
#print axioms runs
#print axioms suffix_bounds
end Eip8282.Audit.Integrator.RuntimeMemoryMonotone
