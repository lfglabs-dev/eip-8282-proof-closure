import Eip8282.Audit.Integrator.RuntimeMemoryCharges
import Eip8282.Audit.Integrator.OrdinaryGas

/-! Initial evaluator gas plus already-paid memory potential funds actual
runtime memory growth. No selected protocol gas cap or predicted post-capacity
is assumed. This binds the pinned evaluator's literal memory charge to its
actual metadata; reference source grants and checked interpretation stay separate.
-/
namespace Eip8282.Audit.Integrator.RuntimeMemoryFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeMemoryMonotone RuntimeOpcodeScope
open ReferenceMemoryCapacity (cost cost_mono)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def energy (s : EVM.State) : Nat := s.gasAvailable.toNat + cost s.activeWords.toNat

private theorem predicted (pre : EVM.State) (op : Operation .EVM) (hop : op ∈ allowedOps) :
    (memoryExpansionCost.μᵢ' pre op).toNat =
      MachineState.M pre.activeWords.toNat (span pre op).1 (span pre op).2 := by
  simp only [allowedOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[1]!)
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[2]!)
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 32 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 1 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))

/-- Literal Z memory charge equals the actual step's memory potential change. -/
theorem expansion_cost {image : Image} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk fuel gasCost (decodeAt pre) mid post) :
    memoryExpansionCost pre (decodeAt pre).1 = cost post.activeWords.toNat - cost pre.activeWords.toNat := by
  have hm := RuntimeMemoryCharges.accepted_expansion hat hz hs
  have hp := predicted pre (decodeAt pre).1 (opcode_allowed hat)
  change cost (memoryExpansionCost.μᵢ' pre (decodeAt pre).1).toNat - cost pre.activeWords.toNat = _
  rw [hp,hm]

theorem accepted_energy {image : Image} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk fuel gasCost (decodeAt pre) mid post) : energy post ≤ energy pre := by
  have he := allowed_excludes _ (opcode_allowed hat)
  have hd := OrdinaryGas.accepted_step_debit ⟨he.2.1,he.2.2.1⟩ hz hs
  rw [expansion_cost hat hz hs] at hd
  have hm := cost_mono (RuntimeMemoryMonotone.accepted hat hz hs).1
  unfold energy
  omega

theorem runs_energy {image : Image} {pre post : EVM.State} {fuel rem : Nat} {trace : List Labelled}
    (hat : At image pre) (hr : XRuns (D_J image.code ⟨0⟩) fuel pre trace rem post) :
    energy post ≤ energy pre := by
  revert hat
  induction hr with
  | refl => intro hat; exact Nat.le_refl _
  | cons step tail ih =>
    intro hat
    obtain ⟨mid,hz,hs,hh⟩ := step
    exact (ih (accepted_next hat hz hs hh)).trans (accepted_energy hat hz hs)

/-- A strict initial potential threshold yields a capacity, not a post-cap premise. -/
theorem capacity_of_energy {post : EVM.State} {initialEnergy cap : Nat}
    (bound : cost post.activeWords.toNat ≤ initialEnergy)
    (threshold : initialEnergy < cost (cap+1)) : post.activeWords.toNat ≤ cap := by
  by_contra h
  have hm := cost_mono (show cap+1 ≤ post.activeWords.toNat by omega)
  omega

theorem runs_capacity {image : Image} {pre post : EVM.State} {fuel rem cap : Nat}
    {trace : List Labelled} (hat : At image pre)
    (hr : XRuns (D_J image.code ⟨0⟩) fuel pre trace rem post)
    (threshold : energy pre < cost (cap+1)) : post.activeWords.toNat ≤ cap := by
  apply capacity_of_energy (initialEnergy := energy pre) _ threshold
  have he := runs_energy hat hr
  unfold energy at he ⊢
  omega

#print axioms expansion_cost
#print axioms accepted_energy
#print axioms runs_energy
#print axioms capacity_of_energy
#print axioms runs_capacity
end Eip8282.Audit.Integrator.RuntimeMemoryFunding
