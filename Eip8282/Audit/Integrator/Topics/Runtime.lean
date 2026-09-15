import Eip8282.Audit.Integrator.OrdinaryGas
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.RuntimeMemoryCharges
import Eip8282.Audit.Integrator.SuccessInversion

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## RuntimeMemoryFunding -/

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

end

section

/-! ## RuntimeRevertTrace -/

/-! Recover the exact internal REVERT path from the actual finite evaluator.
The returned result hides the terminal world; this producer recovers its actual
state and accepted step without assuming a trace, resources or postcondition.
Wrapper rollback and source interpretation are separate consumers. -/
namespace Eip8282.Audit.Integrator.RuntimeRevertTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem revert_step {fuel : Nat} {vj : Array UInt256} {pre : EVM.State} {gas : UInt256}
    {out : ByteArray} (h : X fuel vj pre = .ok (.revert gas out)) :
    ∃ (rest cost : Nat) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (mid post : EVM.State),
      fuel = rest + 1 ∧ decodeAt pre = (op, arg) ∧
      Z vj op pre = .ok (mid, cost) ∧ StepOk rest cost (op, arg) mid post ∧
      ((H post.toMachineState op = none ∧ X rest vj post = .ok (.revert gas out)) ∨
       (H post.toMachineState op = some out ∧ op = .REVERT ∧ post.gasAvailable = gas)) := by
  cases fuel with
  | zero => simp only [X_zero] at h; contradiction
  | succ rest =>
      rcases hdec : decodeAt pre with ⟨op, arg⟩
      cases hz : Z vj op pre with
      | error err =>
          rw [X_succ_of_Z_error hdec hz] at h
          contradiction
      | ok charged =>
          obtain ⟨mid, cost⟩ := charged
          cases hs : EvmYul.EVM.step rest cost (some (op, arg)) mid with
          | error err =>
              rw [X_succ_of_step_error hdec hz hs] at h
              contradiction
          | ok post =>
              refine ⟨rest, cost, op, arg, mid, post, rfl, rfl, hz, hs, ?_⟩
              cases hh : H post.toMachineState op with
              | none =>
                  exact Or.inl ⟨rfl, (X_succ_of_continue hdec hz hs hh).symm.trans h⟩
              | some data =>
                  by_cases hr : op = .REVERT
                  · rw [X_succ_of_revert hdec hz hs hh hr] at h
                    have heq := Except.ok.inj h
                    cases heq
                    exact Or.inr ⟨rfl, hr, rfl⟩
                  · rw [X_succ_of_halt hdec hz hs hh hr] at h
                    cases h

structure RevertTrace (vj : Array UInt256) (fuel : Nat)
    (pre : EVM.State) (gas : UInt256) (out : ByteArray) where
  rem : Nat
  cost : Nat
  trace : List Labelled
  exit : EVM.State
  mid : EVM.State
  post : EVM.State
  run : XRuns vj fuel pre trace (rem+1) exit
  decode : decodeAt exit = (.REVERT,none)
  charge : Z vj .REVERT exit = .ok (mid,cost)
  step : StepOk rem cost (.REVERT,none) mid post
  output : H post.toMachineState .REVERT = some out
  gas_eq : post.gasAvailable = gas

/-- Arbitrary actual evaluator REVERT produces its same finite prefix and
literal accepted REVERT terminal. No caller-supplied trace or terminal state. -/
theorem revert_trace {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {gas : UInt256} {out : ByteArray} (h : X fuel vj pre = .ok (.revert gas out)) :
    Nonempty (RevertTrace vj fuel pre gas out) := by
  induction fuel generalizing pre with
  | zero => simp only [X_zero] at h; contradiction
  | succ fuel ih =>
    obtain ⟨rest,cost,op,arg,mid,post,hf,hd,hz,hs,hcase⟩ := revert_step h
    have he : rest = fuel := by omega
    subst rest
    rcases hcase with ⟨hh,htail⟩ | ⟨hh,hop,hgas⟩
    · obtain ⟨t⟩ := ih htail
      have hstep : XStepAt vj fuel cost pre post :=
        ⟨mid,by simpa only [hd] using hz,by simpa only [hd] using hs,
          by simpa only [hd] using hh⟩
      exact ⟨{
        rem := t.rem
        cost := t.cost
        trace := (fuel,cost,decodeAt pre)::t.trace
        exit := t.exit
        mid := t.mid
        post := t.post
        run := .cons hstep t.run
        decode := t.decode
        charge := t.charge
        step := t.step
        output := t.output
        gas_eq := t.gas_eq}⟩
    · subst op
      have hfixed := ReferenceDecodeShape.fixed pre .REVERT (congrArg Prod.fst hd) rfl
      have heq := hd.symm.trans hfixed
      have harg : arg = none := congrArg Prod.snd heq
      subst arg
      exact ⟨{
        rem := fuel
        cost := cost
        trace := []
        exit := pre
        mid := mid
        post := post
        run := .refl _ _
        decode := hd
        charge := hz
        step := hs
        output := hh
        gas_eq := hgas}⟩

#print axioms revert_step
#print axioms revert_trace
end Eip8282.Audit.Integrator.RuntimeRevertTrace

end
