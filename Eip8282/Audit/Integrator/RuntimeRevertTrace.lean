import Eip8282.Audit.Integrator.SuccessInversion
import Eip8282.Audit.Integrator.ReferenceDecodeShape

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
