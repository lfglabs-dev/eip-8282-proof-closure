import Eip8282.Audit.Integrator.ReferenceStorageGas

/-! Arbitrary finite paths through the audited source-meter transcription.
Only aggregate INITIAL budgets are premises; each sentry and ordered payment
is derived. Store events are explicitly nonstatic, as required for SYSTEM.
Mapping an actual interpreter trace to these events remains a separate adapter;
this theorem alone does not assert reference execution or protocol progress. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterPath
open EvmYul ReferenceStorageGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

inductive Event where
  | ordinary (amount : Nat)
  | store (warm : Bool) (original current new : UInt256)
  deriving DecidableEq, Repr

def executionBudget : Event → Nat
  | .ordinary amount => amount
  | .store _ _ _ _ => 12100

def stateBudget : Event → Nat
  | .ordinary _ => 0
  | .store _ _ _ _ => 97920

def sumExec (events : List Event) : Nat := (events.map executionBudget).sum

def sumState (events : List Event) : Nat := (events.map stateBudget).sum

/-- Literal charge order, including the possibility of failure. -/
def pay (event : Event) (m : Meter) : Option Meter :=
  match event with
  | .ordinary amount => chargeExecution m amount
  | .store warm original current new => storageCharge false warm original current new m

def run : List Event → Meter → Option Meter
  | [], m => some m
  | event::events, m => (pay event m).bind (run events)

/-- The generic one-event lemma is internal evidence for the aggregate producer. -/
theorem pay_success (event : Event) (m : Meter)
    (he : executionBudget event ≤ m.execution)
    (hr : stateBudget event ≤ m.reservoir) :
    ∃ post, pay event m = some post ∧
      m.execution-executionBudget event ≤ post.execution ∧
      m.reservoir-stateBudget event ≤ post.reservoir := by
  cases event with
  | ordinary amount =>
    refine ⟨{m with execution := m.execution-amount},?_,?_,?_⟩
    · exact if_pos he
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  | store warm original current new =>
    exact conservative_success warm original current new m he hr

/-- Initial totals alone imply every payment succeeds in sequence. The lower
bounds do not spend future refunds in advance, and require no iteration cap. -/
theorem payment (events : List Event) (initial : Meter)
    (he : sumExec events ≤ initial.execution)
    (hr : sumState events ≤ initial.reservoir) :
    ∃ final, run events initial = some final ∧
      initial.execution-sumExec events ≤ final.execution ∧
      initial.reservoir-sumState events ≤ final.reservoir := by
  induction events generalizing initial with
  | nil => exact ⟨initial,rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons event events ih =>
    have hex : sumExec (event::events) = executionBudget event + sumExec events := rfl
    have hst : sumState (event::events) = stateBudget event + sumState events := rfl
    obtain ⟨middle,hm,hme,hmr⟩ := pay_success event initial (by omega) (by omega)
    obtain ⟨final,hf,hfe,hfr⟩ := ih middle (by omega) (by omega)
    refine ⟨final,?_,?_,?_⟩
    · simp only [run,hm,Option.bind_some,hf]
    · omega
    · omega

theorem budgets_append (xs ys : List Event) :
    sumExec (xs++ys) = sumExec xs+sumExec ys ∧
    sumState (xs++ys) = sumState xs+sumState ys := by
  simp [sumExec,sumState]

/-- Chunking a path preserves the literal sequential charge computation. -/
theorem run_append (xs ys : List Event) (m : Meter) :
    run (xs++ys) m = (run xs m).bind (run ys) := by
  induction xs generalizing m with
  | nil => rfl
  | cons event xs ih =>
    simp only [List.cons_append,run]
    cases hm : pay event m with
    | none => rfl
    | some middle => exact ih middle

#print axioms pay_success
#print axioms payment
#print axioms budgets_append
#print axioms run_append
end Eip8282.Audit.Integrator.ReferenceMeterPath
