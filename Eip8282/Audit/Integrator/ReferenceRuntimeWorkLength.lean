import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
import Eip8282.Audit.Integrator.ReferenceExecutionLedger

/-! Every paid protected nonterminal action consumes positive execution work.
This derives an instruction-count bound and rules out an infinite sequence of
paid running steps, even when state credits increase the execution pool itself.
Potential includes outstanding/committed spill; terminal/failure handling and
extraction from an actual source evaluator remain distinct obligations. No fee
iteration ceiling, success assumption or net-state sign assumption is added. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeReadings ReferenceSourceReadings
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceExecutionLedger ReferenceExecutionPotential
open ReferenceMeterPath
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem nonterminal {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) :
    instr.1 ≠ .STOP ∧ instr.1 ≠ .RETURN ∧ instr.1 ≠ .REVERT := by
  cases effect with
  | copy => decide
  | log => decide
  | base effect =>
    cases effect with
    | pure actual =>
      have excluded : ∀ op, (op = Operation.STOP ∨ op = .RETURN ∨ op = .REVERT) → instr.1 ≠ op := by
        intro op halt eq
        unfold ReferencePureAction.action at actual
        rw [eq] at actual
        rcases halt with rfl | rfl | rfl <;> simp [ReferencePureAction.classify] at actual
      exact ⟨excluded _ (Or.inl rfl),excluded _ (Or.inr (Or.inl rfl)),excluded _ (Or.inr (Or.inr rfl))⟩
    | load => decide
    | store => decide
    | word => decide
    | byte => decide

private theorem ordinary_positive {op : Operation .EVM} {warm : Bool} {stack : Stack UInt256} {n : Nat}
    (stop : op ≠ .STOP) (returned : op ≠ .RETURN) (reverted : op ≠ .REVERT)
    (cost : ReferenceCopyLogGas.ordinaryCost op warm stack = some n) : 1 ≤ n := by
  cases op <;> simp_all [ReferenceCopyLogGas.ordinaryCost,ReferenceOrdinaryGas.ordinaryCost,
    ReferenceCopyLogGas.copyCost,ReferenceCopyLogGas.logCost]
  all_goals rename_i subop
  all_goals cases subop <;> cases warm <;> simp_all
  all_goals omega

/-- The positive base charge is derived from the same literal action/price. -/
theorem positive {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View} {warm : Warm} {event : Event}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next)
    (price : Price parent v warm next instr.1 event) : 1 ≤ eventWork event := by
  have nt := nonterminal effect
  unfold Price at price
  split at price
  · obtain ⟨_,rfl⟩ := price
    simp only [eventWork,ReferenceStorageGas.classify]
    split <;> omega
  · obtain ⟨n,cost,rfl⟩ := price
    have hn := ordinary_positive nt.1 nt.2.1 nt.2.2 cost
    change 1 ≤ n+_
    omega

/-- Arbitrarily many finite iterations are allowed, but each running event
counts once and costs at least one unit of execution work. -/
theorem length_le_work {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run kind parent v warm finish finalWarm events) :
    events.length ≤ work events := by
  induction source with
  | refl => simp [work]
  | cons effect price stack tail ih =>
    have hp := positive effect price
    simp only [List.length_cons,work,List.map_cons,List.sum_cons] at ih ⊢
    omega

/-- A paid finite running prefix cannot exceed its entry potential. -/
theorem paid_length {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {events : List Event} {pre post : Meter}
    (source : ReferenceSourceReplayTrace.Run kind parent v warm finish finalWarm events)
    (paid : runFull events pre = some post) : potential post+events.length ≤ potential pre := by
  have hl := length_le_work source
  have hw := ReferenceExecutionLedger.bounded (.paid events paid)
  omega

/-- Infinite paid nonterminal execution is impossible. This does not assert
that a particular source call succeeds: a source evaluator must still connect
its next step or terminal/exception case to these literal operations. -/
theorem no_infinite_paid (kind : Kind) (parent : ReferenceStorageView.Parent)
    (views : Nat → View) (warms : Nat → Warm) (meters : Nat → Meter) (events : Nat → Event)
    (effect : ∀ n, ReferenceRuntimeAction.Action kind parent
      (ReferenceSourceReplayTrace.instruction (views n)) (views n) (views (n+1)))
    (price : ∀ n, Price parent (views n) (warms n) (views (n+1))
      (ReferenceSourceReplayTrace.instruction (views n)).1 (events n))
    (paid : ∀ n, runFull [events n] (meters n) = some (meters (n+1))) : False := by
  have bound : ∀ n, potential (meters n)+n ≤ potential (meters 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hp := positive (effect n) (price n)
      have hw := ReferenceExecutionLedger.bounded (.paid [events n] (paid n))
      simp only [work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hw
      omega
  have impossible := bound (potential (meters 0)+1)
  omega

#print axioms positive
#print axioms length_le_work
#print axioms paid_length
#print axioms no_infinite_paid
end Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength
