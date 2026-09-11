import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Resource-bounded evaluator for the audited protected source dispatcher.
The computational fuel is not EVM gas: none explicitly means proof evaluator
budget exhaustion. From bounded stack/aligned memory and a fixed destination
context, initial execution potential+1 suffices, without any fixed loop cap.
A terminal/failure/EOF/unsupported result retains its exact final local outcome.
Executed successful running steps are extracted once in order; a failed handler
is kept separately with its partial effects and meter. No committed append is
inferred from an attempted log or a locally successful prefix.
Actual source frame/account lookup, op implementation refinement, exception
settlement and outer journal/history bindings remain separate producers. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
open ReferenceActionMemoryBounds (Aligned)
open ReferenceExecutionPotential (potential)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- A local stopped evaluation includes failures and explicitly unsupported
valid opcodes. Neither is mistaken for a successful committed call. -/
def Ended : Outcome → Prop
  | .continued .. => False
  | _ => True

noncomputable def eval (destinations : List Nat) (ownerExists : Bool)
    (parent : ReferenceStorageView.Parent) (output : ByteArray) :
    Nat → View → Warm → Meter → Option (List Event × Outcome)
  | 0,_,_,_ => none
  | fuel+1,v,warm,meter =>
    match run destinations ownerExists parent v warm meter output with
    | .continued next nextWarm nextMeter event =>
      (eval destinations ownerExists parent output fuel next nextWarm nextMeter).map
        (fun (events,result) => (event::events,result))
    | result => some ([],result)

/-- Every evaluated running step supplies the existing Step relation, and the
last outcome is the exact dispatcher result at the same final state/meter. -/
theorem extract {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : eval destinations ownerExists parent output fuel v warm meter = some (events,result)) :
    ∃ finish finalWarm final,
      ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
      run destinations ownerExists parent finish finalWarm final output = result ∧ Ended result := by
  induction fuel generalizing v warm meter events result with
  | zero => simp only [eval] at actual; contradiction
  | succ fuel ih =>
    simp only [eval] at actual
    cases hd : run destinations ownerExists parent v warm meter output with
    | continued next nextWarm nextMeter event =>
      simp only [hd] at actual
      obtain ⟨pair,tail,same⟩ := Option.map_eq_some_iff.mp actual
      rcases pair with ⟨tailEvents,tailResult⟩
      cases same
      obtain ⟨finish,finalWarm,final,trace,last,ended⟩ := ih tail
      exact ⟨finish,finalWarm,final,.cons (ReferenceCheckedDispatch.step context hd) trace,last,ended⟩
    | terminal terminal =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact ⟨v,warm,meter,.refl _ _ _,hd,True.intro⟩
    | eof last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact ⟨v,warm,meter,.refl _ _ _,hd,True.intro⟩
    | failed error last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact ⟨v,warm,meter,.refl _ _ _,hd,True.intro⟩
    | unsupported tag last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact ⟨v,warm,meter,.refl _ _ _,hd,True.intro⟩

/-- At least one unit of execution potential is spent by every successfully
executed running instruction, including when state credits replenish gas. -/
theorem progress {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {v next : View} {warm nextWarm : Warm} {meter nextMeter : Meter} {event : Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v)
    (actual : run destinations ownerExists parent v warm meter output = .continued next nextWarm nextMeter event) :
    next.stack.length ≤ 1024 ∧ Aligned next ∧ potential nextMeter+1 ≤ potential meter := by
  have step := ReferenceCheckedDispatch.step context actual
  obtain ⟨action,_,_,_,stack⟩ := step.sound initial aligned
  have one : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter next nextWarm nextMeter [event] :=
    .cons step (.refl _ _ _)
  exact ⟨stack,ReferenceActionMemoryBounds.preserves_alignment action aligned,
    by simpa only [List.length_singleton] using one.length_bound initial aligned⟩

/-- No artificial finite iteration cap. Evaluator budget is derived from this
same source meter, separately from success, exception and rollback. -/
theorem sufficient {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {meter : Meter}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v) (budget : potential meter < fuel) :
    eval destinations ownerExists parent output fuel v warm meter ≠ none := by
  induction fuel generalizing v warm meter with
  | zero => omega
  | succ fuel ih =>
    simp only [eval]
    cases hd : run destinations ownerExists parent v warm meter output with
    | continued next nextWarm nextMeter event =>
      obtain ⟨stack,alignment,spent⟩ := progress context initial aligned hd
      have enough := ih (warm := nextWarm) (meter := nextMeter) stack alignment (by omega)
      cases tail : eval destinations ownerExists parent output fuel next nextWarm nextMeter with
      | none => exact False.elim (enough tail)
      | some pair => simpa using enough
    | terminal terminal => simp
    | eof last lastWarm lastMeter lastOutput => simp
    | failed error last lastWarm lastMeter lastOutput => simp
    | unsupported tag last lastWarm lastMeter lastOutput => simp

/-- Compute a complete local result with gas-derived evaluation budget and
produce its same trace. Failure/EOF/unsupported remain explicit outcomes. -/
theorem completes {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {v : View} {warm : Warm} {meter : Meter}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v) :
    ∃ events result finish finalWarm final,
      eval destinations ownerExists parent output (potential meter+1) v warm meter = some (events,result) ∧
      ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
      run destinations ownerExists parent finish finalWarm final output = result ∧ Ended result := by
  have enough := sufficient (ownerExists := ownerExists) (parent := parent) (warm := warm) (output := output) context initial aligned (Nat.lt_succ_self (potential meter))
  cases he : eval destinations ownerExists parent output (potential meter+1) v warm meter with
  | none => exact False.elim (enough he)
  | some pair =>
    rcases pair with ⟨events,result⟩
    obtain ⟨finish,finalWarm,final,trace,last,ended⟩ := extract context he
    exact ⟨events,result,finish,finalWarm,final,rfl,trace,last,ended⟩

#print axioms extract
#print axioms progress
#print axioms sufficient
#print axioms completes
end Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
