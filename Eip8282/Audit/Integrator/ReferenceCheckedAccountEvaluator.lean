import Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch

/-! Account-aware execution of the protected checked dispatcher. Presence is
computed from the layered optional-account lookup at each instruction, never
supplied as an independent Bool. Successful steps preserve account writes and
the environment, so the same initial lookup determines the entire projection.
Account read metadata is threaded also through a terminal assertion failure.
This is a source-shaped local evaluator; concrete Python dictionaries, full
account fields, source frame creation and canonical histories remain external
refinement obligations. Computational exhaustion remains `none`, not REVERT.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceActionMemoryBounds (Aligned)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

noncomputable def eval {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (destinations : List Nat) (parent : ReferenceStorageView.Parent) (output : ByteArray) :
    Nat → ReferenceAccountLookup.Tx Account → View → Warm → Meter →
      Option ((List Event × Outcome) × ReferenceAccountLookup.Tx Account)
  | 0,_,_,_,_ => none
  | fuel+1,accounts,v,warm,meter =>
    let step := ReferenceCheckedAccountDispatch.run accountsParent accounts destinations parent v warm meter output
    match step.1 with
    | .continued next nextWarm nextMeter event =>
      (eval accountsParent destinations parent output fuel step.2 next nextWarm nextMeter).map
        (fun ((events,result),finalAccounts) => ((event::events,result),finalAccounts))
    | result => some (([],result),step.2)

/-- Erasure is the same computed checked evaluation for every finite fuel,
including computational exhaustion and every terminal/fault class. -/
theorem projection {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {kind : Kind} {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (fuel : Nat) (accounts : ReferenceAccountLookup.Tx Account) (v : View) (warm : Warm) (meter : Meter)
    (stack : v.stack.length ≤ 1024) (aligned : Aligned v) :
    (eval accountsParent destinations parent output fuel accounts v warm meter).map Prod.fst =
      ReferenceCheckedEvaluator.eval destinations
        (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent output fuel v warm meter := by
  induction fuel generalizing accounts v warm meter with
  | zero => rfl
  | succ fuel ih =>
    cases step : ReferenceCheckedAccountDispatch.run accountsParent accounts destinations parent v warm meter output with
    | mk result nextAccounts =>
      have checked := congrArg Prod.fst step
      rw [ReferenceCheckedAccountDispatch.result] at checked
      cases result with
      | continued next nextWarm nextMeter event =>
        obtain ⟨env,nextStack,nextAligned,same⟩ := ReferenceCheckedAccountDispatch.continued context step stack aligned
        have tail := ih nextAccounts next nextWarm nextMeter nextStack nextAligned
        rw [same] at tail
        simp only [eval,step,ReferenceCheckedEvaluator.eval,checked,Option.map_map]
        rw [← tail]
        cases eval accountsParent destinations parent output fuel nextAccounts next nextWarm nextMeter <;> rfl
      | terminal last => simp only [eval,step,ReferenceCheckedEvaluator.eval,checked,Option.map_some]
      | eof last lastWarm lastMeter lastOutput => simp only [eval,step,ReferenceCheckedEvaluator.eval,checked,Option.map_some]
      | failed error last lastWarm lastMeter lastOutput => simp only [eval,step,ReferenceCheckedEvaluator.eval,checked,Option.map_some]
      | unsupported tag last lastWarm lastMeter lastOutput => simp only [eval,step,ReferenceCheckedEvaluator.eval,checked,Option.map_some]

/-- Every completed local outcome keeps the original account write overlay.
Storage writes and account-read metadata are distinct and are not erased here. -/
theorem writes {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {fuel : Nat} {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    (actual : eval accountsParent destinations parent output fuel accounts v warm meter =
      some ((events,result),finalAccounts)) : finalAccounts.writes = accounts.writes := by
  induction fuel generalizing accounts v warm meter events result finalAccounts with
  | zero => simp only [eval] at actual; contradiction
  | succ fuel ih =>
    cases step : ReferenceCheckedAccountDispatch.run accountsParent accounts destinations parent v warm meter output with
    | mk outcome nextAccounts =>
      have same := ReferenceCheckedAccountDispatch.writes accountsParent accounts destinations parent v warm meter output
      rw [step] at same
      cases outcome with
      | continued next nextWarm nextMeter event =>
        simp only [eval,step] at actual
        obtain ⟨pair,tail,equality⟩ := Option.map_eq_some_iff.mp actual
        rcases pair with ⟨⟨tailEvents,tailResult⟩,tailAccounts⟩
        cases equality
        exact (ih tail).trans same
      | terminal last =>
        simp only [eval,step,Option.some.injEq] at actual
        cases actual
        exact same
      | eof last lastWarm lastMeter lastOutput =>
        simp only [eval,step,Option.some.injEq] at actual
        cases actual
        exact same
      | failed error last lastWarm lastMeter lastOutput =>
        simp only [eval,step,Option.some.injEq] at actual
        cases actual
        exact same
      | unsupported tag last lastWarm lastMeter lastOutput =>
        simp only [eval,step,Option.some.injEq] at actual
        cases actual
        exact same

/-- Same computed endpoint supplies the old checked consumer; the presence
Boolean is computed from a precise account lookup, never supplied separately. -/
theorem evaluated {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {kind : Kind} {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {fuel : Nat} {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : eval accountsParent destinations parent output fuel accounts v warm meter =
      some ((events,result),finalAccounts))
    (stack : v.stack.length ≤ 1024) (aligned : Aligned v) :
    ReferenceCheckedEvaluator.eval destinations
      (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent output fuel v warm meter =
      some (events,result) ∧ finalAccounts.writes = accounts.writes := by
  have h := projection (accountsParent := accountsParent) (parent := parent) (output := output) context fuel accounts v warm meter stack aligned
  rw [actual] at h
  exact ⟨h.symm,writes actual⟩

/-- Account-derived dispatch inherits the gas-potential computation bound.
This establishes completion as a local outcome, never successful EVM status. -/
theorem sufficient {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {kind : Kind} {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {fuel : Nat} {accounts : ReferenceAccountLookup.Tx Account}
    {v : View} {warm : Warm} {meter : Meter}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (stack : v.stack.length ≤ 1024) (aligned : Aligned v)
    (budget : ReferenceExecutionPotential.potential meter < fuel) :
    eval accountsParent destinations parent output fuel accounts v warm meter ≠ none := by
  intro absent
  have h := projection (accountsParent := accountsParent) (parent := parent) (output := output) context fuel accounts v warm meter stack aligned
  rw [absent] at h
  exact ReferenceCheckedEvaluator.sufficient context stack aligned budget h.symm

#print axioms projection
#print axioms writes
#print axioms evaluated
#print axioms sufficient
end Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator
