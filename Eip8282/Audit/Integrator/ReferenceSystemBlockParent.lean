import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator
import Eip8282.Audit.Integrator.ReferenceSystemBlockFootprint
import Eip8282.Audit.Integrator.ReferenceCheckedTheta

/-! Parent-overlay locality of the actual account-aware checked evaluator.
An earlier protected call can change a different account's block storage.
Every instruction of this evaluator observes only its fixed owner's slots;
the theorem preserves the complete result, including exact resource failures,
warmth, account reads and arbitrary finite computational exhaustion. Consumer:
the mandatory Exit execution after actual Deposit journal incorporation. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockParent
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch ReferenceStorageView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def AtOwner (p q : Parent) (owner : AccountAddress) : Prop :=
  ∀ key, parentRead p owner key = parentRead q owner key

private theorem current_eq {p q : Parent} {owner : AccountAddress}
    (same : AtOwner p q owner) (tx : Tx) (key : ByteArray) :
    current p tx owner key = current q tx owner key := by
  simp only [current,same key]

private theorem original_eq {p q : Parent} {owner : AccountAddress}
    (same : AtOwner p q owner) (tx : Tx) (key : ByteArray) :
    original p tx owner key = original q tx owner key := by
  classical
  simp only [original,same key]

private theorem reading_eq {p q : Parent} (v : View) (same : AtOwner p q v.env.codeOwner) (warm : Warm) :
    sourceReading p v warm = sourceReading q v warm := by
  simp only [sourceReading,current_eq same,original_eq same]

private theorem load_eq {p q : Parent} (v : View) (same : AtOwner p q v.env.codeOwner) (warm : Warm) (meter : Meter) :
    ReferenceCheckedStorageStep.load p v warm meter = ReferenceCheckedStorageStep.load q v warm meter := by
  simp only [ReferenceCheckedStorageStep.load,current_eq same]

private theorem store_eq {p q : Parent} (v : View) (same : AtOwner p q v.env.codeOwner)
    (ownerExists : Bool) (warm : Warm) (meter : Meter) :
    ReferenceCheckedStorageStep.store ownerExists p v warm meter = ReferenceCheckedStorageStep.store ownerExists q v warm meter := by
  simp only [ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,current_eq same,original_eq same]

private theorem step {p q : Parent} {kind : Kind} {v next : View} {warm nextWarm : Warm}
    {meter nextMeter : Meter} {event : Event} (same : AtOwner p q v.env.codeOwner)
    (actual : ReferenceCheckedRuntimeTrace.Step kind p v warm meter next nextWarm nextMeter event) :
    ReferenceCheckedRuntimeTrace.Step kind q v warm meter next nextWarm nextMeter event := by
  cases actual with
  | binary b decoded actual => exact .binary b decoded actual
  | environment h decoded actual => exact .environment h decoded actual
  | stackControl h destinations context decoded actual => exact .stackControl h destinations context decoded actual
  | memoryStore byte decoded actual => exact .memoryStore byte decoded actual
  | copyLog h decoded actual => exact .copyLog h decoded actual
  | load decoded actual =>
    rw [reading_eq v same warm]
    exact .load decoded ((load_eq v same warm meter).symm.trans actual)
  | store ownerExists decoded actual =>
    rw [reading_eq v same warm]
    exact .store ownerExists decoded ((store_eq v same ownerExists warm meter).symm.trans actual)

theorem trace {p q : Parent} {kind : Kind} {v finish : View} {warm finalWarm : Warm}
    {meter final : Meter} {events : List Event} (same : AtOwner p q v.env.codeOwner)
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v warm meter finish finalWarm final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ReferenceCheckedRuntimeTrace.Run kind q v warm meter finish finalWarm final events ∧ finish.env = v.env := by
  induction actual with
  | refl => exact ⟨.refl _ _ _,rfl⟩
  | cons edge tail ih =>
    obtain ⟨effect,_,_,_,nextStack⟩ := edge.sound stack aligned
    have env := ReferenceCheckedPrefix.action_env effect
    obtain ⟨nextTrace,finishEnv⟩ := ih (by simpa only [env] using same) nextStack
      (ReferenceActionMemoryBounds.preserves_alignment effect aligned)
    exact ⟨.cons (step same edge) nextTrace,finishEnv.trans env⟩

theorem handler {p q : Parent} (v : View) (same : AtOwner p q v.env.codeOwner)
    (h : Handler) (destinations : List Nat) (ownerExists : Bool)
    (warm : Warm) (meter : Meter) (output : ByteArray) :
    runHandler h destinations ownerExists p v warm meter output =
      runHandler h destinations ownerExists q v warm meter output := by
  cases h <;> try rfl
  all_goals
    simp only [runHandler,ReferenceCheckedStorageStep.load,ReferenceCheckedStorageStep.store,
      ReferenceCheckedStorageStep.storeAfterPop,current_eq same,original_eq same,
      sourceReading]
  all_goals rfl

theorem dispatch {p q : Parent} (v : View) (same : AtOwner p q v.env.codeOwner)
    (destinations : List Nat) (ownerExists : Bool) (warm : Warm) (meter : Meter) (output : ByteArray) :
    ReferenceCheckedDispatch.run destinations ownerExists p v warm meter output =
      ReferenceCheckedDispatch.run destinations ownerExists q v warm meter output := by
  unfold ReferenceCheckedDispatch.run
  cases read v.env.code v.pc <;> try rfl
  exact handler v same _ destinations ownerExists warm meter output

def CompletedRun (kind : Kind) (parent : Parent) (destinations : List Nat) (ownerExists : Bool)
    (v : View) (warm : Warm) (meter : Meter) (events : List Event)
    (ended : ReferenceCheckedTerminalStep.End) (finalWarm : Warm) : Prop :=
  ∃ finish final, ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
    ReferenceCheckedDispatch.run destinations ownerExists parent finish finalWarm final ByteArray.empty = .terminal ended

theorem completed_run {p q : Parent} {kind : Kind} {v : View} {warm finalWarm : Warm}
    {meter : Meter} {events : List Event} {ended : ReferenceCheckedTerminalStep.End}
    {destinations : List Nat} {ownerExists : Bool}
    (same : AtOwner p q v.env.codeOwner)
    (actual : CompletedRun kind p destinations ownerExists v warm meter events ended finalWarm)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    CompletedRun kind q destinations ownerExists v warm meter events ended finalWarm := by
  obtain ⟨finish,final,run,last⟩ := actual
  obtain ⟨nextTrace,env⟩ := trace same run stack aligned
  refine ⟨finish,final,nextTrace,?_⟩
  rw [←dispatch finish (by simpa only [env] using same)]
  exact last

theorem account_dispatch {Account : Type} {p q : Parent}
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (v : View) (same : AtOwner p q v.env.codeOwner)
    (destinations : List Nat) (warm : Warm) (meter : Meter) (output : ByteArray) :
    ReferenceCheckedAccountDispatch.run accountsParent accounts destinations p v warm meter output =
      ReferenceCheckedAccountDispatch.run accountsParent accounts destinations q v warm meter output := by
  unfold ReferenceCheckedAccountDispatch.run
  rw [dispatch v same]

/-- Same evaluator, not a separately related successful trace. The equality
includes both `none` (computational exhaustion) and all completed outcomes. -/
theorem evaluated {Account : Type} {p q : Parent} {kind : Kind}
    {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (accountsParent : ReferenceAccountLookup.Parent Account) (fuel : Nat)
    (accounts : ReferenceAccountLookup.Tx Account) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
    (same : AtOwner p q v.env.codeOwner)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ReferenceCheckedAccountEvaluator.eval accountsParent destinations p output fuel accounts v warm meter =
      ReferenceCheckedAccountEvaluator.eval accountsParent destinations q output fuel accounts v warm meter := by
  induction fuel generalizing accounts v warm meter with
  | zero => rfl
  | succ fuel ih =>
    have eq := account_dispatch accountsParent accounts v same destinations warm meter output
    cases step : ReferenceCheckedAccountDispatch.run accountsParent accounts destinations p v warm meter output with
    | mk result nextAccounts =>
      have other := eq.symm.trans step
      cases result with
      | continued next nextWarm nextMeter event =>
        obtain ⟨env,nextStack,nextAligned,_⟩ := ReferenceCheckedAccountDispatch.continued context step stack aligned
        have tail := ih nextAccounts next nextWarm nextMeter (by simpa only [env] using same) nextStack nextAligned
        simp only [ReferenceCheckedAccountEvaluator.eval,step,other,tail]
      | terminal ended => simp only [ReferenceCheckedAccountEvaluator.eval,step,other]
      | eof last lastWarm lastMeter lastOutput => simp only [ReferenceCheckedAccountEvaluator.eval,step,other]
      | failed error last lastWarm lastMeter lastOutput => simp only [ReferenceCheckedAccountEvaluator.eval,step,other]
      | unsupported tag last lastWarm lastMeter lastOutput => simp only [ReferenceCheckedAccountEvaluator.eval,step,other]

theorem foreign {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (support : ReferenceSystemBlockFootprint.Support owner tx keys) (parent : Parent)
    (other : AccountAddress) (distinct : other ≠ owner) : AtOwner (commit parent tx) parent other :=
  ReferenceSystemBlockFootprint.foreign_commit support parent other distinct

/-- The terminal observation and all three predicates retain their same
replay witness while its actual source parent changes at foreign addresses. -/
theorem completion {p q : Parent} {kind : ReachableCalls.Contract} {c : MessageCall.Context}
    {events : List Event} {v : View} {success : Bool} {output : ByteArray}
    (same : AtOwner q p v.env.codeOwner)
    (completed : ReferenceCheckedTheta.Completed kind c p events v success output) :
    ReferenceCheckedTheta.Completed kind c q events v success output := by
  obtain ⟨extra,post,observed,result,claims⟩ := completed
  refine ⟨extra,post,{observed with storage := ?_},result,claims⟩
  intro key
  have old := observed.storage key
  change current p v.storage post.executionEnv.codeOwner key.toByteArray = _ at old
  change current q v.storage post.executionEnv.codeOwner key.toByteArray = _
  rw [←observed.env,current_eq same]
  simpa only [←observed.env] using old

#print axioms handler
#print axioms trace
#print axioms completed_run
#print axioms dispatch
#print axioms account_dispatch
#print axioms evaluated
#print axioms foreign
#print axioms completion
end Eip8282.Audit.Integrator.ReferenceSystemBlockParent
