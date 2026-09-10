import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
import Eip8282.Audit.Integrator.ReferenceSourceReplayEntry

/-! Resource and context facts at the final dispatcher input of the same
computed evaluation, including failed evaluations. No caught-fault or successful
terminal hypothesis is used. These facts discharge source checked conversions;
the actual source account-presence binding remains separate from old HasOwner.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedPrefix
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem family_env {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) : next.env = v.env := by
  cases p <;> simp only [familyAction] at effect
  all_goals repeat' first | split at effect | cases effect
  all_goals rfl

private theorem pure_env {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) : next.env = v.env := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    exact family_env p effect

theorem action_env {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind parent instr v next) : next.env = v.env := by
  cases actual with
  | base base =>
    cases base with
    | pure effect => exact pure_env effect
    | load => rfl
    | store => rfl
    | word => rfl
    | byte => rfl
  | copy => rfl
  | log => rfl

theorem trace_env {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    finish.env = v.env := by
  induction actual with
  | refl => rfl
  | cons step tail ih =>
    obtain ⟨action,_,_,_,nextStack⟩ := step.sound stack aligned
    exact (ih nextStack (ReferenceActionMemoryBounds.preserves_alignment action aligned)).trans (action_env action)

/-- Derive both conversion bounds before the last dispatcher runs. The
result may be a fault, EOF, unsupported, or a successful terminal. -/
theorem evaluated_bounds {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : Outcome} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (cdfit : c.env.calldata.size < UInt256.size) :
    ∃ finish finalWarm final post,
      run destinations ownerExists parent finish finalWarm final ByteArray.empty = result ∧
      Related parent finish post ∧ RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post ∧
      finish.env = c.env ∧ finish.env.calldata.size < UInt256.size ∧ finish.pc+1 < UInt256.size := by
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  have stack : (initial c tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial c tx) rfl
  have env := trace_env trace stack aligned
  obtain ⟨source,paid,_⟩ := trace.extract stack aligned
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events+0 ≤ 30000000 := by omega
  obtain ⟨post,_,_,related,site,_⟩ := ReferenceSourceReplayEntry.from_entry c 0 source slots owner warmRelated bound
  refine ⟨finish,finalWarm,final,post,last,related,site,env,?_,?_⟩
  · rw [env]; exact cdfit
  · have fit := ReferenceRuntimeSites.pc_fit site
    rw [related.pc]
    omega

#print axioms action_env
#print axioms trace_env
#print axioms evaluated_bounds
end Eip8282.Audit.Integrator.ReferenceCheckedPrefix
