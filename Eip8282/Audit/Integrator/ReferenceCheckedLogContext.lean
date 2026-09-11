import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome

/-! Log-context lens for the checked runtime. The replay View carries the fixed
incoming protected-address log prefix plus this frame's local projected logs.
Every successful running handler preserves that prefix; removing it before
parent incorporation prevents inherited logs from being counted twice.
These are executed logs, not persistent records: REVERT, failures and ancestors
can discard their contribution. Source frame initialization, transfer LOG3
projection and actual parent journal identity are separate binding producers. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedLogContext
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary
open ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem family_logs {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) : next.logs = v.logs := by
  cases p <;> simp only [familyAction] at effect
  all_goals repeat' first | split at effect | cases effect
  all_goals rfl

private theorem pure_logs {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) : next.logs = v.logs := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    exact family_logs p effect

/-- Only LOG0 appends a log; every other represented action preserves the
same log sequence. Its source output bytes are already fixed by that action. -/
theorem action_suffix {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind parent instr v next) :
    ∃ suffix, next.logs = v.logs++suffix := by
  cases actual with
  | base base =>
    cases base with
    | pure effect => exact ⟨[],by simpa only [List.append_nil] using pure_logs effect⟩
    | load => exact ⟨[],(List.append_nil _).symm⟩
    | store => exact ⟨[],(List.append_nil _).symm⟩
    | word => exact ⟨[],(List.append_nil _).symm⟩
    | byte => exact ⟨[],(List.append_nil _).symm⟩
  | copy => exact ⟨[],(List.append_nil _).symm⟩
  | log => exact ⟨_,rfl⟩

/-- The same computed checked trace produces the suffix; it is not an assumed
matching source log list. The entry prefix is retained exactly once. -/
theorem trace_suffix {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ∃ suffix, finish.logs = v.logs++suffix := by
  induction actual with
  | refl => exact ⟨[],(List.append_nil _).symm⟩
  | cons step tail ih =>
    obtain ⟨action,_,_,_,stack⟩ := step.sound initial aligned
    obtain ⟨first,firstLogs⟩ := action_suffix action
    obtain ⟨rest,restLogs⟩ := ih stack (ReferenceActionMemoryBounds.preserves_alignment action aligned)
    exact ⟨first++rest,by rw [restLogs,firstLogs,List.append_assoc]⟩

/-- Success contributes only the generated suffix. Incoming logs are neither
omitted from the replay view nor re-emitted to the parent. -/
theorem success_contribution {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (output : ByteArray) :
    ∃ suffix, finish.logs = v.logs++suffix ∧
      (ReferenceCheckedFrameOutcome.success v.logs finish finalWarm final output).logsForParent = suffix := by
  obtain ⟨suffix,logs⟩ := trace_suffix actual initial aligned
  exact ⟨suffix,logs,ReferenceCheckedFrameOutcome.success_logs v.logs suffix finish finalWarm final output logs⟩

/-- Every successful terminal preserves the exact running log list; STOP's
source PC increment is immaterial to this log-context equation. -/
theorem terminal_logs {h : ReferenceCheckedTerminalStep.Halt} {v : View} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedTerminalStep.run h v meter output = .ok result) : result.view.logs = v.logs := by
  unfold ReferenceCheckedTerminalStep.run at actual
  repeat' first | split at actual | cases actual
  all_goals rfl

/-- The actual successful evaluated terminal contributes exactly its generated
suffix. Terminal warmth, prefix and local logs come from the same evaluation. -/
theorem terminal_contribution {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End}
    (snapshot : ReferenceStorageView.Tx)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm meter =
      some (events,.terminal result))
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (success : result.halt ≠ .reverted) :
    ∃ finalWarm suffix,
      result.view.logs = v.logs++suffix ∧
      ReferenceCheckedFrameOutcome.settle snapshot v.logs finalWarm (.terminal result) =
        .returned (ReferenceCheckedFrameOutcome.success v.logs result.view finalWarm result.meter result.output) ∧
      (ReferenceCheckedFrameOutcome.success v.logs result.view finalWarm result.meter result.output).logsForParent = suffix := by
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨halt,terminal,_⟩ := ReferenceCheckedDispatchTerminal.terminal last
  obtain ⟨suffix,logs⟩ := trace_suffix trace initial aligned
  have completeLogs := (terminal_logs terminal).trans logs
  refine ⟨finalWarm,suffix,completeLogs,?_,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.settle,if_neg success]
  · exact ReferenceCheckedFrameOutcome.success_logs v.logs suffix result.view finalWarm result.meter result.output completeLogs

#print axioms action_suffix
#print axioms trace_suffix
#print axioms success_contribution
#print axioms terminal_logs
#print axioms terminal_contribution
end Eip8282.Audit.Integrator.ReferenceCheckedLogContext
