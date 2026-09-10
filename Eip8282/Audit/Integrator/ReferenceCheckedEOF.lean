import Eip8282.Audit.Integrator.ReferenceCheckedExecution

/-! Genuine code exhaustion has an exact source outcome distinct from STOP.
The checked evaluator preserves PC/view/meter/output at EOF. For a protected
initialized frame with empty previous output, its same running trace produces
the pinned evaluator's EOF fallback result and all terminal observations.
The fallback is used only after actual absence of a code byte is established;
an invalid opcode cannot enter this proof. Outer source receipt/rollback and
initial frame bindings remain separate, as in CheckedExecution. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedEOF
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem handler_not_eof {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v last : View} {warm lastWarm : Warm} {meter lastMeter : Meter}
    {output lastOutput : ByteArray} :
    runHandler h destinations ownerExists parent v warm meter output ≠ .eof last lastWarm lastMeter lastOutput := by
  intro actual
  cases h <;> simp only [runHandler] at actual
  all_goals split at actual <;> contradiction

theorem lookup {bytes : ByteArray} {pc : Nat} (actual : read bytes pc = .eof) : bytes[pc]? = none := by
  unfold ReferenceCheckedDispatch.read at actual
  cases ht : bytes[pc]? with
  | none => rfl
  | some tag =>
    simp only [ht] at actual
    split at actual
    · cases hs : select tag <;> simp only [hs] at actual <;> contradiction
    · contradiction

/-- A genuine EOF leaves every local field unchanged, including PC and the
incoming output. No terminal handler or synthetic PC increment is inserted. -/
theorem fields {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v last : View} {warm lastWarm : Warm} {meter lastMeter : Meter}
    {output lastOutput : ByteArray}
    (actual : run destinations ownerExists parent v warm meter output = .eof last lastWarm lastMeter lastOutput) :
    v = last ∧ warm = lastWarm ∧ meter = lastMeter ∧ output = lastOutput ∧ v.env.code[v.pc]? = none := by
  unfold ReferenceCheckedDispatch.run at actual
  cases hd : read v.env.code v.pc <;> rw [hd] at actual
  · cases actual
    exact ⟨rfl,rfl,rfl,rfl,lookup hd⟩
  · contradiction
  · contradiction
  · exact False.elim (handler_not_eof actual)

/-- Full EOF replay from the computed evaluator, without treating unsupported
or invalid source opcodes as successful STOP. Empty output is the fresh-frame
binding supplied here; the evaluator preserves it on every running handler. -/
theorem execution {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat}
    {events : List Event} {last : View} {output : ByteArray} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.eof last finalWarm final output))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    output = ByteArray.empty ∧
    runFull events pre = some final ∧
    ∃ post, X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call c events 0).entry = .ok (.success post output) ∧
      ReferenceCheckedCompletion.Observations parent last post := by
  obtain ⟨finish,endWarm,middle,trace,ended,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨viewEq,warmEq,meterEq,outputEq,absent⟩ := fields ended
  subst finish
  subst endWarm
  subst middle
  subst output
  obtain ⟨source,paid,_⟩ := trace.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events ≤ 30000000 := by omega
  have halt : ReferenceSourceReplayTrace.instruction last = (.STOP,none) := by
    simp [ReferenceSourceReplayTrace.instruction,ReferenceDecodeSites.referenceDecode,absent]
  obtain ⟨_,post,_,_,_,execution,related⟩ := ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  exact ⟨rfl,paid,post,execution,related.env,related.stack,related.memory,related.storage,related.logs,related.owner⟩

#print axioms lookup
#print axioms fields
#print axioms execution
end Eip8282.Audit.Integrator.ReferenceCheckedEOF
