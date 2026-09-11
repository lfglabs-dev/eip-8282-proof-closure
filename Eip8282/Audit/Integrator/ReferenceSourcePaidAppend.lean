import Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion
import Eip8282.Audit.Integrator.ReferenceSelectedAppendWork

/-! Produce an existing completed-append resource leaf from a paid source-shaped
run. Old execution success and its complete trace are reconstructed and aligned.
The same event list is used for source effects, prices, payment and leaf work.
Actual source frame identity/extraction and global survivor coverage are still
required; resource threading alone is not an occurrence-completeness proof. -/
namespace Eip8282.Audit.Integrator.ReferenceSourcePaidAppend
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceExecutionLedger ReferenceSourceReplayTrace ReferenceSelectedAppendWork ReferenceTraceAgreement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem aligned_success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {created : Set AccountAddress} {v finish : View} {warm finalWarm : Warm} {events : List Event}
    {vj : Array UInt256} {fuel rem : Nat} {pre middle post : EVM.State} {trace : List Labelled} {out : ByteArray}
    (tables : vj = D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
    (actual : X fuel vj pre = .ok (.success post out))
    (coupled : Coupled kind parent created fuel pre v warm trace rem middle finish finalWarm events)
    (stopped : decodeAt middle = (.STOP,none)) :
    ∃ t : SuccessInversion.SuccessTrace vj fuel pre post out,
      Coupled kind parent created fuel pre v warm t.trace (t.rem+1) t.exit finish finalWarm events := by
  subst vj
  obtain ⟨t⟩ := SuccessInversion.success_trace actual
  have terminal : Blocked (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (t.rem+1) t.exit := by
    apply blocked_of_terminal
    · rw [t.decode]; exact t.charge
    · rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
    · rw [t.decode]; exact t.output
  obtain ⟨sameTrace,sameRem,sameExit⟩ := complete_unique coupled.viewed.erase t.run.toXRuns
    (blocked_of_stop stopped) terminal
  exact ⟨t,by simpa only [sameTrace,sameRem,sameExit] using coupled⟩

private theorem paid_bound {events : List Event} {pre post : Meter}
    (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) : work events ≤ 30000000 := by
  have h := ReferenceExecutionLedger.bounded (.paid _ paid)
  simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] at h
  unfold work
  omega

theorem exit (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .exit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
    {pre post : Meter} (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    ProtectedPaid pre post (work events) := by
  have bound := paid_bound paid grant
  obtain ⟨middle,final,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have tables : exitJumpdests = D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩ := by
    change exitJumpdests = D_J exitRuntime ⟨0⟩
    rw [exit_D_J]
  have actual' : X (events.length+2) exitJumpdests replay.entry = .ok (.success final ByteArray.empty) := by
    rw [tables]
    exact actual
  obtain ⟨t,priced⟩ := aligned_success tables actual' coupled decoded
  have leaf := ProtectedPaid.exit replay user size actual' t priced 0 paid
  simpa only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] using leaf

theorem deposit (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .deposit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
    {pre post : Meter} (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    ProtectedPaid pre post (work events) := by
  have bound := paid_bound paid grant
  obtain ⟨middle,final,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have tables : depositJumpdests = D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩ := by
    change depositJumpdests = D_J depositRuntime ⟨0⟩
    rw [deposit_D_J]
  have actual' : X (events.length+2) depositJumpdests replay.entry = .ok (.success final ByteArray.empty) := by
    rw [tables]
    exact actual
  obtain ⟨t,priced⟩ := aligned_success tables actual' coupled decoded
  have leaf := ProtectedPaid.deposit replay user size actual' t priced 0 paid
  simpa only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] using leaf

#print axioms exit
#print axioms deposit
end Eip8282.Audit.Integrator.ReferenceSourcePaidAppend
