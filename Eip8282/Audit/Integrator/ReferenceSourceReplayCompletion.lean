import Eip8282.Audit.Integrator.ReferenceSourceReplayEntry
import Eip8282.Audit.Integrator.ReferenceTerminalReplay

/-! Whole finite protected effect replay, including actual STOP/RETURN/REVERT.
The source-shaped prefix is supplied, never an old execution. Its paid-work
bound builds synthetic gas/fuel and memory bounds. Actual Python source and
outer journal/rollback extraction remain explicit; REVERT's internal view is
not treated as a committed result. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceExecutionLedger ReferenceSourceReplayTrace
open ReferenceSourceReplayEntry
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem decode_view {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v : View} {pre : EVM.State} (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre) :
    decodeAt pre = instruction v := by
  unfold instruction
  rw [related.env,related.pc,site.1,ReferenceRuntimeSites.code_eq]
  exact ReferenceAllDecode.decode_matches site

theorem stop {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2) (call c events 0).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      decodeAt middle = (.STOP,none) ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events 0).entry = .ok (.success post ByteArray.empty) ∧ Related parent finish post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,_,_,stack⟩ :=
    from_entry c 0 source slots owner warmRelated (by simpa using bound)
  have decoded := (decode_view related site).trans halt
  obtain ⟨post,terminal,postRelated,_⟩ := ReferenceTerminalReplay.stop 0 related decoded stack
  have same := coupled.viewed.erase.X_eq
  exact ⟨middle,post,trace,coupled,decoded,same.trans terminal,postRelated⟩

theorem returned {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {off len : UInt256} {rest : Stack UInt256}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (shape : finish.stack = off::len::rest)
    (bound : work events+ReferenceTerminalReplay.charge finish off len ≤ 30000000)
    (halt : instruction finish = (.RETURN,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry =
          .ok (.success post (ReferenceReturnView.output finish off len)) ∧
      ReferenceReturnView.Result parent finish off len rest post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,gas,domain,stack⟩ :=
    from_entry c (ReferenceTerminalReplay.charge finish off len) source slots owner warmRelated bound
  have decoded := (decode_view related site).trans halt
  have restBound : rest.length ≤ 1024 := by rw [shape] at stack; simp only [List.length_cons] at stack; omega
  obtain ⟨post,terminal,result,_⟩ := ReferenceTerminalReplay.returned 0 related decoded shape restBound domain (by omega)
  exact ⟨middle,post,trace,coupled,coupled.viewed.erase.X_eq.trans terminal,result⟩

theorem reverted {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {off len : UInt256} {rest : Stack UInt256}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (shape : finish.stack = off::len::rest)
    (bound : work events+ReferenceTerminalReplay.charge finish off len ≤ 30000000)
    (halt : instruction finish = (.REVERT,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry =
          .ok (.revert post.gasAvailable (ReferenceReturnView.output finish off len)) ∧
      ReferenceReturnView.Result parent finish off len rest post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,gas,domain,stack⟩ :=
    from_entry c (ReferenceTerminalReplay.charge finish off len) source slots owner warmRelated bound
  have decoded := (decode_view related site).trans halt
  have restBound : rest.length ≤ 1024 := by rw [shape] at stack; simp only [List.length_cons] at stack; omega
  obtain ⟨post,terminal,result,_⟩ := ReferenceTerminalReplay.reverted 0 related decoded shape restBound domain (by omega)
  exact ⟨middle,post,trace,coupled,coupled.viewed.erase.X_eq.trans terminal,result⟩

#print axioms stop
#print axioms returned
#print axioms reverted
end Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion
