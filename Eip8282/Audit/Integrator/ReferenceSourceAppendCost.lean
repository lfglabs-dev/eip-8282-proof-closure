import Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion
import Eip8282.Audit.Integrator.ReferenceAppendCompletedCost

/-! Mandatory append costs from the same finite source-shaped completed call.
Synthetic old success is constructed, never supplied. Ordered actual instruction
markers align with the replayed source event trace; old gas is not the measure.
Actual source frame/price/entry extraction and global occurrence coverage remain
separate producers. No queue invariant, no-wrap assumption or loop cap occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceAppendCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceExecutionLedger ReferenceSourceReplayTrace
open ReferenceAppendOccurrences ReferenceAppendPrice ReferenceTraceAgreement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem exit_cost (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run .exit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48) :
    1419 ≤ work events := by
  obtain ⟨middle,post,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have actual' : X (events.length+2) exitJumpdests replay.entry = .ok (.success post ByteArray.empty) := by
    change X _ (D_J exitRuntime ⟨0⟩) _ = _ at actual
    rw [exit_D_J] at actual
    exact actual
  obtain ⟨rem,exit,marked,stopped,_⟩ := ReferenceAppendEntry.exit_entry replay user size actual'
  have marked' : Marked (D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩)
      (events.length+2) replay.entry rem exit exitMarkers := by
    change Marked (D_J exitRuntime ⟨0⟩) _ _ _ _ _
    rw [exit_D_J]
    exact marked
  obtain ⟨markerTrace,markerRun,_⟩ := marked'.erase
  obtain ⟨_,sameRem,sameExit⟩ := complete_unique markerRun coupled.viewed.erase
    (blocked_of_stop stopped) (blocked_of_stop decoded)
  have aligned : Marked (D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩)
      (events.length+2) replay.entry 2 middle exitMarkers := by
    simpa only [sameRem,sameExit] using marked'
  have cost := selected_cost aligned coupled
  rw [exact_marker_costs.1] at cost
  exact cost

theorem deposit_cost (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run .deposit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184) :
    2647 ≤ work events := by
  obtain ⟨middle,post,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have actual' : X (events.length+2) depositJumpdests replay.entry = .ok (.success post ByteArray.empty) := by
    change X _ (D_J depositRuntime ⟨0⟩) _ = _ at actual
    rw [deposit_D_J] at actual
    exact actual
  obtain ⟨rem,exit,marked,stopped,_⟩ := ReferenceAppendEntry.deposit_entry replay user size actual'
  have marked' : Marked (D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩)
      (events.length+2) replay.entry rem exit depositMarkers := by
    change Marked (D_J depositRuntime ⟨0⟩) _ _ _ _ _
    rw [deposit_D_J]
    exact marked
  obtain ⟨markerTrace,markerRun,_⟩ := marked'.erase
  obtain ⟨_,sameRem,sameExit⟩ := complete_unique markerRun coupled.viewed.erase
    (blocked_of_stop stopped) (blocked_of_stop decoded)
  have aligned : Marked (D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩)
      (events.length+2) replay.entry 2 middle depositMarkers := by
    simpa only [sameRem,sameExit] using marked'
  have cost := selected_cost aligned coupled
  rw [exact_marker_costs.2] at cost
  exact cost

#print axioms exit_cost
#print axioms deposit_cost
end Eip8282.Audit.Integrator.ReferenceSourceAppendCost
