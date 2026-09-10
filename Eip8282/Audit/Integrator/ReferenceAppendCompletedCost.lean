import Eip8282.Audit.Integrator.ReferenceAppendEntry
import Eip8282.Audit.Integrator.ReferenceAppendPrice
import Eip8282.Audit.Integrator.ReferenceTraceAgreement

/-! Completed actual user appends derive their exact mandatory execution-cost
lower bound on the same source-priced trace. Neither an assumed instruction
count nor a fee iteration/resource bound appears. This is local protected
runtime composition; actual source-frame extraction is still separate. -/
namespace Eip8282.Audit.Integrator.ReferenceAppendCompletedCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceAppendOccurrences ReferenceAppendEntry ReferenceAppendPrice ReferenceExecutionLedger ReferenceTraceAgreement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem align_success {vj : Array UInt256} {fuel rem : Nat} {pre exit final : EVM.State}
    {out : ByteArray} {markers : List Marker}
    (marked : Marked vj fuel pre rem exit markers) (stopped : decodeAt exit = (.STOP,none))
    (t : SuccessInversion.SuccessTrace vj fuel pre final out) :
    Marked vj fuel pre (t.rem+1) t.exit markers := by
  obtain ⟨trace,run,_⟩ := marked.erase
  have terminal : Blocked vj (t.rem+1) t.exit := by
    apply blocked_of_terminal
    · rw [t.decode]; exact t.charge
    · rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
    · rw [t.decode]; exact t.output
  obtain ⟨_,hr,hp⟩ := complete_unique run t.run.toXRuns (blocked_of_stop stopped) terminal
  simpa only [hr,hp] using marked

theorem exit_cost (c : XiCall .exit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (hsize : c.env.calldata.size = 48)
    (actual : X fuel exitJumpdests c.entry = .ok (.success final out))
    (t : SuccessInversion.SuccessTrace exitJumpdests fuel c.entry final out)
    {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
    (priced : Coupled .exit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events) :
    1419 ≤ work events := by
  obtain ⟨rest,finish,marked,stopped,_⟩ := exit_entry c huser hsize actual
  have aligned := align_success marked stopped t
  have converted : Marked (D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩)
      fuel c.entry (t.rem+1) t.exit exitMarkers := by
    change Marked (D_J exitRuntime ⟨0⟩) _ _ _ _ _
    rw [exit_D_J]
    exact aligned
  have bound := selected_cost converted priced
  rw [exact_marker_costs.1] at bound
  exact bound

theorem deposit_cost (c : XiCall .deposit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (hsize : c.env.calldata.size = 184)
    (actual : X fuel depositJumpdests c.entry = .ok (.success final out))
    (t : SuccessInversion.SuccessTrace depositJumpdests fuel c.entry final out)
    {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
    (priced : Coupled .deposit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events) :
    2647 ≤ work events := by
  obtain ⟨rest,finish,marked,stopped,_⟩ := deposit_entry c huser hsize actual
  have aligned := align_success marked stopped t
  have converted : Marked (D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩)
      fuel c.entry (t.rem+1) t.exit depositMarkers := by
    change Marked (D_J depositRuntime ⟨0⟩) _ _ _ _ _
    rw [deposit_D_J]
    exact aligned
  have bound := selected_cost converted priced
  rw [exact_marker_costs.2] at bound
  exact bound

#print axioms align_success
#print axioms exit_cost
#print axioms deposit_cost
end Eip8282.Audit.Integrator.ReferenceAppendCompletedCost
