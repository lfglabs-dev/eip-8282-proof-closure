import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
import Eip8282.Audit.Integrator.ReferenceNestedSourceAppend

/-! Existing nested append consumer now takes one literal checked handler
history. Intermediate source Actions, Price, stack/memory alignment and the
entire payment sequence are derived, including zero-cost STOP. The numerical
entry cap comes from the same surrounding resource ledger's root allocation.
Actual source frame identity/global occurrence coverage and initial world/code/
owner/warm bindings remain distinct producers; EntryAt is not a unique path.
This does not assert success or canonical reachability of a chosen input call. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedAppend
open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceExecutionLedger
open ReferenceResourceEntryBound ReferenceSelectedAppendWork
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem stop_payment {events : List Event} {pre post : Meter}
    (paid : runFull events pre = some post) : runFull (events++[.ordinary 0]) pre = some post := by
  rw [ReferenceCheckedRuntimeTrace.runFull_append,paid,Option.bind_some]
  simp [runFull,ReferenceMeterPath.run,pay,ReferenceStorageGas.chargeExecution,core,update]

theorem exit (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre post : Meter}
    (actual : ReferenceCheckedRuntimeTrace.Run .exit parent (initial c tx) warm pre finish finalWarm post events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    ProtectedPaid pre post (work events) := by
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  exact ReferenceNestedSourceAppend.exit c source slots owner warmRelated halt user size located (stop_payment paid)

theorem deposit (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre post : Meter}
    (actual : ReferenceCheckedRuntimeTrace.Run .deposit parent (initial c tx) warm pre finish finalWarm post events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    ProtectedPaid pre post (work events) := by
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  exact ReferenceNestedSourceAppend.deposit c source slots owner warmRelated halt user size located (stop_payment paid)

#print axioms exit
#print axioms deposit
end Eip8282.Audit.Integrator.ReferenceCheckedAppend
