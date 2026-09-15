import Eip8282.Audit.Integrator.Topics.Reference5
import Eip8282.Audit.Integrator.Topics.ReferenceSource2

/-! Source-shaped paid append at an entry of the same nested resource ledger.
The protected frame's local potential cap is derived from the literal root
transaction allocation; it is not a new internal admission hypothesis. EntryAt
is a numeric ledger location, not a unique occurrence identity. Actual source
frame extraction, source context bindings and complete occurrence coverage
remain separate producers. No total source termination is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceNestedSourceAppend
open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceExecutionLedger ReferenceResourceEntryBound ReferenceSelectedAppendWork
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Even before admission is applied, the literal allocator never grants more
than the execution maximum. Protocol validity must still supply its real inputs. -/
theorem transaction_entry {txGas intrinsic totalWork : Nat} {final node : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork node) :
    ReferenceExecutionPotential.potential node ≤ 16777216 := by
  apply located.cap
  simp only [ReferenceTransactionWork.initial,ReferenceChildMeter.init,
    ReferenceExecutionPotential.potential,ReferenceTransactionGas.allocate,Nat.add_zero]
  omega

theorem exit (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .exit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
    {txGas intrinsic totalWork : Nat} {final pre post : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre)
    (paid : runFull (events++[.ordinary 0]) pre = some post) :
    ProtectedPaid pre post (work events) := by
  have bound := transaction_entry located
  exact ReferenceSourcePaidAppend.exit c source slots owner warmRelated halt user size paid (by omega)

theorem deposit (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .deposit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
    {txGas intrinsic totalWork : Nat} {final pre post : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre)
    (paid : runFull (events++[.ordinary 0]) pre = some post) :
    ProtectedPaid pre post (work events) := by
  have bound := transaction_entry located
  exact ReferenceSourcePaidAppend.deposit c source slots owner warmRelated halt user size paid (by omega)

#print axioms transaction_entry
#print axioms exit
#print axioms deposit
end Eip8282.Audit.Integrator.ReferenceNestedSourceAppend
