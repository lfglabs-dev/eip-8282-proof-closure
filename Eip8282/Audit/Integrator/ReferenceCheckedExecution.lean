import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
import Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal
import Eip8282.Audit.Integrator.ReferenceCheckedCompletion
import Eip8282.Audit.Integrator.ReferenceNestedSourceAppend

/-! Connect the computed checked evaluator to pinned bytecode execution.
No running trace, terminal instruction, terminal operands, prices or payment
annotations are inputs: they are extracted from the evaluator's actual result.
Exact initialized world/owner/warmth remain explicit source frame bindings.
Source and synthetic gas/PC are not equated. REVERT observations are internal;
outer restoration and actual source journal occurrence identity remain open.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedExecution
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedDispatch ReferenceCheckedTerminalStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Same terminal observable tuple. The old gas field of the internal REVERT
witness is deliberately distinct from the actual source terminal meter. -/
def Replayed {kind : Kind} (c : XiCall kind) (parent : ReferenceStorageView.Parent)
    (events : List Event) (result : End) : Prop :=
  ∃ amount post,
    X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call c events amount).entry =
      (if result.halt = .reverted then .ok (.revert post.gasAvailable result.output)
        else .ok (.success post result.output)) ∧
    ReferenceCheckedCompletion.Observations parent result.view post

/-- A terminal returned by actual checked evaluation produces the complete
pinned execution and same observations. This is conditional on that terminal
outcome, not an assumption that all calls succeed. -/
theorem terminal {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : End} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    Replayed c parent events result := by
  obtain ⟨finish,finalWarm,middle,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨halt,checked,decoded⟩ := ReferenceCheckedDispatchTerminal.terminal last
  cases halt with
  | stop =>
    obtain ⟨halt,_,post,execution,observed⟩ := ReferenceCheckedCompletion.stop c trace checked decoded slots owner warmRelated grant
    exact ⟨0,post,by simpa only [halt,reduceCtorEq,if_false] using execution,observed⟩
  | returned =>
    obtain ⟨halt,amount,post,_,execution,observed⟩ := ReferenceCheckedCompletion.slice c (by decide) trace checked decoded slots owner warmRelated grant
    exact ⟨amount,post,by simpa only [halt,if_true,reduceCtorEq,if_false] using execution,observed⟩
  | reverted =>
    obtain ⟨halt,amount,post,_,execution,observed⟩ := ReferenceCheckedCompletion.slice c (by decide) trace checked decoded slots owner warmRelated grant
    exact ⟨amount,post,by simpa only [halt,if_true,reduceCtorEq,if_false] using execution,observed⟩

/-- For a transaction nested entry, the replay resource domain is derived
from the literal root allocation and nested grants, rather than supplied. The
numeric location is still not the source occurrence's unique identity. -/
theorem transaction_terminal {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : End} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : ReferenceResourceEntryBound.EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    Replayed c parent events result := by
  have grant := ReferenceNestedSourceAppend.transaction_entry located
  exact terminal c context actual slots owner warmRelated (by omega)

/-- From exact initialized context, the final checked dispatch lies on a
supported runtime site or genuine EOF. Invalid/unsupported opcodes cannot be
introduced by the helper fallback at this point. EOF is retained explicitly. -/
theorem final_site_or_eof {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {pre final : Meter}
    {finish : View} {events : List Event}
    (trace : ReferenceCheckedRuntimeTrace.Run kind parent (initial c tx) warm pre finish finalWarm final events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    (∃ h, read finish.env.code finish.pc = .handler h) ∨ read finish.env.code finish.pc = .eof := by
  obtain ⟨source,paid,_⟩ := trace.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events+0 ≤ 30000000 := by omega
  obtain ⟨post,_,_,related,site,_⟩ := ReferenceSourceReplayEntry.from_entry c 0 source slots owner warmRelated bound
  have code : finish.env.code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind) := by
    rw [related.env,site.1,ReferenceRuntimeSites.code_eq]
  rcases ReferenceRuntimeSites.site_or_eof site with hp | he
  · exact Or.inl (ReferenceCheckedDispatchTerminal.runtime_coverage kind finish code (by rw [related.pc]; exact hp))
  · right
    apply read_eof
    rw [code,related.pc,he]
    change (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)).data[
      (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)).data.size]? = none
    simp

#print axioms terminal
#print axioms transaction_terminal
#print axioms final_site_or_eof
end Eip8282.Audit.Integrator.ReferenceCheckedExecution
