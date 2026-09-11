import Eip8282.Audit.Integrator.ReferenceCheckedSystemTraceForward
import Eip8282.Audit.Integrator.ReferenceCheckedSystemReturn

/-! Whole's paid actual SYSTEM trace is one successful checked computation.
The result's output, storage and logs are those of that same trace. Source
meter potential supplies computational budget; replay gas is never substituted.
Consumer: mandatory SYSTEM success from source_whole and constructed entry. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemWhole
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceSystemSourcePayment ReferenceExecutionPotential
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem evaluated {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : SystemExecutionResources.Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {warm : Warm} {meter : Meter} {destinations : List Nat}
    (whole : Whole parent created h v warm (core meter))
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ∃ events ended,
      ReferenceCheckedEvaluator.eval destinations true parent ByteArray.empty (potential meter+1) v warm meter =
        some (events,.terminal ended) ∧
      ended.halt = .returned ∧ ended.output = h.output ∧
      ReferenceStorageView.Related parent ended.view.storage h.finalState.toState ∧
      ended.view.logs = ProtectedLogFrame.project h.finalState.executionEnv.codeOwner h.finalState.substate := by
  obtain ⟨prefixEvents,events,finalCore,finish,finalWarm,off,len,rest,coupled,related,warmRelated,createdEq,
    decoded,shape,result,outputEq,costEq,eventEq,paid,execution,reservoir,lastWarm⟩ := whole
  subst events
  have fullPaid : runFull (prefixEvents++[.ordinary (terminalCost finish off len)]) meter =
      some (update meter finalCore) := by simp only [runFull,paid,Option.map_some]
  rw [ReferenceCheckedRuntimeTrace.runFull_append] at fullPaid
  obtain ⟨lastMeter,prefixPaid,returnPaid⟩ := Option.bind_eq_some_iff.mp fullPaid
  obtain ⟨trace,continuation⟩ := ReferenceCheckedSystemTraceForward.coupled coupled site context aligned prefixPaid
  have lengthBound := trace.length_bound stack aligned
  have lastAligned : ReferenceActionMemoryBounds.Aligned finish := by
    unfold ReferenceActionMemoryBounds.Aligned
    rw [words_related related]
    exact related.memory.size
  have enough : prefixEvents.length ≤ potential meter := by omega
  obtain ⟨budget,budgetEq⟩ := Nat.exists_eq_add_of_le enough
  have terminal := ReferenceCheckedSystemReturn.evaluated (destinations := destinations) (parent := parent) (warm := finalWarm) decoded shape lastAligned returnPaid budget ByteArray.empty
  have actual := continuation (budget+1) ByteArray.empty
  rw [terminal] at actual
  have budgetFit : prefixEvents.length+(budget+1) = potential meter+1 := by omega
  rw [budgetFit] at actual
  simp only [Option.map_some,List.append_nil] at actual
  exact ⟨prefixEvents,ReferenceCheckedSystemReturn.result finish off len rest (update meter finalCore),
    actual,rfl,outputEq.symm,result.storage,result.logs⟩

#print axioms evaluated
end Eip8282.Audit.Integrator.ReferenceCheckedSystemWhole
