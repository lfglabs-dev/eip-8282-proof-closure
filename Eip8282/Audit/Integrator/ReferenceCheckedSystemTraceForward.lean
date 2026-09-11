import Eip8282.Audit.Integrator.ReferenceSystemStackBound
import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
import Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection

/-! The paid SYSTEM prefix is the actual checked evaluator prefix, with the
same views, warmth, ordered meter events and arbitrary continuation budget.
Consumer: successful mandatory SYSTEM return on the already computed run. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemTraceForward
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMeterPath ReferenceCheckedDispatch ReferenceSystemReadingsTrace
open ReferenceSourceReplayTrace (instruction)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def isHandler : Dispatch → Bool
  | .handler _ => true
  | _ => false

theorem site_table (kind : Kind) :
    (ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)).all
      (fun pc => isHandler (read (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)) pc)) = true := by
  cases kind <;> decide +kernel

theorem selected {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View} {pre post : EVM.State}
    (related : Related parent v pre) (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (nonhalting : H post.toMachineState (decodeAt pre).1 = none) :
    ∃ h, read v.env.code v.pc = .handler h := by
  have member := ReferenceRuntimeSites.nonhalting_site site nonhalting
  have yes := List.all_eq_true.mp (site_table kind) _ member
  rw [←ReferenceRuntimeSites.code_eq,←site.1,←related.env,←related.pc] at yes
  cases selected : read v.env.code v.pc with
  | handler h => exact ⟨h,rfl⟩
  | eof => simp [selected,isHandler] at yes
  | invalid t => simp [selected,isHandler] at yes
  | unsupported t => simp [selected,isHandler] at yes

/-- No post-stack premise: the actual Z guard and literal same action derive it.
The continuation equation identifies this prefix inside the executable fold. -/
theorem coupled {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {warm finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    {destinations : List Nat} {meter final : Meter}
    (coupled : Coupled kind parent created fuel pre v warm trace rem post finish finalWarm events)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull events meter = some final) :
    ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
    ∀ budget output, ReferenceCheckedEvaluator.eval destinations true parent output (events.length+budget) v warm meter =
      (ReferenceCheckedEvaluator.eval destinations true parent output budget finish finalWarm final).map
        (fun (tail,result) => (events++tail,result)) := by
  induction coupled generalizing meter final with
  | refl =>
    have eq : meter = final := by simpa [runFull,ReferenceMeterPath.run,core,update] using paid
    subst final
    refine ⟨.refl _ _ _,?_⟩
    intro budget output
    simp only [List.length_nil,Nat.zero_add,List.nil_append]
    cases ReferenceCheckedEvaluator.eval destinations true parent output budget _ _ _ <;> rfl
  | @cons edgeFuel gasCost rem pre middle post v next finish warm finalWarm trace event events
      actual decoded related nextRelated warmRelated createdEq action readings oldPrice sourcePrice tail ih =>
    obtain ⟨mid,hz,hs,hh⟩ := actual
    obtain ⟨h,hread⟩ := selected related site hh
    obtain ⟨arg,hdecode⟩ := read_handler hread
    have instrEq : instruction v = (opcode h,arg) := by
      simp only [instruction,hdecode,Option.getD_some]
    have oldInstr : decodeAt pre = (opcode h,arg) := decoded.trans instrEq
    have act : ReferenceSystemAction.Action kind parent (instruction v) v next := by
      rw [instrEq,←oldInstr]; exact action
    have bounds := ReferenceAcceptedStack.bounds hz
    rw [oldInstr,←related.stack] at bounds
    have postbound := ReferenceSystemStackBound.handler (by rw [←oldInstr]; exact action) bounds.1 bounds.2
    have pcfit : v.pc+1 < UInt256.size := by
      have fit := ReferenceRuntimeSites.pc_fit site
      rw [related.pc]
      omega
    change runFull ([event]++events) meter = some final at paid
    rw [ReferenceCheckedRuntimeTrace.runFull_append] at paid
    obtain ⟨nextMeter,headPaid,tailPaid⟩ := Option.bind_eq_some_iff.mp paid
    have hprice : SourcePrice parent v warm next (instruction v).1 event := by
      rw [instrEq,←oldInstr]; exact sourcePrice
    have actualRun : ∀ output, run destinations true parent v warm meter output =
        .continued next (warmAfter (decodeAt pre).1 v warm) nextMeter event := by
      intro output
      rw [ReferenceCheckedDispatch.run,hread]
      simpa only [instrEq,oldInstr] using ReferenceCheckedSystemForward.handler output context
        (congrArg Prod.fst instrEq) act hprice postbound aligned pcfit headPaid
    have nextSite := RuntimeExecutionScope.accepted_next site hz hs hh
    have nextAligned := ReferenceActionMemoryBounds.preserves_alignment (.base act) aligned
    obtain ⟨checked,continuation⟩ := ih nextSite nextAligned tailPaid
    refine ⟨.cons (ReferenceCheckedDispatch.step context (actualRun ByteArray.empty)) checked,?_⟩
    intro budget output
    simp only [List.length_cons,Nat.add_right_comm _ 1 budget,ReferenceCheckedEvaluator.eval,actualRun]
    rw [continuation]
    simp only [Option.map_map]
    congr 1

#print axioms site_table
#print axioms selected
#print axioms coupled
end Eip8282.Audit.Integrator.ReferenceCheckedSystemTraceForward
