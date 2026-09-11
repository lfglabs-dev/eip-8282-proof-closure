import Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace
import Eip8282.Audit.Integrator.ReferenceSystemGuarantees

/-! A complete source-formula payment over evolving SYSTEM views, including
RETURN. Each storage event uses the same view's current/original/new values and
pre-access warmth. The literal meter fold, source output and actual receipt
share one completed execution; source interpreter and context bindings remain
separate. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemSourcePayment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceSystemReadingsTrace
open SystemTraceAnnotations SystemExecutionResources SystemMeterResources ReferenceMeterPath
open ReferenceMemoryCapacity (cost)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def terminalCost (v : View) (off len : UInt256) : Nat :=
  cost ((ReferenceReturnView.returnMemory v off len).size/32)-cost (words v)

def Whole {kind : Kind} (parent : ReferenceStorageView.Parent) (created : Set AccountAddress)
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (v : View) (w : Warm) (meter : ReferenceStorageGas.Meter) : Prop :=
  ∃ prefixEvents events final finish finalWarm off len rest,
    Coupled kind parent created fuel pre v w h.trace (h.rem+2) h.exitState finish finalWarm prefixEvents ∧
    Related parent finish h.exitState ∧ WarmRelated finalWarm h.exitState ∧
    finish.storage.created = created ∧
    ReferenceDecodeSites.referenceDecode finish.env.code finish.pc = some (.RETURN,none) ∧
    finish.stack = off::len::rest ∧
    ReferenceReturnView.Result parent finish off len rest h.finalState ∧
    h.output = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat) ∧
    terminalCost finish off len = delta h.exitState h.finalState ∧
    events = prefixEvents++[.ordinary (terminalCost finish off len)] ∧
    run events meter = some final ∧
    meter.execution-(2100*(steps+1)+12100*4+cost cap) ≤ final.execution ∧
    meter.reservoir-97920*4 ≤ final.reservoir ∧ WarmRelated finalWarm h.finalState

/-- Every internal view, access set, reading and payment is constructed from
the actual trace and initial aggregate resources. -/
theorem attach {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (w : Warm) (related : Related parent v pre) (warm : WarmRelated w pre)
    (created_eq : v.storage.created = created)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits)
    (meter : ReferenceStorageGas.Meter)
    (execution : 2100*(steps+1)+12100*4+cost cap ≤ meter.execution)
    (reservoir : 97920*4 ≤ meter.reservoir) : Whole parent created h v w meter := by
  obtain ⟨prefixEvents,events,final,hpriced,_,hevents,hpaid,he,hr⟩ :=
    pay_completed (ReferenceSourceReadings.inputs parent created) h hat output_fit meter execution reservoir
  obtain ⟨finish,finalWarm,hcoupled,hrel,hw,hcreated⟩ := from_priced hpriced hat v w related warm created_eq
    (fun op hop => h.allowed op (List.mem_append_left _ hop)) permission cdfit h.exit_capacity host
  obtain ⟨_,_,_,hcap,_⟩ := SystemMemoryResources.attach h hat output_fit
  obtain ⟨off,len,rest,_,hshape,hresult,hout⟩ :=
    ReferenceReturnView.halted h.halt.charge h.terminal hrel hcap host h.returned
  have hcost : terminalCost finish off len = delta h.exitState h.finalState := by
    unfold terminalCost delta
    rw [hresult.memory.size,words_related hrel]
    congr 2
    omega
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (decodeAt h.exitState).1 h.exitState =
      .ok (Eip8282.Audit.SymExec.charged h.exitState .RETURN,
        C' (Eip8282.Audit.SymExec.charged h.exitState .RETURN) .RETURN) := by
    rw [h.halt.decode]
    exact h.halt.charge
  have hs : StepOk (h.rem+1)
      (C' (Eip8282.Audit.SymExec.charged h.exitState .RETURN) .RETURN)
      (decodeAt h.exitState) (Eip8282.Audit.SymExec.charged h.exitState .RETURN) h.finalState := by
    rw [h.halt.decode]
    exact h.terminal
  have hwfinal : WarmRelated finalWarm h.finalState := by
    have hh := ReferenceStorageWarmth.accepted_warm h.at_exit hz hs hrel hw
    simpa only [h.halt.decode,warmAfter] using hh
  refine ⟨prefixEvents,events,final,finish,finalWarm,off,len,rest,
    hcoupled,hrel,hw,hcreated,?_,hshape,hresult,?_,hcost,?_,hpaid,he,hr,hwfinal⟩
  · rw [hrel.env,hrel.pc,h.at_exit.1,ReferenceRuntimeSites.code_eq]
    exact ReferenceTerminalDecode.return_decode h.at_exit (congrArg Prod.fst h.halt.decode)
  · exact hout.trans (ReferenceReturnSlice.output_eq_extract hrel off len)
  · rw [hcost]; exact hevents

theorem Whole.observed {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {w : Warm} {meter : ReferenceStorageGas.Meter}
    (whole : Whole parent created h v w meter) :
    ReferenceSystemTrace.Observed (parent := parent) h v := by
  obtain ⟨_,_,_,finish,_,off,len,rest,hcoupled,hrel,_,_,hdecode,hshape,hresult,hout,_⟩ := whole
  exact ⟨finish,off,len,rest,hcoupled.viewed,hrel,hdecode,hshape,hresult,hout⟩

theorem Whole.paid {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {w : Warm} {meter : ReferenceStorageGas.Meter}
    (whole : Whole parent created h v w meter) :
    Paid (ReferenceSourceReadings.inputs parent created) h meter := by
  obtain ⟨prefixEvents,events,final,_,_,_,_,_,hc,_,_,_,_,_,_,_,hcost,hevents,hpaid,he,hr,_⟩ := whole
  refine ⟨prefixEvents,events,final,hc.priced,?_,?_,hpaid,he,hr⟩
  · exact ⟨0,rfl,by simp⟩
  · rw [hcost] at hevents; exact hevents

#print axioms attach
#print axioms Whole.observed
#print axioms Whole.paid
end Eip8282.Audit.Integrator.ReferenceSystemSourcePayment
