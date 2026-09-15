import Eip8282.Audit.Integrator.SystemMemoryResources
import Eip8282.Audit.Integrator.ReferenceOrdinaryGas
import Eip8282.Audit.Integrator.Topics.ReferenceMeter2

/-! Source-meter events constructed from one actual successful SYSTEM trace.
Warmth and original/current/new storage readings are universally parameterized:
the resource bound holds for every reading, rather than assuming an actual
reference replay. The remaining reference-state/dispatch adapter must bind those
readings, instruction effects, checked types and this meter to its execution. -/
namespace Eip8282.Audit.Integrator.SystemMeterResources
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall)
open RuntimeExecutionScope SystemTraceAnnotations SystemPathBudget
open RuntimeMemoryCharges SystemExecutionResources ReferenceMeterPath
open ReferenceMemoryCapacity (cost)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

structure Reading where
  warm : Bool
  original : UInt256
  current : UInt256
  new : UInt256

abbrev Inputs := EVM.State → Reading

def delta (pre post : EVM.State) : Nat := cost post.activeWords.toNat-cost pre.activeWords.toNat

/-- The operation's literal source price uses the selected reading and actual
memory expansion. In particular SSTORE cannot hide a memory charge. -/
def EdgePrice (inputs : Inputs) (pre post : EVM.State) (op : Operation .EVM) (event : Event) : Prop :=
  if op = .SSTORE then delta pre post = 0 ∧
    event = .store (inputs pre).warm (inputs pre).original (inputs pre).current (inputs pre).new
  else ∃ n, ReferenceOrdinaryGas.ordinaryCost op (inputs pre).warm = some n ∧
    event = .ordinary (n+delta pre post)

theorem edge {image : Image} (inputs : Inputs) {pre post : EVM.State} {fuel gasCost : Nat}
    (hat : At image pre) (hs : XStepAt (D_J image.code ⟨0⟩) fuel gasCost pre post)
    (ha : Allowed (decodeAt pre).1) :
    ∃ event, EdgePrice inputs pre post (decodeAt pre).1 event ∧
      executionBudget event ≤ 2100+12100*storeWeight (decodeAt pre).1+delta pre post ∧
      stateBudget event = 97920*storeWeight (decodeAt pre).1 := by
  by_cases hstore : (decodeAt pre).1 = .SSTORE
  · obtain ⟨mid,hz,hstep,_⟩ := hs
    have hm := accepted_expansion hat hz hstep
    have hsame : post.activeWords.toNat = pre.activeWords.toNat := by
      simpa [hstore,RuntimeMemoryMonotone.span,MachineState.M] using hm
    refine ⟨.store (inputs pre).warm (inputs pre).original (inputs pre).current (inputs pre).new,?_,?_,?_⟩
    · simp [EdgePrice,hstore,delta,hsame]
    · simp only [executionBudget,storeWeight,hstore,↓reduceIte]
      omega
    · simp [stateBudget,storeWeight,hstore]
  · obtain ⟨n,hc,hn⟩ := ReferenceOrdinaryGas.defined_bound (inputs pre).warm ha hstore
    refine ⟨.ordinary (n+delta pre post),?_,?_,?_⟩
    · unfold EdgePrice
      rw [if_neg hstore]
      exact ⟨n,hc,rfl⟩
    · simp only [executionBudget,storeWeight,if_neg hstore]; omega
    · simp [stateBudget,storeWeight,hstore]

/-- Each price is attached to the actual instruction and intermediate state. -/
inductive PricedTrace (inputs : Inputs) (vj : Array UInt256) :
    Nat → EVM.State → List Labelled → Nat → EVM.State → List Event → Prop where
  | refl (fuel : Nat) (pre : EVM.State) : PricedTrace inputs vj fuel pre [] fuel pre []
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {trace : List Labelled}
      {event : Event} {events : List Event}
      (step : XStepAt vj fuel gasCost pre mid)
      (price : EdgePrice inputs pre mid (decodeAt pre).1 event)
      (tail : PricedTrace inputs vj fuel mid trace rem post events) :
      PricedTrace inputs vj (fuel+1) pre ((fuel,gasCost,decodeAt pre)::trace) rem post (event::events)

theorem from_charges {image : Image} (inputs : Inputs) {fuel rem total : Nat}
    {pre post : EVM.State} {trace : List Labelled} (hat : At image pre)
    (hc : TraceCharges (D_J image.code ⟨0⟩) fuel pre trace rem post total)
    (ha : ∀ op ∈ operations trace, Allowed op) :
    ∃ events, PricedTrace inputs (D_J image.code ⟨0⟩) fuel pre trace rem post events ∧
      sumExec events ≤ 2100*trace.length+12100*weight storeWeight (operations trace)+total ∧
      sumState events = 97920*weight storeWeight (operations trace) := by
  revert hat ha
  induction hc with
  | refl => intro _ _; exact ⟨[],.refl _ _,by simp [sumExec,weight,operations],by simp [sumState,weight,operations]⟩
  | @cons fuel gasCost rem total pre mid post trace step tail ih =>
    intro hat ha
    obtain ⟨event,he,hex,hst⟩ := edge inputs hat step (ha _ (by simp [operations]))
    obtain ⟨charged,hz,hstep,hh⟩ := step
    obtain ⟨events,ht,htx,hts⟩ := ih (accepted_next hat hz hstep hh)
      (fun op hop => ha op (by simp [operations] at hop ⊢; exact Or.inr hop))
    refine ⟨event::events,.cons ⟨charged,hz,hstep,hh⟩ he ht,?_,?_⟩
    · simp only [sumExec,List.map_cons,List.sum_cons,List.length_cons,operations,List.map_cons,
        weight,List.sum_cons,Nat.mul_add,Nat.mul_one] at *
      unfold delta at hex
      omega
    · simp only [sumState,List.map_cons,List.sum_cons,operations,List.map_cons,weight,List.sum_cons,Nat.mul_add] at *
      omega

/-- Payment is constructed for this complete execution, including RETURN.
Only aggregate initial resources are needed; payment derives every sentry. -/
theorem pay_completed {image : Image} (inputs : Inputs) {steps cap outputBytes fuel : Nat}
    {pre : EVM.State} (h : Completed image steps cap outputBytes fuel pre)
    (hat : At image pre) (output_fit : outputBytes ≤ 32*cap)
    (initial : ReferenceStorageGas.Meter)
    (execution : 2100*(steps+1)+12100*4+cost cap ≤ initial.execution)
    (reservoir : 97920*4 ≤ initial.reservoir) :
    ∃ prefixEvents events final,
      PricedTrace inputs (D_J image.code ⟨0⟩) fuel pre h.trace (h.rem+2) h.exitState prefixEvents ∧
      EdgePrice inputs h.exitState h.finalState .RETURN (.ordinary (delta h.exitState h.finalState)) ∧
      events = prefixEvents++[.ordinary (delta h.exitState h.finalState)] ∧
      run events initial = some final ∧
      initial.execution-(2100*(steps+1)+12100*4+cost cap) ≤ final.execution ∧
      initial.reservoir-97920*4 ≤ final.reservoir := by
  obtain ⟨total,⟨prefixCost,hc,hcost⟩,_,_,hbound⟩ := SystemMemoryResources.attach h hat output_fit
  have ha : ∀ op ∈ operations h.trace, Allowed op := fun op hop => h.allowed op (List.mem_append_left _ hop)
  obtain ⟨events,hp,he,hs⟩ := from_charges inputs hat hc ha
  have hlen : h.trace.length ≤ steps := by simpa [operations] using h.operations_bound
  have hstores : weight storeWeight (operations h.trace) ≤ 4 := by
    simpa [weight_append,weight,storeWeight] using h.stores_bound
  let whole := events++[Event.ordinary (delta h.exitState h.finalState)]
  have hE : sumExec whole ≤ 2100*(steps+1)+12100*4+cost cap := by
    have hb := (budgets_append events [Event.ordinary (delta h.exitState h.finalState)]).1
    change sumExec whole = sumExec events + delta h.exitState h.finalState at hb
    unfold delta at hb
    omega
  have hS : sumState whole ≤ 97920*4 := by
    have hb := (budgets_append events [Event.ordinary (delta h.exitState h.finalState)]).2
    change sumState whole = sumState events+0 at hb
    omega
  obtain ⟨final,hf,hfe,hfr⟩ := payment whole initial (hE.trans execution) (hS.trans reservoir)
  refine ⟨events,whole,final,hp,?_,rfl,hf,by omega,by omega⟩
  exact ⟨0,rfl,by simp⟩

/-- Proposed pinned dispatcher grant; this declaration does not adopt a fork. -/
def systemMeter : ReferenceStorageGas.Meter :=
  { execution := 30000000, reservoir := 16*97920, spill := 0, refund := 0 }


/-- Both the complete evaluator result and each source-meter event remain
available to the reference-execution adapter. -/
def Paid {image : Image} {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (inputs : Inputs) (h : Completed image steps cap outputBytes fuel pre)
    (initial : ReferenceStorageGas.Meter) : Prop :=
  ∃ prefixEvents events final,
    PricedTrace inputs (D_J image.code ⟨0⟩) fuel pre h.trace (h.rem+2) h.exitState prefixEvents ∧
    EdgePrice inputs h.exitState h.finalState .RETURN (.ordinary (delta h.exitState h.finalState)) ∧
    events = prefixEvents++[.ordinary (delta h.exitState h.finalState)] ∧
    run events initial = some final ∧
    initial.execution-(2100*(steps+1)+12100*4+cost cap) ≤ final.execution ∧
    initial.reservoir-97920*4 ≤ final.reservoir

theorem deposit (inputs : Inputs) (c : XiCall .deposit)
    (system : Deposit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 8502 ≤ c.fuel) :
    ∃ h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry,
      Paid inputs h systemMeter := by
  obtain ⟨h⟩ := SystemExecutionResources.deposit c system permission (by rw [gas]; decide) fuel
  exact ⟨h,pay_completed inputs h ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    (by decide) systemMeter (by decide) (by decide)⟩

theorem exit (inputs : Inputs) (c : XiCall .exit)
    (system : Exit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 802 ≤ c.fuel) :
    ∃ h : Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry,
      Paid inputs h systemMeter := by
  obtain ⟨h⟩ := SystemExecutionResources.exit c system permission (by rw [gas]; decide) fuel
  exact ⟨h,pay_completed inputs h ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
    (by decide) systemMeter (by decide) (by decide)⟩

/-- Arithmetic only; the two constructors above supply its actual traces. -/
theorem envelopes :
    2100*(8500+1)+12100*4+cost 400 = 17902012 ∧
    2100*(800+1)+12100*4+cost 40 = 1730623 ∧
    97920*4 = 391680 := by decide +kernel

#print axioms edge
#print axioms from_charges
#print axioms pay_completed
#print axioms deposit
#print axioms exit
#print axioms envelopes
end Eip8282.Audit.Integrator.SystemMeterResources
