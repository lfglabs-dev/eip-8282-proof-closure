import Eip8282.Audit.Integrator.ReferenceActionControlAdmission
import Eip8282.Audit.Integrator.ReferenceActionStackBounds
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.ReferenceAppendOccurrences
import Eip8282.Audit.Integrator.ReferenceExecutionLedger
import Eip8282.Audit.Integrator.ReferenceRuntimeCompletion
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime
import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.ResourceBounds
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCoupledPrefix -/

/-! Split the same source-priced actual trace at an actual earlier endpoint.
The earlier length is not guessed: exact instruction determinism identifies its
steps, and remaining fuel proves it is contained in the supplied whole trace. -/
namespace Eip8282.Audit.Integrator.ReferenceCoupledPrefix
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem same_fuel {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p created fuel pre v w trace fuel post last finalWarm events) :
    trace = [] ∧ events = [] := by
  cases h with
  | refl => exact ⟨rfl,rfl⟩
  | cons actual decoded related nextRelated warm created_eq action readings price tail =>
    have bound := tail.viewed.erase.rem_le
    omega

theorem split_at {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel middleFuel rem : Nat} {pre middle post : EVM.State} {v last : View} {w finalWarm : Warm}
    {earlier trace : List Labelled} {events : List Event}
    (head : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre earlier middleFuel middle)
    (whole : Coupled kind p created fuel pre v w trace rem post last finalWarm events)
    (fits : rem ≤ middleFuel) :
    ∃ middleView middleWarm tail firstEvents restEvents,
      trace = earlier++tail ∧ events = firstEvents++restEvents ∧
      Coupled kind p created fuel pre v w earlier middleFuel middle middleView middleWarm firstEvents ∧
      Coupled kind p created middleFuel middle middleView middleWarm tail rem post last finalWarm restEvents := by
  induction head generalizing v w trace events with
  | refl => exact ⟨v,w,trace,[],events,rfl,rfl,.refl _ _ _ _,whole⟩
  | @cons fuel gasCost middleFuel pre mid middle earlier actual tail ih =>
    cases whole with
    | refl => have bound := tail.rem_le; omega
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ event _ other decoded related nextRelated warm created_eq action readings price rest =>
      obtain ⟨rfl,rfl⟩ := XStepAt.deterministic actual other
      obtain ⟨middleView,middleWarm,remaining,firstEvents,restEvents,ht,he,hfirst,hrest⟩ := ih rest fits
      refine ⟨middleView,middleWarm,remaining,event::firstEvents,restEvents,?_,?_,?_,hrest⟩
      · simp only [List.cons_append,ht]
      · simp only [List.cons_append,he]
      · exact .cons actual decoded related nextRelated warm created_eq action readings price hfirst

#print axioms same_fuel
#print axioms split_at
end Eip8282.Audit.Integrator.ReferenceCoupledPrefix

end

section

/-! ## ReferenceAppendPrice -/

/-! Price actual selected append instructions on the same Coupled execution.
All store classes cost at least100 execution gas, even if slots alias or a write
is a no-op. LOG length comes from the actual stack. Selection is ordered and
nonoverlapping, including the tail store after LOG. -/
namespace Eip8282.Audit.Integrator.ReferenceAppendPrice
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceAppendOccurrences ReferenceExecutionLedger ReferenceCoupledPrefix
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def markerWork : Marker → Nat
  | .store => 100
  | .log len => 375+8*len.toNat

def selectedWork (markers : List Marker) : Nat := (markers.map markerWork).sum

theorem marker_price {p : Parent} {pre : EVM.State} {v next : View} {w : Warm}
    {marker : Marker} {event : Event} (mark : Matches marker pre)
    (related : Related p v pre) (price : Price p v w next (decodeAt pre).1 event) :
    markerWork marker ≤ eventWork event := by
  cases marker with
  | store =>
    change decodeAt pre = (.SSTORE,none) at mark
    simp only [Price,mark,↓reduceIte] at price
    rw [price.2]
    simp only [markerWork,eventWork,ReferenceStorageGas.classify]
    split <;> omega
  | log len =>
    obtain ⟨decoded,off,rest,hstack⟩ := mark
    simp only [Price,decoded,show (Operation.LOG0 : Operation .EVM) ≠ .SSTORE by decide,↓reduceIte] at price
    obtain ⟨n,hcost,rfl⟩ := price
    rw [related.stack,hstack] at hcost
    have hn : 375+8*len.toNat = n := Option.some.inj hcost
    simp only [markerWork,eventWork]
    omega

/-- The actual earlier split threads source views, warmth and prices at the
same intermediate state. It introduces no arbitrary second event sequence. -/
theorem selected_cost {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {markers : List Marker}
    (marked : Marked (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre rem post markers)
    (priced : Coupled kind p created fuel pre v w trace rem post last finalWarm events) :
    selectedWork markers ≤ work events := by
  induction marked generalizing v last w finalWarm trace events with
  | skip run => exact Nat.zero_le _
  | single actual mark =>
    cases priced with
    | cons other decoded related nextRelated warm created_eq action readings price tail =>
      have empty := same_fuel tail
      have hm := marker_price mark related price
      simp only [work,List.map_cons,List.sum_cons,empty.2,List.map_nil,List.sum_nil,Nat.add_zero]
      simpa only [selectedWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hm
  | trans first second ih1 ih2 =>
    obtain ⟨earlier,hprefix,_⟩ := first.erase
    obtain ⟨suffix,hsuffix,_⟩ := second.erase
    obtain ⟨middleView,middleWarm,remaining,firstEvents,restEvents,ht,he,hfirst,hrest⟩ :=
      split_at hprefix priced hsuffix.rem_le
    have h1 := ih1 hfirst
    have h2 := ih2 hrest
    simp only [selectedWork,List.map_append,List.sum_append] at h1 h2 ⊢
    rw [he]
    simp only [work,List.map_append,List.sum_append] at h1 h2 ⊢
    omega

theorem exact_marker_costs : selectedWork exitMarkers = 1419 ∧ selectedWork depositMarkers = 2647 := by
  decide +kernel

#print axioms marker_price
#print axioms selected_cost
#print axioms exact_marker_costs
end Eip8282.Audit.Integrator.ReferenceAppendPrice

end

section

/-! ## ReferenceTraceAgreement -/

/-! Uniqueness of a complete actual nonhalting instruction trace. This lets a
structural append path and a source-priced protected runtime certificate share
exactly one trace, without assuming equal lengths or supplying a second desired
instruction list. The result concerns the pinned evaluator's actual XRuns. -/
namespace Eip8282.Audit.Integrator.ReferenceTraceAgreement
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Blocked (vj : Array UInt256) (fuel : Nat) (pre : EVM.State) : Prop :=
  ∀ cost next, ¬ XStepAt vj (fuel-1) cost pre next

theorem blocked_of_stop {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    (decoded : decodeAt pre = (.STOP,none)) : Blocked vj fuel pre := by
  intro cost next h
  obtain ⟨mid,hz,hs,hh⟩ := h
  rw [decoded] at hh
  simp [H] at hh

theorem blocked_of_terminal {vj : Array UInt256} {fuel cost : Nat}
    {pre mid post : EVM.State} {out : ByteArray}
    (charged : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (step : StepOk (fuel-1) cost (decodeAt pre) mid post)
    (halted : H post.toMachineState (decodeAt pre).1 = some out) : Blocked vj fuel pre := by
  intro otherCost next h
  obtain ⟨otherMid,hz,hs,hh⟩ := h
  rw [charged] at hz
  obtain ⟨rfl,rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hz
  have he := Step.deterministic_ok step hs
  subst next
  rw [halted] at hh
  contradiction

theorem complete_unique {vj : Array UInt256} {fuel rem₁ rem₂ : Nat}
    {pre exit₁ exit₂ : EVM.State} {trace₁ trace₂ : List Labelled}
    (first : XRuns vj fuel pre trace₁ rem₁ exit₁)
    (second : XRuns vj fuel pre trace₂ rem₂ exit₂)
    (end₁ : Blocked vj rem₁ exit₁) (end₂ : Blocked vj rem₂ exit₂) :
    trace₁ = trace₂ ∧ rem₁ = rem₂ ∧ exit₁ = exit₂ := by
  induction first generalizing rem₂ exit₂ trace₂ with
  | refl fuel pre =>
    cases second with
    | refl => exact ⟨rfl,rfl,rfl⟩
    | cons step tail =>
      exact False.elim (end₁ _ _ (by simpa only [Nat.add_sub_cancel] using step))
  | @cons fuel gasCost rem pre mid post trace step tail ih =>
    cases second with
    | refl =>
      exact False.elim (end₂ _ _ (by simpa only [Nat.add_sub_cancel] using step))
    | cons otherStep otherTail =>
      obtain ⟨rfl,rfl⟩ := XStepAt.deterministic step otherStep
      obtain ⟨ht,hr,hp⟩ := ih otherTail end₁ end₂
      exact ⟨by rw [ht],hr,hp⟩

#print axioms blocked_of_stop
#print axioms blocked_of_terminal
#print axioms complete_unique
end Eip8282.Audit.Integrator.ReferenceTraceAgreement

end

section

/-! ## ReferenceAppendCompletedCost -/

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

end

section

/-! ## ReferenceReplayAdmission -/

/-! Construct actual old Z admission from source-shaped action guards and a
synthetic sufficient budget. The budget is explicit and must be derived from
source work; this theorem never equates source and old gas meters. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayAdmission
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Protected opcode prices do not read the synthetic gas/step counters. -/
theorem base_charged (pre : EVM.State) (op : Operation .EVM)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps) :
    C' (zMid pre op) op = C' pre op := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem base_replay (pre : EVM.State) (op : Operation .EVM) (cost : Nat)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps) :
    C' (stepPre cost (zMid pre op)) op = C' pre op := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- All non-gas guards are produced from the same running action and source
stack bound. The reserve also discharges the actual SSTORE sentry after memory
has been charged, in the order used by Z. -/
theorem z {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View} {pre : EVM.State}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : Action kind parent (decodeAt pre) v next)
    (postbounded : next.stack.length ≤ 1024)
    (budget : C' pre (decodeAt pre).1+memoryExpansionCost pre (decodeAt pre).1+2301 ≤ pre.gasAvailable.toNat) :
    Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre =
      .ok (zMid pre (decodeAt pre).1,C' pre (decodeAt pre).1) := by
  have allowed := RuntimeExecutionScope.opcode_allowed site
  have bounds := ReferenceActionStackBounds.admission effect postbounded
  rw [related.stack] at bounds
  have jumps := ReferenceActionControlAdmission.jump_guards related effect
  have others := ReferenceActionControlAdmission.other_guards site
  have hm : memoryExpansionCost pre (decodeAt pre).1 ≤ pre.gasAvailable.toNat := by omega
  have hg : (charged pre (decodeAt pre).1).gasAvailable.toNat =
      pre.gasAvailable.toNat-memoryExpansionCost pre (decodeAt pre).1 := toNat_sub_ofNat hm
  have hb := base_charged pre (decodeAt pre).1 allowed
  have result := Z_of_facts (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre
    hm (by change C' (zMid pre (decodeAt pre).1) _ ≤ _; rw [hb,hg]; omega)
    others.1 others.2.1 bounds.1 bounds.2 jumps.1 jumps.2 others.2.2.1
    (ReferenceActionControlAdmission.static_guard related effect)
    (fun _ => by change 2300 < _; rw [hg]; omega) others.2.2.2
  change Z _ _ pre = .ok (zMid pre (decodeAt pre).1,C' (zMid pre (decodeAt pre).1) (decodeAt pre).1) at result
  rw [hb] at result
  exact result

#print axioms base_charged
#print axioms base_replay
#print axioms z
end Eip8282.Audit.Integrator.ReferenceReplayAdmission

end

section

/-! ## ReferenceReplayCost -/

/-! A coarse synthetic execution budget for protected effect replay. This
compares old opcode prices with literal source execution prices, without
identifying the two gas meters or their original-storage/warmth histories.
Memory expansion and source stack/decoder admission are separate obligations.
The factor is a proof budget, never a change to the runtime's actual tariff. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceExecutionLedger
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem ordinary_ratio {op : Operation .EVM} {n : Nat} (pre : EVM.State) (warm : Bool)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps)
    (price : ReferenceOrdinaryGas.ordinaryCost op warm = some n) : C' pre op ≤ 221*n := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp_all [ReferenceOrdinaryGas.ordinaryCost]; done)
    | (simp_all +decide [C',ReferenceOrdinaryGas.ordinaryCost,GasConstants.Gzero,GasConstants.Gbase,
        GasConstants.Gverylow,GasConstants.Glow,GasConstants.Gmid,GasConstants.Ghigh,GasConstants.Gjumpdest,
        Csload,GasConstants.Gcoldsload,GasConstants.Gwarmaccess]
       try split_ifs at *
       all_goals omega)

/-- The same stack supplies COPY and LOG lengths. SSTORE uses the universal
old22100 upper bound and the actual source class's100 lower bound; no equality
of original-state or warm sets is needed for this deliberately coarse ratio. -/
theorem opcode_ratio {op : Operation .EVM} {p : Parent} {v next : View} {w : Warm} {event : Event}
    (pre : EVM.State) (stack : pre.stack = v.stack) (allowed : op ∈ RuntimeOpcodeScope.allowedOps)
    (price : Price p v w next op event) : C' pre op ≤ 221*eventWork event := by
  by_cases hs : op = .SSTORE
  · subst op
    simp only [Price,↓reduceIte] at price
    rw [price.2]
    have upper := Csstore_le pre
    have lower : 100 ≤ (ReferenceStorageGas.classify (sourceReading p v w).warm
        (sourceReading p v w).original (sourceReading p v w).current (sourceReading p v w).new).execution := by
      simp only [ReferenceStorageGas.classify]
      split <;> omega
    change Csstore pre ≤ _
    simp only [GasConstants.Gcoldsload,GasConstants.Gsset] at upper
    simp only [eventWork]
    omega
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,computed,rfl⟩ := price
    have base : C' pre op ≤ 221*n := by
      by_cases hc : op = .CALLDATACOPY
      · subst op
        have hn : ReferenceCopyLogGas.copyCost v.stack[2]!.toNat = n := Option.some.inj computed
        have hold : C' pre .CALLDATACOPY = ReferenceCopyLogGas.copyCost v.stack[2]!.toNat := by
          simp +decide [C',ReferenceCopyLogGas.copyCost,stack,GasConstants.Gverylow,GasConstants.Gcopy]
        omega
      · by_cases hl : op = .LOG0
        · subst op
          have hn : ReferenceCopyLogGas.logCost v.stack[1]!.toNat = n := Option.some.inj computed
          have hold : C' pre .LOG0 = ReferenceCopyLogGas.logCost v.stack[1]!.toNat := by
            simp [C',ReferenceCopyLogGas.logCost,stack,GasConstants.Glog,GasConstants.Glogdata]
          omega
        · simp only [ReferenceCopyLogGas.ordinaryCost,if_neg hc,if_neg hl] at computed
          exact ordinary_ratio pre _ allowed computed
    simp only [eventWork]
    omega

#print axioms opcode_ratio
end Eip8282.Audit.Integrator.ReferenceReplayCost

end

section

/-! ## ReferenceReplayMemoryCost -/

/-! Synthetic total replay budget from the same raw effects and literal source
prices. Memory correspondence is derived from raw metadata, before Z admission.
The source resource ledger remains separate; 222 is a conservative proof budget.
No bound on the number of fee-loop iterations is imposed. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayMemoryCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open RuntimeOpcodeScope RuntimeMemoryMonotone
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceExecutionLedger
open ReferenceMemoryCapacity (cost)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem predicted (pre : EVM.State) (op : Operation .EVM) (hop : op ∈ allowedOps) :
    (memoryExpansionCost.μᵢ' pre op).toNat =
      MachineState.M pre.activeWords.toNat (span pre op).1 (span pre op).2 := by
  simp only [allowedOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[1]!)
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[2]!)
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 32 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 1 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))

/-- Both memory potentials concern this actual raw step, not a post-state
chosen independently to satisfy a desired charge. -/
theorem raw_memory {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} {parent : Parent} {v next : View}
    (allowed : op ∈ allowedOps) (related : Related parent v pre)
    (nextRelated : Related parent next post)
    (raw : EvmYul.step op arg pre = .ok post) :
    memoryExpansionCost pre op = cost (words next)-cost (words v) := by
  have hp := predicted pre op allowed
  have hm := RuntimeMemoryCharges.raw_expansion allowed raw
  change cost (memoryExpansionCost.μᵢ' pre op).toNat-cost pre.activeWords.toNat = _
  rw [hp,←hm,words_related related,words_related nextRelated]

theorem memory_component {op : Operation .EVM} {parent : Parent}
    {v next : View} {warm : Warm} {event : Event}
    (price : Price parent v warm next op event) :
    cost (words next)-cost (words v) ≤ eventWork event := by
  by_cases hs : op = .SSTORE
  · simp only [Price,if_pos hs] at price
    rw [price.1]
    exact Nat.zero_le _
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,_,rfl⟩ := price
    simp only [eventWork]
    omega

/-- Opcode and memory charges are counted separately, so the coarse opcode
ratio never spends a memory summand twice. -/
theorem total_ratio {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} {parent : Parent} {v next : View} {warm : Warm} {event : Event}
    (allowed : op ∈ allowedOps) (related : Related parent v pre)
    (nextRelated : Related parent next post)
    (raw : EvmYul.step op arg pre = .ok post)
    (price : Price parent v warm next op event) :
    C' pre op+memoryExpansionCost pre op ≤ 222*eventWork event := by
  have hb := ReferenceReplayCost.opcode_ratio pre related.stack.symm allowed price
  have hm := memory_component price
  rw [←raw_memory allowed related nextRelated raw] at hm
  omega

/-- This numerical transport applies to a work bound already derived from the
source ledger (transaction cap or SYSTEM grant). It does not produce that ledger
or turn the synthetic budget into gas actually supplied by Ethereum. -/
theorem word_fit {work : Nat} (bounded : work ≤ 30000000) :
    222*work+2301 < UInt256.size := by
  have small : 222*30000000+2301 < UInt256.size := by decide +kernel
  omega

#print axioms raw_memory
#print axioms memory_component
#print axioms total_ratio
#print axioms word_fit
end Eip8282.Audit.Integrator.ReferenceReplayMemoryCost

end

section

/-! ## ReferenceResourceEntryBound -/

/-! Potential bounds at nested entries of the literal resource ledger. This
relation retains actual ledger branches and grant equations, but is deliberately
NOT an occurrence identity: proofs are propositions, and no path uniqueness or
source frame coverage is asserted. Actual source tree extraction remains open.
No Selected premise, fixed internal cap, or net-state sign hypothesis occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceResourceEntryBound
open EvmYul
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCallGrant
open ReferenceChildMeter ReferenceCallChildBoundary ReferenceExecutionPotential
open ReferenceCallPotential ReferenceExecutionLedger
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual prior CALL charges cover the stipend before granting the child. -/
theorem call_entry {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre charged : Meter}
    (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
    (requested : UInt256) : potential (start (split hasValue requested charged)) ≤ potential pre := by
  have hp := prepared_debit prepared
  have hg := split_potential hasValue requested charged
  have ho := overhead_exact cold delegated delegationCold hasValue memoryCost
  have hi : potential (start (split hasValue requested charged)) =
      (split hasValue requested charged).childExecution := by simp [start,init,potential]
  omega

/-- State charging transfers between pools without creating execution potential. -/
theorem creation_entry {pre : Meter} {chargedCore : ReferenceStorageGas.Meter} {amount : Nat}
    (charged : ReferenceStorageGas.chargeState (core pre) amount = some chargedCore) :
    potential (start (creationSplit (update pre chargedCore))) ≤ potential pre := by
  have hp := state_preserves charged
  have hg := creation_potential (update pre chargedCore)
  omega

/-- A nested resource entry, with all surrounding ledger evidence retained.
This relation supports a numeric bound only; it does not identify unique nodes. -/
inductive EntryAt : Meter → Meter → Nat → Meter → Prop where
  | here {pre post : Meter} {work : Nat} (actual : Run pre post work) : EntryAt pre post work pre
  | left {pre mid post node : Meter} {first second : Nat}
      (head : EntryAt pre mid first node) (tail : Run mid post second) :
      EntryAt pre post (first+second) node
  | right {pre mid post node : Meter} {first second : Nat}
      (head : Run pre mid first) (tail : EntryAt mid post second node) :
      EntryAt pre post (first+second) node
  | call {pre charged child final node : Meter} {childWork : Nat}
      (cold delegated delegationCold hasValue deadRecipient : Bool) (memoryCost : Nat)
      (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
      (requested : UInt256) (outcome : Outcome)
      (body : EntryAt (start (split hasValue requested charged)) child childWork node)
      (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
      EntryAt pre final (overhead cold delegated delegationCold hasValue memoryCost+childWork) node
  | create {pre child final node : Meter} {chargedCore : ReferenceStorageGas.Meter} {childWork : Nat}
      (stateAmount : Nat) (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
      (outcome : Outcome) (newAccount : Bool)
      (body : EntryAt (start (creationSplit (update pre chargedCore))) child childWork node)
      (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
      EntryAt pre final childWork node

theorem EntryAt.sound_top {pre post node : Meter} {work : Nat} (h : EntryAt pre post work node) :
    Run pre post work := by
  induction h with
  | here actual => exact actual
  | left head tail ih => exact .trans ih tail
  | right head tail ih => exact .trans head ih
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact .call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome ih finished
  | create stateAmount charged outcome newAccount body finished ih =>
    exact .create stateAmount charged outcome newAccount ih finished

theorem EntryAt.potential_le {pre post node : Meter} {work : Nat} (h : EntryAt pre post work node) :
    potential node ≤ potential pre := by
  induction h with
  | here actual => exact Nat.le_refl _
  | left head tail ih => exact ih
  | right head tail ih =>
    have bound := bounded head
    omega
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact ih.trans (call_entry prepared requested)
  | create stateAmount charged outcome newAccount body finished ih =>
    exact ih.trans (creation_entry charged)

theorem EntryAt.cap {pre post node : Meter} {work cap : Nat} (h : EntryAt pre post work node)
    (bound : potential pre ≤ cap) : potential node ≤ cap := h.potential_le.trans bound

#print axioms call_entry
#print axioms creation_entry
#print axioms EntryAt.sound_top
#print axioms EntryAt.potential_le
#print axioms EntryAt.cap
end Eip8282.Audit.Integrator.ReferenceResourceEntryBound

end

section

/-! ## ReferenceTransactionWork -/

/-! Source execution allocation and calldata floor consume the finite nested
resource ledger. No nonnegative net-state premise is needed for the comparison
with block execution charge. Actual source transaction/frame/block extraction
and the completed-append instruction-cost producer remain explicit inputs.
The arithmetic does not manufacture a completed append count from LOG0 alone. -/
namespace Eip8282.Audit.Integrator.ReferenceTransactionWork
open EvmYul ReferenceMeterRollback ReferenceExecutionPotential ReferenceExecutionLedger
open ReferenceTransactionGas
set_option autoImplicit false

def initial (txGas intrinsic : Nat) : Meter :=
  ReferenceChildMeter.init (allocate txGas intrinsic).execution (allocate txGas intrinsic).reservoir

theorem allocated_work {txGas intrinsic executed : Nat} {post : Meter}
    (h : Run (initial txGas intrinsic) post executed)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    intrinsic+executed ≤ 16777216 := by
  have hrun := bounded h
  have halloc := allocation txGas intrinsic affords maximum
  simp only [initial,ReferenceChildMeter.init,potential,Nat.add_zero] at hrun
  omega

/-- The 1419 premise is a structural completed-append cost certificate, to be
produced on actual disjoint completed protected frames. It is never an
admission condition or a count bound assumed about a canonical history. -/
theorem appends_le_execution_charge {txGas intrinsic executed appends : Nat} {post : Meter}
    (h : Run (initial txGas intrinsic) post executed)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216)
    (completedCost : 1419*appends ≤ executed)
    (dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat)
    (refund : UInt256) (netState : Int) :
    appends ≤ 11823 ∧
    appends ≤ (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
      gasLeft stateLeft refund netState).executionUsed := by
  have hw := allocated_work h affords maximum
  have hf : 12000 ≤ ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens := by
    simp only [ReferenceCalldataAdmission.floor]
    omega
  have he : ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens ≤
      (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
        gasLeft stateLeft refund netState).executionUsed := Nat.le_max_right _ _
  omega

/-- The sender refund and signed state usage may vary arbitrarily here; the
same literal source execution settlement is always at least its calldata floor.
Checked Uint subtraction validity is still required by the source adapter. -/
theorem floor_execution (txGas dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat)
    (refund : UInt256) (netState : Int) :
    12000 ≤ (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
      gasLeft stateLeft refund netState).executionUsed := by
  have h : 12000 ≤ ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens := by
    simp only [ReferenceCalldataAdmission.floor]
    omega
  exact h.trans (Nat.le_max_right _ _)

#print axioms allocated_work
#print axioms appends_le_execution_charge
#print axioms floor_execution
end Eip8282.Audit.Integrator.ReferenceTransactionWork

end

section

/-! ## ReferenceSelectedAppendWork -/

/-! Actual completed protected payments supply the leaf costs in a finite
nested resource ledger. Selection denotes a subset of executed completed
frames, not the full protocol occurrence enumeration. In particular skipped
resource runs may contain unselected appends. A retained-history consumer must
produce this selection for every retained occurrence, with its source journals;
that extraction is not assumed complete merely because the arithmetic closes.
Selected child work remains counted when its parent later reverts. -/
namespace Eip8282.Audit.Integrator.ReferenceSelectedAppendWork
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Jumpdests
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCallGrant ReferenceChildMeter ReferenceCallChildBoundary
open ReferenceExecutionLedger ReferenceCallPotential ReferenceAppendCompletedCost
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive ProtectedPaid : Meter → Meter → Nat → Prop where
  | exit (c : XiCall .exit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
      (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
      (actual : X fuel exitJumpdests c.entry = .ok (.success final out))
      (t : SuccessInversion.SuccessTrace exitJumpdests fuel c.entry final out)
      {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
      (priced : Coupled .exit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events)
      {pre post : Meter} (amount : Nat) (paid : runFull (events++[.ordinary amount]) pre = some post) :
      ProtectedPaid pre post (work (events++[.ordinary amount]))
  | deposit (c : XiCall .deposit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
      (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
      (actual : X fuel depositJumpdests c.entry = .ok (.success final out))
      (t : SuccessInversion.SuccessTrace depositJumpdests fuel c.entry final out)
      {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
      (priced : Coupled .deposit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events)
      {pre post : Meter} (amount : Nat) (paid : runFull (events++[.ordinary amount]) pre = some post) :
      ProtectedPaid pre post (work (events++[.ordinary amount]))

theorem ProtectedPaid.cost {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) :
    1419 ≤ executed := by
  cases h with
  | exit c user size actual t priced amount paid =>
    have bound := exit_cost c user size actual t priced
    simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      eventWork,Nat.add_zero] at bound ⊢
    omega
  | deposit c user size actual t priced amount paid =>
    have bound := deposit_cost c user size actual t priced
    simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      eventWork,Nat.add_zero] at bound ⊢
    omega

theorem ProtectedPaid.run {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) :
    Run pre post executed := by
  cases h with
  | exit c user size actual t priced amount paid => exact .paid _ paid
  | deposit c user size actual t priced amount paid => exact .paid _ paid

/-- Sequential pieces share exact returned meters. A selected protected leaf
contains its whole actual append trace, so it cannot also count a child or a
second overlapping piece of that same resource payment. Protocol occurrence
identity/completeness must still be supplied when constructing this selection. -/
inductive Selected : Meter → Meter → Nat → Nat → Prop where
  | skip {pre post : Meter} {executed : Nat} (h : Run pre post executed) : Selected pre post executed 0
  | append {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) : Selected pre post executed 1
  | trans {pre mid post : Meter} {first second left right : Nat}
      (head : Selected pre mid first left) (tail : Selected mid post second right) :
      Selected pre post (first+second) (left+right)
  | call {pre charged child final : Meter} {childWork count : Nat}
      (cold delegated delegationCold hasValue deadRecipient : Bool) (memoryCost : Nat)
      (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
      (requested : UInt256) (outcome : Outcome)
      (body : Selected (start (split hasValue requested charged)) child childWork count)
      (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
      Selected pre final (overhead cold delegated delegationCold hasValue memoryCost+childWork) count
  | create {pre child final : Meter} {chargedCore : ReferenceStorageGas.Meter} {childWork count : Nat}
      (stateAmount : Nat) (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
      (outcome : Outcome) (newAccount : Bool)
      (body : Selected (start (creationSplit (update pre chargedCore))) child childWork count)
      (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
      Selected pre final childWork count

theorem Selected.accounted {pre post : Meter} {executed count : Nat}
    (h : Selected pre post executed count) : Run pre post executed ∧ 1419*count ≤ executed := by
  induction h with
  | skip actual => exact ⟨actual,by simp⟩
  | append actual => exact ⟨actual.run,by simpa using actual.cost⟩
  | trans first second ih1 ih2 => exact ⟨.trans ih1.1 ih2.1,by omega⟩
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact ⟨.call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome ih.1 finished,by omega⟩
  | create stateAmount charged outcome newAccount body finished ih =>
    exact ⟨.create stateAmount charged outcome newAccount ih.1 finished,ih.2⟩

/-- The structural cost premise of ReferenceTransactionWork is now derived
from the same selected actual completed leaf executions, not supplied as a
numerical bound. Canonical source extraction and source settlement validity
remain explicit external producers for a transaction-history application. -/
theorem transaction_count {txGas intrinsic executed count : Nat} {post : Meter}
    (h : Selected (ReferenceTransactionWork.initial txGas intrinsic) post executed count)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216)
    (dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) :
    count ≤ 11823 ∧ count ≤
      (ReferenceTransactionGas.settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
        gasLeft stateLeft refund netState).executionUsed := by
  exact ReferenceTransactionWork.appends_le_execution_charge h.accounted.1 affords maximum h.accounted.2
    dataBytes recipientExecution accessTokens gasLeft stateLeft refund netState

#print axioms ProtectedPaid.cost
#print axioms ProtectedPaid.run
#print axioms Selected.accounted
#print axioms transaction_count
end Eip8282.Audit.Integrator.ReferenceSelectedAppendWork

end
