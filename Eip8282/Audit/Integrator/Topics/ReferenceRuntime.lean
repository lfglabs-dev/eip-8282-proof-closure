import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.Topics.ReferenceCall2
import Eip8282.Audit.Integrator.Topics.ReferenceMemory2
import Eip8282.Audit.Integrator.Topics.ReferencePure
import Eip8282.Audit.Integrator.Topics.ReferenceStorage
import Eip8282.Audit.Integrator.ReferenceStorageWarmth
import Eip8282.Audit.Integrator.Topics.ReferenceSystem
import Eip8282.Audit.Integrator.RuntimeMemoryCharges
import Eip8282.Audit.Integrator.SystemTraceAnnotations

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceRuntimeAction -/

/-! All nonhalting instructions actually reachable in the two pinned runtimes.
Write permission is derived only at admitted SSTORE/LOG0; static fee getters
and other read-only successful paths require no global writable-context premise.
Whole user-path resource production and terminal rollback are separate layers. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

inductive Action (kind : Kind) (parent : ReferenceStorageView.Parent) : Instruction → View → View → Prop where
  | base {instr : Instruction} {v next : View} :
      ReferenceSystemAction.Action kind parent instr v next → Action kind parent instr v next
  | copy {v : View} {dest source len : UInt256} {rest : Stack UInt256} :
      v.stack = dest::source::len::rest → Action kind parent (.CALLDATACOPY,none) v
        (ReferenceCalldataCopy.copyAction v dest source len rest)
  | log {v : View} {off len : UInt256} {rest : Stack UInt256} :
      v.env.perm = true → v.stack = off::len::rest → Action kind parent (.LOG0,none) v
        (ReferenceLogView.logAction v off len rest)

private theorem store_permission {vj : Array UInt256} {pre mid : EVM.State} {gasCost : Nat}
    (hz : Z vj .SSTORE pre = .ok (mid,gasCost)) : pre.executionEnv.perm = true := by
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 8 replace hz := elim_guard hz
  have hn := elim_guard_not hz
  cases hp : pre.executionEnv.perm <;> simp [hp,W] at hn ⊢

private theorem base_step {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (related : Related parent v pre) (ha : SystemPathBudget.Allowed (decodeAt pre).1)
    (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ next, ReferenceSystemAction.Action kind parent (decodeAt pre) v next ∧ Related parent next post := by
  rcases ReferenceSystemAction.cases_of_nonhalting ha hh with hp | hp | hp | hp | hp
  · obtain ⟨next,ha,hr⟩ := ReferencePureComplete.accepted related hat hp hz hs cdfit
    exact ⟨next,.pure ha,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SLOAD hp rfl
    obtain ⟨key,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sload hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .load hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SSTORE hp rfl
    have permission : v.env.perm = true := by
      rw [related.env]
      exact store_permission (by simpa only [hd] using hz)
    obtain ⟨key,value,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sstore hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .store permission hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .word hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE8 hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore8 hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .byte hstack,hr⟩

/-- Actual runtime scope supplies opcode membership. No user/SYSTEM classifier
or global permission, desired action, operand shape or next view is supplied. -/
theorem step {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (related : Related parent v pre) (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ next, Action kind parent (decodeAt pre) v next ∧ Related parent next post := by
  by_cases hcopy : (decodeAt pre).1 = .CALLDATACOPY
  · have hd := ReferenceDecodeShape.fixed pre .CALLDATACOPY hcopy rfl
    obtain ⟨dest,source,len,rest,_,hshape,hr⟩ := ReferenceCalldataCopy.accepted hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .copy hshape,hr⟩
  · by_cases hlog : (decodeAt pre).1 = .LOG0
    · have hd := ReferenceDecodeShape.fixed pre .LOG0 hlog rfl
      obtain ⟨off,len,rest,_,hshape,hpermission,hr⟩ := ReferenceLogView.accepted hat hd hz hs related capacity host
      exact ⟨_,by rw [hd]; exact .log hpermission hshape,hr⟩
    · obtain ⟨next,ha,hr⟩ := base_step hat hz hs hh related
        ⟨RuntimeExecutionScope.opcode_allowed hat,hlog,hcopy⟩ cdfit capacity host
      exact ⟨next,.base ha,hr⟩

#print axioms step
end Eip8282.Audit.Integrator.ReferenceRuntimeAction

end

section

/-! ## ReferenceRuntimePriceBounds -/

/-! Source-formula ordinary prices bounded using the same actual step's memory
capacity. COPY/LOG lengths come from accepted execution, including length zero;
no source-offset bound or fixed iteration count is imposed. Initial resource
and capacity producers, source gas interpretation, and SSTORE remain separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open RuntimeExecutionScope RuntimeMemoryMonotone
open ReferenceCopyLogGas
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem copy_bound {len cap : Nat} (h : len ≤ 32*cap) :
    copyCost len ≤ max 2100 (375+256*cap) := by
  have hc : (len+31)/32 ≤ cap := by omega
  unfold copyCost
  omega

private theorem log_bound {len cap : Nat} (h : len ≤ 32*cap) :
    logCost len ≤ max 2100 (375+256*cap) := by
  unfold logCost
  omega

/-- Every actual accepted runtime instruction except SSTORE supplies its price
and a uniform capacity-dependent bound. The post-cap is supplied by the
initial-energy producer at the full-trace consumer. -/
theorem accepted {image : Image} {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk fuel gasCost (decodeAt pre) mid post)
    (notStore : (decodeAt pre).1 ≠ .SSTORE)
    (capacity : post.activeWords.toNat ≤ cap) (warm : Bool) :
    ∃ n, ordinaryCost (decodeAt pre).1 warm pre.stack = some n ∧
      n ≤ max 2100 (375+256*cap) := by
  have he := RuntimeMemoryCharges.accepted_expansion hat hz hs
  by_cases hc : (decodeAt pre).1 = .CALLDATACOPY
  · have hz' : Z (D_J image.code ⟨0⟩) .CALLDATACOPY pre = .ok (mid,gasCost) := by
      simpa only [hc] using hz
    obtain ⟨rest,dest,source,len,pop,shape,price⟩ := accepted_copy hz' warm
    have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat dest.toNat len.toNat := by
      simpa only [hc,span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using he
    have hb : len.toNat ≤ 32*cap := by
      by_cases hzlen : len.toNat = 0
      · omega
      · have hm := (ReferenceMemoryCapacity.expansion_bounds
          pre.activeWords.toNat dest.toNat len.toNat).2 (by omega)
        rw [← hex] at hm
        omega
    exact ⟨copyCost len.toNat,by rw [hc]; exact price,copy_bound hb⟩
  · by_cases hl : (decodeAt pre).1 = .LOG0
    · have hz' : Z (D_J image.code ⟨0⟩) .LOG0 pre = .ok (mid,gasCost) := by
        simpa only [hl] using hz
      obtain ⟨rest,off,len,pop,shape,price⟩ := accepted_log hz' warm
      have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat := by
        simpa only [hl,span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using he
      have hb : len.toNat ≤ 32*cap := by
        by_cases hzlen : len.toNat = 0
        · omega
        · have hm := (ReferenceMemoryCapacity.expansion_bounds
            pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
          rw [← hex] at hm
          omega
      exact ⟨logCost len.toNat,by rw [hl]; exact price,log_bound hb⟩
    · obtain ⟨n,hn,hbound⟩ := ReferenceOrdinaryGas.defined_bound warm
        ⟨opcode_allowed hat,hl,hc⟩ notStore
      exact ⟨n,by simp only [ordinaryCost,if_neg hc,if_neg hl]; exact hn,
        hbound.trans (Nat.le_max_left _ _)⟩

#print axioms accepted
end Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds

end

section

/-! ## ReferenceRuntimeTrace -/

/-! Source-shaped views along arbitrary finite actual runtime traces, including
user COPY/LOG0. No global permission or source-state sequence is supplied.
Endpoint capacity is still a local resource premise; initial-call resource
producers and complete halting/failure observations remain separate consumers. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction SystemTraceAnnotations
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Viewed (kind : Kind) (parent : ReferenceStorageView.Parent) :
    Nat → EVM.State → View → List Labelled → Nat → EVM.State → View → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) : Viewed kind parent fuel pre v [] fuel pre v
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View} {trace : List Labelled}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (related : Related parent v pre) (nextRelated : Related parent next mid)
      (action : Action kind parent (decodeAt pre) v next)
      (tail : Viewed kind parent fuel mid next trace rem post finish) :
      Viewed kind parent (fuel+1) pre v ((fuel,gasCost,decodeAt pre)::trace) rem post finish

theorem Viewed.erase {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem : Nat}
    {pre post : EVM.State} {v finish : View} {trace : List Labelled}
    (h : Viewed kind parent fuel pre v trace rem post finish) :
    XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post := by
  induction h with
  | refl => exact .refl _ _
  | cons hs _ _ _ _ _ ih => exact .cons hs ih

theorem from_runs {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem cap : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (hr : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (related : Related parent v pre)
    (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ finish, Viewed kind parent fuel pre v trace rem post finish ∧ Related parent finish post := by
  revert hat v
  induction hr with
  | refl => intro hat v related cdfit; exact ⟨v,.refl _ _ _,related⟩
  | @cons edgeFuel gasCost rem pre middle post trace actual tail ih =>
    intro hat v related cdfit
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatnext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have hc := (RuntimeMemoryMonotone.runs hatnext tail).2.trans capacity
    have hd : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none) := by
      rw [related.env,related.pc,hat.1,ReferenceRuntimeSites.code_eq]
      exact ReferenceRuntimeSites.decode_matches hat hh
    cases edgeFuel with
    | zero => cases hs
    | succ f =>
      obtain ⟨next,hact,hrel⟩ := ReferenceRuntimeAction.step hat hz hs hh related cdfit hc host
      have henv : next.env = v.env :=
        hrel.env.trans ((RuntimeExecutionScope.accepted_environment hat hz hs).trans related.env.symm)
      obtain ⟨finish,hview,hfinish⟩ := ih capacity hatnext next hrel (by rw [henv]; exact cdfit)
      exact ⟨finish,.cons ⟨charged,hz,hs,hh⟩ hd related hrel hact hview,hfinish⟩

#print axioms Viewed.erase
#print axioms from_runs
end Eip8282.Audit.Integrator.ReferenceRuntimeTrace

end

section

/-! ## ReferenceRuntimeReadings -/

/-! Exact source readings and literal prices on the same viewed runtime trace,
including user COPY and LOG0. The input trace is already derived from execution;
this annotation does not choose a second trace or arbitrary storage readings.
Initial source parent/created/warm bindings and source execution remain distinct. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReadings
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction ReferenceRuntimeTrace
open ReferenceSourceReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem created {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View} (h : Action kind parent instr v next) :
    next.storage.created = v.storage.created := by
  cases h with
  | base h => exact ReferenceActionMetadata.created h
  | copy => rfl
  | log => rfl

noncomputable def Price (parent : ReferenceStorageView.Parent) (v : View) (w : Warm)
    (next : View) (op : Operation .EVM) (event : Event) : Prop :=
  let reading := sourceReading parent v w
  let memoryCost := ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)
  if op = .SSTORE then memoryCost = 0 ∧
    event = .store reading.warm reading.original reading.current reading.new
  else ∃ n, ReferenceCopyLogGas.ordinaryCost op reading.warm v.stack = some n ∧
    event = .ordinary (n+memoryCost)

inductive Coupled (kind : Kind) (parent : ReferenceStorageView.Parent) (initialCreated : Set AccountAddress) :
    Nat → EVM.State → View → Warm → List Labelled → Nat → EVM.State → View → Warm → List Event → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) (w : Warm) :
      Coupled kind parent initialCreated fuel pre v w [] fuel pre v w []
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View}
      {w finalWarm : Warm} {trace : List Labelled} {event : Event} {events : List Event}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (related : Related parent v pre) (nextRelated : Related parent next mid)
      (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated)
      (action : Action kind parent (decodeAt pre) v next)
      (readings : ReferenceSourceReadings.inputs parent initialCreated pre = sourceReading parent v w)
      (price : Price parent v w next (decodeAt pre).1 event)
      (tail : Coupled kind parent initialCreated fuel mid next (warmAfter (decodeAt pre).1 v w)
        trace rem post finish finalWarm events) :
      Coupled kind parent initialCreated (fuel+1) pre v w ((fuel,gasCost,decodeAt pre)::trace)
        rem post finish finalWarm (event::events)

theorem Coupled.viewed {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events) :
    Viewed kind parent fuel pre v trace rem post finish := by
  induction h with
  | refl => exact .refl _ _ _
  | cons actual decoded related nextRelated _ _ action _ _ _ ih =>
    exact .cons actual decoded related nextRelated action ih

/-- Produce the event sequence and evolving warmth on exactly the supplied
viewed trace, retaining its final source view. No per-edge payment is assumed. -/
theorem from_viewed {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {trace : List Labelled}
    (viewed : Viewed kind parent fuel pre v trace rem post finish)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (w : Warm) (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated) :
    ∃ finalWarm events,
      Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events ∧
      WarmRelated finalWarm post ∧ finish.storage.created = initialCreated := by
  revert hat w
  induction viewed with
  | refl => intro _ w warm; exact ⟨w,[],.refl _ _ _ _,warm,created_eq⟩
  | @cons edgeFuel gasCost rem pre mid post v next finish trace actual decoded related nextRelated action tail ih =>
    intro hat w warm
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatNext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have warmNext : WarmRelated (warmAfter (decodeAt pre).1 v w) mid := by
      cases edgeFuel with
      | zero => cases hs
      | succ f => exact ReferenceStorageWarmth.accepted_warm hat hz hs related warm
    have createdNext := (created action).trans created_eq
    obtain ⟨finalWarm,events,hcoupled,hfinalWarm,hfinalCreated⟩ :=
      ih createdNext hatNext (warmAfter (decodeAt pre).1 v w) warmNext
    have readings := ReferenceSourceReadings.reading_eq related warm created_eq
    have priced : ∃ event, Price parent v w next (decodeAt pre).1 event := by
      by_cases hop : (decodeAt pre).1 = .SSTORE
      · refine ⟨.store (sourceReading parent v w).warm (sourceReading parent v w).original
          (sourceReading parent v w).current (sourceReading parent v w).new,?_⟩
        simp only [Price,if_pos hop]
        refine ⟨?_,True.intro⟩
        rw [words_related related,words_related nextRelated]
        have hm := RuntimeMemoryCharges.accepted_expansion hat hz hs
        rw [hop] at hm
        simp only [RuntimeMemoryMonotone.span,MachineState.M] at hm
        rw [hm,Nat.sub_self]
      · obtain ⟨n,hn⟩ := ReferenceCopyLogGas.defined (sourceReading parent v w).warm v.stack
          (RuntimeExecutionScope.opcode_allowed hat) hop
        exact ⟨.ordinary (n+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v))),
          by simp only [Price,if_neg hop]; exact ⟨n,hn,rfl⟩⟩
    obtain ⟨event,hprice⟩ := priced
    exact ⟨finalWarm,event::events,
      .cons ⟨charged,hz,hs,hh⟩ decoded related nextRelated warm created_eq action readings hprice hcoupled,
      hfinalWarm,hfinalCreated⟩

#print axioms created
#print axioms Coupled.viewed
#print axioms from_viewed
end Eip8282.Audit.Integrator.ReferenceRuntimeReadings

end

section

/-! ## ReferenceRuntimePayment -/

/-! Aggregate initial resources pay the literal event sequence attached to the
same actual runtime prefix. The state reserve counts executed SSTORE instructions,
not append records or committed effects. Bounds use arbitrary finite traces;
the host/protocol must still supply these initial grants. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimePayment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceMemoryCapacity (cost cost_mono)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def baseBound (cap : Nat) : Nat := max 12100 (max 2100 (375+256*cap))

/-- Only actual SSTORE instruction occurrences; this is not a persistent queue metric. -/
def storageWrites : List Labelled → Nat
  | [] => 0
  | label::tail => (if label.2.2.1 = .SSTORE then 1 else 0)+storageWrites tail

theorem state_total {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events) :
    sumState events = 97920*storageWrites trace := by
  induction h with
  | refl => rfl
  | @cons fuel gasCost rem pre mid post v next finish w finalWarm trace event events
      actual decoded related nextRelated warm created_eq action readings price tail ih =>
    by_cases hop : (decodeAt pre).1 = .SSTORE
    · simp only [Price,if_pos hop] at price
      obtain ⟨_,rfl⟩ := price
      change 97920+sumState events = 97920*((if (decodeAt pre).1 = .SSTORE then 1 else 0)+storageWrites trace)
      rw [ih,if_pos hop]; omega
    · simp only [Price,if_neg hop] at price
      obtain ⟨n,_,rfl⟩ := price
      change 0+sumState events = 97920*((if (decodeAt pre).1 = .SSTORE then 1 else 0)+storageWrites trace)
      rw [ih,if_neg hop]; omega

theorem execution_bound {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem cap : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (capacity : post.activeWords.toNat ≤ cap) :
    sumExec events ≤ baseBound cap*trace.length + (cost post.activeWords.toNat-cost pre.activeWords.toNat) := by
  revert hat
  induction h with
  | refl => intro _; simp [sumExec]
  | @cons fuel gasCost rem pre mid post v next finish w finalWarm trace event events
      actual decoded related nextRelated warm created_eq action readings price tail ih =>
    intro hat
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatMid := RuntimeExecutionScope.accepted_next hat hz hs hh
    have hm := (RuntimeMemoryMonotone.runs hatMid tail.viewed.erase).2
    have headBound : executionBudget event ≤ baseBound cap+(cost mid.activeWords.toNat-cost pre.activeWords.toNat) := by
      by_cases hop : (decodeAt pre).1 = .SSTORE
      · simp only [Price,if_pos hop] at price
        obtain ⟨_,rfl⟩ := price
        exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
      · simp only [Price,if_neg hop] at price
        obtain ⟨n,hn,rfl⟩ := price
        obtain ⟨m,hprice,hbound⟩ := ReferenceRuntimePriceBounds.accepted hat hz hs hop
          (hm.trans capacity) (sourceReading parent v w).warm
        rw [ReferenceCopyLogGas.related_cost related] at hn
        have he : n = m := Option.some.inj (hn.symm.trans hprice)
        subst m
        change n+(cost (words next)-cost (words v)) ≤ _
        rw [words_related related,words_related nextRelated]
        exact Nat.add_le_add_right (hbound.trans (Nat.le_max_right _ _)) _
    have tailBound := ih capacity hatMid
    have monoHead := cost_mono (RuntimeMemoryMonotone.accepted hat hz hs).1
    have monoTail := cost_mono hm
    change executionBudget event+sumExec events ≤ baseBound cap*(trace.length+1)+_
    rw [Nat.mul_add,Nat.mul_one]
    omega

/-- Initial aggregate grants discharge every sentry and payment in order,
without spending future refunds in advance. Terminal charging is composed by
the complete-execution consumer. -/
theorem payment {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem cap : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (capacity : post.activeWords.toNat ≤ cap) (meter : ReferenceStorageGas.Meter)
    (exec : baseBound cap*trace.length+(cost post.activeWords.toNat-cost pre.activeWords.toNat) ≤ meter.execution)
    (reserve : 97920*storageWrites trace ≤ meter.reservoir) :
    ∃ final, run events meter = some final ∧
      meter.execution-sumExec events ≤ final.execution ∧
      meter.reservoir-sumState events ≤ final.reservoir := by
  exact ReferenceMeterPath.payment events meter ((execution_bound h hat capacity).trans exec)
    (by rw [state_total h]; exact reserve)

#print axioms state_total
#print axioms execution_bound
#print axioms payment
end Eip8282.Audit.Integrator.ReferenceRuntimePayment

end

section

/-! ## ReferenceRuntimeReverse -/

/-! Compose all running protected-runtime raw effects in the reverse direction.
Successful source-shaped Action supplies its result; the pinned raw result is
constructed. The host premise concerns input-derived expansion, never a chosen
post-state. Source extraction and guarded resource replay remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {instr : Instruction}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = instr)
    (effect : Action kind parent instr v next)
    (host : 32*MachineState.M (words v) (RuntimeMemoryMonotone.span pre instr.1).1
      (RuntimeMemoryMonotone.span pre instr.1).2 < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step instr.1 instr.2 pre = .ok post ∧ Related parent next post := by
  cases effect with
  | base base =>
    cases base with
    | pure effect =>
      rw [←decoded] at effect ⊢
      exact ReferencePureReverseComplete.raw related site effect
    | load shape => exact ReferenceStorageReverse.load related site shape
    | store permission shape => exact ReferenceStorageReverse.store related site shape
    | word shape =>
      apply ReferenceMemoryReverse.mstore related site shape
      simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero] using host
    | byte shape =>
      apply ReferenceMemoryReverse.mstore8 related site shape
      simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero] using host
  | copy shape =>
    apply ReferenceCopyLogReverse.copy related site shape
    simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero,
      List.getElem!_cons_succ] using host
  | log permission shape =>
    apply ReferenceCopyLogReverse.log related site shape
    simpa only [RuntimeMemoryMonotone.span,←related.stack,shape,List.getElem!_cons_zero,
      List.getElem!_cons_succ] using host

#print axioms raw
end Eip8282.Audit.Integrator.ReferenceRuntimeReverse

end
