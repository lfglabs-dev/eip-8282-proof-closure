import Eip8282.Audit.Integrator.ReferenceRuntimeReadings
import Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds

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
