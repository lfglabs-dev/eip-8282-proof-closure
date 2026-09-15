import Eip8282.Audit.Integrator.Topics.ReferenceStorage

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceMeterPath -/

/-! Arbitrary finite paths through the audited source-meter transcription.
Only aggregate INITIAL budgets are premises; each sentry and ordered payment
is derived. Store events are explicitly nonstatic, as required for SYSTEM.
Mapping an actual interpreter trace to these events remains a separate adapter;
this theorem alone does not assert reference execution or protocol progress. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterPath
open EvmYul ReferenceStorageGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

inductive Event where
  | ordinary (amount : Nat)
  | store (warm : Bool) (original current new : UInt256)
  deriving DecidableEq, Repr

def executionBudget : Event → Nat
  | .ordinary amount => amount
  | .store _ _ _ _ => 12100

def stateBudget : Event → Nat
  | .ordinary _ => 0
  | .store _ _ _ _ => 97920

def sumExec (events : List Event) : Nat := (events.map executionBudget).sum

def sumState (events : List Event) : Nat := (events.map stateBudget).sum

/-- Literal charge order, including the possibility of failure. -/
def pay (event : Event) (m : Meter) : Option Meter :=
  match event with
  | .ordinary amount => chargeExecution m amount
  | .store warm original current new => storageCharge false warm original current new m

def run : List Event → Meter → Option Meter
  | [], m => some m
  | event::events, m => (pay event m).bind (run events)

/-- The generic one-event lemma is internal evidence for the aggregate producer. -/
theorem pay_success (event : Event) (m : Meter)
    (he : executionBudget event ≤ m.execution)
    (hr : stateBudget event ≤ m.reservoir) :
    ∃ post, pay event m = some post ∧
      m.execution-executionBudget event ≤ post.execution ∧
      m.reservoir-stateBudget event ≤ post.reservoir := by
  cases event with
  | ordinary amount =>
    refine ⟨{m with execution := m.execution-amount},?_,?_,?_⟩
    · exact if_pos he
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  | store warm original current new =>
    exact conservative_success warm original current new m he hr

/-- Initial totals alone imply every payment succeeds in sequence. The lower
bounds do not spend future refunds in advance, and require no iteration cap. -/
theorem payment (events : List Event) (initial : Meter)
    (he : sumExec events ≤ initial.execution)
    (hr : sumState events ≤ initial.reservoir) :
    ∃ final, run events initial = some final ∧
      initial.execution-sumExec events ≤ final.execution ∧
      initial.reservoir-sumState events ≤ final.reservoir := by
  induction events generalizing initial with
  | nil => exact ⟨initial,rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons event events ih =>
    have hex : sumExec (event::events) = executionBudget event + sumExec events := rfl
    have hst : sumState (event::events) = stateBudget event + sumState events := rfl
    obtain ⟨middle,hm,hme,hmr⟩ := pay_success event initial (by omega) (by omega)
    obtain ⟨final,hf,hfe,hfr⟩ := ih middle (by omega) (by omega)
    refine ⟨final,?_,?_,?_⟩
    · simp only [run,hm,Option.bind_some,hf]
    · omega
    · omega

theorem budgets_append (xs ys : List Event) :
    sumExec (xs++ys) = sumExec xs+sumExec ys ∧
    sumState (xs++ys) = sumState xs+sumState ys := by
  simp [sumExec,sumState]

/-- Chunking a path preserves the literal sequential charge computation. -/
theorem run_append (xs ys : List Event) (m : Meter) :
    run (xs++ys) m = (run xs m).bind (run ys) := by
  induction xs generalizing m with
  | nil => rfl
  | cons event xs ih =>
    simp only [List.cons_append,run]
    cases hm : pay event m with
    | none => rfl
    | some middle => exact ih middle

#print axioms pay_success
#print axioms payment
#print axioms budgets_append
#print axioms run_append
end Eip8282.Audit.Integrator.ReferenceMeterPath

end

section

/-! ## ReferenceMeterConservation -/

/-! Conservation for successful literal source-meter payments. These identities
use actual class prices, not the conservative 12100/97920 budgets. Signed state
credits are retained. No linkage of original/current values, funding premise,
or refund provenance is assumed. Applying this algebra to actual storage and
nested rollback requires the separate storage-flow and full-meter adapters.
Source transcription boundary is inherited from ReferenceStorageGas (EL0cc
vm/gas.py, archived direct-reference-admission-sources-20260910.json). -/
namespace Eip8282.Audit.Integrator.ReferenceMeterConservation
open EvmYul ReferenceStorageGas ReferenceMeterPath
set_option autoImplicit false

def actualExec : Event → Int
  | .ordinary amount => amount
  | .store warm original current new => (classify warm original current new).execution

def stateDelta : Event → Int
  | .ordinary _ => 0
  | .store warm original current new =>
    ((classify warm original current new).state : Int)-
      (classify warm original current new).stateRefund

def pools (m : Meter) : Int := (m.execution : Int)+m.reservoir
def stateBalance (m : Meter) : Int := -(m.reservoir : Int)+m.spill

private theorem credit_balance (m : Meter) (amount : Nat) :
    pools (creditState m amount)-pools m = amount ∧
    stateBalance (creditState m amount)-stateBalance m = -(amount : Int) := by
  simp only [creditState,pools,stateBalance]
  omega

private theorem execution_balance {m post : Meter} {amount : Nat}
    (h : chargeExecution m amount = some post) :
    pools m-pools post = amount ∧ stateBalance post = stateBalance m := by
  unfold chargeExecution at h
  split at h
  · cases h
    simp [pools,stateBalance]
    omega
  · contradiction

private theorem state_balance {m post : Meter} {amount : Nat}
    (h : chargeState m amount = some post) :
    pools m-pools post = amount ∧ stateBalance post-stateBalance m = amount := by
  unfold chargeState at h
  split at h
  · cases h
    simp only [pools,stateBalance]
    omega
  · split at h
    · cases h
      simp only [pools,stateBalance]
      omega
    · contradiction

/-- Exact accounting for the actual successful ordered payment. The execution
refund counter is not spendable execution gas and contributes no early credit. -/
theorem pay_balance {event : Event} {pre post : Meter}
    (h : pay event pre = some post) :
    pools pre-pools post = actualExec event+stateDelta event ∧
    stateBalance post-stateBalance pre = stateDelta event := by
  cases event with
  | ordinary amount =>
    obtain ⟨hp,hs⟩ := execution_balance h
    simp only [actualExec,stateDelta]
    omega
  | store warm original current new =>
    let c := classify warm original current new
    let refunded := {pre with refund := pre.refund+c.refundDelta}
    let credited := creditState refunded c.stateRefund
    have hc := credit_balance refunded c.stateRefund
    change (storageCharge false warm original current new pre) = some post at h
    unfold storageCharge at h
    simp only [Bool.false_eq_true,↓reduceIte] at h
    split at h
    · change (chargeExecution credited c.execution).bind (fun m => chargeState m c.state) = some post at h
      cases he : chargeExecution credited c.execution with
      | none => simp only [he,Option.bind_none] at h; contradiction
      | some middle =>
        rw [he,Option.bind_some] at h
        obtain ⟨ep,es⟩ := execution_balance he
        obtain ⟨sp,ss⟩ := state_balance h
        have rp : pools refunded = pools pre := rfl
        have rs : stateBalance refunded = stateBalance pre := rfl
        change pools pre-pools post = (c.execution : Int)+((c.state : Int)-c.stateRefund) ∧
          stateBalance post-stateBalance pre = (c.state : Int)-c.stateRefund
        change pools credited-pools refunded = (c.stateRefund : Int) ∧
          stateBalance credited-stateBalance refunded = -(c.stateRefund : Int) at hc
        omega
    · contradiction

/-- Arbitrary finite successful runs telescope on the exact returned meters.
Unlinked event lists can have negative signed state usage; this theorem does
not claim otherwise. -/
theorem run_balance {events : List Event} {pre post : Meter}
    (h : run events pre = some post) :
    pools pre-pools post = (events.map actualExec).sum+(events.map stateDelta).sum ∧
    stateBalance post-stateBalance pre = (events.map stateDelta).sum := by
  induction events generalizing pre with
  | nil =>
    cases h
    simp
  | cons event events ih =>
    change (pay event pre).bind (run events) = some post at h
    cases hp : pay event pre with
    | none => simp only [hp,Option.bind_none] at h; contradiction
    | some middle =>
      rw [hp,Option.bind_some] at h
      have first := pay_balance hp
      have rest := ih h
      simp only [List.map_cons,List.sum_cons]
      omega

#print axioms pay_balance
#print axioms run_balance
end Eip8282.Audit.Integrator.ReferenceMeterConservation

end
