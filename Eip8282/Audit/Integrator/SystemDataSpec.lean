import Eip8282.Audit.Integrator.SuccessfulSystem
import Eip8282.Audit.Integrator.QueueArithmetic
import Eip8282.Audit.Integrator.AccountedState

/-!
# Code-independent SYSTEM storage observations

The read-map overlay is independent of an execution state or pinned bytecode.
Its projections separate controls from drain pointers and stale storage. Actual
Theta success gives the overlay; natural arithmetic requires input bounds only.
-/
namespace Eip8282.Audit.Integrator.SystemDataSpec

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall CallBridge SystemSpec

set_option maxHeartbeats 800000

def target : Kind → Nat | .deposit => 8 | .exit => 2

def cap : Kind → Nat | .deposit => 64 | .exit => 16

def length (read : UInt256 → UInt256) : Nat :=
  (read (UInt256.ofNat 3)).toNat - (read (UInt256.ofNat 2)).toNat

def drainWord (kind : Kind) (read : UInt256 → UInt256) : UInt256 :=
  let n := read (UInt256.ofNat 3) - read (UInt256.ofNat 2)
  if n < UInt256.ofNat (cap kind) then n else UInt256.ofNat (cap kind)

/-- Exact four-slot overlay, including word arithmetic outside ordered domains. -/
def expected (read : UInt256 → UInt256) (target count cds key : UInt256) : UInt256 :=
  if key = UInt256.ofNat 0 then
    ControlSpec.systemExcess target (read (UInt256.ofNat 0)) (read (UInt256.ofNat 1)) cds
  else if key = UInt256.ofNat 1 then ⟨0⟩
  else if key = UInt256.ofNat 2 then
    if read (UInt256.ofNat 3) = read (UInt256.ofNat 2) + count then ⟨0⟩
    else read (UInt256.ofNat 2) + count
  else if key = UInt256.ofNat 3 ∧
    read (UInt256.ofNat 3) = read (UInt256.ofNat 2) + count then ⟨0⟩
  else read key

theorem expected_entry (st : EvmYul.State .EVM) (target count cds : UInt256) :
    expected (slotW st) target count cds = expectedSlot st target count cds := rfl

/-- The observable all-slot claim has no code pin in its type. -/
def Observed (kind : Kind) (c : Context) (world : AccountMap .EVM) : Prop :=
  ∀ k, worldSlot world c.target k = expected (worldSlot c.world c.target)
    (UInt256.ofNat (target kind)) (drainWord kind (worldSlot c.world c.target))
    (UInt256.ofNat c.calldata.size) k

private theorem transport_expected (kind : Kind) (c : Context)
    (hcode : c.code = runtimeCode kind) (steps : Nat) :
    expectedSlot (entrySt (codeCall c hcode steps)) =
      expected (worldSlot c.world c.target) := by
  have hr : slotW (entrySt (codeCall c hcode steps)) = worldSlot c.world c.target :=
    funext (TransferFrame.codeCall_storage c hcode steps)
  funext target count cds
  rw [← expected_entry, hr]

private theorem transport_drain (kind : Kind) (c : Context)
    (hcode : c.code = runtimeCode kind) (steps : Nat) :
    drainWord kind (slotW (entrySt (codeCall c hcode steps))) =
      drainWord kind (worldSlot c.world c.target) := by
  rw [show slotW (entrySt (codeCall c hcode steps)) = worldSlot c.world c.target from
    funext (TransferFrame.codeCall_storage c hcode steps)]

theorem exit_system (c : Context) (hcode : c.code = runtimeCode .exit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed .exit c world := by
  obtain ⟨ew, ec, eg, es, he, hs⟩ := SuccessfulSystem.exit_system c hcode hsys ho h
  have hw : world = ew := by
    have hh := h.symm.trans he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    exact hh.2.1
  rw [Observed, hw]
  intro k
  rw [hs, transport_expected]
  have hd := transport_drain .exit c hcode (c.fuel-1)
  change Exit.drainWord (codeCall c hcode (c.fuel-1)) = _ at hd
  rw [hd]
  rfl

theorem deposit_system (c : Context) (hcode : c.code = runtimeCode .deposit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed .deposit c world := by
  obtain ⟨ew, ec, eg, es, he, hs⟩ := SuccessfulSystem.deposit_system c hcode hsys ho h
  have hw : world = ew := by
    have hh := h.symm.trans he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    exact hh.2.1
  rw [Observed, hw]
  intro k
  rw [hs, transport_expected]
  have hd := transport_drain .deposit c hcode (c.fuel-1)
  change Deposit.drainWord (codeCall c hcode (c.fuel-1)) = _ at hd
  rw [hd]
  rfl

/-- Separate drain projection; its stale-slot clause covers all old record words. -/
def DrainSlots (kind : Kind) (pre post : UInt256 → UInt256) : Prop :=
  let n := min (length pre) (cap kind)
  (post (UInt256.ofNat 2)).toNat =
    (if n = length pre then 0 else (pre (UInt256.ofNat 2)).toNat + n) ∧
  (post (UInt256.ofNat 3)).toNat =
    (if n = length pre then 0 else (pre (UInt256.ofNat 3)).toNat) ∧
  ∀ k, 4 ≤ k.toNat → post k = pre k

theorem drain_count (kind : Kind) (pre : UInt256 → UInt256)
    (ho : (pre (UInt256.ofNat 2)).toNat ≤ (pre (UInt256.ofNat 3)).toNat) :
    (drainWord kind pre).toNat = min (length pre) (cap kind) :=
  QueueArithmetic.capped_sub_toNat _ _ _ (by cases kind <;> decide) ho

theorem drain_projection (kind : Kind) (pre : UInt256 → UInt256) (cds : UInt256)
    (ho : (pre (UInt256.ofNat 2)).toNat ≤ (pre (UInt256.ofNat 3)).toNat) :
    DrainSlots kind pre (expected pre (UInt256.ofNat (target kind)) (drainWord kind pre) cds) := by
  have hc := drain_count kind pre ho
  have hle : (drainWord kind pre).toNat ≤
      (pre (UInt256.ofNat 3)).toNat - (pre (UInt256.ofNat 2)).toNat := by
    rw [hc]; exact Nat.min_le_left _ _
  have he := QueueArithmetic.full_iff _ _ (drainWord kind pre) ho hle
  have ha := QueueArithmetic.advanced_head _ _ (drainWord kind pre) ho hle
  change (_ ↔ (drainWord kind pre).toNat = length pre) at he
  rw [hc] at he ha
  unfold DrainSlots
  refine ⟨?_, ?_, ?_⟩
  · simp only [expected, show UInt256.ofNat 2 ≠ UInt256.ofNat 0 by decide,
      show UInt256.ofNat 2 ≠ UInt256.ofNat 1 by decide, ↓reduceIte, he]
    split <;> simp_all
  · simp only [expected, show UInt256.ofNat 3 ≠ UInt256.ofNat 0 by decide,
      show UInt256.ofNat 3 ≠ UInt256.ofNat 1 by decide,
      show UInt256.ofNat 3 ≠ UInt256.ofNat 2 by decide, ↓reduceIte, true_and, he]
    split <;> simp_all
  · intro k hk
    have h0 : k ≠ UInt256.ofNat 0 := by intro h; subst k; change 4 ≤ 0 at hk; omega
    have h1 : k ≠ UInt256.ofNat 1 := by intro h; subst k; change 4 ≤ 1 at hk; omega
    have h2 : k ≠ UInt256.ofNat 2 := by intro h; subst k; change 4 ≤ 2 at hk; omega
    have h3 : k ≠ UInt256.ofNat 3 := by intro h; subst k; change 4 ≤ 3 at hk; omega
    simp only [expected, h0, h1, h2, h3, ↓reduceIte, false_and]

/-- Natural control rule, separate from the quote numerator. -/
def ControlSlots (kind : Kind) (cds : Nat) (pre post : UInt256 → UInt256) : Prop :=
  (post (UInt256.ofNat 0)).toNat =
    (if cds ≠ 0 then INH.toNat else if pre (UInt256.ofNat 0) = INH then 0
      else (pre (UInt256.ofNat 0)).toNat + (pre (UInt256.ofNat 1)).toNat - target kind) ∧
  post (UInt256.ofNat 1) = ⟨0⟩

theorem control_projection (kind : Kind) (pre : UInt256 → UInt256) (cds budget : Nat)
    (hsize : cds < UInt256.size) (hb : AccountedState.Bounded budget pre)
    (hbudget : budget < UInt256.size) :
    ControlSlots kind cds pre
      (expected pre (UInt256.ofNat (target kind)) (drainWord kind pre) (UInt256.ofNat cds)) := by
  have hzero : UInt256.ofNat cds = ⟨0⟩ ↔ cds = 0 := by
    constructor
    · intro he
      have hn := congrArg UInt256.toNat he
      rw [toNat_ofNat_lit cds hsize] at hn
      exact hn
    · rintro rfl; rfl
  unfold ControlSlots
  refine ⟨?_, ?_⟩
  · simp only [expected, ↓reduceIte, ControlSpec.systemExcess, ne_eq, hzero]
    by_cases hz : cds = 0
    · simp only [hz, not_true_eq_false, ↓reduceIte]
      by_cases hi : pre (UInt256.ofNat 0) = INH
      · simp only [hi, ↓reduceIte]; rfl
      · simp only [hi, ↓reduceIte]
        have hh := ControlSpec.foldWord_eq_nat_of_sum_lt
          (UInt256.ofNat (target kind)) (pre (UInt256.ofNat 0)) (pre (UInt256.ofNat 1))
          ((hb.active hi).trans_lt hbudget)
        rw [hh]
        unfold ControlSpec.foldNat
        rw [toNat_ofNat_lit _ (by cases kind <;> decide)]
    · simp only [hz, not_false_eq_true, ↓reduceIte]
  · simp only [expected, show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide, ↓reduceIte]

/-- Both natural projections follow from one actual all-slot observation. -/
theorem projections {kind : Kind} {c : Context} {world : AccountMap .EVM}
    (h : Observed kind c world) (budget : Nat)
    (hb : AccountedState.Bounded budget (worldSlot c.world c.target))
    (hbudget : budget < UInt256.size) (hsize : c.calldata.size < UInt256.size) :
    ControlSlots kind c.calldata.size (worldSlot c.world c.target) (worldSlot world c.target) ∧
    DrainSlots kind (worldSlot c.world c.target) (worldSlot world c.target) := by
  have he := funext h
  rw [he]
  exact ⟨control_projection kind _ _ budget hsize hb hbudget,
    drain_projection kind _ _ hb.ordered⟩

#print axioms exit_system
#print axioms deposit_system
#print axioms control_projection
#print axioms projections
#print axioms drain_projection

end Eip8282.Audit.Integrator.SystemDataSpec
