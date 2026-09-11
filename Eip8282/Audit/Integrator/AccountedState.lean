import Eip8282.Audit.Integrator.ResourceBounds
import Eip8282.Audit.Integrator.QueueArithmetic

/-!
# Structural state bounds from an independent append budget

This is an invariant of observed storage maps, not another execution model.
Append and SYSTEM maps already have direct bytecode proofs. The budget counts
locally successful append events, including events later reverted by an ancestor;
it is monotone across rollbacks. No gas-accounting or protocol-history bridge is
assumed proved here. The joint excess+count bound is needed for the SYSTEM fold.
-/
namespace Eip8282.Audit.Integrator.AccountedState

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open AppendStorage SystemSpec ControlSpec

structure Bounded (budget : Nat) (read : UInt256 → UInt256) : Prop where
  ordered : (read (UInt256.ofNat 2)).toNat ≤ (read (UInt256.ofNat 3)).toNat
  tail : (read (UInt256.ofNat 3)).toNat ≤ budget
  count : (read (UInt256.ofNat 1)).toNat ≤ budget
  active : read (UInt256.ofNat 0) ≠ INH →
    (read (UInt256.ofNat 0)).toNat + (read (UInt256.ofNat 1)).toNat ≤ budget

/-- Restoring an older journal preserves the larger monotone budget. -/
theorem mono {a b : Nat} {read : UInt256 → UInt256}
    (h : Bounded a read) (hab : a ≤ b) : Bounded b read :=
  ⟨h.ordered, h.tail.trans hab, h.count.trans hab, fun hi => (h.active hi).trans hab⟩

theorem initial {read : UInt256 → UInt256}
    (hh : read (UInt256.ofNat 2) = ⟨0⟩) (ht : read (UInt256.ofNat 3) = ⟨0⟩)
    (hc : read (UInt256.ofNat 1) = ⟨0⟩)
    (he : read (UInt256.ofNat 0) = ⟨0⟩ ∨ read (UInt256.ofNat 0) = INH) :
    Bounded 0 read := by
  constructor
  · rw [hh, ht]
  · rw [ht]; exact Nat.le_refl 0
  · rw [hc]; exact Nat.le_refl 0
  · intro hi
    rw [he.resolve_right hi, hc]
    exact Nat.le_refl 0

/-- Fit is derived BEFORE using an append's storage postcondition. -/
theorem append_fits (q : XiCall kind) {budget : Nat}
    (h : Bounded budget (slotW (entrySt q))) (hb : budget < 2^128) : AppendFits q := by
  have ht := h.tail
  have hc := h.count
  have hw : 4 + 6 * 2^128 + 6 < UInt256.size := by decide
  have hs : stride kind ≤ 6 := by cases kind <;> decide
  have hm := Nat.mul_le_mul_right (entryTail q).toNat hs
  change (entryTail q).toNat ≤ budget at ht
  change (entryCount q).toNat ≤ budget at hc
  unfold AppendFits
  omega

/-- One append increments the independent budget and preserves the coupled
control bound. The enabled gate is an input fact derived from actual success. -/
theorem append (q : XiCall kind) {budget : Nat}
    (h : Bounded budget (slotW (entrySt q))) (hb : budget < 2^128)
    (hen : slotW (entrySt q) (UInt256.ofNat 0) ≠ INH) :
    Bounded (budget+1) (expected q) := by
  have hf := append_fits q h hb
  have ho := h.ordered
  have ht := h.tail
  have hc := h.count
  have he := h.active hen
  constructor
  · rw [expected_head q hf, expected_tail_nat q hf]
    exact Nat.le_trans ho (Nat.le_succ _)
  · rw [expected_tail_nat q hf]
    exact Nat.add_le_add_right ht 1
  · rw [expected_count_nat q hf]
    exact Nat.add_le_add_right hc 1
  · intro _
    rw [expected_excess q hf, expected_count_nat q hf]
    change _ + ((slotW (entrySt q) (UInt256.ofNat 1)).toNat + 1) ≤ _
    omega

/-- Latch, unlock and the natural fold preserve the same append budget.
The coupled input bound supplies the no-wrap fact needed by the fold. -/
theorem system_control (target excess count cds : UInt256) {budget : Nat}
    (hb : budget < UInt256.size)
    (he : excess ≠ INH → excess.toNat + count.toNat ≤ budget) :
    systemExcess target excess count cds ≠ INH →
      (systemExcess target excess count cds).toNat ≤ budget := by
  intro hen
  by_cases hd : cds ≠ ⟨0⟩
  · exact False.elim (hen (systemExcess_latch _ _ _ _ hd))
  · have hz : cds = ⟨0⟩ := by simpa using hd
    subst cds
    by_cases hi : excess = INH
    · subst excess
      rw [systemExcess_unlock]
      exact Nat.zero_le _
    · have hsum := he hi
      rw [systemExcess, if_neg (by simp), if_neg hi,
        foldWord_eq_nat_of_sum_lt _ _ _ (hsum.trans_lt hb)]
      exact (Nat.sub_le _ _).trans hsum

/-- Actual SYSTEM's independent slot map retains queue order and all budget
bounds. Its drain count must be bounded by the input queue length. -/
theorem system (st : EvmYul.State .EVM) (target drained cds : UInt256) {budget : Nat}
    (h : Bounded budget (slotW st)) (hb : budget < UInt256.size)
    (hn : drained.toNat ≤ QueueArithmetic.length st) :
    Bounded budget (expectedSlot st target drained cds) := by
  obtain ⟨hh, ht⟩ := QueueArithmetic.pointers st target drained cds h.ordered hn
  have ho := h.ordered
  have htail := h.tail
  constructor
  · rw [hh, ht]
    split
    · exact Nat.le_refl _
    · unfold QueueArithmetic.length at hn
      omega
  · rw [ht]
    split
    · exact Nat.zero_le _
    · exact htail
  · rw [expectedSlot_count]
    exact Nat.zero_le _
  · rw [expectedSlot_excess, expectedSlot_count]
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero] using
      system_control target _ _ cds hb h.active

#print axioms initial
#print axioms mono
#print axioms append_fits
#print axioms append
#print axioms system_control
#print axioms system

end Eip8282.Audit.Integrator.AccountedState
