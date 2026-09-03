import Eip8282.Audit.EntryReach.Words
import Eip8282.Audit.UniversalBoundary

/-!
# The fee loop on words is `fakeExponential.go` on naturals

`Path.feeExit` is the `fake_expo` recurrence exactly as the pinned bytes compute
it, in 256-bit words. `Model.fakeExponential.go` is the same recurrence in
unbounded naturals. `UniversalBoundary.fakeExpoFitsWord` says, iteration by
iteration, that none of the three products and sums the loop forms leaves the
word, and that the loop reaches `accum = 0` before its fuel is spent. Under that
witness the two recurrences march in step, so the word loop terminates where the
natural one does and returns the same quotient: the fee `Model.currentFee` quotes.

This is the discharge of the `FeeLoopEnds` premise every uninhibited user
endpoint of `EntryReach.Deposit` / `EntryReach.Exit` carries, from the
word-exactness witness `WordExactCall` alone.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul
open Eip8282.Audit.Model (fakeExponential)
open Eip8282.Audit.UniversalBoundary (fakeExpoFitsWord FeeQuoteNoWrap)

theorem toNat_seventeen : (UInt256.ofNat 17).toNat = 17 := rfl
theorem toNat_one : (UInt256.ofNat 1).toNat = 1 := rfl

/-- **`feeExit` follows `go` while the words fit.** -/
theorem feeExit_of_fits (X : UInt256) :
    ∀ (fuel : Nat) (o a i : UInt256),
      fakeExpoFitsWord X.toNat 17 fuel i.toNat o.toNat a.toNat = true → 0 < i.toNat →
      ∃ o' i' : UInt256, feeExit X fuel o a i = some (o', i') ∧
        o'.toNat / 17 = fakeExponential.go X.toNat 17 fuel i.toNat o.toNat a.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro o a i hfit _
    simp only [fakeExpoFitsWord, beq_iff_eq] at hfit
    have ha : a = ⟨0⟩ := (eq_zero_iff_toNat a).mpr hfit
    refine ⟨o, i, ?_, ?_⟩
    · simp [feeExit, ha]
    · simp [fakeExponential.go]
  | succ fuel ih =>
    intro o a i hfit hi
    by_cases ha : a = ⟨0⟩
    · refine ⟨o, i, by simp [feeExit, ha], ?_⟩
      have h0 : a.toNat = 0 := by rw [ha]; rfl
      rw [h0, Eip8282.Audit.Guarantees.PSubmit1.FakeExpo.go_accum_zero]
    · have ha0 : a.toNat ≠ 0 := fun h => ha ((eq_zero_iff_toNat a).mpr h)
      simp only [fakeExpoFitsWord, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        decide_eq_true_eq] at hfit
      rcases hfit with h0 | ⟨⟨⟨hsum, hmul⟩, hden⟩, hrest⟩
      · exact absurd h0 ha0
      have hstep : feeExit X (fuel + 1) o a i
          = feeExit X fuel (a + o) ((X * a) / (i * UInt256.ofNat 17)) (UInt256.ofNat 1 + i) := by
        simp [feeExit, ha]
      have hi17 : (i * UInt256.ofNat 17).toNat = 17 * i.toNat := by
        rw [toNat_mul_of_lt _ _ (by rw [toNat_seventeen, Nat.mul_comm]; exact hden), toNat_seventeen,
          Nat.mul_comm]
      have hXa : (X * a).toNat = a.toNat * X.toNat := by
        rw [toNat_mul_of_lt _ _ (by rw [Nat.mul_comm]; exact hmul), Nat.mul_comm]
      have hao : (a + o).toNat = o.toNat + a.toNat := by
        rw [toNat_add_of_lt _ _ (by rw [Nat.add_comm]; exact hsum), Nat.add_comm]
      have hi1 : (UInt256.ofNat 1 + i).toNat = i.toNat + 1 := by
        rw [toNat_add_of_lt _ _ (by rw [toNat_one]; rw [size_eq] at hden ⊢; omega), toNat_one,
          Nat.add_comm]
      have hq : ((X * a) / (i * UInt256.ofNat 17)).toNat = a.toNat * X.toNat / (17 * i.toNat) := by
        rw [toNat_div, hXa, hi17]
      obtain ⟨o', i', hexit, hval⟩ := ih (a + o) ((X * a) / (i * UInt256.ofNat 17))
        (UInt256.ofNat 1 + i) (by rw [hi1, hao, hq]; exact hrest) (by rw [hi1]; omega)
      refine ⟨o', i', hstep.trans hexit, ?_⟩
      rw [Eip8282.Audit.Guarantees.PSubmit1.FakeExpo.go_step _ _ _ _ _ _ ha0, hval, hi1, hao, hq]

end Eip8282.Audit.EntryReach
