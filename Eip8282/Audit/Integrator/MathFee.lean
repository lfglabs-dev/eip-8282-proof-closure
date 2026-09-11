import Eip8282.Audit.EntryReach.FeeQuote

/-!
# Mathematical fees and exact finite prefixes

This specification uses natural arithmetic and an explicit completion result.
Fuel exhaustion is `none`, never a partial tariff. No fixed iteration bound is
part of the specification. `PrefixFits` is an arithmetic side condition on a
finite prefix, not a termination assumption or a protocol reachability claim.
The correspondence below concerns the fee helper; it does not execute a call.
-/

namespace Eip8282.Audit.Integrator.MathFee

open EvmYul
open Eip8282.Audit.EntryReach

/-- The mathematical recurrence, with output and counter when it stops. -/
def feeExitNat (X : Nat) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, o, a, i => if a = 0 then some (o, i) else none
  | n + 1, o, a, i =>
      if a = 0 then some (o, i)
      else feeExitNat X n (a + o) (X * a / (i * 17)) (1 + i)

/-- Only a completed recurrence supplies a mathematical tariff. -/
def quoteWithinNat (X steps : Nat) : Option Nat :=
  (feeExitNat X steps 0 17 1).map (·.1 / 17)

def MathQuoteCompletes (X price : Nat) : Prop :=
  ∃ steps, quoteWithinNat X steps = some price

theorem feeExitNat_stopped (X o i n : Nat) :
    feeExitNat X n o 0 i = some (o, i) := by
  cases n <;> simp [feeExitNat]

theorem feeExitNat_stable {X : Nat} :
    ∀ {n o a i : Nat} {r : Nat × Nat},
      feeExitNat X n o a i = some r →
      ∀ {m : Nat}, n ≤ m → feeExitNat X m o a i = some r := by
  intro n
  induction n with
  | zero =>
      intro o a i r h m _
      by_cases ha : a = 0
      · subst a
        rw [feeExitNat_stopped] at h
        obtain rfl := Option.some.inj h
        exact feeExitNat_stopped X o i m
      · simp [feeExitNat, ha] at h
  | succ n ih =>
      intro o a i r h m hm
      by_cases ha : a = 0
      · subst a
        rw [feeExitNat_stopped] at h
        obtain rfl := Option.some.inj h
        exact feeExitNat_stopped X o i m
      · cases m with
        | zero => omega
        | succ m =>
          simp only [feeExitNat, ha, ↓reduceIte] at h ⊢
          exact ih h (Nat.le_of_succ_le_succ hm)

theorem quoteWithinNat_stable {X m n p : Nat}
    (h : quoteWithinNat X m = some p) (hle : m ≤ n) :
    quoteWithinNat X n = some p := by
  unfold quoteWithinNat at h ⊢
  cases hf : feeExitNat X m 0 17 1 with
  | none => simp [hf] at h
  | some r =>
      rw [feeExitNat_stable hf hle]
      simpa [hf] using h

theorem quoteWithinNat_unique {X m n p q : Nat}
    (hp : quoteWithinNat X m = some p) (hq : quoteWithinNat X n = some q) :
    p = q := by
  rcases le_total m n with h | h
  · rw [quoteWithinNat_stable hp h] at hq
    exact Option.some.inj hq
  · rw [quoteWithinNat_stable hq h] at hp
    exact (Option.some.inj hp).symm

theorem mathQuoteCompletes_unique {X p q : Nat}
    (hp : MathQuoteCompletes X p) (hq : MathQuoteCompletes X q) : p = q := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  exact quoteWithinNat_unique hm hn

/-- Once the counter exceeds the numerator, each nonzero accumulator strictly
decreases. This is a natural-number argument, with no EVM fit assumption. -/
theorem feeExitNat_terminates_above (X a : Nat) :
    ∀ o i : Nat, X < i → ∃ n r, feeExitNat X n o a i = some r := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro o i hi
      by_cases ha : a = 0
      · subst a
        exact ⟨0, (o, i), feeExitNat_stopped X o i 0⟩
      · have hden : X < i * 17 := by omega
        have hsmall : X * a / (i * 17) < a :=
          Nat.div_lt_of_lt_mul
            (Nat.mul_lt_mul_of_pos_right hden (Nat.pos_of_ne_zero ha))
        obtain ⟨n, r, hr⟩ := ih _ hsmall (a + o) (1 + i) (by omega)
        refine ⟨n + 1, r, ?_⟩
        simpa only [feeExitNat, ha, ↓reduceIte] using hr

/-- Advance a finite number of steps to a counter above the numerator, unless
the recurrence stops earlier. The accumulator may grow during this prefix. -/
theorem feeExitNat_terminates_after (X k : Nat) :
    ∀ o a i : Nat, X < i + k → ∃ n r, feeExitNat X n o a i = some r := by
  induction k with
  | zero =>
      intro o a i hi
      exact feeExitNat_terminates_above X a o i (by omega)
  | succ k ih =>
      intro o a i hi
      by_cases ha : a = 0
      · subst a
        exact ⟨0, (o, i), feeExitNat_stopped X o i 0⟩
      · obtain ⟨n, r, hr⟩ := ih (a + o) (X * a / (i * 17)) (1 + i) (by omega)
        refine ⟨n + 1, r, ?_⟩
        simpa only [feeExitNat, ha, ↓reduceIte] using hr

/-- Every natural recurrence terminates. Its witness is derived, not assumed;
this does not imply EVM termination when arithmetic wraps. -/
theorem feeExitNat_terminates (X o a i : Nat) :
    ∃ n r, feeExitNat X n o a i = some r :=
  feeExitNat_terminates_after X (X + 1) o a i (by omega)

theorem mathQuoteCompletes_exists (X : Nat) : ∃ price, MathQuoteCompletes X price := by
  obtain ⟨n, ⟨o, i⟩, h⟩ := feeExitNat_terminates X 0 17 1
  exact ⟨o / 17, n, by simp [quoteWithinNat, h]⟩

/-- The mathematical tariff is total and single-valued, without a fuel cutoff. -/
theorem mathQuoteCompletes_existsUnique (X : Nat) :
    ∃! price, MathQuoteCompletes X price := by
  obtain ⟨p, hp⟩ := mathQuoteCompletes_exists X
  exact ⟨p, hp, fun q hq => mathQuoteCompletes_unique hq hp⟩

/-- The mathematical state is represented exactly by three EVM words. -/
def StateFits (o a i : Nat) : Prop :=
  o < UInt256.size ∧ a < UInt256.size ∧ i < UInt256.size

/-- Every intermediate operation in the requested prefix fits a word.
At zero budget this checks representation only: it does not require stopping.
The product bounds precede division, because the EVM wraps before dividing.
Counter increment is checked explicitly as well. -/
def PrefixFits (X : Nat) : Nat → Nat → Nat → Nat → Prop
  | 0, o, a, i => StateFits o a i
  | n + 1, o, a, i => StateFits o a i ∧ (a ≠ 0 →
      a + o < UInt256.size ∧ X * a < UInt256.size ∧
      i * 17 < UInt256.size ∧ 1 + i < UInt256.size ∧
      PrefixFits X n (a + o) (X * a / (i * 17)) (1 + i))

private theorem of_toNat {w : UInt256} {n : Nat} (h : w.toNat = n) :
    w = UInt256.ofNat n := by
  rw [← ofNat_toNat' w, h]

private theorem toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := Nat.mod_eq_of_lt h

private theorem word_zero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl

private theorem add_exact {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (hs : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply of_toNat
  change ((UInt256.ofNat a).toNat + (UInt256.ofNat b).toNat) % UInt256.size = _
  rw [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb, Nat.mod_eq_of_lt hs]

private theorem mul_exact {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (hs : a * b < UInt256.size) :
    UInt256.ofNat a * UInt256.ofNat b = UInt256.ofNat (a * b) := by
  apply of_toNat
  change ((UInt256.ofNat a).toNat * (UInt256.ofNat b).toNat) % UInt256.size = _
  rw [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb, Nat.mod_eq_of_lt hs]

private theorem div_exact {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) :
    UInt256.ofNat a / UInt256.ofNat b = UInt256.ofNat (a / b) := by
  apply of_toNat
  change (UInt256.ofNat a).toNat / (UInt256.ofNat b).toNat = _
  rw [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]

private theorem zero_iff {a : Nat} (ha : a < UInt256.size) :
    UInt256.ofNat a = (⟨0⟩ : UInt256) ↔ a = 0 := by
  constructor
  · intro h
    have he := congrArg UInt256.toNat h
    simpa [toNat_ofNat_of_lt ha] using he
  · rintro rfl
    rfl

/-- Arbitrary finite-prefix correspondence, including exhaustion (`none`).
The right-hand side is independently defined over natural numbers. -/
theorem feeExit_corresponds {X : Nat} (hX : X < UInt256.size) :
    ∀ (n o a i : Nat), PrefixFits X n o a i →
      (feeExit (UInt256.ofNat X) n (UInt256.ofNat o)
        (UInt256.ofNat a) (UInt256.ofNat i)).map
          (fun r => (r.1.toNat, r.2.toNat)) = feeExitNat X n o a i := by
  intro n
  induction n with
  | zero =>
      intro o a i hf
      obtain ⟨ho, ha, hi⟩ := hf
      simp [feeExit, feeExitNat, zero_iff ha,
        toNat_ofNat_of_lt ho, toNat_ofNat_of_lt hi]
  | succ n ih =>
      intro o a i hf
      obtain ⟨⟨ho, ha, hi⟩, hstep⟩ := hf
      by_cases hzero : a = 0
      · subst a
        simp [feeExit, feeExitNat, word_zero,
          toNat_ofNat_of_lt ho, toNat_ofNat_of_lt hi]
      · obtain ⟨hs, hp, hd, hc, hnext⟩ := hstep hzero
        have hwzero : UInt256.ofNat a ≠ (⟨0⟩ : UInt256) :=
          fun h => hzero ((zero_iff ha).mp h)
        simp only [feeExit, feeExitNat, hwzero, hzero, ↓reduceIte]
        rw [add_exact ha ho hs, mul_exact hX ha hp,
          mul_exact hi (by decide : 17 < UInt256.size) hd, div_exact hp hd,
          add_exact (by decide : 1 < UInt256.size) hi hc]
        exact ih _ _ _ hnext

/-- The completed EVM-helper price agrees with the mathematical evaluator
at any prefix satisfying the explicit arithmetic bounds. -/
theorem quoteWithin_corresponds {X n : Nat} (hX : X < UInt256.size)
    (hf : PrefixFits X n 0 17 1) :
    (quoteWithin (UInt256.ofNat X) n).map UInt256.toNat = quoteWithinNat X n := by
  have h := feeExit_corresponds hX n 0 17 1 hf
  rw [word_zero] at h
  unfold quoteWithin quoteWithinNat
  cases hw : feeExit (UInt256.ofNat X) n ⟨0⟩ (UInt256.ofNat 17)
      (UInt256.ofNat 1) with
  | none =>
      rw [hw] at h
      simp only [Option.map_none] at h
      simp [← h]
  | some r =>
      rw [hw] at h
      simp only [Option.map_some] at h
      rw [← h]
      simp only [Option.map_some]
      rfl

/-- In particular, a completed natural prefix cannot correspond to an
unfinished word prefix when all its intermediates fit. -/
theorem word_quote_of_math {X n p : Nat} (hX : X < UInt256.size)
    (hf : PrefixFits X n 0 17 1) (hq : quoteWithinNat X n = some p) :
    ∃ price : UInt256,
      quoteWithin (UInt256.ofNat X) n = some price ∧ price.toNat = p := by
  have h := quoteWithin_corresponds hX hf
  rw [hq] at h
  cases hw : quoteWithin (UInt256.ofNat X) n with
  | none => simp [hw] at h
  | some price =>
      refine ⟨price, rfl, ?_⟩
      simpa [hw] using h

/-- Completion and arithmetic correspondence are separate obligations.
The witness has no prescribed maximum number of iterations. -/
theorem mathQuoteCompletes_of_word {X n : Nat} {price : UInt256}
    (hX : X < UInt256.size) (hf : PrefixFits X n 0 17 1)
    (hq : quoteWithin (UInt256.ofNat X) n = some price) :
    MathQuoteCompletes X price.toNat := by
  refine ⟨n, ?_⟩
  rw [← quoteWithin_corresponds hX hf, hq]
  rfl

/-- A zero budget cannot manufacture a partial mathematical quote. -/
theorem quoteWithinNat_zero (X : Nat) : quoteWithinNat X 0 = none := by
  simp [quoteWithinNat, feeExitNat]

/-- An already stopped mathematical loop also returns at zero budget. -/
theorem feeExitNat_stopped_zero (X o i : Nat) :
    feeExitNat X 0 o 0 i = some (o, i) := feeExitNat_stopped X o i 0

#print axioms feeExit_corresponds
#print axioms quoteWithin_corresponds
#print axioms mathQuoteCompletes_unique
#print axioms feeExitNat_terminates
#print axioms mathQuoteCompletes_existsUnique
#print axioms mathQuoteCompletes_of_word

end Eip8282.Audit.Integrator.MathFee
