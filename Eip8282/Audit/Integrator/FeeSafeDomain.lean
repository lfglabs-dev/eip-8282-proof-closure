import Eip8282.Audit.Integrator.MathFee

/-!
# A universally quantified arithmetic domain for the natural fee recurrence

The numerator bound below is an explicit mathematical domain, not a protocol
invariant. A single upper trajectory supplies a kernel-checked certificate;
monotonicity covers every smaller numerator. Its 462-step witness is a proof
budget, not a cutoff in either the natural or word fee definition.
-/
namespace Eip8282.Audit.Integrator.FeeSafeDomain

open EvmYul
open Eip8282.Audit.EntryReach
open MathFee

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- With the same counter, smaller numerator/output/accumulator preserve every
intermediate product and addition bound of the larger trajectory. -/
theorem prefixFits_mono {X Y : Nat} (hX : X ≤ Y) :
    ∀ {n o O a A i : Nat}, o ≤ O → a ≤ A → PrefixFits Y n O A i → PrefixFits X n o a i := by
  intro n
  induction n with
  | zero =>
      intro o O a A i ho ha hf
      obtain ⟨hO, hA, hi⟩ := hf
      exact ⟨ho.trans_lt hO, ha.trans_lt hA, hi⟩
  | succ n ih =>
      intro o O a A i ho ha hf
      obtain ⟨⟨hO, hA, hi⟩, hstep⟩ := hf
      refine ⟨⟨ho.trans_lt hO, ha.trans_lt hA, hi⟩, ?_⟩
      intro hne
      have hAne : A ≠ 0 := by omega
      obtain ⟨hs, hp, hd, hc, hn⟩ := hstep hAne
      have hsum := Nat.add_le_add ha ho
      have hprod := Nat.mul_le_mul hX ha
      exact ⟨hsum.trans_lt hs, hprod.trans_lt hp, hd, hc,
        ih hsum (Nat.div_le_div_right hprod) hn⟩

/-- If the upper trajectory stops within a budget, every componentwise smaller
trajectory with the same counter also stops within that budget. -/
theorem completes_mono {X Y : Nat} (hX : X ≤ Y) :
    ∀ {n o O a A i : Nat} {r : Nat × Nat}, o ≤ O → a ≤ A →
      feeExitNat Y n O A i = some r → ∃ result, feeExitNat X n o a i = some result := by
  intro n
  induction n with
  | zero =>
      intro o O a A i r ho ha hf
      by_cases hA : A = 0
      · have hz : a = 0 := by omega
        subst a
        exact ⟨(o,i), feeExitNat_stopped X o i 0⟩
      · simp [feeExitNat, hA] at hf
  | succ n ih =>
      intro o O a A i r ho ha hf
      by_cases hz : a = 0
      · subst a
        exact ⟨(o,i), feeExitNat_stopped X o i (n+1)⟩
      · have hA : A ≠ 0 := by omega
        simp only [feeExitNat, hA, ↓reduceIte] at hf
        obtain ⟨result, hr⟩ := ih (Nat.add_le_add ha ho)
          (Nat.div_le_div_right (Nat.mul_le_mul hX ha)) hf
        exact ⟨result, by simpa only [feeExitNat, hz, ↓reduceIte] using hr⟩

/-- A structural decision procedure for the finite arithmetic certificate. -/
def prefixFitsDecidable (X : Nat) : (n o a i : Nat) → Decidable (PrefixFits X n o a i)
  | 0, o, a, i => inferInstanceAs (Decidable (o < UInt256.size ∧ a < UInt256.size ∧ i < UInt256.size))
  | n+1, o, a, i =>
      letI := prefixFitsDecidable X n (a+o) (X*a/(i*17)) (1+i)
      inferInstanceAs (Decidable ((o < UInt256.size ∧ a < UInt256.size ∧ i < UInt256.size) ∧
        (a ≠ 0 → a+o < UInt256.size ∧ X*a < UInt256.size ∧ i*17 < UInt256.size ∧
          1+i < UInt256.size ∧ PrefixFits X n (a+o) (X*a/(i*17)) (1+i))))

/-- The concrete upper trajectory's actual stopping budget, computed and then
checked as a witness; it does not alter feeExitNat or quoteWithin. -/
def certificateBudget : Nat := 462

def certificateOutput : Nat :=
  1293016615363553351305261411891033154262342899586402592153715843914719896707

set_option maxRecDepth 100000 in
/-- Kernel-checked arithmetic, including multiplication before division. -/
theorem upper_fits : PrefixFits 2892 certificateBudget 0 17 1 := by
  letI := prefixFitsDecidable 2892 certificateBudget 0 17 1
  decide

theorem upper_stops :
    feeExitNat 2892 certificateBudget 0 17 1 = some (certificateOutput, 463) := by
  decide


/-- Every numerator in the interval has a safe, completed trajectory within
the certified upper budget. This is universally quantified, not an enumeration. -/
theorem domain_certificate (X : Nat) (hX : X ≤ 2892) :
    PrefixFits X certificateBudget 0 17 1 ∧
      ∃ price, quoteWithinNat X certificateBudget = some price := by
  refine ⟨prefixFits_mono hX (Nat.le_refl 0) (Nat.le_refl 17) upper_fits, ?_⟩
  obtain ⟨⟨o,i⟩, hr⟩ := completes_mono hX (Nat.le_refl 0) (Nat.le_refl 17) upper_stops
  exact ⟨o/17, by simp only [quoteWithinNat, hr, Option.map_some]⟩

/-- Natural and word quotes both complete and agree throughout the domain. -/
theorem safe_quote (X : Nat) (hX : X ≤ 2892) :
    ∃ price : UInt256,
      quoteWithin (UInt256.ofNat X) certificateBudget = some price ∧
      MathQuoteCompletes X price.toNat := by
  obtain ⟨hf, p, hp⟩ := domain_certificate X hX
  have hx : X < UInt256.size := lt_of_le_of_lt hX (by decide)
  obtain ⟨price, hword, he⟩ := word_quote_of_math hx hf hp
  exact ⟨price, hword, certificateBudget, by rwa [he]⟩

/-- Any completed word quote in the domain is the mathematical tariff,
regardless of the budget used to witness it. The certificate is not a
semantic iteration cutoff. -/
theorem any_quote_agrees (X : Nat) (hX : X ≤ 2892) {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat X) n = some price) : MathQuoteCompletes X price.toNat := by
  obtain ⟨certified, hc, hm⟩ := safe_quote X hX
  have he := quoteWithin_unique hq hc
  simpa only [he] using hm

/-- Word-input form, for consumers that independently justify the effective
numerator's domain from an actual call or a protocol state. -/
theorem operational_quote_agrees (X : UInt256) (hX : X.toNat ≤ 2892)
    {n : Nat} {price : UInt256} (hq : quoteWithin X n = some price) :
    MathQuoteCompletes X.toNat price.toNat := by
  apply any_quote_agrees X.toNat hX
  simpa only [ofNat_toNat'] using hq

#print axioms domain_certificate
#print axioms safe_quote
#print axioms any_quote_agrees
#print axioms operational_quote_agrees

#print axioms prefixFits_mono
#print axioms completes_mono
#print axioms upper_fits
#print axioms upper_stops

end Eip8282.Audit.Integrator.FeeSafeDomain
