import Eip8282.Audit.Integrator.FundedDomain

/-!
# Conditional arithmetic bounds on external funding

All quantities below are natural numbers. Genesis and PoW credits are in wei;
withdrawal amounts are in gwei. Lists are accounting inputs, not an abstract
state-transition semantics or a claim that actual Ethereum history has these
bounds. No genesis parser, EVM conservation, call admission, or fork
correspondence is asserted here. Those obligations must supply the hypotheses
before the value bound can discharge FundedDomain's funding premise.
-/
namespace Eip8282.Audit.Integrator.FundingBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- An upper bound for lists whose entries are independently bounded. -/
theorem sum_le_length_mul (xs : List Nat) (bound : Nat)
    (h : ∀ x ∈ xs, x ≤ bound) : xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Total credits counted from external sources. Every withdrawal is counted,
even if it returns a deposit already included in the initial funding. This is
an overcount suitable for a supply upper bound once conservation is proved. -/
def externalCredits (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat)) : Nat :=
  genesis + powRewards.sum + (withdrawals.map List.sum).sum * 10^9

/-- Coarse arithmetic envelope; perPayload is an explicit domain parameter. -/
def envelope (perPayload : Nat) : Nat :=
  2^96 + 2^64 * (16 * 10^18) + (2^64 * (perPayload * 2^64)) * 10^9

/-- The supplied genesis/issuance/list bounds imply the envelope. The bound
2^64 on list length permits all distinct values of a 64-bit index; distinctness
or protocol provenance itself must be justified outside this lemma. -/
theorem credits_le_envelope (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat)) (perPayload : Nat)
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ perPayload ∧ ∀ amount ∈ ws, amount < 2^64) :
    externalCredits genesis powRewards withdrawals ≤ envelope perPayload := by
  have hp := (sum_le_length_mul powRewards (16 * 10^18) hpow).trans
    (Nat.mul_le_mul_right (16 * 10^18) hpowCount)
  have hw : ∀ amount ∈ withdrawals.map List.sum, amount ≤ perPayload * 2^64 := by
    intro amount hm
    obtain ⟨ws, hws, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hlen, heach⟩ := hwithdrawals ws hws
    exact (sum_le_length_mul ws (2^64) (fun a ha => (heach a ha).le)).trans
      (Nat.mul_le_mul_right (2^64) hlen)
  have hs := sum_le_length_mul (withdrawals.map List.sum) (perPayload * 2^64) hw
  simp only [List.length_map] at hs
  have hb := hs.trans (Nat.mul_le_mul_right (perPayload * 2^64) hpayloadCount)
  have hwWei := Nat.mul_le_mul_right (10^9) hb
  exact Nat.add_le_add (Nat.add_le_add hgenesis.le hp) hwWei

/-- Kernel arithmetic only; this certifies no actual genesis or execution. -/
theorem envelope_16_lt : envelope 16 < 2^163 := by decide

/-- Even the much weaker payload-size allowance leaves a wide margin. -/
theorem envelope_flexible_lt : envelope (2^64) < 2^223 := by decide

theorem bound_163_lt_funding : 2^163 < FundedDomain.fundingCeiling := by decide

theorem bound_223_lt_funding : 2^223 < FundedDomain.fundingCeiling := by decide

/-- Standard conditional aggregate bound: at most 16 withdrawals per payload. -/
theorem credits_lt_163 (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat))
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ 16 ∧ ∀ amount ∈ ws, amount < 2^64) :
    externalCredits genesis powRewards withdrawals < 2^163 :=
  lt_of_le_of_lt (credits_le_envelope genesis powRewards withdrawals 16
    hgenesis hpowCount hpow hpayloadCount hwithdrawals) envelope_16_lt

/-- Flexible conditional aggregate bound, without fixing the list limit to 16. -/
theorem credits_lt_223 (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat))
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ 2^64 ∧ ∀ amount ∈ ws, amount < 2^64) :
    externalCredits genesis powRewards withdrawals < 2^223 :=
  lt_of_le_of_lt (credits_le_envelope genesis powRewards withdrawals (2^64)
    hgenesis hpowCount hpow hpayloadCount hwithdrawals) envelope_flexible_lt

theorem credits_lt_funding (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat))
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ 16 ∧ ∀ amount ∈ ws, amount < 2^64) :
    externalCredits genesis powRewards withdrawals < FundedDomain.fundingCeiling :=
  (credits_lt_163 genesis powRewards withdrawals hgenesis hpowCount hpow
    hpayloadCount hwithdrawals).trans bound_163_lt_funding

theorem flexible_credits_lt_funding (genesis : Nat) (powRewards : List Nat)
    (withdrawals : List (List Nat))
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ 2^64 ∧ ∀ amount ∈ ws, amount < 2^64) :
    externalCredits genesis powRewards withdrawals < FundedDomain.fundingCeiling :=
  (credits_lt_223 genesis powRewards withdrawals hgenesis hpowCount hpow
    hpayloadCount hwithdrawals).trans bound_223_lt_funding

/-- The funding implication is arithmetic. Sufficient funds, the individual
balance-to-total comparison, and the actual world's total budget are supplied
facts; this theorem does not establish any of them from Θ or Υ. -/
theorem value_lt_funding_of_budget (value balance total budget : Nat)
    (hfunded : value ≤ balance) (hbalance : balance ≤ total)
    (htotal : total ≤ budget) (hbudget : budget < FundedDomain.fundingCeiling) :
    value < FundedDomain.fundingCeiling :=
  lt_of_le_of_lt (hfunded.trans (hbalance.trans htotal)) hbudget

/-- Actual admission may reserve fees as well as transferred value. In Nat,
that stronger funding premise supplies the needed value comparison. -/
theorem value_lt_funding_of_reserved_budget (value fees balance total budget : Nat)
    (hfunded : value + fees ≤ balance) (hbalance : balance ≤ total)
    (htotal : total ≤ budget) (hbudget : budget < FundedDomain.fundingCeiling) :
    value < FundedDomain.fundingCeiling :=
  value_lt_funding_of_budget value balance total budget (by omega) hbalance htotal hbudget

/-- Composition with the conditional standard issuance envelope. Conservation
and admission remain visible premises, not assumed desired call poststates. -/
theorem value_lt_funding_of_credits (value balance total genesis : Nat)
    (powRewards : List Nat) (withdrawals : List (List Nat))
    (hfunded : value ≤ balance) (hbalance : balance ≤ total)
    (htotal : total ≤ externalCredits genesis powRewards withdrawals)
    (hgenesis : genesis < 2^96)
    (hpowCount : powRewards.length ≤ 2^64)
    (hpow : ∀ reward ∈ powRewards, reward ≤ 16 * 10^18)
    (hpayloadCount : withdrawals.length ≤ 2^64)
    (hwithdrawals : ∀ ws ∈ withdrawals,
      ws.length ≤ 16 ∧ ∀ amount ∈ ws, amount < 2^64) :
    value < FundedDomain.fundingCeiling :=
  value_lt_funding_of_budget value balance total _ hfunded hbalance htotal
    (credits_lt_funding genesis powRewards withdrawals hgenesis hpowCount hpow
      hpayloadCount hwithdrawals)

#print axioms credits_le_envelope
#print axioms envelope_16_lt
#print axioms envelope_flexible_lt
#print axioms credits_lt_163
#print axioms credits_lt_223
#print axioms credits_lt_funding
#print axioms flexible_credits_lt_funding
#print axioms value_lt_funding_of_reserved_budget
#print axioms value_lt_funding_of_credits

end Eip8282.Audit.Integrator.FundingBounds
