import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! Owner: Dewey, protocol input arithmetic. Proposed mainnet policy only.
Reference EL 0cc100eb190b64b23baba72dac0165652eaec252 and CL
ad0058fd0d34c5dcf504fa51ea2f4f11077b9996; source audit planned at
audit/receipts/direct-pow-count-producer-dewey-20260910.md.
The natural cumulative-difficulty linkage and canonical reward-batch linkage
are explicit inputs. No block-number width, terminal-TD upper bound, fork
selection, hash lookup correctness or protocol adoption is asserted here. -/
namespace Eip8282.Audit.Integrator.ProtocolPowCount
set_option autoImplicit false

def minimumDifficulty : Nat := 131072
def mainnetTTD : Nat := 58750000000000000000000
def maximumCount : Nat := 448226928710937500

/-- External selection of the proposed default policy, not a proved config loader.
The natural hash encoding is zero precisely for the disabled override input. -/
structure MainnetZeroOverride (configuredTTD configuredHash : Nat) : Prop where
  threshold : configuredTTD = mainnetTTD
  no_override : configuredHash = 0

/-- The list excludes genesis and the one terminal crossing block. -/
theorem difficulty_sum_lower (difficulties : List Nat)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d) :
    minimumDifficulty * difficulties.length ≤ difficulties.sum := by
  induction difficulties with
  | nil => simp
  | cons d ds ih =>
    have hd := valid d (by simp)
    have hs := ih (fun x hx => valid x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Genesis contributes to TD but is not a reward batch. Only the parent's TD
is bounded: the terminal block may overshoot the threshold arbitrarily. -/
theorem count_of_terminal_parent (difficulties : List Nat)
    (genesisDifficulty parentTD : Nat)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < mainnetTTD) :
    difficulties.length + 1 ≤ maximumCount := by
  have hs := difficulty_sum_lower difficulties valid
  unfold minimumDifficulty at hs
  unfold mainnetTTD at below
  unfold maximumCount
  omega

theorem maximum_lt_uint64 : maximumCount < 2^64 := by decide +kernel

/-- A ledger prefix may contain fewer batches than the complete terminal
ancestry. The link is to canonical non-genesis batches, not ommer count. -/
theorem reward_count (difficulties : List Nat)
    (genesisDifficulty parentTD configuredTTD configuredHash batches : Nat)
    (policy : MainnetZeroOverride configuredTTD configuredHash)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < configuredTTD)
    (batchLink : batches ≤ difficulties.length + 1) : batches ≤ 2^64 := by
  have hb := count_of_terminal_parent difficulties genesisDifficulty parentTD valid linked
    (by simpa only [policy.threshold] using below)
  exact Nat.le_trans (Nat.le_trans batchLink hb) (Nat.le_of_lt maximum_lt_uint64)

/-- Populate the count interface while leaving withdrawal and migration
producers independent. `batches` must be the same index used by the ledger. -/
theorem counts (difficulties : List Nat)
    (genesisDifficulty parentTD configuredTTD configuredHash batches withdrawals migrations : Nat)
    (policy : MainnetZeroOverride configuredTTD configuredHash)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < configuredTTD)
    (batchLink : batches ≤ difficulties.length + 1)
    (withdrawalBound : withdrawals ≤ 16*2^64) (migrationConserving : migrations = 0) :
    ProtocolCreditEnvelope.Counts batches withdrawals migrations :=
  ⟨reward_count difficulties genesisDifficulty parentTD configuredTTD configuredHash batches
    policy valid linked below batchLink, withdrawalBound, migrationConserving⟩

#print axioms difficulty_sum_lower
#print axioms count_of_terminal_parent
#print axioms maximum_lt_uint64
#print axioms reward_count
#print axioms counts
end Eip8282.Audit.Integrator.ProtocolPowCount
