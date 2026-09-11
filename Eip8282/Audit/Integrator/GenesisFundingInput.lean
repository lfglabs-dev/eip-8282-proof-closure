import Mathlib.Algebra.BigOperators.Group.List.Basic
import Eip8282.Audit.Integrator.GenesisFundingData

/-!
# Kernel-certified sum of the complete generated genesis allocation input

The finite input retains all 8,893 address/credit pairs from the source asset.
These theorems check the generated Lean data, not JSON parsing, construction of
an account world, canonical genesis adoption, future issuance or a history.
The exact source-byte and extraction checks are external reproducibility
receipts. No native_decide or assumed sum is used in the arithmetic proof.
-/
namespace Eip8282.Audit.Integrator.GenesisFundingInput

open GenesisFundingData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Sum of every allocation credit, including zero entries. -/
def totalCredit : Nat := (allocations.map Prod.snd).sum

theorem allocation_count : allocations.length = 8893 := by
  decide +kernel

theorem allocation_addresses_fit : ∀ entry ∈ allocations, entry.1 < 2^160 := by
  decide +kernel

theorem total_credit_exact : totalCredit = 72009990499480000000000000 := by
  decide +kernel

/-- A bound on this concrete complete input, not a protocol supply invariant. -/
theorem total_credit_lt_96 : totalCredit < 2^96 := by
  rw [total_credit_exact]
  decide +kernel

/-- Any independently justified world-funding upper bound by this input can
consume its numeric envelope; establishing that input correspondence is separate. -/
theorem bounded_by_input_lt_96 (funds : Nat) (h : funds ≤ totalCredit) : funds < 2^96 :=
  Nat.lt_of_le_of_lt h total_credit_lt_96

#print axioms allocation_count
#print axioms allocation_addresses_fit
#print axioms total_credit_exact
#print axioms total_credit_lt_96
#print axioms bounded_by_input_lt_96
end Eip8282.Audit.Integrator.GenesisFundingInput
