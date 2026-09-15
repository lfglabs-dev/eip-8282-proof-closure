import Eip8282.Audit.Integrator.GenesisFundingData
import Eip8282.Audit.Integrator.TransferFunding
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## GenesisFundingInput -/

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

end

section

/-! ## GenesisFundingWorld -/

/-!
# Account-map funding from the complete allocation input

This constructs the EVM account map from every generated allocation and derives
its initial-funds bound. The source JSON/parser and reference genesis loader
correspondence remain separate; naming this world does not adopt it as Ethereum's
canonical state. The finite-map bound even tolerates repeated addresses, because
replacing an allocation cannot increase funds beyond all input credits.
-/
namespace Eip8282.Audit.Integrator.GenesisFundingWorld
open EvmYul EvmYul.EVM
open TransferFunding
set_option autoImplicit false

def allocated (credit : Nat) : Account .EVM :=
  { (default : Account .EVM) with balance := UInt256.ofNat credit }

def populate : List (Nat × Nat) → AccountMap .EVM → AccountMap .EVM
  | [], world => world
  | (address,credit)::rest, world =>
    populate rest (world.insert (AccountAddress.ofUInt256 (UInt256.ofNat address)) (allocated credit))

/-- The actual map insert's previous balance is debited from the finite sum.
No injective-address or credit-word-fit premise is needed for this upper bound. -/
theorem insertion_bound (world : AccountMap .EVM) (address credit : Nat) :
    worldFunds (world.insert (AccountAddress.ofUInt256 (UInt256.ofNat address)) (allocated credit)) ≤
      worldFunds world + credit := by
  have hi := funds_insert world (AccountAddress.ofUInt256 (UInt256.ofNat address)) (allocated credit)
  have hw : (allocated credit).balance.toNat ≤ credit := Nat.mod_le _ _
  omega

theorem populate_bound (entries : List (Nat × Nat)) (world : AccountMap .EVM) :
    worldFunds (populate entries world) ≤ worldFunds world + (entries.map Prod.snd).sum := by
  induction entries generalizing world with
  | nil => simp [populate]
  | cons entry rest ih =>
    obtain ⟨address,credit⟩ := entry
    have hi := insertion_bound world address credit
    have ht := ih (world.insert (AccountAddress.ofUInt256 (UInt256.ofNat address)) (allocated credit))
    simp only [populate, List.map_cons, List.sum_cons]
    omega

def world : AccountMap .EVM := populate GenesisFundingData.allocations ∅

theorem initial_funds_le : worldFunds world ≤ GenesisFundingInput.totalCredit := by
  have h := populate_bound GenesisFundingData.allocations ∅
  unfold world GenesisFundingInput.totalCredit
  simpa only [show worldFunds (∅ : AccountMap .EVM) = 0 from rfl, Nat.zero_add] using h

/-- This bound is derived for the constructed complete-input account map. -/
theorem initial_funds_lt_96 : worldFunds world < 2^96 :=
  initial_funds_le.trans_lt GenesisFundingInput.total_credit_lt_96

#print axioms insertion_bound
#print axioms populate_bound
#print axioms initial_funds_le
#print axioms initial_funds_lt_96
end Eip8282.Audit.Integrator.GenesisFundingWorld

end
