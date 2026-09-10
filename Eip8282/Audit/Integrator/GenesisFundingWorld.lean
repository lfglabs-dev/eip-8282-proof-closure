import Eip8282.Audit.Integrator.GenesisFundingInput
import Eip8282.Audit.Integrator.TransferFunding

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
