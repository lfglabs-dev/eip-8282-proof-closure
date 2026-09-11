import Eip8282.Tests.DirectThetaSubmitMutation

/-!
# The funded Theta LOG mutant refutes the same direct submission predicate

The only finite execution receipt is kernel checked in the imported module.
Its pre-domain and financing are independently established below. No new native
axiom, impossible code pin or supplied execution post-state enters the witness.
-/
namespace Eip8282.Tests.DirectThetaSubmitCounterexample

open EvmYul EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Integrator
open MessageCall SystemSpec DirectThetaSubmitMutation

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/- Use the proved receipt rather than re-evaluating the complete call during elaboration. -/
attribute [local irreducible] MessageCall.Context.result

theorem input_size : Eip8282.Audit.Guarantees.PSubmit1.depositInput.size = 184 := by decide +kernel

theorem pre_read (code : ByteArray) (k : UInt256) :
    worldSlot (fixture code).world (fixture code).target k = u256 0 := by rfl

theorem domain (code : ByteArray) : DirectGuarantees.Domain .deposit (fixture code) 0 := by
  refine ⟨⟨mkAccount code ZERO_U256, rfl⟩, rfl, ?_, by decide, ?_, ?_⟩
  · change Eip8282.Audit.Guarantees.PSubmit1.depositInput.size < UInt256.size
    rw [input_size]; decide
  · constructor
    · rw [pre_read, pre_read]
    · rw [pre_read]; decide
    · rw [pre_read]; decide
    · intro _; rw [pre_read, pre_read]; decide
  · right
    change (worldSlot (fixture code).world (fixture code).target (u256 0)).toNat +
      ((worldSlot (fixture code).world (fixture code).target (u256 1)).toNat - 8) ≤ 2892
    rw [pre_read, pre_read]; decide

/-- Real transferred value is funded by the real sender balance before Θ. -/
theorem funded (code : ByteArray) :
    (fixture code).value.toNat ≤ TransferFunding.worldBalance (fixture code).world (fixture code).caller := by
  change (u256 (10^18 + 1)).toNat ≤ (u256 (2*10^18)).toNat
  decide

/-- The fixture contains only two ETH, not an artificial wrapped target credit. -/
theorem funds (code : ByteArray) :
    TransferFunding.worldFunds (fixture code).world = 2*10^18 := by
  let empty : AccountMap .EVM := default
  let first := empty.insert depositAddr (mkAccount code ZERO_U256)
  have h0 := TransferFunding.funds_insert empty depositAddr (mkAccount code ZERO_U256)
  change TransferFunding.worldFunds first + 0 = 0 + 0 at h0
  have h1 := TransferFunding.funds_insert first (toAddress 0x1234)
    (mkAccount ByteArray.empty (u256 (2*10^18)))
  change TransferFunding.worldFunds (fixture code).world + 0 =
    TransferFunding.worldFunds first + 2000000000000000000 at h1
  omega

theorem theta_counterexample :
    ∃ created world gas substate out,
      (fixture PSubmit1Mutant.logSizeMutatedDeposit).result =
        .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectGuarantees.SubmitObserved .deposit (fixture PSubmit1Mutant.logSizeMutatedDeposit)
        created world substate true out := by
  have ht := actual_empty_log
  unfold hasEmptyLog at ht
  cases hr : (fixture PSubmit1Mutant.logSizeMutatedDeposit).result with
  | error e => rw [hr] at ht; cases ht
  | ok result =>
    rcases result with ⟨created, world, gas, substate, success, out⟩
    cases success with
    | false => rw [hr] at ht; cases ht
    | true =>
      rw [hr] at ht
      refine ⟨created, world, gas, substate, out, rfl, ?_⟩
      intro hp
      have huser : (fixture PSubmit1Mutant.logSizeMutatedDeposit).caller ≠ Eip8282.Audit.EvmRunner.sysAddr := by decide
      rw [DirectGuarantees.SubmitObserved, if_neg huser] at hp
      have hn : (fixture PSubmit1Mutant.logSizeMutatedDeposit).calldata.size ≠ 0 := by
        change Eip8282.Audit.Guarantees.PSubmit1.depositInput.size ≠ 0
        rw [input_size]; decide
      have ha := (hp.1.2.2 rfl hn).2.1
      have hl := ha.2.2.1
      change substate.logSeries = #[⟨depositAddr, #[], Eip8282.Audit.Guarantees.PSubmit1.depositInput⟩] at hl
      simp only at ht
      rw [hl] at ht
      change ((1 : Nat) == 1 && some Eip8282.Audit.Guarantees.PSubmit1.depositInput.size == some 0) = true at ht
      rw [input_size] at ht
      cases ht

theorem log_refutes_psubmit :
    ¬ DirectGuarantees.PSubmit .deposit PSubmit1Mutant.logSizeMutatedDeposit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := theta_counterexample
  exact hn (hp _ 0 rfl (domain _) created world gas substate true out hr)

#print axioms domain
#print axioms funded
#print axioms theta_counterexample
#print axioms log_refutes_psubmit

end Eip8282.Tests.DirectThetaSubmitCounterexample
