import Eip8282.Audit.Integrator.SuccessfulQuote
import Eip8282.Audit.Integrator.AdmissionInversion
import Eip8282.Audit.Integrator.TransferFrame
import Eip8282.Audit.Integrator.FeeSafeDomain

/-!
# Actual user-call admission and natural getter fee

The successful-call input is actual Θ execution. Completion, checked payment
and returned getter price are derived, at arbitrary gas/fuel. The mathematical
fee theorem uses an explicit bound on the independently computed pre-call
natural numerator, not a bound on an already-wrapped word.
-/
namespace Eip8282.Audit.Integrator.SuccessfulUser

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open MessageCall CallBridge CallSuccess SuccessfulQuote AdmissionInversion
open Eip8282.Audit.Correspondence (runtimeCode)

/-- The agreed natural fee numerator, observed before Θ transfers value. -/
def numerator (c : Context) (target : Nat) : Nat :=
  (SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0)).toNat +
    ((SystemSpec.worldSlot c.world c.target (UInt256.ofNat 1)).toNat-target)

theorem deposit_admission (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Deposit.excessWord q ≠ INH ∧ ∃ n price,
      quoteWithin (Deposit.effExcess q) n = some price ∧
      ((c.calldata.size = 0 ∧ c.value = ⟨0⟩ ∧ out = price.toByteArray) ∨
       (c.calldata.size = 184 ∧ 1000000000 ≤ SubmissionCall.amount c.calldata ∧
        price.toNat+1000000000*SubmissionCall.amount c.calldata ≤ c.value.toNat)) := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  obtain ⟨hen, n, price, hq, hc⟩ := deposit_user_success_inputs _ huser hdata he
  refine ⟨hen, n, price, hq, ?_⟩
  simpa only [DepositInputs, codeCall, Context.environment, hactual] using hc

theorem exit_admission (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Exit.excessWord q ≠ INH ∧ ∃ n price,
      quoteWithin (Exit.effExcess q) n = some price ∧
      ((c.calldata.size = 0 ∧ c.value = ⟨0⟩ ∧ out = price.toByteArray) ∨
       (c.calldata.size = 48 ∧ price.toNat ≤ c.value.toNat)) := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  obtain ⟨hen, n, price, hq, hc⟩ := exit_user_success_inputs _ huser hdata he
  refine ⟨hen, n, price, hq, ?_⟩
  simpa only [ExitInputs, codeCall, Context.environment, hactual] using hc

theorem deposit_numerator (c : Context) (hcode : c.code = runtimeCode .deposit) (steps : Nat)
    (hb : numerator c 8 ≤ 2892) :
    (Deposit.effExcess (codeCall c hcode steps)).toNat = numerator c 8 := by
  rw [← ControlSpec.deposit_feeInput, ControlSpec.feeInput_toNat]
  change ((Deposit.excessWord (codeCall c hcode steps)).toNat +
    ((Deposit.countWord (codeCall c hcode steps)).toNat-8)) % UInt256.size = _
  change ((slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 0)).toNat +
    ((slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 1)).toNat-8)) % UInt256.size = _
  rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hb (by decide))

theorem exit_numerator (c : Context) (hcode : c.code = runtimeCode .exit) (steps : Nat)
    (hb : numerator c 2 ≤ 2892) :
    (Exit.effExcess (codeCall c hcode steps)).toNat = numerator c 2 := by
  rw [← ControlSpec.exit_feeInput, ControlSpec.feeInput_toNat]
  change ((slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 0)).toNat +
    ((slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 1)).toNat-2)) % UInt256.size = _
  rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hb (by decide))

theorem deposit_getter_math (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size = 0) (hbound : numerator c 8 ≤ 2892)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ∃ price : UInt256, c.value = ⟨0⟩ ∧ out = price.toByteArray ∧
      MathFee.MathQuoteCompletes (numerator c 8) price.toNat := by
  obtain ⟨_, n, price, hq, hc⟩ := deposit_admission c hcode huser hactual
    (by rw [hdata]; decide) h
  have hn := deposit_numerator c hcode (c.fuel-1) hbound
  have hm := FeeSafeDomain.operational_quote_agrees _ (by rw [hn]; exact hbound) hq
  rw [hn] at hm
  rcases hc with ⟨_, hv, ho⟩ | ⟨hs, _⟩
  · exact ⟨price, hv, ho, hm⟩
  · omega

theorem exit_getter_math (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size = 0) (hbound : numerator c 2 ≤ 2892)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ∃ price : UInt256, c.value = ⟨0⟩ ∧ out = price.toByteArray ∧
      MathFee.MathQuoteCompletes (numerator c 2) price.toNat := by
  obtain ⟨_, n, price, hq, hc⟩ := exit_admission c hcode huser hactual
    (by rw [hdata]; decide) h
  have hn := exit_numerator c hcode (c.fuel-1) hbound
  have hm := FeeSafeDomain.operational_quote_agrees _ (by rw [hn]; exact hbound) hq
  rw [hn] at hm
  rcases hc with ⟨_, hv, ho⟩ | ⟨hs, _⟩
  · exact ⟨price, hv, ho, hm⟩
  · omega

#print axioms deposit_admission
#print axioms exit_admission
#print axioms deposit_getter_math
#print axioms exit_getter_math

end Eip8282.Audit.Integrator.SuccessfulUser
