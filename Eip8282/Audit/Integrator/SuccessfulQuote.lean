import Eip8282.Audit.Integrator.CallSuccess
import Eip8282.Audit.Integrator.SuccessInversion

/-!
# Every successful user message call completed its operational quote

This is a necessity theorem about actual Θ results, at arbitrary gas and
interpreter fuel. The quote-completion witness and uninhibited entry condition
are conclusions. It is not mathematical-fee agreement or a liveness theorem.
-/
namespace Eip8282.Audit.Integrator.SuccessfulQuote

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open MessageCall CallBridge CallSuccess SuccessInversion
open Eip8282.Audit.Correspondence (runtimeCode)

theorem positive_fuel (c : Context)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) : 0 < c.fuel := by
  obtain ⟨ew, es, he, _, _⟩ := execution_of_success c h
  by_contra hn
  have hz : c.fuel = 0 := by omega
  unfold Context.execution at he
  rw [hz] at he
  cases he

theorem deposit_quote_of_success (c : Context)
    (hcode : c.code = runtimeCode .deposit) (huser : c.caller ≠ EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Deposit.excessWord q ≠ INH ∧ ∃ n price, quoteWithin (Deposit.effExcess q) n = some price := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  exact deposit_user_success_quote _ huser he

theorem exit_quote_of_success (c : Context)
    (hcode : c.code = runtimeCode .exit) (huser : c.caller ≠ EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Exit.excessWord q ≠ INH ∧ ∃ n price, quoteWithin (Exit.effExcess q) n = some price := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  exact exit_user_success_quote _ huser he

#print axioms deposit_quote_of_success
#print axioms exit_quote_of_success

end Eip8282.Audit.Integrator.SuccessfulQuote
