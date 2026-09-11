import Eip8282.Audit.Integrator.SuccessfulQuote
import Eip8282.Audit.Integrator.TransferFrame

/-!
# Inhibited user calls cannot commit, at arbitrary resources

For any actual completed Θ result, inhibition forces failure and restores the
whole pre-call journal. No sufficient gas, completed quote, or nonempty-world
condition is assumed. Proof-evaluator OutOfFuel is not a completed Θ result.
-/
namespace Eip8282.Audit.Integrator.UniversalGate

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open MessageCall CallBridge SuccessfulQuote
open Eip8282.Audit.Correspondence (runtimeCode)

def FailedJournal (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) (success : Bool) : Prop :=
  success = false ∧ created = c.created ∧ world = c.world ∧ substate = c.substate

theorem deposit_inhibited (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr)
    (hinh : SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0) = INH)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    FailedJournal c created world substate success := by
  cases success with
  | false =>
    obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out h
    exact ⟨rfl, hc, hw, hs⟩
  | true =>
    obtain ⟨hen, _⟩ := deposit_quote_of_success c hcode huser h
    apply False.elim
    apply hen
    change slotW (entrySt (codeCall c hcode (c.fuel-1))) (UInt256.ofNat 0) = _
    rw [TransferFrame.codeCall_storage, hinh]

theorem exit_inhibited (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr)
    (hinh : SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0) = INH)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    FailedJournal c created world substate success := by
  cases success with
  | false =>
    obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out h
    exact ⟨rfl, hc, hw, hs⟩
  | true =>
    obtain ⟨hen, _⟩ := exit_quote_of_success c hcode huser h
    apply False.elim
    apply hen
    change slotW (entrySt (codeCall c hcode (c.fuel-1))) (UInt256.ofNat 0) = _
    rw [TransferFrame.codeCall_storage, hinh]

#print axioms deposit_inhibited
#print axioms exit_inhibited

end Eip8282.Audit.Integrator.UniversalGate
