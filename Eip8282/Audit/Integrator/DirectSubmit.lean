import Eip8282.Audit.Integrator.DirectAppend
import Eip8282.Audit.Integrator.UniversalGate

/-!
# Code-independent complete-call submission observation

This success-necessity statement does not promise success for under-resourced
paid calls. The fee and physical/log effects belong to the same actual result.
The local safe domain is explicit and the predicate contains no bytecode pin.
-/
namespace Eip8282.Audit.Integrator.DirectSubmit

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall SystemSpec

def Observed (kind : Kind) (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  (success = false → UniversalGate.FailedJournal c created world substate success) ∧
  (worldSlot c.world c.target (UInt256.ofNat 0) = INH →
    UniversalGate.FailedJournal c created world substate success) ∧
  (success = true → c.calldata.size ≠ 0 →
    worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH ∧
    DirectAppend.Observed kind c world substate out ∧
    ∃ price : UInt256,
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target kind)) price.toNat ∧
      DirectAdmission.PaidInput kind c price.toNat)

theorem completed (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (huser : c.caller ≠ EvmRunner.sysAddr)
    (hactual : c.apparentValue = c.value) (hsize : c.calldata.size < UInt256.size)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : AccountedState.Bounded budget (worldSlot c.world c.target))
    (hsafe : FundedDomain.EnabledSafe (DirectAdmission.target kind) (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Observed kind c created world substate success out := by
  refine ⟨?_, ?_, ?_⟩
  · intro hf
    subst success
    obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out h
    exact ⟨rfl, hc, hw, hs⟩
  · intro hi
    cases kind with
    | deposit => exact UniversalGate.deposit_inhibited c hcode huser hi h
    | exit => exact UniversalGate.exit_inhibited c hcode huser hi h
  · intro ht hn
    subst success
    have ha : DirectAdmission.Observed kind c out := by
      cases kind with
      | deposit => exact DirectAdmission.deposit_admission c hcode huser hactual hsize hsafe h
      | exit => exact DirectAdmission.exit_admission c hcode huser hactual hsize hsafe h
    exact ⟨ha.1, DirectAppend.user_append kind c hcode huser hactual hsize hn ho
      budget hbudget hb hsafe h⟩

/-- Invalid nonempty mathematical admission cannot succeed. This derives
rejection from the same behavior predicate, without supplying a completed word
quote or assuming the runtime reached a particular guard. -/
theorem invalid_nonempty {kind : Kind} {c : Context}
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {substate : Substate} {success : Bool} {out : ByteArray}
    (h : Observed kind c created world substate success out)
    (hn : c.calldata.size ≠ 0)
    (hi : ¬ ∃ price : UInt256,
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target kind)) price.toNat ∧
      DirectAdmission.PaidInput kind c price.toNat) :
    UniversalGate.FailedJournal c created world substate success := by
  cases success with
  | false => exact h.1 rfl
  | true => exact False.elim (hi (h.2.2 rfl hn).2.2)

#print axioms completed
#print axioms invalid_nonempty

end Eip8282.Audit.Integrator.DirectSubmit
