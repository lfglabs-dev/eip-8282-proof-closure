import Eip8282.Audit.Integrator.DirectAppend
import Eip8282.Audit.Integrator.SystemDataSpec
import Eip8282.Audit.Integrator.GetterInversion
import Eip8282.Audit.Integrator.UniversalGate

/-!
# Code-independent complete-call control observations

Only the actual caller selects the successful user/SYSTEM control clause.
Actual failures restore the whole journal; inhibited users must fail. Getters
preserve accounts, created accounts and logs, but may change access bookkeeping.
The mathematical quote and natural control fold retain independent input bounds.
Initialization is supplied separately by InitializedInvariant, not by a premise
that this call already ran the right code or produced a desired post-state.
-/
namespace Eip8282.Audit.Integrator.DirectControl

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall SystemSpec

/-- Code-independent successful getter observation, at the natural pre-fee input. -/
def Getter (kind : Kind) (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) (out : ByteArray) : Prop :=
  GetterInversion.ReadOnly c created world substate ∧ ∃ price : UInt256,
    out = price.toByteArray ∧
    MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target kind)) price.toNat

def AppendControls (c : Context) (world : AccountMap .EVM) : Prop :=
  worldSlot world c.target (UInt256.ofNat 0) = worldSlot c.world c.target (UInt256.ofNat 0) ∧
  (worldSlot world c.target (UInt256.ofNat 1)).toNat =
    (worldSlot c.world c.target (UInt256.ofNat 1)).toNat + 1

/-- Observations of one actual completed result. A failed SYSTEM call need not
satisfy successful control updates; fuel/gas sufficiency is not assumed. -/
def Observed (kind : Kind) (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  (success = false → UniversalGate.FailedJournal c created world substate success) ∧
  (c.caller ≠ EvmRunner.sysAddr → worldSlot c.world c.target (UInt256.ofNat 0) = INH →
    UniversalGate.FailedJournal c created world substate success) ∧
  (success = true →
    if c.caller = EvmRunner.sysAddr then
      SystemDataSpec.ControlSlots kind c.calldata.size (worldSlot c.world c.target) (worldSlot world c.target)
    else if c.calldata.size = 0 then Getter kind c created world substate out
    else AppendControls c world)

private theorem getter_price {kind : Kind} {c : Context} {out : ByteArray}
    (h : DirectAdmission.Observed kind c out) (hz : c.calldata.size = 0) :
    ∃ price : UInt256, out = price.toByteArray ∧
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target kind)) price.toNat := by
  obtain ⟨_, price, hm, hg | hp⟩ := h
  · exact ⟨price, hg.2.2, hm⟩
  · cases kind <;> simp only [DirectAdmission.PaidInput, hz] at hp <;> omega

theorem completed (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
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
  · intro hu hi
    cases kind with
    | deposit => exact UniversalGate.deposit_inhibited c hcode hu hi h
    | exit => exact UniversalGate.exit_inhibited c hcode hu hi h
  · intro ht
    subst success
    by_cases hsys : c.caller = EvmRunner.sysAddr
    · rw [if_pos hsys]
      have hs : SystemDataSpec.Observed kind c world := by
        cases kind with
        | deposit => exact SystemDataSpec.deposit_system c hcode hsys ho h
        | exit => exact SystemDataSpec.exit_system c hcode hsys ho h
      exact (SystemDataSpec.projections hs budget hb (hbudget.trans (by decide)) hsize).1
    · rw [if_neg hsys]
      by_cases hz : c.calldata.size = 0
      · rw [if_pos hz]
        have ha : DirectAdmission.Observed kind c out := by
          cases kind with
          | deposit => exact DirectAdmission.deposit_admission c hcode hsys hactual hsize hsafe h
          | exit => exact DirectAdmission.exit_admission c hcode hsys hactual hsize hsafe h
        refine ⟨?_, getter_price ha hz⟩
        cases kind with
        | deposit => exact GetterInversion.deposit_getter_readonly c hcode hsys hactual hz h
        | exit => exact GetterInversion.exit_getter_readonly c hcode hsys hactual hz h
      · rw [if_neg hz]
        have hp := (DirectAppend.user_append kind c hcode hsys hactual hsize hz ho
          budget hbudget hb hsafe h).1.2.1
        exact ⟨hp.1, hp.2.1⟩

#print axioms completed

end Eip8282.Audit.Integrator.DirectControl
