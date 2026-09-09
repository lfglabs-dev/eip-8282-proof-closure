import Eip8282.Audit.Integrator.SuccessfulAppend
import Eip8282.Audit.Integrator.GetterInversion
import Eip8282.Audit.Integrator.AccountedState
import Eip8282.Audit.Integrator.FundedDomain

/-!
# State invariants across actual completed user calls

The budget gains one exactly for a successful nonempty-calldata user call.
Admission inversion proves that such a call is an append. Storage fit is derived
from the pre-call budget before invoking the independent append receipt. Failed
calls restore their journal, and successful getters preserve account observations.
The funding ceiling and initial invariants are explicit external assumptions.
Interpreter exhaustion is an error, outside the completed-result premise.
-/
namespace Eip8282.Audit.Integrator.UserStateInvariant

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.XiTransport (XiCall)
open MessageCall CallBridge AccountedState FundedDomain SystemSpec

/-- An observable event count, not an abstract execution transition. -/
def weight (c : Context) (success : Bool) : Nat :=
  if success = true ∧ c.calldata.size ≠ 0 then 1 else 0

private theorem readonly_storage (c : Context) {created world substate}
    (h : GetterInversion.ReadOnly c created world substate) :
    worldSlot world c.target = worldSlot c.world c.target := by
  funext k
  simp only [worldSlot, h.2.1 c.target]

/-- Join an independently derived append receipt to the given actual result.
The quote matches the natural pre-entry numerator explicitly. -/
private theorem receipt_preserves (c : Context) (q : XiCall kind) (record : ByteArray)
    (target budget : Nat) (hb : Bounded budget (slotW (entrySt q)))
    (hbudget : budget < 2^128) (hen : slotW (entrySt q) (UInt256.ofNat 0) ≠ INH)
    (hsafe : ControlSpec.feeInputNat target (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat ≤ 2892)
    (hvalue : c.value.toNat < fundingCeiling) {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat (ControlSpec.feeInputNat target
      (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat)) n = some price)
    (hpaid : price.toNat ≤ c.value.toNat)
    (hr : CommittedAppend.AppendResult c q record)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Bounded (budget+1) (worldSlot world c.target) ∧ EnabledSafe target (worldSlot world c.target) := by
  obtain ⟨cr, ew, g, es, he, _, hslots, _⟩ := hr
  have hw : world = ew := by
    have hh := h.symm.trans he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    exact hh.2.1
  have hread : worldSlot world c.target = AppendStorage.expected q := by
    rw [hw]
    exact funext hslots
  rw [hread]
  exact ⟨AccountedState.append q hb hbudget hen,
    expected_append_safe q target (append_fits q hb hbudget) hsafe
      c.value.toNat hvalue hq hpaid⟩

/-- Completed ordinary exit user calls preserve the coupled budget and safe
natural fee domain. Every execution-dependent condition is derived from `h`. -/
theorem exit_user (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 2 (worldSlot c.world c.target))
    (hvalue : c.value.toNat < fundingCeiling)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Bounded (budget + weight c success) (worldSlot world c.target) ∧
      EnabledSafe 2 (worldSlot world c.target) := by
  cases success with
  | false =>
      have hw := (failure_restores_journal c created world gas substate out h).1
      simpa only [hw, weight, Bool.false_eq_true, false_and, ↓reduceIte, Nat.add_zero]
        using And.intro hb hsafe
  | true =>
      obtain ⟨hen, n, price, hq, hc⟩ := SuccessfulUser.exit_admission c hcode huser hactual hdata h
      rcases hc with ⟨hzero, _, _⟩ | ⟨hsize, hpaid⟩
      · have hr := GetterInversion.exit_getter_readonly c hcode huser hactual hzero h
        have hw := readonly_storage c hr
        simpa only [hw, weight, hzero, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Nat.add_zero]
          using And.intro hb hsafe
      · let q := codeCall c hcode (c.fuel-1)
        have hentry : Bounded budget (slotW (entrySt q)) :=
          TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
        have hfit := append_fits q hentry hbudget
        have hne : worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH := by
          rw [← TransferFrame.codeCall_storage c hcode (c.fuel-1)]
          exact hen
        have hs : SuccessfulUser.numerator c 2 ≤ 2892 := hsafe.resolve_left hne
        have hnat : ControlSpec.feeInputNat 2
            (slotW (entrySt q) (UInt256.ofNat 0)).toNat
            (slotW (entrySt q) (UInt256.ofNat 1)).toNat = SuccessfulUser.numerator c 2 := by
          unfold ControlSpec.feeInputNat SuccessfulUser.numerator
          rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
        have hn := SuccessfulUser.exit_numerator c hcode (c.fuel-1) hs
        have he : Exit.effExcess q = UInt256.ofNat (SuccessfulUser.numerator c 2) := by
          rw [← ofNat_toNat' (Exit.effExcess q), hn]
        have hquote := hq
        rw [he, ← hnat] at hquote
        have hreceipt := SuccessfulAppend.exit_append c hcode huser hsize ho hfit h
        have hp := receipt_preserves c q _ 2 budget hentry hbudget hen
          (by rw [hnat]; exact hs) hvalue hquote (by omega) hreceipt h
        simpa [weight, hsize] using hp

/-- Completed ordinary deposit user calls preserve the coupled budget and safe
natural fee domain. Every execution-dependent condition is derived from `h`. -/
theorem deposit_user (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 8 (worldSlot c.world c.target))
    (hvalue : c.value.toNat < fundingCeiling)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Bounded (budget + weight c success) (worldSlot world c.target) ∧
      EnabledSafe 8 (worldSlot world c.target) := by
  cases success with
  | false =>
      have hw := (failure_restores_journal c created world gas substate out h).1
      simpa only [hw, weight, Bool.false_eq_true, false_and, ↓reduceIte, Nat.add_zero]
        using And.intro hb hsafe
  | true =>
      obtain ⟨hen, n, price, hq, hc⟩ := SuccessfulUser.deposit_admission c hcode huser hactual hdata h
      rcases hc with ⟨hzero, _, _⟩ | ⟨hsize, hfloor, hpaid⟩
      · have hr := GetterInversion.deposit_getter_readonly c hcode huser hactual hzero h
        have hw := readonly_storage c hr
        simpa only [hw, weight, hzero, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Nat.add_zero]
          using And.intro hb hsafe
      · let q := codeCall c hcode (c.fuel-1)
        have hentry : Bounded budget (slotW (entrySt q)) :=
          TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
        have hfit := append_fits q hentry hbudget
        have hne : worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH := by
          rw [← TransferFrame.codeCall_storage c hcode (c.fuel-1)]
          exact hen
        have hs : SuccessfulUser.numerator c 8 ≤ 2892 := hsafe.resolve_left hne
        have hnat : ControlSpec.feeInputNat 8
            (slotW (entrySt q) (UInt256.ofNat 0)).toNat
            (slotW (entrySt q) (UInt256.ofNat 1)).toNat = SuccessfulUser.numerator c 8 := by
          unfold ControlSpec.feeInputNat SuccessfulUser.numerator
          rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
        have hn := SuccessfulUser.deposit_numerator c hcode (c.fuel-1) hs
        have he : Deposit.effExcess q = UInt256.ofNat (SuccessfulUser.numerator c 8) := by
          rw [← ofNat_toNat' (Deposit.effExcess q), hn]
        have hquote := hq
        rw [he, ← hnat] at hquote
        have hreceipt := SuccessfulAppend.deposit_append c hcode huser hsize ho hfit h
        have hp := receipt_preserves c q _ 8 budget hentry hbudget hen
          (by rw [hnat]; exact hs) hvalue hquote (by omega) hreceipt h
        simpa [weight, hsize] using hp

#print axioms exit_user
#print axioms deposit_user

end Eip8282.Audit.Integrator.UserStateInvariant
