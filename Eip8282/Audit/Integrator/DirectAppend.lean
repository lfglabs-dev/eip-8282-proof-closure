import Eip8282.Audit.Integrator.AppendDataSpec
import Eip8282.Audit.Integrator.DirectAdmission
import Eip8282.Audit.Integrator.SuccessfulAppend
import Eip8282.Audit.Integrator.AccountedState

/-!
# Actual append receipts with code-independent observations

The observation takes the actual published world, substate and output, and
specifies them from pre-call storage and input data. No code pin or execution
witness occurs inside this predicate. Its pinned theorem joins a receipt to
the very same successful Θ result, and binds payment to that execution's
mathematical price. It derives calldata shape and local storage fit before
using the append receipt. The safe and budget pre-invariants remain explicit;
no funding ceiling is required for this isolated call.
-/
namespace Eip8282.Audit.Integrator.DirectAppend

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.EntryReach (slotW entrySt)
open MessageCall CallBridge SystemSpec AccountedState

set_option autoImplicit false

/-- A single authentic physical append and anonymous log in the observed
result. The other-account frame is relative to the actual transferred world. -/
def Observed (kind : Kind) (c : Context) (world : AccountMap .EVM)
    (substate : Substate) (out : ByteArray) : Prop :=
  AppendDataSpec.ExpectedPost kind (worldSlot c.world c.target) c.calldata c.caller
    (worldSlot world c.target) ∧
  AppendDataSpec.StoragePost kind (worldSlot c.world c.target) c.calldata c.caller
    (worldSlot world c.target) ∧
  AppendDataSpec.AuthenticLog kind c.calldata c.caller c.target c.substate substate ∧
  AppendDataSpec.OtherAccountsUnchanged c.entryWorld world c.target ∧
  out = .empty

/-- A receipt's existential world/substate/output are identified with the given
actual result before its observations are exported. Storage reads are moved
back across Θ's actual transfer; balances are not claimed unchanged there. -/
theorem observed_of_receipt {kind : Kind} (c : Context)
    (hcode : c.code = runtimeCode kind) (steps : Nat)
    (hr : CommittedAppend.AppendResult c (codeCall c hcode steps)
      (AppendDataSpec.record kind c.calldata c.caller))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed kind c world substate out := by
  let q := codeCall c hcode steps
  obtain ⟨cr, w, g, s, he, _, hslots, hpost, hlog, hframe⟩ := hr
  have heq := Except.ok.inj (h.symm.trans he)
  have hw : world = w := congrArg (fun t => t.2.1) heq
  have hs : substate = s := congrArg (fun t => t.2.2.2.1) heq
  have hout : out = .empty := congrArg (fun t => t.2.2.2.2.2) heq
  have hread : slotW (entrySt q) = worldSlot c.world c.target :=
    funext (TransferFrame.codeCall_storage c hcode steps)
  have hepost := (AppendDataSpec.expectedPost_iff q w).mpr hslots
  have hspost := (AppendDataSpec.storagePost_iff q w).mpr hpost
  change AppendDataSpec.ExpectedPost kind (slotW (entrySt q)) c.calldata c.caller
    (worldSlot w c.target) at hepost
  change AppendDataSpec.StoragePost kind (slotW (entrySt q)) c.calldata c.caller
    (worldSlot w c.target) at hspost
  rw [hread] at hepost hspost
  unfold Observed
  rw [hw, hs]
  exact ⟨hepost, hspost, hlog, hframe, hout⟩

/-- Every actual successful nonempty ordinary user call commits the authentic
append at the very same natural price as its admission check. The input budget
supplies AppendFits before SuccessfulAppend is applied; no post-state or
execution-resource bound is assumed. -/
theorem user_append (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size) (hnonempty : c.calldata.size ≠ 0)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : FundedDomain.EnabledSafe (DirectAdmission.target kind) (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed kind c world substate out ∧
      ∃ price : UInt256,
        MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target kind)) price.toNat ∧
        DirectAdmission.PaidInput kind c price.toNat := by
  have hadmission : DirectAdmission.Observed kind c out := by
    cases kind with
    | deposit => exact DirectAdmission.deposit_admission c hcode huser hactual hdata hsafe h
    | exit => exact DirectAdmission.exit_admission c hcode huser hactual hdata hsafe h
  obtain ⟨price, hmath, hpaid⟩ := DirectAdmission.paid_of_nonempty hadmission hnonempty
  let q := codeCall c hcode (c.fuel-1)
  have hentry : Bounded budget (slotW (entrySt q)) :=
    TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
  have hfit := AccountedState.append_fits q hentry hbudget
  have hreceipt : CommittedAppend.AppendResult c q
      (AppendDataSpec.record kind c.calldata c.caller) := by
    cases kind with
    | deposit =>
      exact SuccessfulAppend.deposit_append c hcode huser hpaid.1 ho hfit h
    | exit =>
      exact SuccessfulAppend.exit_append c hcode huser hpaid.1 ho hfit h
  exact ⟨observed_of_receipt c hcode (c.fuel-1) hreceipt h, price, hmath, hpaid⟩

#print axioms observed_of_receipt
#print axioms user_append

end Eip8282.Audit.Integrator.DirectAppend
