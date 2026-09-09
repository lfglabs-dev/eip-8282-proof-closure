import Eip8282.Audit.Integrator.SuccessfulUser
import Eip8282.Audit.Integrator.FundedDomain

/-!
# Code-independent mathematical admission observations

The predicate reads the actual call input, pre-storage and returned bytes. It
contains no pinned-code witness, execution path, quote-completion premise or
post-state assumption. The pinned instances derive its untruncated mathematical
price from the very quote checked by successful execution. The safe pre-domain
remains explicit; this file does not establish protocol funding or liveness.
-/
namespace Eip8282.Audit.Integrator.DirectAdmission

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall CallBridge SystemSpec

def target : Kind → Nat | .deposit => 8 | .exit => 2

/-- Exact paid input checks at a supplied mathematical price. -/
def PaidInput (kind : Kind) (c : Context) (price : Nat) : Prop :=
  match kind with
  | .deposit => c.calldata.size = 184 ∧
      1000000000 ≤ SubmissionCall.amount c.calldata ∧
      price + 1000000000 * SubmissionCall.amount c.calldata ≤ c.value.toNat
  | .exit => c.calldata.size = 48 ∧ price ≤ c.value.toNat

/-- Successful user admission, independent of which code is being tested. -/
def Observed (kind : Kind) (c : Context) (out : ByteArray) : Prop :=
  worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH ∧
  ∃ price : UInt256,
    MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (target kind)) price.toNat ∧
    ((c.calldata.size = 0 ∧ c.value = ⟨0⟩ ∧ out = price.toByteArray) ∨
      PaidInput kind c price.toNat)

theorem exit_admission (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (hsafe : FundedDomain.EnabledSafe 2 (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed .exit c out := by
  obtain ⟨hen, n, price, hq, hc⟩ :=
    SuccessfulUser.exit_admission c hcode huser hactual hdata h
  have hne : worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH := by
    rw [← TransferFrame.codeCall_storage c hcode (c.fuel-1)]
    exact hen
  have hs : SuccessfulUser.numerator c 2 ≤ 2892 := hsafe.resolve_left hne
  have hn := SuccessfulUser.exit_numerator c hcode (c.fuel-1) hs
  have hm := FeeSafeDomain.operational_quote_agrees _ (by rw [hn]; exact hs) hq
  rw [hn] at hm
  exact ⟨hne, price, hm, hc⟩

theorem deposit_admission (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (hsafe : FundedDomain.EnabledSafe 8 (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Observed .deposit c out := by
  obtain ⟨hen, n, price, hq, hc⟩ :=
    SuccessfulUser.deposit_admission c hcode huser hactual hdata h
  have hne : worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH := by
    rw [← TransferFrame.codeCall_storage c hcode (c.fuel-1)]
    exact hen
  have hs : SuccessfulUser.numerator c 8 ≤ 2892 := hsafe.resolve_left hne
  have hn := SuccessfulUser.deposit_numerator c hcode (c.fuel-1) hs
  have hm := FeeSafeDomain.operational_quote_agrees _ (by rw [hn]; exact hs) hq
  rw [hn] at hm
  exact ⟨hne, price, hm, hc⟩

/-- The same observed price pays the append; no independent quote is assumed. -/
theorem paid_of_nonempty {kind : Kind} {c : Context} {out : ByteArray}
    (h : Observed kind c out) (hne : c.calldata.size ≠ 0) :
    ∃ price : UInt256,
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (target kind)) price.toNat ∧
      PaidInput kind c price.toNat := by
  obtain ⟨_, price, hm, hc⟩ := h
  exact ⟨price, hm, hc.resolve_left (fun hz => hne hz.1)⟩

#print axioms exit_admission
#print axioms deposit_admission
#print axioms paid_of_nonempty

end Eip8282.Audit.Integrator.DirectAdmission
