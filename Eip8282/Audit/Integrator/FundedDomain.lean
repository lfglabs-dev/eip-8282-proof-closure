import Eip8282.Audit.Integrator.SuccessfulUser
import Eip8282.Audit.Integrator.CommittedSystem

/-!
# Safe fee-domain preservation under an explicit funding ceiling

The ceiling is the certified mathematical fee at numerator2892. It is an
external assumption on call value, NOT an asserted Ethereum supply or balance
fact. To obtain a protocol invariant, one must justify initial state, call
funding (including nested calls), value<=available balance, and a supply/balance
ceiling below this fee. Slot/accounting capacity and arbitrary-success append
state classification remain separate obligations.
-/
namespace Eip8282.Audit.Integrator.FundedDomain

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open MathFee ControlSpec FeeSafeDomain

set_option maxHeartbeats 1200000

/-- Explicit strict call-value ceiling, expressed in wei like the quoted fee. -/
def fundingCeiling : Nat := certificateOutput / 17

theorem boundary_math : MathQuoteCompletes 2892 fundingCeiling := by
  refine ⟨certificateBudget, ?_⟩
  simp only [quoteWithinNat, upper_stops, Option.map_some, fundingCeiling]

/-- Any completed operational quote exactly at the upper numerator is the
certified boundary price, whatever finite budget witnessed completion. -/
theorem boundary_price {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat 2892) n = some price) :
    price.toNat = fundingCeiling :=
  mathQuoteCompletes_unique (any_quote_agrees 2892 (Nat.le_refl _) hq) boundary_math

/-- One ordinary count increment raises the natural numerator by at most one. -/
theorem numerator_step (target excess count : Nat) :
    feeInputNat target excess (count+1) ≤ feeInputNat target excess count + 1 := by
  unfold feeInputNat
  omega

/-- Paying a quote below the explicit value ceiling prevents an append from
crossing the certified numerator boundary. -/
theorem paid_append_safe (target excess count value : Nat)
    (hpre : feeInputNat target excess count ≤ 2892) (hvalue : value < fundingCeiling)
    {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat (feeInputNat target excess count)) n = some price)
    (hpaid : price.toNat ≤ value) : feeInputNat target excess (count+1) ≤ 2892 := by
  have hstrict : feeInputNat target excess count < 2892 := by
    by_contra hn
    have he : feeInputNat target excess count = 2892 := by omega
    rw [he] at hq
    have hp := boundary_price hq
    omega
  have hs := numerator_step target excess count
  omega

/-- Either inhibited, or the independent natural numerator is safe. -/
def EnabledSafe (target : Nat) (read : UInt256 → UInt256) : Prop :=
  read (UInt256.ofNat 0) = INH ∨
    feeInputNat target (read (UInt256.ofNat 0)).toNat (read (UInt256.ofNat 1)).toNat ≤ 2892

/-- Latch/unlock/fold preserves enabled safety. For enabled inputs the safe
numerator and small target themselves imply the pre-fold sum cannot wrap. -/
theorem system_safe (target excess count cds : UInt256) (ht : target.toNat ≤ 8)
    (hpre : excess = INH ∨ feeInputNat target.toNat excess.toNat count.toNat ≤ 2892) :
    systemExcess target excess count cds = INH ∨
      (systemExcess target excess count cds).toNat ≤ 2892 := by
  by_cases hdata : cds ≠ ⟨0⟩
  · exact Or.inl (systemExcess_latch _ _ _ _ hdata)
  · have hz : cds = ⟨0⟩ := by simpa using hdata
    subst cds
    by_cases hi : excess = INH
    · subst excess
      exact Or.inr (by rw [systemExcess_unlock]; decide)
    · have hb := hpre.resolve_left hi
      have hsum : excess.toNat+count.toNat < UInt256.size := by
        have hsize : 2900 < UInt256.size := by decide
        unfold feeInputNat at hb
        omega
      right
      rw [systemExcess, if_neg (by simp), if_neg hi, foldWord_eq_nat_of_sum_lt _ _ _ hsum]
      unfold foldNat feeInputNat at *
      omega

theorem expected_system_safe (st : EvmYul.State .EVM) (target drained cds : UInt256)
    (ht : target.toNat ≤ 8) (hpre : EnabledSafe target.toNat (slotW st)) :
    EnabledSafe target.toNat (SystemSpec.expectedSlot st target drained cds) := by
  unfold EnabledSafe at *
  rw [SystemSpec.expectedSlot_excess, SystemSpec.expectedSlot_count]
  simpa only [feeInputNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    Nat.zero_sub, Nat.add_zero] using system_safe target _ _ cds ht hpre

/-- Control-slot postcondition of an append, driven by the independently
proved storage map and a quote with the matching natural input. -/
theorem expected_append_safe (q : XiCall kind) (target : Nat) (hf : AppendStorage.AppendFits q)
    (hpre : feeInputNat target (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat ≤ 2892)
    (value : Nat) (hvalue : value < fundingCeiling) {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat (feeInputNat target
      (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat)) n = some price)
    (hpaid : price.toNat ≤ value) : EnabledSafe target (AppendStorage.expected q) := by
  right
  unfold feeInputNat
  rw [AppendStorage.expected_excess q hf, AppendStorage.expected_count_nat q hf]
  exact paid_append_safe target _ _ value hpre hvalue hq hpaid

open MessageCall CallBridge CommittedAppend
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Enabled safety in the world actually committed by Θ. -/
def SafeResult (c : Context) (target : Nat) : Prop :=
  ∃ created world gas substate out,
    c.result = .ok (created, world, gas, substate, true, out) ∧
    EnabledSafe target (SystemSpec.worldSlot world c.target)

/-- Composition with the existing actual append receipt, not an assumed safe
post-state. The funding/price inputs remain independently stated. -/
theorem append_result_safe (c : Context) (q : XiCall kind) (record : ByteArray)
    (target : Nat) (hf : AppendStorage.AppendFits q)
    (hpre : feeInputNat target (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat ≤ 2892)
    (hvalue : c.value.toNat < fundingCeiling) {n : Nat} {price : UInt256}
    (hq : quoteWithin (UInt256.ofNat (feeInputNat target
      (slotW (entrySt q) (UInt256.ofNat 0)).toNat
      (slotW (entrySt q) (UInt256.ofNat 1)).toNat)) n = some price)
    (hpaid : price.toNat ≤ c.value.toNat) (hcall : AppendResult c q record) : SafeResult c target := by
  obtain ⟨created, world, gas, substate, he, _, hs, _⟩ := hcall
  refine ⟨created, world, gas, substate, .empty, he, ?_⟩
  have hread : SystemSpec.worldSlot world c.target = AppendStorage.expected q := funext hs
  rw [hread]
  exact expected_append_safe q target hf hpre c.value.toNat hvalue hq hpaid

theorem system_result_safe (c : Context) (q : XiCall kind) (target drained cds : UInt256)
    (out : ByteArray) (ht : target.toNat ≤ 8) (hpre : EnabledSafe target.toNat (slotW (entrySt q)))
    (hcall : CommittedSystem.StorageResult c q target drained cds out) : SafeResult c target.toNat := by
  obtain ⟨world, created, gas, substate, he, hs⟩ := hcall
  refine ⟨created, world, gas, substate, out, he, ?_⟩
  have hread : SystemSpec.worldSlot world c.target = SystemSpec.expectedSlot (entrySt q) target drained cds :=
    funext hs
  rw [hread]
  exact expected_system_safe (entrySt q) target drained cds ht hpre


/-- Actual funded submissions preserve the safe domain, under the explicit
ceiling and the existing sufficient-execution conditions. -/
theorem deposit_submission_safe (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hactual : c.apparentValue = c.value) (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH) (hperm : c.permission = true)
    {n : Nat} {price : UInt256}
    (hq : quoteWithin (Deposit.effExcess (codeCall c hcode steps)) n = some price)
    (hsize : c.calldata.size = 184) (hfloor : 1000000000 ≤ SubmissionCall.amount c.calldata)
    (hpaid : price.toNat + 1000000000 * SubmissionCall.amount c.calldata ≤ c.value.toNat)
    (hg : 87*n+190000 ≤ c.gas.toNat) (hsteps : 24*n+152 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps))
    (hbound : SuccessfulUser.numerator c 8 ≤ 2892)
    (hvalue : c.value.toNat < fundingCeiling) : SafeResult c 8 := by
  have hcall := SubmissionCall.deposit_submission c hcode steps hf hactual huser hen hperm hq hsize hfloor hpaid hg hsteps ho hfit
  have hn := SuccessfulUser.deposit_numerator c hcode steps hbound
  have hnat : feeInputNat 8 (slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 0)).toNat
      (slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 1)).toNat = SuccessfulUser.numerator c 8 := by
    unfold feeInputNat SuccessfulUser.numerator
    rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  have he : Deposit.effExcess (codeCall c hcode steps) = UInt256.ofNat (SuccessfulUser.numerator c 8) := by
    rw [← ofNat_toNat' (Deposit.effExcess (codeCall c hcode steps)), hn]
  have hquote := hq
  rw [he, ← hnat] at hquote
  exact append_result_safe c (codeCall c hcode steps) _ 8 hfit
    (by rw [hnat]; exact hbound) hvalue hquote (by omega) hcall

/-- Actual funded submissions preserve the safe domain, under the explicit
ceiling and the existing sufficient-execution conditions. -/
theorem exit_submission_safe (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hactual : c.apparentValue = c.value) (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH) (hperm : c.permission = true)
    {n : Nat} {price : UInt256}
    (hq : quoteWithin (Exit.effExcess (codeCall c hcode steps)) n = some price)
    (hsize : c.calldata.size = 48) (hpaid : price.toNat ≤ c.value.toNat)
    (hg : 87*n+150000 ≤ c.gas.toNat) (hsteps : 24*n+122 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps))
    (hbound : SuccessfulUser.numerator c 2 ≤ 2892)
    (hvalue : c.value.toNat < fundingCeiling) : SafeResult c 2 := by
  have hcall := SubmissionCall.exit_submission c hcode steps hf hactual huser hen hperm hq hsize hpaid hg hsteps ho hfit
  have hn := SuccessfulUser.exit_numerator c hcode steps hbound
  have hnat : feeInputNat 2 (slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 0)).toNat
      (slotW (entrySt (codeCall c hcode steps)) (UInt256.ofNat 1)).toNat = SuccessfulUser.numerator c 2 := by
    unfold feeInputNat SuccessfulUser.numerator
    rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  have he : Exit.effExcess (codeCall c hcode steps) = UInt256.ofNat (SuccessfulUser.numerator c 2) := by
    rw [← ofNat_toNat' (Exit.effExcess (codeCall c hcode steps)), hn]
  have hquote := hq
  rw [he, ← hnat] at hquote
  exact append_result_safe c (codeCall c hcode steps) _ 2 hfit
    (by rw [hnat]; exact hbound) hvalue hquote (by omega) hcall

/-- SYSTEM preserves the enabled-domain invariant through actual transfer and
storage commitment; inhibition and unlock do not require a funding ceiling. -/
theorem deposit_system_safe (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hpre : EnabledSafe 8 (SystemSpec.worldSlot c.world c.target)) : SafeResult c 8 := by
  have hentry := TransferFrame.codeCall_storage_invariant c hcode steps (EnabledSafe 8) hpre
  have hcall := CommittedSystem.deposit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  exact system_result_safe c (codeCall c hcode steps) (UInt256.ofNat 8) _ _ _ (by decide) hentry hcall

/-- SYSTEM preserves the enabled-domain invariant through actual transfer and
storage commitment; inhibition and unlock do not require a funding ceiling. -/
theorem exit_system_safe (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hpre : EnabledSafe 2 (SystemSpec.worldSlot c.world c.target)) : SafeResult c 2 := by
  have hentry := TransferFrame.codeCall_storage_invariant c hcode steps (EnabledSafe 2) hpre
  have hcall := CommittedSystem.exit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  exact system_result_safe c (codeCall c hcode steps) (UInt256.ofNat 2) _ _ _ (by decide) hentry hcall

#print axioms boundary_price
#print axioms paid_append_safe
#print axioms system_safe
#print axioms expected_append_safe
#print axioms deposit_submission_safe
#print axioms exit_submission_safe
#print axioms deposit_system_safe
#print axioms exit_system_safe

end Eip8282.Audit.Integrator.FundedDomain
