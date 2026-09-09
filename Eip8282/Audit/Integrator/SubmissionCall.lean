import Eip8282.Audit.Integrator.CommittedAppend
import Eip8282.Audit.EntryReach.FeeQuote

/-!
# Paid ordinary submissions with committed authentic records

The admission inputs below are the actual transferred value, untruncated
completed operational quote, and natural stake amount. The uint64 amount field
itself proves the stake product fits a word; no arbitrary product bound is
assumed. Queue-index bounds and quote/resource completion remain explicit.
-/
namespace Eip8282.Audit.Integrator.SubmissionCall

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall bytes)
open MessageCall CallBridge CommittedAppend
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Eight big-endian amount bytes at offset 80. Signature bytes are opaque. -/
def amount (data : ByteArray) : Nat := Model.beBytes ((bytes data).drop 80 |>.take 8)

theorem amount_word (q : XiCall .deposit) (hs : q.env.calldata.size = 184) :
    (Deposit.amountWord q).toNat = amount q.env.calldata := by
  have h := toNat_amount q.env.calldata (by omega)
  simpa only [Deposit.amountWord, cdW_entry, amount, Model.depositAmount, mask,
    show (UInt256.ofNat 56).toNat = 56 from rfl] using h

theorem amount_word_bound (q : XiCall .deposit) : (Deposit.amountWord q).toNat < 2^64 := by
  change (UInt256.land mask _).toNat < _
  rw [toNat_land_mask]
  exact Nat.mod_lt _ (by decide)

/-- The real acceptance checks are equivalent to natural payment of fee plus
stake. In particular the multiplication cannot undercharge through wrap. -/
theorem deposit_checks (q : XiCall .deposit) (price : UInt256)
    (hs : q.env.calldata.size = 184) :
    (¬ Deposit.valueWord q < price ∧
      ¬ Deposit.amountWord q < UInt256.ofNat 1000000000 ∧
      ¬ (Deposit.valueWord q-price) < UInt256.ofNat 1000000000 * Deposit.amountWord q) ↔
      (1000000000 ≤ amount q.env.calldata ∧
        price.toNat + 1000000000 * amount q.env.calldata ≤ (Deposit.valueWord q).toNat) := by
  have ha := amount_word q hs
  have hab := amount_word_bound q
  have hp : (UInt256.ofNat 1000000000 * Deposit.amountWord q).toNat =
      1000000000 * amount q.env.calldata := by
    rw [toNat_mul_of_lt]
    · change 1000000000 * (Deposit.amountWord q).toNat = _
      rw [ha]
    change 1000000000 * (Deposit.amountWord q).toNat < UInt256.size
    have hb : 1000000000 * 2^64 < UInt256.size := by decide
    omega
  simp only [lt_iff_toNat, not_lt, ha, hp,
    show (UInt256.ofNat 1000000000).toNat = 1000000000 from rfl]
  constructor
  · rintro ⟨hpaid, hfloor, hstake⟩
    rw [toNat_sub_of_le _ _ hpaid] at hstake
    exact ⟨hfloor, by omega⟩
  · rintro ⟨hfloor, hpaid⟩
    have hfee : price.toNat ≤ (Deposit.valueWord q).toNat := by omega
    refine ⟨hfee, hfloor, ?_⟩
    rw [toNat_sub_of_le _ _ hfee]
    omega

private theorem quote_initial (X : UInt256) (n : Nat) :
    feeExit X n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
      (UInt256.ofNat 1) = feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) := by
  rfl

theorem deposit_submission (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hactual : c.apparentValue = c.value) (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH) (hperm : c.permission = true)
    {n : Nat} {price : UInt256}
    (hq : quoteWithin (Deposit.effExcess (codeCall c hcode steps)) n = some price)
    (hsize : c.calldata.size = 184) (hfloor : 1000000000 ≤ amount c.calldata)
    (hpaid : price.toNat + 1000000000 * amount c.calldata ≤ c.value.toNat)
    (hg : 87*n+190000 ≤ c.gas.toNat) (hsteps : 24*n+152 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps)) :
    AppendResult c (codeCall c hcode steps) c.calldata := by
  let q := codeCall c hcode steps
  obtain ⟨o, i, hloop, hprice⟩ := quoteWithin_eq_some_iff.mp hq
  have hfee : Deposit.FeeLoopEnds q n o i := by
    simpa only [Deposit.FeeLoopEnds, quote_initial] using hloop
  have hu : Deposit.callerWord q ≠ sysW := by
    intro h
    exact huser ((callerW_eq_sysW_iff q).mp h)
  have hv : (Deposit.valueWord q).toNat = c.value.toNat := congrArg UInt256.toNat hactual
  have checks := (deposit_checks q price hsize).mpr ⟨hfloor, by rw [hv]; exact hpaid⟩
  change price = Deposit.feeWord o at hprice
  rw [hprice] at checks
  exact deposit_append_commits c hcode steps hf hu hen hperm hfee hsize
    checks.1 checks.2.1 checks.2.2 hg hsteps ho hfit

theorem exit_submission (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hactual : c.apparentValue = c.value) (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH) (hperm : c.permission = true)
    {n : Nat} {price : UInt256}
    (hq : quoteWithin (Exit.effExcess (codeCall c hcode steps)) n = some price)
    (hsize : c.calldata.size = 48) (hpaid : price.toNat ≤ c.value.toNat)
    (hg : 87*n+150000 ≤ c.gas.toNat) (hsteps : 24*n+122 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps)) :
    AppendResult c (codeCall c hcode steps) (ExitRecord.record c.caller c.calldata) := by
  let q := codeCall c hcode steps
  obtain ⟨o, i, hloop, hprice⟩ := quoteWithin_eq_some_iff.mp hq
  have hfee : Exit.FeeLoopEnds q n o i := by
    simpa only [Exit.FeeLoopEnds, quote_initial] using hloop
  have hu : Exit.callerWord q ≠ sysW := by
    intro h
    exact huser ((callerW_eq_sysW_iff q).mp h)
  have hv : (Exit.valueWord q).toNat = c.value.toNat := congrArg UInt256.toNat hactual
  change price = Exit.feeWord o at hprice
  have hp : ¬ Exit.valueWord q < Exit.feeWord o := by
    rw [lt_iff_toNat, hv, ← hprice]
    omega
  exact exit_append_commits c hcode steps hf hu hen hperm hfee hsize hp hg hsteps ho hfit

#print axioms deposit_checks
#print axioms deposit_submission
#print axioms exit_submission

end Eip8282.Audit.Integrator.SubmissionCall
