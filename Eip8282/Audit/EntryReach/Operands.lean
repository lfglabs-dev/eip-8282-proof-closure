import Eip8282.Audit.EntryReach
import Eip8282.Audit.EntryReach.Fee

/-!
# OPERANDS: the branch words are the model's operands

`EntryReach.Deposit` / `EntryReach.Exit` select their endpoints by words read off
the entry state — `callerWord`, `excessWord`, `countWord`, `cdsizeWord`,
`valueWord`, `amountWord` and the fee word the loop computes. This module reads
those words back as the fields of the abstract call and state that
`PreCallRepresents` and `AdmissibleCall` bind:

* `Deposit.userWords` / `Exit.userWords` — caller, excess, count, calldata size,
  value and (deposit) amount, as naturals equal to the model's;
* `Deposit.fee_of_noWrap` / `Exit.fee_of_noWrap` — under the word-exactness
  witness the fee loop terminates within `256` iterations and its quotient is
  `Model.currentFee`: the `FeeLoopEnds` premise of every uninhibited user endpoint
  is discharged;
* `Deposit.admissible_iff` / `Exit.admissible_iff` — `Model.admissible` is exactly
  the conjunction of checks the runtime performs, in the model's terms;
* `Deposit.halts_of_admissible` / `Exit.halts_of_admissible` — every admissible,
  word-exact call whose calldata fits a word halts: the `TerminationClosure`
  shape, with its two extra premises stated.

The two extra premises are not conventions. `WordExactCall` is needed because at
a wrapping image the word loop need not terminate at all (the runtime then runs
out of gas, which is not an `XiHalts`); `c.env.calldata.size < 2 ^ 256` because
`CALLDATASIZE` is a word, so a calldata of `2 ^ 256 + 184` bytes would be treated
by the runtime as a 184-byte submission while the model rejects it. Both are
physically vacuous and both are stated.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall bytes)
open Eip8282.Audit.UniversalBoundary
open Eip8282.Audit.Model
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Reachable (drainCount nextExcessOf)
open Eip8282.Audit.Correspondence (targetAddr)

/-! ## Shared facts -/

theorem toNat_INH : INH.toNat = inhibitor := by decide

theorem eq_INH_iff (w : UInt256) : w = INH ↔ w.toNat = inhibitor := by
  rw [← toNat_INH]
  constructor
  · rintro rfl; rfl
  · intro h; rw [← ofNat_toNat' w, h, ofNat_toNat']

theorem gwei_lt (a : Nat) (ha : a < 2 ^ 64) : 1000000000 * a < UInt256.size := by
  rw [size_eq]; omega

theorem toNat_gweiW : (UInt256.ofNat 1000000000).toNat = 1000000000 := rfl

/-- `PreCallRepresents` for a user call, with the account named. -/
theorem user_entry_account {kind : Kind} {c : XiCall kind} {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hrep : PreCallRepresents c s (.user caller calldata value))
    (hadm : AdmissibleCall c s (.user caller calldata value)) :
    ∃ acc : Account .EVM, c.entry.accountMap.get? c.env.codeOwner = some acc ∧
      WellFormed kind acc.storage ∧ s = toModel kind acc.storage (acc.balance.toNat - value) := by
  obtain ⟨acc, hacc, _, hwf, hs, _, _⟩ := hrep
  have henv : UserCallBinding c caller calldata value := hadm.env
  exact ⟨acc, by rw [henv.owner]; exact hacc, hwf, hs⟩

/-- `PreCallRepresents` for a system call, with the account named. -/
theorem system_entry_account {kind : Kind} {c : XiCall kind} {s : Model.State} {b : Bool}
    (hrep : PreCallRepresents c s (.system b)) (hadm : AdmissibleCall c s (.system b)) :
    ∃ acc : Account .EVM, c.entry.accountMap.get? c.env.codeOwner = some acc ∧
      WellFormed kind acc.storage ∧ s = toModel kind acc.storage acc.balance.toNat := by
  obtain ⟨acc, hacc, _, hwf, hs⟩ := hrep
  have henv : SystemCallBinding c b := hadm.env
  exact ⟨acc, by rw [henv.owner]; exact hacc, hwf, hs⟩

/-! ## The deposit runtime -/

namespace Deposit

variable (c : XiCall .deposit)

/-- The entry words of a user call, as the model's operands. -/
structure UserWords (s : Model.State) (calldata : List Byte) (value : Wei) : Prop where
  user : callerWord c ≠ sysW
  kind : s.kind = .deposit
  excess : (excessWord c).toNat = s.storedExcess
  count : (countWord c).toNat = s.count
  size : (cdsizeWord c).toNat = calldata.length
  value : (valueWord c).toNat = value
  amount : calldata.length = 184 → (amountWord c).toNat = depositAmount calldata
  bytesOk : Model.bytesOk calldata = true

theorem userWords {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    (hrep : PreCallRepresents c s (.user caller calldata value))
    (hadm : AdmissibleCall c s (.user caller calldata value))
    (hcd : c.env.calldata.size < UInt256.size) : UserWords c s calldata value := by
  obtain ⟨acc, hacc, _, hs⟩ := user_entry_account hrep hadm
  have henv : UserCallBinding c caller calldata value := hadm.env
  have hcalldata : calldata = bytes c.env.calldata := henv.calldata_eq.symm
  refine ⟨fun h => henv.user ((callerW_eq_sysW_iff c).mp h), by rw [hs]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (slotW (entrySt c) (UInt256.ofNat 0)).toNat = s.storedExcess
    rw [hs, toNat_slotW_entry c hacc 0]; rfl
  · show (slotW (entrySt c) (UInt256.ofNat 1)).toNat = s.count
    rw [hs, toNat_slotW_entry c hacc 1]; rfl
  · rw [hcalldata, length_bytes_calldata]; exact toNat_cdsizeW c hcd
  · exact henv.value_eq
  · intro hlen
    rw [hcalldata, length_bytes_calldata] at hlen
    show (UInt256.land mask (uInt256OfByteArray (c.env.calldata.readBytes (UInt256.ofNat 56).toNat 32))).toNat = _
    rw [show (UInt256.ofNat 56).toNat = 56 from rfl, toNat_amount c.env.calldata (by omega), hcalldata]
  · rw [hcalldata]; exact bytesOk_bytes _

/-- The inhibitor word is the model's `inhibited`. -/
theorem inhibited_iff_word {s : Model.State} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s calldata value) : excessWord c = INH ↔ inhibited s = true := by
  rw [eq_INH_iff, hw.excess]
  unfold inhibited
  simp

/-- **The fee loop ends at the model's fee.** Under the word-exactness witness of
an enabled user call, `fake_expo` terminates within `256` iterations and the
word it quotes is `Model.currentFee`. -/
theorem fee_of_noWrap {s : Model.State} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s calldata value) (hnw : FeeQuoteNoWrap s) :
    ∃ o' i' : UInt256, FeeLoopEnds c 256 o' i' ∧ (feeWord o').toNat = currentFee s := by
  obtain ⟨hlt, hfit⟩ := hnw
  have heff : (effExcess c).toNat = effectiveExcess s := by
    unfold effExcess effectiveExcess
    rw [hw.kind]
    have h8 : (UInt256.ofNat 8).toNat = 8 := rfl
    have hexcess := hw.excess
    have hcount := hw.count
    by_cases hcnt : 8 < (countWord c).toNat
    · rw [if_pos hcnt]
      have hsub : (countWord c - UInt256.ofNat 8).toNat = s.count - 8 := by
        rw [toNat_sub_of_le _ _ (by rw [h8]; omega), h8, hcount]
      have hlt' : s.storedExcess + (s.count - 8) < UInt256.size := by
        unfold effectiveExcess at hlt; rw [hw.kind] at hlt; exact hlt
      rw [toNat_add_of_lt _ _ (by rw [hsub, hexcess]; show s.count - 8 + s.storedExcess < _; omega),
        hsub, hexcess]
      show s.count - 8 + s.storedExcess = s.storedExcess + (s.count - 8)
      omega
    · rw [if_neg hcnt, hexcess]
      show s.storedExcess = s.storedExcess + (s.count - 8)
      omega
  have hfit' : fakeExpoFitsWord (effExcess c).toNat 17 256 (UInt256.ofNat 1).toNat
      (UInt256.ofNat 0).toNat (UInt256.ofNat 17 * UInt256.ofNat 1).toNat = true := by
    rw [heff]; exact hfit
  obtain ⟨o', i', hexit, hval⟩ := feeExit_of_fits (effExcess c) 256 (UInt256.ofNat 0)
    (UInt256.ofNat 17 * UInt256.ofNat 1) (UInt256.ofNat 1) hfit' (by decide)
  refine ⟨o', i', hexit, ?_⟩
  show (o' / UInt256.ofNat 17).toNat = currentFee s
  rw [toNat_div, toNat_seventeen, hval, heff]
  rfl

/-- **`Model.admissible`, as the checks the runtime performs.** -/
theorem admissible_iff {s : Model.State} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s calldata value) (hen : inhibited s = false) :
    admissible s calldata value = true ↔
      calldata.length = 184 ∧ 1000000000 ≤ depositAmount calldata ∧
        depositAmount calldata * 1000000000 + currentFee s ≤ value := by
  unfold admissible
  rw [hen, hw.kind]
  unfold depositWellFormed
  rw [hw.bytesOk]
  simp only [Bool.not_false, Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    depositInputSize, gwei, builderMinDepositWei, ge_iff_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by omega⟩, h3⟩

/-- The three runtime checks after the size dispatch, as the model sees them. -/
theorem checks_iff {s : Model.State} {calldata : List Byte} {value : Wei} {o' : UInt256}
    (hw : UserWords c s calldata value) (hfee : (feeWord o').toNat = currentFee s)
    (hlen : calldata.length = 184) :
    (¬ valueWord c < feeWord o' ∧ ¬ amountWord c < UInt256.ofNat 1000000000 ∧
        ¬ (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c) ↔
      (1000000000 ≤ depositAmount calldata ∧
        depositAmount calldata * 1000000000 + currentFee s ≤ value) := by
  have hamt := hw.amount hlen
  have hamt_lt : (amountWord c).toNat < 2 ^ 64 := by
    show (UInt256.land mask _).toNat < _
    rw [toNat_land_mask]; exact Nat.mod_lt _ (by decide)
  have hprod : (UInt256.ofNat 1000000000 * amountWord c).toNat = 1000000000 * depositAmount calldata := by
    rw [toNat_mul_of_lt _ _ (by rw [toNat_gweiW]; exact gwei_lt _ hamt_lt), toNat_gweiW, hamt]
  simp only [lt_iff_toNat, hw.value, hfee, hamt, toNat_gweiW, hprod, not_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [toNat_sub_of_le _ _ (by rw [hw.value, hfee]; exact h1), hw.value, hfee] at h3
    exact ⟨h2, by omega⟩
  · rintro ⟨h2, h3⟩
    refine ⟨by omega, h2, ?_⟩
    rw [toNat_sub_of_le _ _ (by rw [hw.value, hfee]; omega), hw.value, hfee]
    omega

/-- **The accepted submission is the model's accepted submission.** -/
theorem userCall_append {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {o' : UInt256} (hw : UserWords c s calldata value) (hen : inhibited s = false)
    (hfee : (feeWord o').toNat = currentFee s) (hlen : calldata.length = 184)
    (hpaid : ¬ valueWord c < feeWord o') (hfloor : ¬ amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c) :
    userCall s caller calldata value = .success (appendRecord s caller calldata value) [] := by
  have hadm : admissible s calldata value = true :=
    (admissible_iff c hw hen).mpr ⟨hlen, (checks_iff c hw hfee hlen).mp ⟨hpaid, hfloor, hstake⟩⟩
  have hne : calldata ≠ [] := by
    intro h; rw [h] at hlen; exact absurd hlen (by decide)
  unfold userCall
  rw [hen, if_neg hne, hadm]
  rfl

/-- **Every admissible, word-exact deposit call halts.** The `TerminationClosure`
shape, with the word-exactness and calldata-width premises stated. -/
theorem halts_of_admissible {s : Model.State} {call : Model.Step}
    (hrep : PreCallRepresents c s call) (hadm : AdmissibleCall c s call)
    (hword : WordExactCall s call) (hcd : c.env.calldata.size < UInt256.size) :
    Nonempty (XiHalts c) := by
  have hgas : 30000000 ≤ c.gas.toNat := hadm.gas_ge
  have hfuel : 300000 ≤ c.fuel := hadm.fuel_ge
  rcases call with ⟨caller, calldata, value⟩ | b
  · have hw := userWords c hrep hadm hcd
    by_cases hinh : excessWord c = INH
    · obtain ⟨_, _, hend⟩ := user_inhibited c hw.user hinh (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    have hen : inhibited s = false := by
      rcases Bool.eq_false_or_eq_true (inhibited s) with h | h
      · exact absurd ((inhibited_iff_word c hw).mpr h) hinh
      · exact h
    have hnw : FeeQuoteNoWrap s := by
      rcases hword.noWrap with h | h
      · rw [hen] at h; exact absurd h (by decide)
      · exact h
    obtain ⟨o', i', hfee, hfeeval⟩ := fee_of_noWrap c hw hnw
    by_cases h184 : cdsizeWord c = UInt256.ofNat 184
    · have hlen : calldata.length = 184 := by
        rw [eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size] at h184; exact h184
      by_cases hlt : valueWord c < feeWord o'
      · obtain ⟨_, _, hend⟩ := user_underpay_reverts c hw.user hinh hfee h184 hlt (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
        exact ⟨hx⟩
      by_cases hfloor : amountWord c < UInt256.ofNat 1000000000
      · obtain ⟨_, _, hend⟩ :=
          user_amountFloor_reverts c hw.user hinh hfee h184 hlt hfloor (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
        exact ⟨hx⟩
      by_cases hstake : (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c
      · obtain ⟨_, _, hend⟩ :=
          user_stake_reverts c hw.user hinh hfee h184 hlt hfloor hstake (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
        exact ⟨hx⟩
      have hperm : c.env.perm = true :=
        hadm.writable (userCall_append c hw hen hfeeval hlen hlt hfloor hstake)
      obtain ⟨_, _, hend⟩ :=
        user_append_stops c hw.user hinh hperm hfee h184 hlt hfloor hstake (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_STOP (by omega)
      exact ⟨hx⟩
    by_cases h0 : cdsizeWord c = ⟨0⟩
    · by_cases hval : valueWord c = ⟨0⟩
      · obtain ⟨_, _, hend⟩ := user_getter_returns c hw.user hinh hfee h0 hval (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
        exact ⟨hx⟩
      obtain ⟨_, _, hend⟩ := user_paidGetter_reverts c hw.user hinh hfee h0 hval (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ := user_badsize_reverts c hw.user hinh hfee h184 h0 (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  · have henv : SystemCallBinding c b := hadm.env
    have hsys : callerWord c = sysW := (callerW_eq_sysW_iff c).mpr henv.source_eq
    obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys henv.writable (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
    exact ⟨hx⟩

/-! ### The system words -/

/-- The entry words of a system call, read against the entry image `σ`. -/
structure SystemWords (σ : Storage) (b : Bool) : Prop where
  sys : callerWord c = sysW
  excess : excessWord c = loadU256 σ 0
  count : countWord c = loadU256 σ 1
  head : headWord₀ c = loadU256 σ 2
  tail : tailWord₀ c = loadU256 σ 3
  flag : (cdsizeWord c ≠ ⟨0⟩) ↔ b = true
  wf : WellFormed .deposit σ

theorem systemWords {s : Model.State} {b : Bool} (hrep : PreCallRepresents c s (.system b))
    (hadm : AdmissibleCall c s (.system b)) (hcd : c.env.calldata.size < UInt256.size) :
    ∃ acc : Account .EVM, c.entry.accountMap.get? c.env.codeOwner = some acc ∧
      s = toModel .deposit acc.storage acc.balance.toNat ∧ SystemWords c acc.storage b := by
  obtain ⟨acc, hacc, hwf, hs⟩ := system_entry_account hrep hadm
  have henv : SystemCallBinding c b := hadm.env
  refine ⟨acc, hacc, hs, (callerW_eq_sysW_iff c).mpr henv.source_eq, ?_, ?_, ?_, ?_, ?_, hwf⟩
  · exact slotW_entry_loadU256 c hacc 0
  · exact slotW_entry_loadU256 c hacc 1
  · exact slotW_entry_loadU256 c hacc 2
  · exact slotW_entry_loadU256 c hacc 3
  · rw [henv.calldata_flag, ne_eq, cdsizeW_eq_zero_iff c hcd]
    show ¬ c.env.calldata.size = 0 ↔ (!(c.env.calldata.size == 0)) = true
    simp

theorem toNat_headWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (headWord₀ c).toNat = queueHead σ := by rw [hw.head]; rfl

theorem toNat_tailWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (tailWord₀ c).toNat = queueTail σ := by rw [hw.tail]; rfl

/-- **The drained count is the model's.** `min(tail − head, 64)` on words is
`drainCount` on naturals, the pointers being well-formed. -/
theorem toNat_drainWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (drainWord c).toNat = drainCount .deposit σ := by
  have hle : queueHead σ ≤ queueTail σ := head_le_tail hw.wf
  have hlen : (queueLen c).toNat = queueTail σ - queueHead σ := by
    show (tailWord₀ c - headWord₀ c).toNat = _
    rw [toNat_sub_of_le _ _ (by rw [toNat_headWord c hw, toNat_tailWord c hw]; exact hle),
      toNat_headWord c hw, toNat_tailWord c hw]
  unfold drainWord drainCount
  simp only [capOf, maxDepositPerBlock]
  by_cases h : queueLen c < UInt256.ofNat 64
  · rw [if_pos h, hlen]
    have h' : (queueLen c).toNat < 64 := h
    rw [hlen] at h'
    omega
  · rw [if_neg h]
    have h' : ¬ (queueLen c).toNat < 64 := h
    rw [hlen] at h'
    show 64 = _
    omega

/-- **A full drain is the model's full drain.** -/
theorem full_drain_iff {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    tailWord₀ c = headWord₀ c + drainWord c ↔
      queueHead σ + drainCount .deposit σ = queueTail σ := by
  have hd := toNat_drainWord c hw
  have hlt := tail_lt_2_64 hw.wf
  have hle := head_le_tail hw.wf
  have hdc : drainCount .deposit σ ≤ queueTail σ - queueHead σ := Nat.min_le_right _ _
  have hsum : (headWord₀ c + drainWord c).toNat = queueHead σ + drainCount .deposit σ := by
    rw [toNat_add_of_lt _ _ (by rw [toNat_headWord c hw, hd, size_eq]; omega), toNat_headWord c hw,
      hd]
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    rw [hsum, toNat_tailWord c hw] at this
    exact this.symm
  · intro h
    rw [← ofNat_toNat' (tailWord₀ c), ← ofNat_toNat' (headWord₀ c + drainWord c), hsum,
      toNat_tailWord c hw, h]

/-- **The excess the drain stores is the model's `nextExcess`**, at any state
whose control slots still read the entry words, on the branches where the word
sum is exact. -/
theorem toNat_newExcess {σ : Storage} {b : Bool} (hw : SystemWords c σ b)
    (stX : EvmYul.State .EVM) (h0 : slotW stX (UInt256.ofNat 0) = excessWord c)
    (h1 : slotW stX (UInt256.ofNat 1) = countWord c)
    (hnw : b = true ∨ slotExcess σ = inhibitor ∨ slotExcess σ + slotCount σ < UInt256.size) :
    (newExcess c stX).toNat = nextExcessOf .deposit σ b := by
  have hex : (slotW stX (UInt256.ofNat 0)).toNat = slotExcess σ := by rw [h0, hw.excess]; rfl
  have hct : (slotW stX (UInt256.ofNat 1)).toNat = slotCount σ := by rw [h1, hw.count]; rfl
  have hinh : slotW stX (UInt256.ofNat 0) = INH ↔ slotExcess σ = inhibitor := by
    rw [eq_INH_iff, hex]
  unfold newExcess nextExcessOf nextExcess
  simp only [toModel_excess, toModel_count, toModel_kind, targetOf, targetDeposit, inhibited,
    decide_eq_true_eq]
  cases b with
  | true =>
    rw [if_pos (hw.flag.mpr rfl), if_pos rfl]
    exact toNat_INH
  | false =>
    rw [if_neg (fun h => Bool.false_ne_true (hw.flag.mp h)),
      if_neg (show ¬ (false = true) from Bool.false_ne_true)]
    by_cases hi : slotExcess σ = inhibitor
    · rw [if_pos (hinh.mpr hi), if_pos hi]; rfl
    · rw [if_neg (fun h => hi (hinh.mp h)), if_neg hi]
      have hbound : slotExcess σ + slotCount σ < UInt256.size := by
        rcases hnw with h | h | h
        · exact absurd h (by decide)
        · exact absurd h hi
        · exact h
      have hsum : (slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)).toNat
          = slotCount σ + slotExcess σ := by
        rw [toNat_add_of_lt _ _ (by rw [hct, hex]; omega), hct, hex]
      have h8 : (UInt256.ofNat 8).toNat = 8 := rfl
      by_cases hgt : UInt256.ofNat 8 < slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)
      · rw [if_pos hgt]
        have hgt' : 8 < slotCount σ + slotExcess σ := by
          have := (lt_iff_toNat _ _).mp hgt; rw [h8, hsum] at this; exact this
        rw [if_pos (by omega), toNat_sub_of_le _ _ (by rw [h8, hsum]; omega), hsum, h8]
        omega
      · rw [if_neg hgt]
        have hle' : ¬ 8 < slotCount σ + slotExcess σ := by
          intro h; apply hgt; rw [lt_iff_toNat, h8, hsum]; exact h
        by_cases hge : slotExcess σ + slotCount σ ≥ 8
        · rw [if_pos hge]; show 0 = _; omega
        · rw [if_neg hge]; rfl

end Deposit

/-! ## The exit runtime -/

namespace Exit

variable (c : XiCall .exit)

/-- The entry words of a user call, as the model's operands. -/
structure UserWords (s : Model.State) (caller : Address) (calldata : List Byte) (value : Wei) : Prop where
  user : callerWord c ≠ sysW
  kind : s.kind = .exit
  caller : (callerWord c).toNat = caller
  excess : (excessWord c).toNat = s.storedExcess
  count : (countWord c).toNat = s.count
  size : (cdsizeWord c).toNat = calldata.length
  value : (valueWord c).toNat = value
  bytesOk : Model.bytesOk calldata = true

theorem userWords {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    (hrep : PreCallRepresents c s (.user caller calldata value))
    (hadm : AdmissibleCall c s (.user caller calldata value))
    (hcd : c.env.calldata.size < UInt256.size) : UserWords c s caller calldata value := by
  obtain ⟨acc, hacc, _, hs⟩ := user_entry_account hrep hadm
  have henv : UserCallBinding c caller calldata value := hadm.env
  have hcalldata : calldata = bytes c.env.calldata := henv.calldata_eq.symm
  refine ⟨fun h => henv.user ((callerW_eq_sysW_iff c).mp h), by rw [hs]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (callerW (entrySt c)).toNat = caller
    rw [callerW_entry, henv.source_eq]
    change (UInt256.ofNat (caller % AccountAddress.size)).toNat = caller
    change (caller % AccountAddress.size) % UInt256.size = caller
    rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num [AccountAddress.size])) (by decide))]
    exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using henv.canonical)
  · show (slotW (entrySt c) (UInt256.ofNat 0)).toNat = s.storedExcess
    rw [hs, toNat_slotW_entry c hacc 0]; rfl
  · show (slotW (entrySt c) (UInt256.ofNat 1)).toNat = s.count
    rw [hs, toNat_slotW_entry c hacc 1]; rfl
  · rw [hcalldata, length_bytes_calldata]; exact toNat_cdsizeW c hcd
  · exact henv.value_eq
  · rw [hcalldata]; exact bytesOk_bytes _

theorem inhibited_iff_word {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s caller calldata value) : excessWord c = INH ↔ inhibited s = true := by
  rw [eq_INH_iff, hw.excess]
  unfold inhibited
  simp

/-- **The fee loop ends at the model's fee** (target `2`). -/
theorem fee_of_noWrap {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s caller calldata value) (hnw : FeeQuoteNoWrap s) :
    ∃ o' i' : UInt256, FeeLoopEnds c 256 o' i' ∧ (feeWord o').toNat = currentFee s := by
  obtain ⟨hlt, hfit⟩ := hnw
  have heff : (effExcess c).toNat = effectiveExcess s := by
    unfold effExcess effectiveExcess
    rw [hw.kind]
    have h2 : (UInt256.ofNat 2).toNat = 2 := rfl
    have hexcess := hw.excess
    have hcount := hw.count
    by_cases hcnt : 2 < (countWord c).toNat
    · rw [if_pos hcnt]
      have hsub : (countWord c - UInt256.ofNat 2).toNat = s.count - 2 := by
        rw [toNat_sub_of_le _ _ (by rw [h2]; omega), h2, hcount]
      have hlt' : s.storedExcess + (s.count - 2) < UInt256.size := by
        unfold effectiveExcess at hlt; rw [hw.kind] at hlt; exact hlt
      rw [toNat_add_of_lt _ _ (by rw [hsub, hexcess]; show s.count - 2 + s.storedExcess < _; omega),
        hsub, hexcess]
      show s.count - 2 + s.storedExcess = s.storedExcess + (s.count - 2)
      omega
    · rw [if_neg hcnt, hexcess]
      show s.storedExcess = s.storedExcess + (s.count - 2)
      omega
  have hfit' : fakeExpoFitsWord (effExcess c).toNat 17 256 (UInt256.ofNat 1).toNat
      (UInt256.ofNat 0).toNat (UInt256.ofNat 17 * UInt256.ofNat 1).toNat = true := by
    rw [heff]; exact hfit
  obtain ⟨o', i', hexit, hval⟩ := feeExit_of_fits (effExcess c) 256 (UInt256.ofNat 0)
    (UInt256.ofNat 17 * UInt256.ofNat 1) (UInt256.ofNat 1) hfit' (by decide)
  refine ⟨o', i', hexit, ?_⟩
  show (o' / UInt256.ofNat 17).toNat = currentFee s
  rw [toNat_div, toNat_seventeen, hval, heff]
  rfl

/-- **`Model.admissible`, as the checks the runtime performs.** -/
theorem admissible_iff {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : UserWords c s caller calldata value) (hen : inhibited s = false) :
    admissible s calldata value = true ↔ calldata.length = 48 ∧ currentFee s ≤ value := by
  unfold admissible
  rw [hen, hw.kind]
  unfold exitWellFormed
  rw [hw.bytesOk]
  simp only [Bool.not_false, Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    pubkeySize, ge_iff_le]

/-- The fee check after the size dispatch, as the model sees it. -/
theorem checks_iff {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei} {o' : UInt256}
    (hw : UserWords c s caller calldata value) (hfee : (feeWord o').toNat = currentFee s) :
    ¬ valueWord c < feeWord o' ↔ currentFee s ≤ value := by
  rw [lt_iff_toNat, hw.value, hfee, not_lt]

/-- **The accepted request is the model's accepted request.** -/
theorem userCall_append {s : Model.State} {caller : Address} {calldata : List Byte} {value : Wei}
    {o' : UInt256} (hw : UserWords c s caller calldata value) (hen : inhibited s = false)
    (hfee : (feeWord o').toNat = currentFee s) (hlen : calldata.length = 48)
    (hpaid : ¬ valueWord c < feeWord o') :
    userCall s caller calldata value = .success (appendRecord s caller calldata value) [] := by
  have hadm : admissible s calldata value = true :=
    (admissible_iff c hw hen).mpr ⟨hlen, (checks_iff c hw hfee).mp hpaid⟩
  have hne : calldata ≠ [] := by
    intro h; rw [h] at hlen; exact absurd hlen (by decide)
  unfold userCall
  rw [hen, if_neg hne, hadm]
  rfl

/-- **Every admissible, word-exact exit call halts.** -/
theorem halts_of_admissible {s : Model.State} {call : Model.Step}
    (hrep : PreCallRepresents c s call) (hadm : AdmissibleCall c s call)
    (hword : WordExactCall s call) (hcd : c.env.calldata.size < UInt256.size) :
    Nonempty (XiHalts c) := by
  have hgas : 30000000 ≤ c.gas.toNat := hadm.gas_ge
  have hfuel : 300000 ≤ c.fuel := hadm.fuel_ge
  rcases call with ⟨caller, calldata, value⟩ | b
  · have hw := userWords c hrep hadm hcd
    by_cases hinh : excessWord c = INH
    · obtain ⟨_, _, hend⟩ := user_inhibited c hw.user hinh (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    have hen : inhibited s = false := by
      rcases Bool.eq_false_or_eq_true (inhibited s) with h | h
      · exact absurd ((inhibited_iff_word c hw).mpr h) hinh
      · exact h
    have hnw : FeeQuoteNoWrap s := by
      rcases hword.noWrap with h | h
      · rw [hen] at h; exact absurd h (by decide)
      · exact h
    obtain ⟨o', i', hfee, hfeeval⟩ := fee_of_noWrap c hw hnw
    by_cases h48 : cdsizeWord c = UInt256.ofNat 48
    · have hlen : calldata.length = 48 := by
        rw [eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size] at h48; exact h48
      by_cases hlt : valueWord c < feeWord o'
      · obtain ⟨_, _, hend⟩ := user_underpay_reverts c hw.user hinh hfee h48 hlt (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
        exact ⟨hx⟩
      have hperm : c.env.perm = true :=
        hadm.writable (userCall_append c hw hen hfeeval hlen hlt)
      obtain ⟨_, _, hend⟩ := user_append_stops c hw.user hinh hperm hfee h48 hlt (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_STOP (by omega)
      exact ⟨hx⟩
    by_cases h0 : cdsizeWord c = ⟨0⟩
    · by_cases hval : valueWord c = ⟨0⟩
      · obtain ⟨_, _, hend⟩ := user_getter_returns c hw.user hinh hfee h0 hval (by omega)
        obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
        exact ⟨hx⟩
      obtain ⟨_, _, hend⟩ := user_paidGetter_reverts c hw.user hinh hfee h0 hval (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ := user_badsize_reverts c hw.user hinh hfee h48 h0 (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  · have henv : SystemCallBinding c b := hadm.env
    have hsys : callerWord c = sysW := (callerW_eq_sysW_iff c).mpr henv.source_eq
    obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys henv.writable (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
    exact ⟨hx⟩

/-! ### The system words -/

/-- The entry words of a system call, read against the entry image `σ`. -/
structure SystemWords (σ : Storage) (b : Bool) : Prop where
  sys : callerWord c = sysW
  excess : excessWord c = loadU256 σ 0
  count : countWord c = loadU256 σ 1
  head : headWord₀ c = loadU256 σ 2
  tail : tailWord₀ c = loadU256 σ 3
  flag : (cdsizeWord c ≠ ⟨0⟩) ↔ b = true
  wf : WellFormed .exit σ

theorem systemWords {s : Model.State} {b : Bool} (hrep : PreCallRepresents c s (.system b))
    (hadm : AdmissibleCall c s (.system b)) (hcd : c.env.calldata.size < UInt256.size) :
    ∃ acc : Account .EVM, c.entry.accountMap.get? c.env.codeOwner = some acc ∧
      s = toModel .exit acc.storage acc.balance.toNat ∧ SystemWords c acc.storage b := by
  obtain ⟨acc, hacc, hwf, hs⟩ := system_entry_account hrep hadm
  have henv : SystemCallBinding c b := hadm.env
  refine ⟨acc, hacc, hs, (callerW_eq_sysW_iff c).mpr henv.source_eq, ?_, ?_, ?_, ?_, ?_, hwf⟩
  · exact slotW_entry_loadU256 c hacc 0
  · exact slotW_entry_loadU256 c hacc 1
  · exact slotW_entry_loadU256 c hacc 2
  · exact slotW_entry_loadU256 c hacc 3
  · rw [henv.calldata_flag, ne_eq, cdsizeW_eq_zero_iff c hcd]
    show ¬ c.env.calldata.size = 0 ↔ (!(c.env.calldata.size == 0)) = true
    simp

theorem toNat_headWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (headWord₀ c).toNat = queueHead σ := by rw [hw.head]; rfl

theorem toNat_tailWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (tailWord₀ c).toNat = queueTail σ := by rw [hw.tail]; rfl

/-- **The drained count is the model's** (cap `16`). -/
theorem toNat_drainWord {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    (drainWord c).toNat = drainCount .exit σ := by
  have hle : queueHead σ ≤ queueTail σ := head_le_tail hw.wf
  have hlen : (queueLen c).toNat = queueTail σ - queueHead σ := by
    show (tailWord₀ c - headWord₀ c).toNat = _
    rw [toNat_sub_of_le _ _ (by rw [toNat_headWord c hw, toNat_tailWord c hw]; exact hle),
      toNat_headWord c hw, toNat_tailWord c hw]
  unfold drainWord drainCount
  simp only [capOf, maxExitPerBlock]
  by_cases h : queueLen c < UInt256.ofNat 16
  · rw [if_pos h, hlen]
    have h' : (queueLen c).toNat < 16 := h
    rw [hlen] at h'
    omega
  · rw [if_neg h]
    have h' : ¬ (queueLen c).toNat < 16 := h
    rw [hlen] at h'
    show 16 = _
    omega

/-- **A full drain is the model's full drain.** -/
theorem full_drain_iff {σ : Storage} {b : Bool} (hw : SystemWords c σ b) :
    tailWord₀ c = headWord₀ c + drainWord c ↔
      queueHead σ + drainCount .exit σ = queueTail σ := by
  have hd := toNat_drainWord c hw
  have hlt := tail_lt_2_64 hw.wf
  have hle := head_le_tail hw.wf
  have hdc : drainCount .exit σ ≤ queueTail σ - queueHead σ := Nat.min_le_right _ _
  have hsum : (headWord₀ c + drainWord c).toNat = queueHead σ + drainCount .exit σ := by
    rw [toNat_add_of_lt _ _ (by rw [toNat_headWord c hw, hd, size_eq]; omega), toNat_headWord c hw,
      hd]
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    rw [hsum, toNat_tailWord c hw] at this
    exact this.symm
  · intro h
    rw [← ofNat_toNat' (tailWord₀ c), ← ofNat_toNat' (headWord₀ c + drainWord c), hsum,
      toNat_tailWord c hw, h]

/-- **The excess the drain stores is the model's `nextExcess`** (target `2`). -/
theorem toNat_newExcess {σ : Storage} {b : Bool} (hw : SystemWords c σ b)
    (stX : EvmYul.State .EVM) (h0 : slotW stX (UInt256.ofNat 0) = excessWord c)
    (h1 : slotW stX (UInt256.ofNat 1) = countWord c)
    (hnw : b = true ∨ slotExcess σ = inhibitor ∨ slotExcess σ + slotCount σ < UInt256.size) :
    (newExcess c stX).toNat = nextExcessOf .exit σ b := by
  have hex : (slotW stX (UInt256.ofNat 0)).toNat = slotExcess σ := by rw [h0, hw.excess]; rfl
  have hct : (slotW stX (UInt256.ofNat 1)).toNat = slotCount σ := by rw [h1, hw.count]; rfl
  have hinh : slotW stX (UInt256.ofNat 0) = INH ↔ slotExcess σ = inhibitor := by
    rw [eq_INH_iff, hex]
  unfold newExcess nextExcessOf nextExcess
  simp only [toModel_excess, toModel_count, toModel_kind, targetOf, targetExit, inhibited,
    decide_eq_true_eq]
  cases b with
  | true =>
    rw [if_pos (hw.flag.mpr rfl), if_pos rfl]
    exact toNat_INH
  | false =>
    rw [if_neg (fun h => Bool.false_ne_true (hw.flag.mp h)),
      if_neg (show ¬ (false = true) from Bool.false_ne_true)]
    by_cases hi : slotExcess σ = inhibitor
    · rw [if_pos (hinh.mpr hi), if_pos hi]; rfl
    · rw [if_neg (fun h => hi (hinh.mp h)), if_neg hi]
      have hbound : slotExcess σ + slotCount σ < UInt256.size := by
        rcases hnw with h | h | h
        · exact absurd h (by decide)
        · exact absurd h hi
        · exact h
      have hsum : (slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)).toNat
          = slotCount σ + slotExcess σ := by
        rw [toNat_add_of_lt _ _ (by rw [hct, hex]; omega), hct, hex]
      have h2 : (UInt256.ofNat 2).toNat = 2 := rfl
      by_cases hgt : UInt256.ofNat 2 < slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)
      · rw [if_pos hgt]
        have hgt' : 2 < slotCount σ + slotExcess σ := by
          have := (lt_iff_toNat _ _).mp hgt; rw [h2, hsum] at this; exact this
        rw [if_pos (by omega), toNat_sub_of_le _ _ (by rw [h2, hsum]; omega), hsum, h2]
        omega
      · rw [if_neg hgt]
        have hle' : ¬ 2 < slotCount σ + slotExcess σ := by
          intro h; apply hgt; rw [lt_iff_toNat, h2, hsum]; exact h
        by_cases hge : slotExcess σ + slotCount σ ≥ 2
        · rw [if_pos hge]; show 0 = _; omega
        · rw [if_neg hge]; rfl

end Exit

end Eip8282.Audit.EntryReach
