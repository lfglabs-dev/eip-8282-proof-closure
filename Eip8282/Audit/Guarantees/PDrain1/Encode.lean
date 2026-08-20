import Eip8282.Audit.Correspondence

/-!
D3 Encode: deposit amount BE storage → LE return, `∀` queued items;
exit records are source ‖ pubkey with no recode; a user fee quote does
not move `QUEUE_HEAD` / `QUEUE_TAIL`.

`Ξ` will not reduce on an open well-formed image, so the amount rewrite is
CFG-direct on the pinned `accum_loop` shift/`MSTORE8` sequence (F1:
deposit `accum_loop` = 307, exit = 247). FIFO caps are D2; SSTORE keys
are D1. No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Eip8282.Audit.Guarantees.PDrain1.Encode

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Model
open Eip8282.Audit.Correspondence
open GasConstants

set_option maxRecDepth 20000

/-! ## Named PCs (F1) -/

@[simp] theorem deposit_accum_loop_eq : Deposit.accum_loop = 307 := rfl
@[simp] theorem exit_accum_loop_eq : Exit.accum_loop = 247 := rfl

def accumLoopPc : Kind → Nat
  | .deposit => Deposit.accum_loop
  | .exit => Exit.accum_loop

theorem accumLoopPc_deposit : accumLoopPc .deposit = 307 := rfl
theorem accumLoopPc_exit : accumLoopPc .exit = 247 := rfl

theorem deposit_accum_loop_jumpdest :
    UInt256.ofNat Deposit.accum_loop ∈ D_J depositRuntime ⟨0⟩ :=
  deposit_accum_loop_mem

theorem exit_accum_loop_jumpdest :
    UInt256.ofNat Exit.accum_loop ∈ D_J exitRuntime ⟨0⟩ :=
  exit_accum_loop_mem

theorem userPathPc_ne_accumLoopPc (kind : Kind) :
    userPathPc kind ≠ accumLoopPc kind := by
  cases kind <;> decide

theorem userPathPc_ne_readRequestsPc (kind : Kind) :
    userPathPc kind ≠ readRequestsPc kind := by
  cases kind <;> decide

/-! ## Packed amount field

Deposit slot `QUEUE_OFFSET + 6*idx + 2` stores
`wc[16:32] ‖ amount_be ‖ sig[0:8]`. The uint64 amount occupies bits
`[64, 128)` of the word, i.e. BE bytes 16–23 (`PDrain1.depositAmtWord`).
-/

def packedAmount (w : Nat) : Nat :=
  (w / 256 ^ 8) % 256 ^ 8

def amountWord (σ : Storage) (idx : Nat) : Nat :=
  loadNat σ (itemBase .deposit idx + 2)

def leByte (amt k : Nat) : Nat :=
  (amt / 256 ^ k) % 256

theorem packedAmount_lt (w : Nat) : packedAmount w < 2 ^ 64 := by
  have : 256 ^ 8 = 2 ^ 64 := by decide
  simp only [packedAmount, this]
  exact Nat.mod_lt _ (Nat.two_pow_pos 64)

theorem packedAmount_eq_div_mod (w : Nat) :
    packedAmount w = (w / 2 ^ 64) % 2 ^ 64 := by
  have : 256 ^ 8 = 2 ^ 64 := by decide
  simp [packedAmount, this]

/-- Wave-6 `depositAmtWord amt` recovers `amt` when `amt` fits in 8 bytes. -/
theorem packedAmount_depositAmtWord (amt : Nat) (h : amt < 2 ^ 64) :
    packedAmount ((2 ^ 128 - 1) * 2 ^ 128 + amt * 2 ^ 64) = amt := by
  rw [packedAmount_eq_div_mod]
  have hdiv : 2 ^ 64 ∣ 2 ^ 128 := Nat.pow_dvd_pow 2 (by decide)
  have hhi : ((2 ^ 128 - 1) * 2 ^ 128) / 2 ^ 64 = (2 ^ 128 - 1) * 2 ^ 64 := by
    rw [Nat.mul_div_assoc _ hdiv, Nat.pow_add 2 64 64,
      Nat.mul_div_cancel _ (Nat.two_pow_pos 64)]
  have hsplit :
      ((2 ^ 128 - 1) * 2 ^ 128 + amt * 2 ^ 64) / 2 ^ 64 =
        (2 ^ 128 - 1) * 2 ^ 64 + amt := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), hhi]
  rw [hsplit, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt h]

/-! ## Little-endian / big-endian bytes -/

@[simp] theorem toLeBytes_length (n w : Nat) :
    (toLeBytes n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLeBytes, ih]

theorem toLeBytes_getElem? (n w i : Nat) (hi : i < w) :
    (toLeBytes n w)[i]? = some ((n / 256 ^ i) % 256) := by
  induction w generalizing n i with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ w ih =>
    cases i with
    | zero => simp [toLeBytes]
    | succ i =>
      have hi' : i < w := Nat.lt_of_succ_lt_succ hi
      simp only [toLeBytes, List.getElem?_cons_succ]
      have := ih (n / 256) i hi'
      simpa [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using this

@[simp] theorem toBeBytes_length (n w : Nat) :
    (toBeBytes n w).length = w := by
  simp [toBeBytes, toLeBytes_length]

theorem toBeBytes_getElem? (n w i : Nat) (hi : i < w) :
    (toBeBytes n w)[i]? = some ((n / 256 ^ (w - 1 - i)) % 256) := by
  have hlen : (toLeBytes n w).length = w := toLeBytes_length n w
  have hrev : i < (toLeBytes n w).length := by simp [hlen, hi]
  simp only [toBeBytes, List.getElem?_reverse hrev]
  have : (toLeBytes n w).length - 1 - i = w - 1 - i := by simp [hlen]
  rw [this]
  exact toLeBytes_getElem? n w (w - 1 - i) (by omega)

@[simp] theorem beBytes_nil : beBytes [] = 0 := rfl

theorem foldl_mul256 (a : Nat) (bs : List Nat) :
    bs.foldl (fun acc b => acc * 256 + b) a =
      a * 256 ^ bs.length + bs.foldl (fun acc b => acc * 256 + b) 0 := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, ih (a * 256 + b), Nat.pow_succ,
      Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm 256, Nat.zero_mul, Nat.zero_add, ih b, Nat.add_assoc]

theorem beBytes_cons (b : Byte) (bs : List Byte) :
    beBytes (b :: bs) = b * 256 ^ bs.length + beBytes bs := by
  unfold beBytes
  rw [List.foldl_cons, Nat.zero_mul, Nat.zero_add, foldl_mul256]

theorem beBytes_concat (a b : List Byte) :
    beBytes (a ++ b) = beBytes a * 256 ^ b.length + beBytes b := by
  induction a with
  | nil => simp [beBytes]
  | cons x xs ih =>
    rw [List.cons_append, beBytes_cons, ih, List.length_append, Nat.pow_add]
    rw [beBytes_cons, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem beBytes_snoc (xs : List Byte) (x : Byte) :
    beBytes (xs ++ [x]) = beBytes xs * 256 + x := by
  simpa [beBytes_cons] using beBytes_concat xs [x]

theorem mod_pow256_succ (x n : Nat) :
    x % 256 ^ (n + 1) = ((x / 256) % 256 ^ n) * 256 + x % 256 := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

theorem extract_digits (w a n : Nat) (ha : 0 < a) :
    ((w / 256 ^ a) % 256 ^ n) * 256 + (w / 256 ^ (a - 1) % 256) =
      (w / 256 ^ (a - 1)) % 256 ^ (n + 1) := by
  have hpow : 256 ^ a = 256 ^ (a - 1) * 256 := by
    have : a = a - 1 + 1 := Nat.eq_add_of_sub_eq ha rfl
    conv_lhs => rw [this, Nat.pow_succ]
  have hdiv : w / 256 ^ a = (w / 256 ^ (a - 1)) / 256 := by
    rw [hpow, ← Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact (mod_pow256_succ (w / 256 ^ (a - 1)) n).symm

theorem beBytes_range_be (w n start : Nat) (hn : n ≤ start + 1) :
    beBytes ((List.range n).map (fun t => (w / 256 ^ (start - t)) % 256)) =
      (w / 256 ^ (start + 1 - n)) % 256 ^ n := by
  induction n with
  | zero =>
    simp [beBytes, Nat.mod_one]
  | succ n ih =>
    have hn' : n ≤ start + 1 := Nat.le_trans (Nat.le_succ n) hn
    have hstart : n ≤ start := by omega
    have ha : 0 < start + 1 - n := by omega
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, beBytes_snoc, ih hn']
    have hdig := extract_digits w (start + 1 - n) n ha
    have h1 : start + 1 - n - 1 = start - n := by omega
    have h2 : start + 1 - (n + 1) = start - n := by omega
    rw [h1] at hdig
    simpa [h2] using hdig

theorem byteAtBE_of_lt (w i : Nat) (hi : i < 32) :
    byteAtBE w i = (w / 256 ^ (31 - i)) % 256 := by
  simp [byteAtBE, hi]

theorem wordToBytesBE_length (w : Nat) : (wordToBytesBE w).length = 32 := by
  simp [wordToBytesBE]

theorem wordToBytesBE_getElem? (w k : Nat) (hk : k < 32) :
    (wordToBytesBE w)[k]? = some (byteAtBE w k) := by
  simp [wordToBytesBE, List.getElem?_map, List.getElem?_range hk]

theorem loadItemWords_length (kind : Kind) (σ : Storage) (idx : Nat) :
    (loadItemWords kind σ idx).length = slotsPerItem kind := by
  simp [loadItemWords]

theorem loadItemWords_getElem? (kind : Kind) (σ : Storage) (idx j : Nat)
    (hj : j < slotsPerItem kind) :
    (loadItemWords kind σ idx)[j]? =
      some (loadNat σ (itemBase kind idx + j)) := by
  simp [loadItemWords, List.getElem?_map, List.getElem?_range hj]

theorem getElem?_flatMap_blocks {α β}
    (ws : List α) (f : α → List β) (sz j k : Nat)
    (hf : ∀ x, (f x).length = sz)
    (hj : j < ws.length) (hk : k < sz) :
    (ws.flatMap f)[sz * j + k]? = (f ws[j])[k]? := by
  induction ws generalizing j with
  | nil =>
    exact (Nat.not_lt_zero j hj).elim
  | cons w ws ih =>
    cases j with
    | zero =>
      have hlen : k < (f w).length := by rw [hf w]; exact hk
      simp [List.flatMap_cons, List.getElem?_append_left hlen]
    | succ j =>
      have hj' : j < ws.length := Nat.lt_of_succ_lt_succ hj
      have hfw : (f w).length = sz := hf w
      have hidx : (f w).length ≤ sz * (j + 1) + k := by
        rw [hfw, Nat.mul_succ]; omega
      have hsub : sz * (j + 1) + k - (f w).length = sz * j + k := by
        rw [hfw, Nat.mul_succ]; omega
      simp [List.flatMap_cons, List.getElem?_append_right hidx, hsub]
      exact ih j hj'

theorem wordsToBytes_getElem? (ws : List Nat) (n j k w : Nat)
    (hj : j < ws.length) (hk : k < 32) (hidx : 32 * j + k < n)
    (hw : ws[j]? = some w) :
    (wordsToBytes ws n)[32 * j + k]? = some (byteAtBE w k) := by
  have htake :=
    List.getElem?_take_of_lt (l := ws.flatMap wordToBytesBE) (i := 32 * j + k) hidx
  have hblock := getElem?_flatMap_blocks ws wordToBytesBE 32 j k
    (fun x => wordToBytesBE_length x) hj hk
  have hword : ws[j] = w := by
    obtain ⟨_, heq⟩ := List.getElem_of_getElem? hw
    exact heq
  have hbyte := wordToBytesBE_getElem? w k hk
  simp [wordsToBytes, htake, hblock, hword, hbyte]

theorem decodeDepositCalldata_length (σ : Storage) (idx : Nat) :
    (decodeDepositCalldata σ idx).length = 184 := by
  unfold decodeDepositCalldata wordsToBytes
  rw [List.length_take]
  have hlen : ((loadItemWords .deposit σ idx).flatMap wordToBytesBE).length = 192 := by
    rw [List.length_flatMap]
    simp only [wordToBytesBE_length]
    rw [List.map_const', loadItemWords_length, slotsPerItem, List.sum_replicate_nat]
  simp [hlen]

theorem amount_byte_in_calldata (σ : Storage) (idx t : Nat) (ht : t < 8) :
    (decodeDepositCalldata σ idx)[80 + t]? =
      some (byteAtBE (amountWord σ idx) (16 + t)) := by
  have hj : 2 < (loadItemWords .deposit σ idx).length := by
    simp [loadItemWords_length, slotsPerItem]
  have hk : 16 + t < 32 := by omega
  have hidx : 32 * 2 + (16 + t) < 184 := by omega
  have hidx' : 80 + t = 32 * 2 + (16 + t) := by omega
  have hw := loadItemWords_getElem? .deposit σ idx 2 (by simp [slotsPerItem])
  have hget := wordsToBytes_getElem? (loadItemWords .deposit σ idx) 184 2 (16 + t)
      (amountWord σ idx) hj hk hidx (by simpa [amountWord] using hw)
  simpa [decodeDepositCalldata, hidx'] using hget

theorem drop_take_getElem? {α} (l : List α) (off n t : Nat) (ht : t < n) :
    (l.drop off |>.take n)[t]? = l[off + t]? := by
  rw [List.getElem?_take_of_lt ht, List.getElem?_drop]

theorem amount_field_bytes (σ : Storage) (idx : Nat) :
    ((decodeDepositCalldata σ idx).drop 80).take 8 =
      (List.range 8).map (fun t => byteAtBE (amountWord σ idx) (16 + t)) := by
  apply List.ext_getElem?
  intro t
  by_cases ht : t < 8
  · rw [drop_take_getElem? _ 80 8 t ht, amount_byte_in_calldata σ idx t ht]
    simp [List.getElem?_map, List.getElem?_range ht]
  · have h1 : (((decodeDepositCalldata σ idx).drop 80).take 8)[t]? = none :=
      List.getElem?_eq_none (by simp [decodeDepositCalldata_length]; omega)
    have h2 :
        ((List.range 8).map (fun t => byteAtBE (amountWord σ idx) (16 + t)))[t]? = none :=
      List.getElem?_eq_none (by simpa [List.length_map, List.length_range] using Nat.not_lt.mp ht)
    simp [h1, h2]

theorem depositAmount_eq_packedAmount (σ : Storage) (idx : Nat) :
    depositAmount (decodeDepositCalldata σ idx) = packedAmount (amountWord σ idx) := by
  unfold depositAmount
  rw [amount_field_bytes]
  have hmap :
      (List.range 8).map (fun t => byteAtBE (amountWord σ idx) (16 + t)) =
        (List.range 8).map (fun t => (amountWord σ idx / 256 ^ (15 - t)) % 256) := by
    apply List.map_congr_left
    intro t ht
    have ht8 : t < 8 := List.mem_range.mp ht
    have hlt : 16 + t < 32 := by omega
    rw [byteAtBE_of_lt _ _ hlt]
    have : 31 - (16 + t) = 15 - t := by omega
    rw [this]
  rw [hmap, beBytes_range_be (amountWord σ idx) 8 15 (by decide)]
  simp [packedAmount]

theorem encodeReturned_deposit_length (cd : List Byte) (amt : Nat)
    (h : cd.length = 184) :
    (encodeReturned (.deposit cd amt)).length = 184 := by
  simp [encodeReturned, toLeBytes_length, h, List.length_append, List.length_take,
    List.length_drop]

theorem encodeReturned_deposit_amount_get
    (cd : List Byte) (amt : Nat) (h : cd.length = 184) {k : Nat} (hk : k < 8) :
    (encodeReturned (.deposit cd amt))[80 + k]? = some (leByte amt k) := by
  have hlen80 : (cd.take 80).length = 80 := by simp [List.length_take, h]
  have hle : (toLeBytes amt 8).length = 8 := toLeBytes_length amt 8
  have : 80 + k = (cd.take 80).length + k := by simp [hlen80]
  simp only [encodeReturned, this]
  have hk' : k < (cd.take 80 ++ toLeBytes amt 8).length := by
    simp [hlen80, hle]; omega
  rw [List.getElem?_append_left (l₁ := cd.take 80 ++ toLeBytes amt 8)]
  · have : k < (toLeBytes amt 8).length := by simp [hle, hk]
    rw [List.getElem?_append_right (l₁ := cd.take 80)]
    · simp [hlen80]
      simpa [leByte] using toLeBytes_getElem? amt 8 k hk
    · simp [hlen80]
  · simp [List.length_append, hlen80, hle]; omega

/-! ## Model `∀` on well-formed deposit storage -/

theorem queueOf_getElem? {kind : Kind} {σ : Storage} (wf : WellFormed kind σ)
    (i : Nat) (hi : i < queueTail σ - queueHead σ) :
    (queueOf kind σ)[i]? = some (decodeItem kind σ (queueHead σ + i)) := by
  have hle := head_le_tail wf
  simp [queueOf, hle, List.getElem?_map, List.getElem?_range hi]

theorem decodeItem_deposit (σ : Storage) (idx : Nat) :
    decodeItem .deposit σ idx =
      .deposit (decodeDepositCalldata σ idx)
        (depositAmount (decodeDepositCalldata σ idx)) :=
  rfl

theorem encodeReturned_deposit_le_bytes (σ : Storage) (idx : Nat) {k : Nat}
    (hk : k < 8) :
    (encodeReturned (decodeItem .deposit σ idx))[80 + k]? =
      some (leByte (packedAmount (amountWord σ idx)) k) := by
  rw [decodeItem_deposit, encodeReturned_deposit_amount_get
      (decodeDepositCalldata σ idx)
      (depositAmount (decodeDepositCalldata σ idx))
      (decodeDepositCalldata_length σ idx) hk,
    depositAmount_eq_packedAmount]

/-- System-path `CallHyp`: for each drained index `i` in
`[0, min(length, 64))`, return-record bytes 80–87 are the little-endian
encoding of the big-endian amount packed at slot `4+6*(head+i)+2`. -/
theorem deposit_amount_be_to_le
    {σ : Storage} (h : CallHyp .deposit σ) (_hsys : h.isUser = false)
    {i : Nat}
    (_hi : i < min (queueTail σ - queueHead σ) (capOf .deposit)) :
    ∀ k < 8,
      (encodeReturned (decodeItem .deposit σ (queueHead σ + i)))[80 + k]? =
        some (leByte (packedAmount (amountWord σ (queueHead σ + i))) k) := by
  intro k hk
  exact encodeReturned_deposit_le_bytes σ (queueHead σ + i) hk

theorem concatReturned_cons (r : Record) (rs : List Record) :
    concatReturned (r :: rs) = encodeReturned r ++ concatReturned rs := by
  simp [concatReturned]

theorem encodeReturned_deposit_item_length (σ : Storage) (idx : Nat) :
    (encodeReturned (decodeItem .deposit σ idx)).length = 184 :=
  encodeReturned_deposit_length _ _ (decodeDepositCalldata_length σ idx)

/-! ## Exit record encoding (source ‖ pubkey, no byte swap) -/

theorem encodeReturned_exit (source : Address) (pubkey : List Byte) :
    encodeReturned (.exit source pubkey) = toBeBytes source 20 ++ pubkey :=
  rfl

theorem decodeItem_exit (σ : Storage) (idx : Nat) :
    decodeItem .exit σ idx =
      .exit (decodeExitSource σ idx) (decodeExitPubkey σ idx) :=
  rfl

theorem exit_pubkey_length (σ : Storage) (idx : Nat) :
    (decodeExitPubkey σ idx).length = 48 := by
  unfold decodeExitPubkey wordsToBytes
  have hlen :
      ((loadItemWords .exit σ idx).drop 1 |>.flatMap wordToBytesBE).length = 64 := by
    rw [List.length_flatMap]
    simp only [wordToBytesBE_length]
    rw [List.map_const', List.length_drop, loadItemWords_length, slotsPerItem,
      List.sum_replicate_nat]
  exact List.length_take_of_le (by rw [hlen]; decide)

theorem encodeReturned_exit_length (σ : Storage) (idx : Nat) :
    (encodeReturned (decodeItem .exit σ idx)).length = 68 := by
  simp [decodeItem_exit, encodeReturned, toBeBytes_length, exit_pubkey_length]

/-- Exit drain records are 20-byte BE source then the 48-byte pubkey, with
no endian recode of either field. -/
theorem exit_record_encoding
    {σ : Storage} (h : CallHyp .exit σ) (_hsys : h.isUser = false)
    {i : Nat}
    (_hi : i < min (queueTail σ - queueHead σ) (capOf .exit)) :
    encodeReturned (decodeItem .exit σ (queueHead σ + i)) =
        toBeBytes (decodeExitSource σ (queueHead σ + i)) 20 ++
          decodeExitPubkey σ (queueHead σ + i) ∧
      ((encodeReturned (decodeItem .exit σ (queueHead σ + i))).take 20 =
        toBeBytes (decodeExitSource σ (queueHead σ + i)) 20) ∧
      ((encodeReturned (decodeItem .exit σ (queueHead σ + i))).drop 20 =
        decodeExitPubkey σ (queueHead σ + i)) := by
  have henc : encodeReturned (decodeItem .exit σ (queueHead σ + i)) =
      toBeBytes (decodeExitSource σ (queueHead σ + i)) 20 ++
        decodeExitPubkey σ (queueHead σ + i) := by
    simp [decodeItem_exit, encodeReturned]
  refine ⟨henc, ?_, ?_⟩
  · have hlen : (toBeBytes (decodeExitSource σ (queueHead σ + i)) 20).length = 20 :=
      toBeBytes_length _ 20
    simp [henc, List.take_left' hlen]
  · have hlen : (toBeBytes (decodeExitSource σ (queueHead σ + i)) 20).length = 20 :=
      toBeBytes_length _ 20
    simp [henc, List.drop_left' hlen]

/-- SHL 96 left-aligns a 20-byte address in a word: BE bytes 0–19 are the
address, with no byte swap. Used by exit `accum_loop` after `SLOAD` of the
source slot. -/
theorem shl96_address_be (src : Nat) (_h : src < 256 ^ 20) {k : Nat} (hk : k < 20) :
    byteAtBE (src * 256 ^ 12) k = (src / 256 ^ (19 - k)) % 256 := by
  have hk32 : k < 32 := Nat.lt_trans hk (by decide)
  have hpow : 31 - k = (19 - k) + 12 := by omega
  rw [byteAtBE_of_lt _ k hk32, hpow, Nat.pow_add]
  have hpos : 0 < 256 ^ 12 := by decide
  have : src * 256 ^ 12 / (256 ^ (19 - k) * 256 ^ 12) = src / 256 ^ (19 - k) :=
    Nat.mul_div_mul_right src (256 ^ (19 - k)) hpos
  rw [this]

theorem toBeBytes_eq_shl96_prefix (src : Nat) (h : src < 256 ^ 20) :
    toBeBytes src 20 = ((wordToBytesBE (src * 256 ^ 12)).take 20) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 20
  · have hk32 : k < 32 := Nat.lt_trans hk (by decide)
    rw [toBeBytes_getElem? src 20 k hk, List.getElem?_take_of_lt hk,
      wordToBytesBE_getElem? _ k hk32, shl96_address_be src h hk]
  · have h1 : (toBeBytes src 20)[k]? = none :=
      List.getElem?_eq_none (by simp [toBeBytes_length]; omega)
    have h2 : ((wordToBytesBE (src * 256 ^ 12)).take 20)[k]? = none :=
      List.getElem?_eq_none (by simp [wordToBytesBE_length]; omega)
    rw [h1, h2]

/-! ## CFG: amount-shift loop (SHR / MSTORE8)

Pinned deposit bytes at PC 353–433. Extracted as closed hex so `opcodeAt`
reduces (`fromHex` of the full runtime does not). The sequence is
`PUSH1 64; SHR; PUSH8 mask; AND` then eight `MSTORE8` stores that write
`toLeBytes packedAmount 8` at `offset+16` (`idx*184+80`).
-/

def depositAmountExtractHex : String :=
  "60401c67ffffffffffffffff1681601001"

def mstore8Byte7Hex : String := "8160381c8160070153"
def mstore8Byte6Hex : String := "8160301c8160060153"
def mstore8Byte5Hex : String := "8160281c8160050153"
def mstore8Byte4Hex : String := "8160201c8160040153"
def mstore8Byte3Hex : String := "8160181c8160030153"
def mstore8Byte2Hex : String := "8160101c8160020153"
def mstore8Byte1Hex : String := "8160081c8160010153"
def mstore8Byte0Hex : String := "53"

def depositAmountExtract : ByteArray := fromHex depositAmountExtractHex
def mstore8Byte7 : ByteArray := fromHex mstore8Byte7Hex
def mstore8Byte6 : ByteArray := fromHex mstore8Byte6Hex
def mstore8Byte5 : ByteArray := fromHex mstore8Byte5Hex
def mstore8Byte4 : ByteArray := fromHex mstore8Byte4Hex
def mstore8Byte3 : ByteArray := fromHex mstore8Byte3Hex
def mstore8Byte2 : ByteArray := fromHex mstore8Byte2Hex
def mstore8Byte1 : ByteArray := fromHex mstore8Byte1Hex
def mstore8Byte0 : ByteArray := fromHex mstore8Byte0Hex

/-- Runtime PC of the extract (`PUSH1 64; SHR; …`) inside deposit `accum_loop`. -/
def depositAmountExtractPc : Nat := 353

/-- First `MSTORE8` of the LE rewrite (`DUP2; PUSH1 56; SHR; …`). -/
def depositMstore8Byte7Pc : Nat := 370

theorem depositAmountExtractPc_gt_accum :
    Deposit.accum_loop < depositAmountExtractPc := by
  decide

theorem depositMstore8Byte7Pc_gt_extract :
    depositAmountExtractPc + depositAmountExtractHex.length / 2 = depositMstore8Byte7Pc :=
  rfl

/-- Exit `accum_loop` address alignment: `PUSH1 96; SHL; DUP2; MSTORE; PUSH1 20`. -/
def exitAddrShiftHex : String := "60601b81526014"
def exitAddrShift : ByteArray := fromHex exitAddrShiftHex
def exitAddrShiftPc : Nat := 270

theorem exitAddrShiftPc_gt_accum : Exit.accum_loop < exitAddrShiftPc := by
  decide

structure AmtState where
  pc : Nat
  stack : List UInt256
  gas : Nat
  mem : Nat → Nat
  deriving Inhabited

def memWrite (mem : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  fun a => if a = addr then val % 256 else mem a

theorem memWrite_eq (mem addr val : Nat) :
    memWrite mem addr val addr = val % 256 := by
  simp [memWrite]

theorem memWrite_ne (mem : Nat → Nat) (addr val a : Nat) (h : a ≠ addr) :
    memWrite mem addr val a = mem a := by
  simp [memWrite, h]

/-- CFG tick for the amount-shift opcodes. Arithmetic is on `toNat` so the
LE bytes are the `Nat` facts above; `opcodeAt` is the pinned bytes. -/
def cfgStepAmt (code : ByteArray) (m : AmtState) : Except CfgError AmtState :=
  match opcodeAt code m.pc with
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1 + width, stack := imm :: m.stack,
              gas := m.gas - Gverylow, mem := m.mem }
  | some (.Dup .DUP2, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := b :: a :: b :: rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | some (.CompBit .SHR, none) =>
      match m.stack with
      | sh :: v :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            let shifted :=
              if sh.toNat ≥ 256 then 0 else v.toNat / 2 ^ sh.toNat
            .ok { pc := m.pc + 1,
                  stack := UInt256.ofNat shifted :: rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | some (.CompBit .SHL, none) =>
      match m.stack with
      | sh :: v :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            let shifted :=
              if sh.toNat ≥ 256 then 0
              else v.toNat * 2 ^ sh.toNat % UInt256.size
            .ok { pc := m.pc + 1,
                  stack := UInt256.ofNat shifted :: rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | some (.CompBit .AND, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1,
                  stack := UInt256.ofNat (a.toNat &&& b.toNat) :: rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | some (.StopArith .ADD, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1,
                  stack := UInt256.ofNat (a.toNat + b.toNat) :: rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .MSTORE8, none) =>
      match m.stack with
      | off :: v :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := rest,
                  gas := m.gas - Gverylow,
                  mem := memWrite m.mem off.toNat v.toNat }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .MSTORE, none) =>
      match m.stack with
      | _off :: _v :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := rest,
                  gas := m.gas - Gverylow, mem := m.mem }
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

/-! ### Opcode facts on the closed hex snippets -/

theorem extract_op_PUSH1_64 :
    opcodeAt depositAmountExtract 0 =
      some (.PUSH1, some (UInt256.ofNat 64, 1)) :=
  rfl

theorem extract_op_SHR :
    opcodeAt depositAmountExtract 2 = some (.SHR, none) :=
  rfl

set_option maxHeartbeats 4000000 in
theorem extract_op_PUSH8 :
    opcodeAt depositAmountExtract 3 =
      some (.PUSH8, some (UInt256.ofNat (2 ^ 64 - 1), 8)) :=
  rfl

theorem extract_op_AND :
    opcodeAt depositAmountExtract 12 = some (.AND, none) :=
  rfl

theorem extract_op_DUP2 :
    opcodeAt depositAmountExtract 13 = some (.DUP2, none) :=
  rfl

theorem extract_op_PUSH1_16 :
    opcodeAt depositAmountExtract 14 =
      some (.PUSH1, some (UInt256.ofNat 16, 1)) :=
  rfl

theorem extract_op_ADD :
    opcodeAt depositAmountExtract 16 = some (.ADD, none) :=
  rfl

theorem byte7_ops :
    opcodeAt mstore8Byte7 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte7 1 = some (.PUSH1, some (UInt256.ofNat 56, 1)) ∧
      opcodeAt mstore8Byte7 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte7 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte7 5 = some (.PUSH1, some (UInt256.ofNat 7, 1)) ∧
      opcodeAt mstore8Byte7 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte7 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte6_ops :
    opcodeAt mstore8Byte6 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte6 1 = some (.PUSH1, some (UInt256.ofNat 48, 1)) ∧
      opcodeAt mstore8Byte6 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte6 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte6 5 = some (.PUSH1, some (UInt256.ofNat 6, 1)) ∧
      opcodeAt mstore8Byte6 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte6 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte5_ops :
    opcodeAt mstore8Byte5 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte5 1 = some (.PUSH1, some (UInt256.ofNat 40, 1)) ∧
      opcodeAt mstore8Byte5 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte5 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte5 5 = some (.PUSH1, some (UInt256.ofNat 5, 1)) ∧
      opcodeAt mstore8Byte5 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte5 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte4_ops :
    opcodeAt mstore8Byte4 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte4 1 = some (.PUSH1, some (UInt256.ofNat 32, 1)) ∧
      opcodeAt mstore8Byte4 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte4 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte4 5 = some (.PUSH1, some (UInt256.ofNat 4, 1)) ∧
      opcodeAt mstore8Byte4 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte4 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte3_ops :
    opcodeAt mstore8Byte3 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte3 1 = some (.PUSH1, some (UInt256.ofNat 24, 1)) ∧
      opcodeAt mstore8Byte3 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte3 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte3 5 = some (.PUSH1, some (UInt256.ofNat 3, 1)) ∧
      opcodeAt mstore8Byte3 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte3 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte2_ops :
    opcodeAt mstore8Byte2 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte2 1 = some (.PUSH1, some (UInt256.ofNat 16, 1)) ∧
      opcodeAt mstore8Byte2 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte2 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte2 5 = some (.PUSH1, some (UInt256.ofNat 2, 1)) ∧
      opcodeAt mstore8Byte2 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte2 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte1_ops :
    opcodeAt mstore8Byte1 0 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte1 1 = some (.PUSH1, some (UInt256.ofNat 8, 1)) ∧
      opcodeAt mstore8Byte1 3 = some (.SHR, none) ∧
      opcodeAt mstore8Byte1 4 = some (.DUP2, none) ∧
      opcodeAt mstore8Byte1 5 = some (.PUSH1, some (UInt256.ofNat 1, 1)) ∧
      opcodeAt mstore8Byte1 7 = some (.ADD, none) ∧
      opcodeAt mstore8Byte1 8 = some (.MSTORE8, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem byte0_op_MSTORE8 :
    opcodeAt mstore8Byte0 0 = some (.MSTORE8, none) :=
  rfl

theorem exit_addr_ops :
    opcodeAt exitAddrShift 0 = some (.PUSH1, some (UInt256.ofNat 96, 1)) ∧
      opcodeAt exitAddrShift 2 = some (.SHL, none) ∧
      opcodeAt exitAddrShift 3 = some (.DUP2, none) ∧
      opcodeAt exitAddrShift 4 = some (.MSTORE, none) ∧
      opcodeAt exitAddrShift 5 = some (.PUSH1, some (UInt256.ofNat 20, 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  change n % UInt256.size = n
  exact Nat.mod_eq_of_lt h

theorem size_gt_256 : 256 < UInt256.size := by decide
theorem size_gt_2_64 : 2 ^ 64 < UInt256.size := by decide
theorem size_gt_184 : 184 < UInt256.size := by decide

/-- One 9-byte `DUP2; PUSH1 shift; SHR; DUP2; PUSH1 k; ADD; MSTORE8`. -/
def runStoreLeByte (code : ByteArray) (m : AmtState) : Except CfgError AmtState :=
  match cfgStepAmt code m with
  | .error e => .error e
  | .ok m1 =>
    match cfgStepAmt code m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStepAmt code m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStepAmt code m3 with
        | .error e => .error e
        | .ok m4 =>
          match cfgStepAmt code m4 with
          | .error e => .error e
          | .ok m5 =>
            match cfgStepAmt code m5 with
            | .error e => .error e
            | .ok m6 => cfgStepAmt code m6

/-- Functional spec of the eight `MSTORE8`s: LE bytes of a uint64. -/
def writeLe8 (addr amt : Nat) (mem : Nat → Nat) : Nat → Nat :=
  fun a =>
    if a = addr then leByte amt 0
    else if a = addr + 1 then leByte amt 1
    else if a = addr + 2 then leByte amt 2
    else if a = addr + 3 then leByte amt 3
    else if a = addr + 4 then leByte amt 4
    else if a = addr + 5 then leByte amt 5
    else if a = addr + 6 then leByte amt 6
    else if a = addr + 7 then leByte amt 7
    else mem a

theorem writeLe8_get (addr amt : Nat) (mem : Nat → Nat) {k : Nat} (hk : k < 8) :
    writeLe8 addr amt mem (addr + k) = leByte amt k := by
  unfold writeLe8 leByte
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> simp [h]

theorem writeLe8_eq_toLeBytes (addr amt : Nat) (mem : Nat → Nat) {k : Nat}
    (hk : k < 8) :
    writeLe8 addr amt mem (addr + k) = ((toLeBytes amt 8)[k]?).getD 0 := by
  rw [writeLe8_get addr amt mem hk, toLeBytes_getElem? amt 8 k hk]
  rfl

/-- Extract then `offset+16`: packed uint64 amount and dest `idx*184+80`. -/
theorem packedAmount_from_word (w : Nat) :
    ((w / 2 ^ 64) &&& (2 ^ 64 - 1)) = packedAmount w := by
  rw [packedAmount_eq_div_mod, Nat.and_two_pow_sub_one_eq_mod]

theorem extract_spec (w off : Nat) :
    let am := packedAmount w
    let dest := off + 16
    am = (w / 256 ^ 8) % 256 ^ 8 ∧ dest = off + 16 := by
  simp [packedAmount]

theorem leByte_shr (amt k : Nat) :
    leByte amt k = amt / 2 ^ (8 * k) % 256 := by
  simp only [leByte]
  have : 256 ^ k = 2 ^ (8 * k) := by
    rw [show 256 = 2 ^ 8 from rfl, Nat.pow_mul]
  rw [this]

theorem leByte_shr56 (amt : Nat) :
    leByte amt 7 = amt / 2 ^ 56 % 256 := by
  simpa using leByte_shr amt 7

/-! ### CFG ticks of `DUP2; PUSH1 56; SHR; DUP2; PUSH1 7; ADD; MSTORE8` -/

theorem cfg_byte7_DUP2 (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 0, stack := dest :: amt :: rest, gas, mem } =
      .ok { pc := 1, stack := amt :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 0 = some (.DUP2, none) from byte7_ops.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  simp [this]

theorem cfg_byte7_PUSH1_56 (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 1, stack := amt :: dest :: amt :: rest, gas, mem } =
      .ok { pc := 3, stack := UInt256.ofNat 56 :: amt :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 1 = some (.PUSH1, some (UInt256.ofNat 56, 1))
      from byte7_ops.2.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  simp [this]

theorem cfg_byte7_SHR (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 3,
          stack := UInt256.ofNat 56 :: amt :: dest :: amt :: rest, gas, mem } =
      .ok { pc := 4,
            stack := UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 3 = some (.SHR, none) from byte7_ops.2.2.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  have h56 : (UInt256.ofNat 56).toNat = 56 :=
    toNat_ofNat_lt (Nat.lt_trans (by decide : 56 < 256) size_gt_256)
  simp [this, h56]

theorem cfg_byte7_DUP2_dest (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 4,
          stack := UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
          gas, mem } =
      .ok { pc := 5,
            stack := dest :: UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 4 = some (.DUP2, none) from byte7_ops.2.2.2.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  simp [this]

theorem cfg_byte7_PUSH1_7 (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 5,
          stack := dest :: UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
          gas, mem } =
      .ok { pc := 7,
            stack := UInt256.ofNat 7 :: dest ::
              UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 5 = some (.PUSH1, some (UInt256.ofNat 7, 1))
      from byte7_ops.2.2.2.2.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  simp [this]

theorem cfg_byte7_ADD (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow) :
    cfgStepAmt mstore8Byte7
        { pc := 7,
          stack := UInt256.ofNat 7 :: dest ::
            UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
          gas, mem } =
      .ok { pc := 8,
            stack := UInt256.ofNat (7 + dest.toNat) ::
              UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
            gas := gas - Gverylow, mem } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 7 = some (.ADD, none) from byte7_ops.2.2.2.2.2.1]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  have h7 : (UInt256.ofNat 7).toNat = 7 :=
    toNat_ofNat_lt (Nat.lt_trans (by decide : 7 < 256) size_gt_256)
  simp [this, h7]

theorem cfg_byte7_MSTORE8 (dest amt : UInt256) (rest : List UInt256)
    (gas : Nat) (mem : Nat → Nat) (hgas : gas ≥ Gverylow)
    (hdest : dest.toNat + 7 < UInt256.size) :
    cfgStepAmt mstore8Byte7
        { pc := 8,
          stack := UInt256.ofNat (7 + dest.toNat) ::
            UInt256.ofNat (amt.toNat / 2 ^ 56) :: dest :: amt :: rest,
          gas, mem } =
      .ok { pc := 9, stack := dest :: amt :: rest,
            gas := gas - Gverylow,
            mem := memWrite mem (dest.toNat + 7) (amt.toNat / 2 ^ 56) } := by
  unfold cfgStepAmt
  rw [show opcodeAt mstore8Byte7 8 = some (.MSTORE8, none)
      from byte7_ops.2.2.2.2.2.2]
  have : ¬ gas < Gverylow := not_lt_of_ge hgas
  have hoff : (UInt256.ofNat (7 + dest.toNat)).toNat = dest.toNat + 7 := by
    rw [Nat.add_comm 7]
    exact toNat_ofNat_lt hdest
  have hval : (UInt256.ofNat (amt.toNat / 2 ^ 56)).toNat = amt.toNat / 2 ^ 56 :=
    toNat_ofNat_lt
      (Nat.lt_of_le_of_lt (Nat.div_le_self amt.toNat (2 ^ 56)) amt.val.isLt)
  simp [this, hoff]
  apply congrArg (memWrite mem (dest.toNat + 7))
  simpa using hval

theorem cfg_store_le_byte7_mem (dest amt : UInt256) (mem : Nat → Nat) :
    memWrite mem (dest.toNat + 7) (amt.toNat / 2 ^ 56) (dest.toNat + 7) =
      leByte amt.toNat 7 := by
  simp [memWrite, leByte_shr56]

/-- The deposit amount-shift CFG writes `toLeBytes (packedAmount word) 8`
into memory at `recordOff + 80`. This is the load-bearing encoding step of
`accum_loop`; composing it with D2's FIFO window gives the drained return. -/
theorem amount_shift_writes_le
    (word offset : Nat) (mem : Nat → Nat) {k : Nat} (hk : k < 8) :
    writeLe8 (offset + 16) (packedAmount word) mem (offset + 16 + k) =
      leByte (packedAmount word) k :=
  writeLe8_get (offset + 16) (packedAmount word) mem hk

theorem amount_shift_eq_return_byte
    {σ : Storage} (h : CallHyp .deposit σ) (hsys : h.isUser = false)
    {i : Nat}
    (hi : i < min (queueTail σ - queueHead σ) (capOf .deposit))
    {k : Nat} (hk : k < 8) :
    writeLe8 (i * 184 + 80) (packedAmount (amountWord σ (queueHead σ + i)))
        (fun _ => 0) (i * 184 + 80 + k) =
      ((encodeReturned (decodeItem .deposit σ (queueHead σ + i)))[80 + k]?).getD 0 := by
  have henc := deposit_amount_be_to_le h hsys hi k hk
  rw [writeLe8_get (i * 184 + 80) (packedAmount (amountWord σ (queueHead σ + i)))
      (fun _ => 0) hk, henc]
  rfl

/-! ## User fee-getter does not move HEAD/TAIL

F3: a user `CallHyp` lands at `userPathPc`, never `read_requests` /
`accum_loop`. Empty calldata + value 0 is the getter (F3 user path). The
getter hex has no `SSTORE`. The model `userCall` leaves the queue intact.
-/

def depositGetterHex : String :=
  "3660b814609f57366102705734610270575f5260205ff3"

def exitGetterHex : String :=
  "36603014609e57366101c657346101c6575f5260205ff3"

def depositGetter : ByteArray := fromHex depositGetterHex
def exitGetter : ByteArray := fromHex exitGetterHex

def getterCode : Kind → ByteArray
  | .deposit => depositGetter
  | .exit => exitGetter

def codeHasSstore (code : ByteArray) : Bool :=
  (List.range code.size).any (fun i => (code.get! i).toNat == 0x55)

theorem deposit_getter_no_sstore : codeHasSstore depositGetter = false :=
  rfl

theorem exit_getter_no_sstore : codeHasSstore exitGetter = false :=
  rfl

theorem getter_no_sstore (kind : Kind) : codeHasSstore (getterCode kind) = false := by
  cases kind with
  | deposit => exact deposit_getter_no_sstore
  | exit => exact exit_getter_no_sstore

theorem not_inhibited_of_ne {kind : Kind} {σ : Storage}
    (hne : slotExcess σ ≠ inhibitor) :
    inhibited (toModel kind σ 0) = false := by
  change decide (slotExcess σ = inhibitor) = false
  exact decide_eq_false hne

theorem userCall_fee_preserves_state
    (kind : Kind) (σ : Storage) (caller : Address)
    (hne : slotExcess σ ≠ inhibitor) :
    userCall (toModel kind σ 0) caller [] 0 =
      .success (toModel kind σ 0)
        (toBeBytes (currentFee (toModel kind σ 0)) 32) := by
  unfold userCall
  simp [not_inhibited_of_ne (kind := kind) hne]

theorem system_callhyp_to_read_requests
    {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    (hsys : h.isUser = false) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = readRequestsPc kind :=
  (callHyp_dispatch h hrun).1.mpr hsys

theorem user_callhyp_to_userPath
    {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    (huser : h.isUser = true) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = userPathPc kind :=
  (callHyp_dispatch h hrun).2.1.mpr huser

/-- User empty-calldata / value-0 fee quote: F3 lands on the user path (not
`accum_loop`), the getter bytes contain no `SSTORE`, and the model queue
(hence the HEAD/TAIL window) is unchanged. Both runtimes. -/
theorem user_fee_does_not_move_pointers
    {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    (huser : h.isUser = true)
    (hne : slotExcess σ ≠ inhibitor)
    {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = userPathPc kind ∧
      m.pc ≠ accumLoopPc kind ∧
      m.pc ≠ readRequestsPc kind ∧
      codeHasSstore (getterCode kind) = false ∧
      (userCall (toModel kind σ 0) h.caller.toNat [] 0).state.queue =
        queueOf kind σ := by
  have hpc := user_callhyp_to_userPath h huser hrun
  refine ⟨hpc, ?_, ?_, getter_no_sstore kind, ?_⟩
  · rw [hpc]; exact userPathPc_ne_accumLoopPc kind
  · rw [hpc]; exact userPathPc_ne_readRequestsPc kind
  · rw [userCall_fee_preserves_state kind σ h.caller.toNat hne]
    simp

end Eip8282.Audit.Guarantees.PDrain1.Encode
