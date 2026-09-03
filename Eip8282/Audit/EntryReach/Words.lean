import Eip8282.Audit.EntryReach.Path
import Eip8282.Audit.WellFormed

/-!
# The words the runtimes read, in terms of the call

`Machine.lean` reads the branch words off the entry state with `callerW`, `valueW`,
`cdsizeW`, `cdW` and `slotW`. This module says what those words *are* in terms of
the message call `Ξ` was handed — its `ExecutionEnv` and the predeploy account of
its entry world — and collects the 256-bit arithmetic facts the OPERANDS slice
needs: `toNat` of a sum, product, quotient or difference that does not wrap, the
`uint64` mask as a remainder, and the big-endian value of a `CALLDATALOAD`.

Nothing here runs `Ξ` or mentions the model: these are definitional readings of
EVMYulLean's `State.sload`, `State.calldataload` and `ExecutionEnv`.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall bytes)
open Eip8282.Audit.Model (Kind beBytes)
open Eip8282.Audit.WellFormed (loadU256 loadNat)

/-! ## Word arithmetic that does not wrap -/

theorem toNat_lt_size (a : UInt256) : a.toNat < UInt256.size := a.val.isLt

theorem toNat_add_of_lt (a b : UInt256) (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  show (a.toNat + b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt h

theorem toNat_mul_of_lt (a b : UInt256) (h : a.toNat * b.toNat < UInt256.size) :
    (a * b).toNat = a.toNat * b.toNat := by
  show (a.toNat * b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt h

theorem toNat_div (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := rfl

theorem toNat_sub_of_le (a b : UInt256) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have hb : b.toNat < UInt256.size := b.val.isLt
  have ha : a.toNat < UInt256.size := a.val.isLt
  have e : UInt256.size - b.toNat + a.toNat = UInt256.size + (a.toNat - b.toNat) := by omega
  show (a.val - b.val).val = a.toNat - b.toNat
  rw [Fin.sub_def]
  show (UInt256.size - b.toNat + a.toNat) % UInt256.size = a.toNat - b.toNat
  rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem toNat_land (a b : UInt256) :
    (UInt256.land a b).toNat = (a.toNat &&& b.toNat) % UInt256.size := rfl

/-- The `uint64` mask keeps the low 64 bits: a remainder modulo `2 ^ 64`. -/
theorem toNat_land_mask (w : UInt256) : (UInt256.land mask w).toNat = w.toNat % 2 ^ 64 := by
  rw [toNat_land]
  have hm : mask.toNat = 2 ^ 64 - 1 := rfl
  rw [hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by rw [size_eq]; decide))

theorem toNat_ofNat_lit (n : Nat) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  toNat_ofNat_of_lt h

theorem eq_zero_iff_toNat (a : UInt256) : a = ⟨0⟩ ↔ a.toNat = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h
    have : a = UInt256.ofNat a.toNat := (ofNat_toNat' a).symm
    rw [this, h]; rfl

theorem eq_ofNat_iff_toNat (a : UInt256) (n : Nat) (hn : n < UInt256.size) :
    a = UInt256.ofNat n ↔ a.toNat = n := by
  constructor
  · rintro rfl; exact toNat_ofNat_of_lt hn
  · intro h
    rw [← ofNat_toNat' a, h]

theorem lt_iff_toNat (a b : UInt256) : a < b ↔ a.toNat < b.toNat := Iff.rfl

/-! ## The environment words -/

section Env

variable {kind : Kind} (c : XiCall kind)

theorem callerW_entry : callerW (entrySt c) = UInt256.ofNat c.env.source.val := rfl
theorem valueW_entry : valueW (entrySt c) = c.env.weiValue := rfl
theorem cdsizeW_entry : cdsizeW (entrySt c) = UInt256.ofNat c.env.calldata.size := rfl
theorem cdW_entry (off : UInt256) :
    cdW (entrySt c) off = uInt256OfByteArray (c.env.calldata.readBytes off.toNat 32) := rfl

/-- `CALLER` is `SYSTEM_ADDR` exactly when the message call's source is. -/
theorem callerW_eq_sysW_iff :
    callerW (entrySt c) = sysW ↔ c.env.source = EvmRunner.sysAddr := by
  rw [callerW_entry]
  have hsys : (EvmRunner.sysAddr : AccountAddress).val = 1461501637330902918203684832716283019655932542974 := by
    decide
  have hlt : c.env.source.val < UInt256.size :=
    lt_trans c.env.source.isLt (by rw [size_eq]; decide)
  constructor
  · intro h
    have := ofNat_inj_of_lt (n := 1461501637330902918203684832716283019655932542974) hlt
      (by rw [size_eq]; decide) h
    exact Fin.ext (this.trans hsys.symm)
  · intro h
    rw [h, hsys]

/-- The value word is the wei the call carries. -/
theorem toNat_valueW : (valueW (entrySt c)).toNat = c.env.weiValue.toNat := rfl

/-- The calldata-size word, when the calldata fits a word. -/
theorem toNat_cdsizeW (hcd : c.env.calldata.size < UInt256.size) :
    (cdsizeW (entrySt c)).toNat = c.env.calldata.size := toNat_ofNat_of_lt hcd

theorem cdsizeW_eq_zero_iff (hcd : c.env.calldata.size < UInt256.size) :
    cdsizeW (entrySt c) = ⟨0⟩ ↔ c.env.calldata.size = 0 := by
  rw [eq_zero_iff_toNat, toNat_cdsizeW c hcd]

theorem cdsizeW_eq_ofNat_iff (hcd : c.env.calldata.size < UInt256.size) (n : Nat)
    (hn : n < UInt256.size) :
    cdsizeW (entrySt c) = UInt256.ofNat n ↔ c.env.calldata.size = n := by
  rw [eq_ofNat_iff_toNat _ _ hn, toNat_cdsizeW c hcd]

/-- The abstract calldata has the length of the byte string. -/
theorem length_bytes_calldata : (bytes c.env.calldata).length = c.env.calldata.size :=
  Eip8282.Audit.XiTransport.bytes_length _

end Env

/-! ## Storage words -/

section Storage

variable {kind : Kind} (c : XiCall kind)

/-- `SLOAD k` at the entry reads slot `k` of the account the code runs as. -/
theorem slotW_entry {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (k : UInt256) :
    slotW (entrySt c) k = acc.storage.getD k ⟨0⟩ := by
  show (Option.option ⟨0⟩ (fun a => Account.lookupStorage a k)
    ((entrySt c).accountMap.get? (entrySt c).executionEnv.codeOwner)) = _
  have h : (entrySt c).accountMap.get? (entrySt c).executionEnv.codeOwner = some acc := hacc
  rw [h]
  rfl

/-- The same, read through `WellFormed.loadU256` at a small slot number. -/
theorem slotW_entry_loadU256 {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (n : Nat) :
    slotW (entrySt c) (UInt256.ofNat n) = loadU256 acc.storage n :=
  slotW_entry c hacc _

theorem toNat_slotW_entry {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (n : Nat) :
    (slotW (entrySt c) (UInt256.ofNat n)).toNat = loadNat acc.storage n := by
  rw [slotW_entry_loadU256 c hacc]; rfl

end Storage

/-! ## The value of a `CALLDATALOAD`

`State.calldataload off` is the 32 bytes of calldata at `off`, zero-padded, read
big-endian. `byteAt` is one such byte as a natural; `cdBytes b off n` the list of
`n` of them. -/

/-- Byte `j` of `b`, zero past the end. -/
def byteAt (b : ByteArray) (j : Nat) : Nat := if j < b.size then (b.get! j).toNat else 0

/-- The `n` bytes of `b` from `off`, zero-padded. -/
def cdBytes (b : ByteArray) (off n : Nat) : List Nat := (List.range n).map fun i => byteAt b (off + i)

theorem cdBytes_length (b : ByteArray) (off n : Nat) : (cdBytes b off n).length = n := by
  simp [cdBytes]

theorem cdBytes_add (b : ByteArray) (off m n : Nat) :
    cdBytes b off (m + n) = cdBytes b off m ++ cdBytes b (off + m) n := by
  unfold cdBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_assoc]

/-- Inside the array, `byteAt` is the byte the observation `bytes` lists. -/
theorem byteAt_eq_bytes_getElem (b : ByteArray) (j : Nat) (hj : j < b.size) :
    byteAt b j = (bytes b)[j]'(by rw [Eip8282.Audit.XiTransport.bytes_length]; exact hj) := by
  unfold byteAt
  rw [if_pos hj]
  simp [Eip8282.Audit.XiTransport.bytes]

/-- Within the array, `cdBytes` is a slice of the observation. -/
theorem cdBytes_eq_drop_take (b : ByteArray) (off n : Nat) (h : off + n ≤ b.size) :
    cdBytes b off n = ((bytes b).drop off).take n := by
  have hlen : (bytes b).length = b.size := Eip8282.Audit.XiTransport.bytes_length b
  refine List.ext_getElem (by simp [cdBytes_length, hlen]; omega) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa [cdBytes_length] using h₁
  simp only [cdBytes, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  exact byteAt_eq_bytes_getElem b (off + i) (by omega)

theorem beBytes_lt (l : List Nat) (hl : ∀ x ∈ l, x < 256) : beBytes l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [beBytes]
  | append_singleton xs x ih =>
    rw [Eip8282.Audit.Guarantees.PDrain1.Encode.beBytes_snoc, List.length_append,
      List.length_singleton, Nat.pow_succ]
    have hx : x < 256 := hl x (by simp)
    have hxs : beBytes xs < 256 ^ xs.length := ih (fun y hy => hl y (by simp [hy]))
    calc beBytes xs * 256 + x < beBytes xs * 256 + 256 := by omega
      _ = (beBytes xs + 1) * 256 := by ring
      _ ≤ 256 ^ xs.length * 256 := Nat.mul_le_mul_right _ hxs

theorem byteAt_lt (b : ByteArray) (j : Nat) : byteAt b j < 256 := by
  unfold byteAt
  split
  · exact (b.get! j).toNat_lt
  · decide

theorem cdBytes_lt (b : ByteArray) (off n : Nat) : ∀ x ∈ cdBytes b off n, x < 256 := by
  intro x hx
  simp only [cdBytes, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact byteAt_lt b _

/-- `fromBytes'` of the reversed list is the big-endian value. -/
theorem fromBytes'_reverse (l : List UInt8) :
    fromBytes' l.reverse = beBytes (l.map UInt8.toNat) := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBytes', beBytes]
  | append_singleton xs x ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, fromBytes',
      List.map_append, List.map_singleton,
      Eip8282.Audit.Guarantees.PDrain1.Encode.beBytes_snoc, ih]
    simp only [UInt8.toFin_val]
    omega

/-- The bytes `readBytes b off 32` holds, as naturals. -/
theorem map_toNat_readBytes (b : ByteArray) (off : Nat) (hoff : off < 2 ^ 64) :
    (b.readBytes off 32).data.toList.map UInt8.toNat = cdBytes b off 32 := by
  unfold ByteArray.readBytes
  simp only [hoff, decide_true, Bool.true_and, show (32 : Nat) < 2 ^ 64 by decide, ite_true]
  have hreadE : b.copySlice off ByteArray.empty 0 32 = b.extract off (off + 32) := by
    unfold ByteArray.extract; rw [Nat.add_sub_cancel_left]
  rw [hreadE]
  have hsz : (b.extract off (off + 32)).size = min (off + 32) b.size - off :=
    ByteArray.size_extract
  have hsz_le : (b.extract off (off + 32)).size ≤ 32 := by omega
  have hz : ∀ u : USize, (ffi.ByteArray.zeroes u).data.toList = List.replicate u.toNat 0 := by
    intro u; simp [ffi.ByteArray.zeroes]
  have hpad : ((⟨32 - (b.extract off (off + 32)).size⟩ : USize)).toNat
      = 32 - (b.extract off (off + 32)).size :=
    ffi.ByteArray.toNat_usizeSub_of_le _ hsz_le
  rw [ByteArray.toList_data_append, hz]
  show List.map UInt8.toNat ((b.extract off (off + 32)).data.toList
    ++ List.replicate ((⟨32 - (b.extract off (off + 32)).size⟩ : USize)).toNat 0) = cdBytes b off 32
  rw [hpad, List.map_append, List.map_replicate]
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_append, List.length_map, List.length_replicate, Array.length_toList,
      ByteArray.size_data, cdBytes_length]
    omega
  · have hi : i < 32 := by simpa [cdBytes_length] using h₂
    simp only [cdBytes, List.getElem_map, List.getElem_range]
    by_cases hlt : i < (b.extract off (off + 32)).size
    · rw [List.getElem_append_left
        (by rw [List.length_map, Array.length_toList, ByteArray.size_data]; exact hlt)]
      simp only [List.getElem_map, Array.getElem_toList, ByteArray.data_extract,
        Array.getElem_extract]
      have hib : off + i < b.size := by omega
      unfold byteAt
      rw [if_pos hib]
      show (b.data[off + i]'_).toNat = (b.data[off + i]!).toNat
      rw [getElem!_pos b.data (off + i) (by simpa using hib)]
    · rw [List.getElem_append_right
        (by rw [List.length_map, Array.length_toList, ByteArray.size_data]; omega)]
      simp only [List.getElem_replicate]
      unfold byteAt
      rw [if_neg (by omega)]
      rfl

/-- **The value of a `CALLDATALOAD`.** -/
theorem toNat_calldataload (b : ByteArray) (off : Nat) (hoff : off < 2 ^ 64) :
    (uInt256OfByteArray (b.readBytes off 32)).toNat = beBytes (cdBytes b off 32) := by
  unfold uInt256OfByteArray
  rw [fromBytes'_reverse, map_toNat_readBytes b off hoff]
  apply toNat_ofNat_of_lt
  have := beBytes_lt _ (cdBytes_lt b off 32)
  rw [cdBytes_length] at this
  rw [size_eq]
  exact lt_of_lt_of_eq this (by norm_num)

/-- **The masked amount field.** `PUSH8 ~u64; AND` on the word loaded at `56`
leaves bytes `80..87`, big-endian: the model's `depositAmount`. -/
theorem toNat_amount (b : ByteArray) (hsize : 88 ≤ b.size) :
    (UInt256.land mask (uInt256OfByteArray (b.readBytes 56 32))).toNat
      = Eip8282.Audit.Model.depositAmount (bytes b) := by
  rw [toNat_land_mask, toNat_calldataload b 56 (by decide),
    show (32 : Nat) = 24 + 8 from rfl, cdBytes_add,
    Eip8282.Audit.Guarantees.PDrain1.Encode.beBytes_concat, cdBytes_length]
  have h8 : beBytes (cdBytes b (56 + 24) 8) < 256 ^ 8 := by
    have := beBytes_lt _ (cdBytes_lt b (56 + 24) 8)
    rwa [cdBytes_length] at this
  rw [show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h8]
  unfold Eip8282.Audit.Model.depositAmount
  rw [cdBytes_eq_drop_take b (56 + 24) 8 (by omega)]

/-- Every byte the observation lists is a byte. -/
theorem bytesOk_bytes (b : ByteArray) : Eip8282.Audit.Model.bytesOk (bytes b) = true := by
  unfold Eip8282.Audit.Model.bytesOk
  rw [List.all_eq_true]
  intro x hx
  simp only [Eip8282.Audit.XiTransport.bytes, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact decide_eq_true (b.get! i).toNat_lt

end Eip8282.Audit.EntryReach
