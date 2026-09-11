import Eip8282.Audit.Integrator.ExitDrain

/-! Concrete deposit drain memory, including the descending MSTORE8 amount rewrite. -/
namespace Eip8282.Audit.Integrator.DepositDrain

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Model (Byte toBeBytes toLeBytes)

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

/-- Write the last byte first, exactly the order used by the pinned amount macro. -/
def descending (mem : ByteArray) (p : Nat) : List UInt256 → ByteArray
  | [] => mem
  | v :: vs => mstore8Mem (descending mem (p+1) vs) (UInt256.ofNat p) v

theorem bytes_mstore8 (mem : ByteArray) (p : Nat) (v : UInt256)
    (hp : p < UInt256.size) (hfit : p+1 ≤ mem.size) :
    bytes (mstore8Mem mem (UInt256.ofNat p) v) =
      (bytes mem).take p ++ (v.toNat % 256) :: (bytes mem).drop (p+1) := by
  have h := bytes_memory_mstore8 ({ (default : MachineState) with memory := mem })
    (UInt256.ofNat p) v (by simpa [toNat_ofNat_lit p hp] using hfit)
  rw [memory_mstore8_eq] at h
  simpa only [toNat_ofNat_lit p hp, mstore8Mem] using h

theorem size_mstore8 (mem : ByteArray) (p : Nat) (v : UInt256)
    (hp : p < UInt256.size) (hfit : p+1 ≤ mem.size) :
    (mstore8Mem mem (UInt256.ofNat p) v).size = mem.size := by
  rw [← bytes_length, bytes_mstore8 mem p v hp hfit]
  simp only [List.length_append, List.length_take, bytes_length, List.length_cons,
    List.length_drop]
  omega

/-- Descending writes have the same independently specified byte slice as the
little-endian list; the proof follows their actual order, not an assumed trace. -/
theorem descending_bytes (mem : ByteArray) (p : Nat) (vs : List UInt256)
    (hp : p+vs.length < UInt256.size) (hfit : p+vs.length ≤ mem.size) :
    (descending mem p vs).size = mem.size ∧
    bytes (descending mem p vs) =
      (bytes mem).take p ++ vs.map (fun (v : UInt256) => v.toNat % 256) ++
        (bytes mem).drop (p+vs.length) := by
  induction vs generalizing p with
  | nil => simp [descending]
  | cons v vs ih =>
    obtain ⟨hs, hb⟩ := ih (p+1) (by simp at hp ⊢; omega) (by simp at hfit ⊢; omega)
    have hf : p+1 ≤ (descending mem (p+1) vs).size := by rw [hs]; simp at hfit; omega
    have hp' : p < UInt256.size := by simp at hp; omega
    constructor
    · exact (size_mstore8 _ p v hp' hf).trans hs
    · rw [descending, bytes_mstore8 _ p v hp' hf, hb]
      have hl : ((bytes mem).take (p+1)).length = p+1 := by
        rw [List.length_take, bytes_length]; simp at hfit; omega
      have ht : (((bytes mem).take (p+1) ++ vs.map (fun (v : UInt256) => v.toNat % 256)) ++
          (bytes mem).drop (p+1+vs.length)).take p = (bytes mem).take p := by
        rw [List.take_append_of_le_length (by simp [hl]; omega),
          List.take_append_of_le_length (by omega), List.take_take]
        rw [Nat.min_eq_left (by omega)]
      have hd : (((bytes mem).take (p+1) ++ vs.map (fun (v : UInt256) => v.toNat % 256)) ++
          (bytes mem).drop (p+1+vs.length)).drop (p+1) =
          vs.map (fun (v : UInt256) => v.toNat % 256) ++ (bytes mem).drop (p+1+vs.length) := by
        rw [List.append_assoc]
        exact List.drop_left' hl
      rw [ht, hd]
      simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Actual eight operands, listed in increasing destination order. -/
def amountOperands (a : UInt256) : List UInt256 :=
  [a, UInt256.shiftRight a (UInt256.ofNat 8), UInt256.shiftRight a (UInt256.ofNat 16),
    UInt256.shiftRight a (UInt256.ofNat 24), UInt256.shiftRight a (UInt256.ofNat 32),
    UInt256.shiftRight a (UInt256.ofNat 40), UInt256.shiftRight a (UInt256.ofNat 48),
    UInt256.shiftRight a (UInt256.ofNat 56)]

theorem shr_nat (a : UInt256) (k : Nat) (hk : k < 256) :
    (UInt256.shiftRight a (UInt256.ofNat k)).toNat = a.toNat / 2^k := by
  have hks : k < UInt256.size := lt_trans hk (by decide)
  have hv : (UInt256.ofNat k).val.val = k := toNat_ofNat_lit k hks
  have hnot : ¬ (UInt256.ofNat k).val ≥ 256 := by
    change ¬ 256 ≤ (UInt256.ofNat k).val.val
    rw [hv]
    omega
  rw [UInt256.shiftRight, if_neg hnot]
  simp only [UInt256.toNat, Fin.shiftRight_val, hv, Nat.shiftRight_eq_div_pow]

theorem amountOperands_bytes (a : UInt256) :
    (amountOperands a).map (fun v => v.toNat % 256) = toLeBytes a.toNat 8 := by
  simp only [amountOperands, List.map_cons, List.map_nil]
  rw [shr_nat a 8 (by decide), shr_nat a 16 (by decide), shr_nat a 24 (by decide),
    shr_nat a 32 (by decide), shr_nat a 40 (by decide), shr_nat a 48 (by decide),
    shr_nat a 56 (by decide)]
  simp [toLeBytes, Nat.div_div_eq_div_mul]

/-- BE amount at bytes 16..23 of the third storage word, as a natural uint64. -/
def amount (w : UInt256) : Nat := (w.toNat / 2^64) % 2^64

theorem amount_word (w : UInt256) :
    (UInt256.land mask (UInt256.shiftRight w (UInt256.ofNat 64))).toNat = amount w := by
  rw [toNat_land_mask, shr_nat w 64 (by decide)]
  rfl


/-- The natural amount is decoded from exactly the eight BE storage bytes,
independently of the operational mask/shift calculation. -/
theorem amount_eq_beBytes (w : UInt256) :
    amount w = Eip8282.Audit.Model.beBytes ((toBeBytes w.toNat 32).drop 16 |>.take 8) := by
  let field := (toBeBytes w.toNat 32).drop 16 |>.take 8
  have hm : field = (List.range 8).map (fun t => (w.toNat / 256^(15-t)) % 256) := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < 8
    · change ((toBeBytes w.toNat 32).drop 16 |>.take 8)[t]? = _
      rw [List.getElem?_take_of_lt ht, List.getElem?_drop,
        Eip8282.Audit.Guarantees.PDrain1.Encode.toBeBytes_getElem? w.toNat 32 (16+t) (by omega)]
      rw [show 32-1-(16+t)=15-t from by omega]
      simp [List.getElem?_map, List.getElem?_range ht]
    · have hl : field.length = 8 := by simp [field]
      rw [List.getElem?_eq_none (by rw [hl]; omega),
        List.getElem?_eq_none (by simp; omega)]
  change amount w = Eip8282.Audit.Model.beBytes field
  rw [hm, Eip8282.Audit.Guarantees.PDrain1.Encode.beBytes_range_be w.toNat 8 15 (by decide)]
  rfl

/-- The output amount bytes are exactly the reverse of its stored BE field. -/
theorem amount_reversed (w : UInt256) :
    toLeBytes (amount w) 8 = ((toBeBytes w.toNat 32).drop 16 |>.take 8).reverse := by
  let field := (toBeBytes w.toNat 32).drop 16 |>.take 8
  have hf : field.length = 8 := by simp [field]
  have hb : ∀ x ∈ field, x < 256 := by
    intro x hx
    have hmem := List.mem_of_mem_drop (List.mem_of_mem_take hx)
    exact toLeBytes_lt w.toNat 32 x (List.mem_reverse.mp hmem)
  have h := toBeBytes_beBytes field hb
  rw [hf, ← amount_eq_beBytes] at h
  have hr := congrArg List.reverse h
  simpa only [field, Eip8282.Audit.Model.toBeBytes, List.reverse_reverse] using hr

/-- Independent physical record: big-endian storage bytes, with the eight-byte
amount field alone encoded little-endian. The sixth word contributes 24 bytes. -/
def encodeWords (w0 w1 w2 w3 w4 w5 : UInt256) : List Byte :=
  toBeBytes w0.toNat 32 ++ toBeBytes w1.toNat 32 ++
    (toBeBytes w2.toNat 32).take 16 ++ toLeBytes (amount w2) 8 ++
    (toBeBytes w2.toNat 32).drop 24 ++ toBeBytes w3.toNat 32 ++
    toBeBytes w4.toNat 32 ++ (toBeBytes w5.toNat 32).take 24

theorem encodeWords_length (w0 w1 w2 w3 w4 w5 : UInt256) :
    (encodeWords w0 w1 w2 w3 w4 w5).length = 184 := by
  simp [encodeWords]

/-- Natural-index spelling of the actual stores, retaining their exact order. -/
def writePacked (mem : ByteArray) (b : Nat) (w0 w1 w2 w3 w4 w5 : UInt256) : ByteArray :=
  let m := mstoreMem mem (UInt256.ofNat b) w0
  let m := mstoreMem m (UInt256.ofNat (b+32)) w1
  let m := mstoreMem m (UInt256.ofNat (b+64)) w2
  let m := descending m (b+80)
    (amountOperands (UInt256.land mask (UInt256.shiftRight w2 (UInt256.ofNat 64))))
  let m := mstoreMem m (UInt256.ofNat (b+96)) w3
  let m := mstoreMem m (UInt256.ofNat (b+128)) w4
  mstoreMem m (UInt256.ofNat (b+160)) w5

theorem writeItem_eq (st : EvmYul.State .EVM) (mem : ByteArray) (b : Nat) (base : UInt256) :
    Deposit.writeItem st mem (UInt256.ofNat b) base =
      writePacked mem b (slotW st base) (slotW st (UInt256.ofNat 1+base))
        (slotW st (UInt256.ofNat 2+base)) (slotW st (UInt256.ofNat 3+base))
        (slotW st (UInt256.ofNat 4+base)) (slotW st (UInt256.ofNat 5+base)) := by
  simp only [Deposit.writeItem, writePacked, amountOperands, descending, ofNat_add_ofNat,
    Nat.add_comm, Nat.add_left_comm]

/-- A word store with a natural offset below the word modulus. -/
theorem store_word (mem : ByteArray) (b : Nat) (w : UInt256)
    (hb : b < UInt256.size) (hle : b ≤ mem.size) (hcov : mem.size ≤ b+32) :
    (mstoreMem mem (UInt256.ofNat b) w).size = b+32 ∧
    bytes (mstoreMem mem (UInt256.ofNat b) w) =
      (bytes mem).take b ++ toBeBytes w.toNat 32 := by
  have h := toNat_ofNat_lit b hb
  constructor
  · simpa only [h] using (ExitDrain.size_mstore mem (UInt256.ofNat b) w
      (by simpa only [h] using hle) (by simpa only [h] using hcov))
  · simpa only [h] using (ExitDrain.bytes_mstore mem (UInt256.ofNat b) w
      (by simpa only [h] using hle) (by simpa only [h] using hcov))

/-- All concrete stores for one record, including the eight descending byte
writes, leave the record and an eight-byte overhang. No storage invariant is needed. -/
theorem writePacked_bytes (mem : ByteArray) (b : Nat) (w0 w1 w2 w3 w4 w5 : UInt256)
    (hb : b+200 < UInt256.size) (hle : b ≤ mem.size) (hcov : mem.size ≤ b+32) :
    (writePacked mem b w0 w1 w2 w3 w4 w5).size = b+192 ∧
    bytes (writePacked mem b w0 w1 w2 w3 w4 w5) =
      (bytes mem).take b ++ encodeWords w0 w1 w2 w3 w4 w5 ++
        (toBeBytes w5.toNat 32).drop 24 := by
  let m0 := mstoreMem mem (UInt256.ofNat b) w0
  let m1 := mstoreMem m0 (UInt256.ofNat (b+32)) w1
  let m2 := mstoreMem m1 (UInt256.ofNat (b+64)) w2
  let am := UInt256.land mask (UInt256.shiftRight w2 (UInt256.ofNat 64))
  let m3 := descending m2 (b+80) (amountOperands am)
  let m4 := mstoreMem m3 (UInt256.ofNat (b+96)) w3
  let m5 := mstoreMem m4 (UInt256.ofNat (b+128)) w4
  obtain ⟨s0, e0⟩ := store_word mem b w0 (by omega) hle hcov
  change m0.size = b+32 at s0
  obtain ⟨s1, e1⟩ := store_word m0 (b+32) w1 (by omega) (by omega) (by omega)
  change m1.size = b+64 at s1
  obtain ⟨s2, e2⟩ := store_word m1 (b+64) w2 (by omega) (by omega) (by omega)
  change m2.size = b+96 at s2
  have ha : ((bytes mem).take b).length = b := by
    rw [List.length_take, bytes_length, Nat.min_eq_left hle]
  have e02 : bytes m2 = (bytes mem).take b ++ toBeBytes w0.toNat 32 ++
      toBeBytes w1.toNat 32 ++ toBeBytes w2.toNat 32 := by
    rw [e2, e1, e0]
    rw [List.take_of_length_le (by simp [ha]), List.take_of_length_le (by simp [ha])]
  obtain ⟨s3, e3⟩ := descending_bytes m2 (b+80) (amountOperands am)
    (by simp [amountOperands]; omega) (by simp [amountOperands, s2])
  change m3.size = m2.size at s3
  rw [s2] at s3
  rw [amountOperands_bytes, amount_word] at e3
  change bytes m3 = _ at e3
  have hlen : (amountOperands am).length = 8 := rfl
  rw [hlen, e02] at e3
  let pre := (bytes mem).take b ++ toBeBytes w0.toNat 32 ++ toBeBytes w1.toNat 32
  have hpre : pre.length = b+64 := by simp [pre, ha]
  have ht : (pre ++ toBeBytes w2.toNat 32).take (b+80) =
      pre ++ (toBeBytes w2.toNat 32).take 16 := by
    rw [List.take_append, List.take_of_length_le (by rw [hpre]; omega), hpre]
    rw [show b+80-(b+64)=16 from by omega]
  have hd : (pre ++ toBeBytes w2.toNat 32).drop (b+80+8) =
      (toBeBytes w2.toNat 32).drop 24 := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hpre]; omega), List.nil_append, hpre]
    rw [show b+80+8-(b+64)=24 from by omega]
  change bytes m3 = (pre ++ toBeBytes w2.toNat 32).take (b+80) ++
    toLeBytes (amount w2) 8 ++ (pre ++ toBeBytes w2.toNat 32).drop (b+80+8) at e3
  rw [ht, hd] at e3
  obtain ⟨s4, e4⟩ := store_word m3 (b+96) w3 (by omega) (by omega) (by omega)
  change m4.size = b+128 at s4
  obtain ⟨s5, e5⟩ := store_word m4 (b+128) w4 (by omega) (by omega) (by omega)
  change m5.size = b+160 at s5
  obtain ⟨s6, e6⟩ := store_word m5 (b+160) w5 (by omega) (by omega) (by omega)
  constructor
  · exact s6
  · change bytes (mstoreMem m5 _ w5) = _
    rw [e6, List.take_of_length_le (by rw [bytes_length]; omega), e5,
      List.take_of_length_le (by rw [bytes_length]; omega), e4,
      List.take_of_length_le (by rw [bytes_length]; omega), e3]
    simp only [encodeWords, pre, List.append_assoc]
    rw [List.take_append_drop]


/-- Read the physical six-word deposit record at HEAD+i. Queue arithmetic is
still UInt256 arithmetic; initialized-history correspondence is separate. -/
def recordAt (st : EvmYul.State .EVM) (head : UInt256) (i : Nat) : List Byte :=
  let base := Deposit.base (UInt256.ofNat i) head
  encodeWords (slotW st base) (slotW st (UInt256.ofNat 1+base))
    (slotW st (UInt256.ofNat 2+base)) (slotW st (UInt256.ofNat 3+base))
    (slotW st (UInt256.ofNat 4+base)) (slotW st (UInt256.ofNat 5+base))

def fifoBytes (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) : List Byte :=
  (List.range n).flatMap (recordAt st head)

theorem recordAt_length (st : EvmYul.State .EVM) (head : UInt256) (i : Nat) :
    (recordAt st head i).length = 184 := encodeWords_length _ _ _ _ _ _

theorem fifoBytes_succ (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) :
    fifoBytes st head (n+1) = fifoBytes st head n ++ recordAt st head n := by
  simp [fifoBytes, List.range_succ]

theorem fifoBytes_length (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) :
    (fifoBytes st head n).length = 184*n := by
  induction n with
  | zero => simp [fifoBytes]
  | succ n ih => rw [fifoBytes_succ, List.length_append, ih, recordAt_length]; omega

private theorem mul_index (n : Nat) (hn : n ≤ 64) :
    UInt256.ofNat 184 * UInt256.ofNat n = UInt256.ofNat (184*n) := by
  have hs : 20000 < UInt256.size := by decide
  apply (eq_ofNat_iff_toNat _ _ (by omega)).mpr
  rw [EntryReach.toNat_mul_of_lt]
  · change 184 * (UInt256.ofNat n).toNat = 184*n
    rw [toNat_ofNat_lit n (by omega)]
  change 184 * (UInt256.ofNat n).toNat < UInt256.size
  rw [toNat_ofNat_lit n (by omega)]
  omega

/-- Every actual iteration preserves the completed prefix and leaves eight
extra bytes for the next iteration to overwrite or RETURN to exclude. -/
theorem drainMem_prefix (st : EvmYul.State .EVM) (head : UInt256) (n : Nat)
    (hn : n ≤ 64) :
    (Deposit.drainMem st head ByteArray.empty n).size = (if n=0 then 0 else 184*n+8) ∧
    (bytes (Deposit.drainMem st head ByteArray.empty n)).take (184*n) = fifoBytes st head n := by
  induction n with
  | zero => simp [Deposit.drainMem, fifoBytes, bytes]
  | succ n ih =>
    obtain ⟨hsize, hprefix⟩ := ih (by omega)
    let mem := Deposit.drainMem st head ByteArray.empty n
    let base := Deposit.base (UInt256.ofNat n) head
    have hle : 184*n ≤ mem.size := by dsimp [mem]; rw [hsize]; split <;> omega
    have hcov : mem.size ≤ 184*n+32 := by dsimp [mem]; rw [hsize]; split <;> omega
    have hmod : 184*n+200 < UInt256.size := by
      have : 20000 < UInt256.size := by decide
      omega
    obtain ⟨hs, hw⟩ := writePacked_bytes mem (184*n) (slotW st base)
      (slotW st (UInt256.ofNat 1+base)) (slotW st (UInt256.ofNat 2+base))
      (slotW st (UInt256.ofNat 3+base)) (slotW st (UInt256.ofNat 4+base))
      (slotW st (UInt256.ofNat 5+base)) hmod hle hcov
    rw [← writeItem_eq] at hs hw
    rw [hprefix] at hw
    have hfull : bytes (Deposit.drainMem st head ByteArray.empty (n+1)) =
        fifoBytes st head (n+1) ++ (toBeBytes (slotW st (UInt256.ofNat 5+base)).toNat 32).drop 24 := by
      simpa only [Deposit.drainMem, mul_index n (by omega), fifoBytes_succ, recordAt] using hw
    constructor
    · rw [← bytes_length, hfull]
      simp only [List.length_append, fifoBytes_length, List.length_drop, length_toBeBytes]
      simp
    · rw [hfull]
      exact List.take_left' (fifoBytes_length st head (n+1))

theorem drain_bytes (st : EvmYul.State .EVM) (head : UInt256) (n : Nat)
    (hn : n ≤ 64) :
    bytes ((Deposit.drainMem st head ByteArray.empty n).readWithPadding 0 (184*n)) =
      fifoBytes st head n := by
  obtain ⟨hs, hp⟩ := drainMem_prefix st head n hn
  by_cases hz : n=0
  · subst n; simp [bytes_readWithPadding_zero, fifoBytes]
  · rw [bytes_readWithPadding_prefix _ _ (by omega) (by omega) (by rw [hs]; simp [hz])]
    exact hp

theorem depositData_bytes (q : XiCall .deposit) :
    bytes (CommittedSystem.depositData q) =
      fifoBytes (entrySt q) (Deposit.headWord₀ q) (Deposit.drainWord q).toNat := by
  have hn := Deposit.drainWord_le q
  have hmul : (UInt256.ofNat 184 * Deposit.drainWord q).toNat = 184*(Deposit.drainWord q).toNat := by
    rw [EntryReach.toNat_mul_of_lt]
    · rfl
    change 184 * (Deposit.drainWord q).toNat < UInt256.size
    have : 20000 < UInt256.size := by decide
    omega
  unfold CommittedSystem.depositData
  rw [hmul, show Deposit.mem₀ q = ByteArray.empty from memory_entry q]
  exact drain_bytes _ _ _ hn

open MessageCall CallBridge SystemSpec CommittedSystem
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Actual Θ commits the direct storage postcondition and returns the exact
capped word-indexed deposit FIFO with little-endian amounts. No source-record
or encoding agreement is assumed; protocol-history arithmetic remains separate. -/
theorem deposit_system_fifo (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps))) :
    let q := codeCall c hcode steps
    ∃ world created gas substate out,
      c.result = .ok (created, world, gas, substate, true, out) ∧
      bytes out = fifoBytes (entrySt q) (Deposit.headWord₀ q) (Deposit.drainWord q).toNat ∧
      ∀ k, worldSlot world c.target k =
        expectedSlot (entrySt q) (UInt256.ofNat 8) (Deposit.drainWord q) (Deposit.cdsizeWord q) k := by
  obtain ⟨world, created, gas, substate, hr, hs⟩ :=
    deposit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  exact ⟨world, created, gas, substate, _, hr, depositData_bytes _, hs⟩

#print axioms amount_reversed
#print axioms descending_bytes
#print axioms writePacked_bytes
#print axioms deposit_system_fifo

end Eip8282.Audit.Integrator.DepositDrain
