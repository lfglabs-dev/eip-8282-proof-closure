import Eip8282.Audit.Integrator.CommittedSystem

/-!
# Exit FIFO bytes from the actual drain buffer

The record specification concatenates the stored 20-byte source address and
48-byte public key. Storage indices remain word-exact; ordinary queue order
and the source-address invariant must be connected to append histories.
-/
namespace Eip8282.Audit.Integrator.ExitDrain

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Model (Byte toBeBytes)

set_option maxHeartbeats 1200000

/-- Independent 68-byte format of the three stored exit words. -/
def encodeWords (source first last : UInt256) : List Byte :=
  toBeBytes source.toNat 20 ++ toBeBytes first.toNat 32 ++
    (toBeBytes last.toNat 32).take 16

theorem encodeWords_length (source first last : UInt256) :
    (encodeWords source first last).length = 68 := by
  simp [encodeWords]

/-- Read the oldest indexed record using the pinned three-word layout. -/
def recordAt (st : EvmYul.State .EVM) (head : UInt256) (i : Nat) : List Byte :=
  let base := Exit.base (UInt256.ofNat i) head
  encodeWords (slotW st base) (slotW st (UInt256.ofNat 1 + base))
    (slotW st (UInt256.ofNat 2 + base))

def fifoBytes (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) : List Byte :=
  (List.range n).flatMap (recordAt st head)

theorem recordAt_length (st : EvmYul.State .EVM) (head : UInt256) (i : Nat) :
    (recordAt st head i).length = 68 := encodeWords_length _ _ _

theorem fifoBytes_succ (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) :
    fifoBytes st head (n + 1) = fifoBytes st head n ++ recordAt st head n := by
  simp [fifoBytes, List.range_succ]

theorem fifoBytes_length (st : EvmYul.State .EVM) (head : UInt256) (n : Nat) :
    (fifoBytes st head n).length = 68 * n := by
  induction n with
  | zero => simp [fifoBytes]
  | succ n ih => rw [fifoBytes_succ, List.length_append, ih, recordAt_length]; omega

theorem shifted_address (source : UInt256) (h : source.toNat < 2 ^ 160) :
    (UInt256.shiftLeft source (UInt256.ofNat 96)).toNat = source.toNat * 2 ^ 96 := by
  change (source.toNat <<< 96) % UInt256.size = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  have hm := Nat.mul_lt_mul_of_pos_right h (by decide : 0 < 2 ^ 96)
  exact hm.trans_eq (by decide : 2 ^ 160 * 2 ^ 96 = UInt256.size)

theorem bytes_mstore (mem : ByteArray) (off v : UInt256)
    (hle : off.toNat ≤ mem.size) (hcov : mem.size ≤ off.toNat + 32) :
    bytes (mstoreMem mem off v) = (bytes mem).take off.toNat ++ toBeBytes v.toNat 32 := by
  have h := memory_mstore_overwrite ({ (default : EvmYul.MachineState) with memory := mem })
    off v hle hcov
  change mstoreMem mem off v = _ at h
  rw [h, bytes_append, bytes_extract_zero, bytes_toByteArray]

theorem size_mstore (mem : ByteArray) (off v : UInt256)
    (hle : off.toNat ≤ mem.size) (hcov : mem.size ≤ off.toNat + 32) :
    (mstoreMem mem off v).size = off.toNat + 32 := by
  rw [← bytes_length, bytes_mstore mem off v hle hcov]
  simp only [List.length_append, List.length_take, bytes_length, length_toBeBytes]
  rw [Nat.min_eq_left hle]

/-- One actual drain iteration writes the independently specified record;
the extra 16 memory bytes are outside its return slice. -/
theorem writeItem_bytes (st : EvmYul.State .EVM) (mem : ByteArray) (b : Nat)
    (base : UInt256) (hb : b ≤ 1100) (hle : b ≤ mem.size) (hcov : mem.size ≤ b + 32)
    (hsrc : (slotW st base).toNat < 2 ^ 160) :
    bytes (Exit.writeItem st mem (UInt256.ofNat b) base) =
      (bytes mem).take b ++ encodeWords (slotW st base)
        (slotW st (UInt256.ofNat 1 + base)) (slotW st (UInt256.ofNat 2 + base)) ++
      (toBeBytes (slotW st (UInt256.ofNat 2 + base)).toNat 32).drop 16 := by
  have hsmall : 1200 < UInt256.size := by decide
  have h0 : (UInt256.ofNat b).toNat = b := toNat_ofNat_lit b (by omega)
  have h20 : (UInt256.ofNat 20 + UInt256.ofNat b).toNat = b + 20 := by
    rw [toNat_add_of_lt, h0]
    · change 20 + b = b + 20; omega
    change 20 + (UInt256.ofNat b).toNat < UInt256.size
    rw [h0]; omega
  have h52 : (UInt256.ofNat 32 + (UInt256.ofNat 20 + UInt256.ofNat b)).toNat = b + 52 := by
    rw [toNat_add_of_lt, h20]
    · change 32 + (b + 20) = b + 52; omega
    change 32 + (UInt256.ofNat 20 + UInt256.ofNat b).toNat < UInt256.size
    rw [h20]; omega
  let v0 := UInt256.shiftLeft (slotW st base) (UInt256.ofNat 96)
  let v1 := slotW st (UInt256.ofNat 1 + base)
  let v2 := slotW st (UInt256.ofNat 2 + base)
  let m1 := mstoreMem mem (UInt256.ofNat b) v0
  let m2 := mstoreMem m1 (UInt256.ofNat 20 + UInt256.ofNat b) v1
  have hm1 : m1.size = b + 32 := by
    rw [size_mstore mem _ v0 (by simpa [h0] using hle) (by simpa [h0] using hcov), h0]
  have hm2 : m2.size = b + 52 := by
    rw [size_mstore m1 _ v1 (by rw [h20, hm1]; omega) (by rw [h20, hm1]; omega), h20]
  have e0 := bytes_mstore mem (UInt256.ofNat b) v0
    (by simpa [h0] using hle) (by simpa [h0] using hcov)
  have e1 := bytes_mstore m1 (UInt256.ofNat 20 + UInt256.ofNat b) v1
    (by rw [h20, hm1]; omega) (by rw [h20, hm1]; omega)
  have e2 := bytes_mstore m2 (UInt256.ofNat 32 + (UInt256.ofNat 20 + UInt256.ofNat b)) v2
    (by rw [h52, hm2]) (by rw [h52, hm2]; omega)
  have ha : ((bytes mem).take b).length = b := by
    rw [List.length_take, bytes_length, Nat.min_eq_left hle]
  have eaddr : toBeBytes v0.toNat 32 = toBeBytes (slotW st base).toNat 20 ++ List.replicate 12 0 := by
    rw [show v0.toNat = (slotW st base).toNat * 2 ^ 96 from shifted_address _ hsrc]
    rw [show (2 : Nat)^96 = 256^12 by decide]
    exact toBeBytes_mul_pow _ 12 20
  change bytes (mstoreMem m2 _ v2) = _
  rw [e2, h52, e1, h20, e0, h0, eaddr]
  have ht1 : ((bytes mem).take b ++ (toBeBytes (slotW st base).toNat 20 ++ List.replicate 12 0)).take (b+20) =
      (bytes mem).take b ++ toBeBytes (slotW st base).toNat 20 := by
    rw [← List.append_assoc]
    exact List.take_left' (by simp [ha])
  rw [ht1, List.take_of_length_le (by simp [ha, v1])]
  simp only [encodeWords, ← List.append_assoc]
  rw [List.append_assoc ((bytes mem).take b ++ toBeBytes (slotW st base).toNat 20 ++ toBeBytes v1.toNat 32),
    List.take_append_drop]

private theorem mul_index (n : Nat) (hn : n ≤ 16) :
    UInt256.ofNat 68 * UInt256.ofNat n = UInt256.ofNat (68*n) := by
  have hs : 1200 < UInt256.size := by decide
  apply (eq_ofNat_iff_toNat _ _ (by omega)).mpr
  rw [EntryReach.toNat_mul_of_lt]
  · change 68 * (UInt256.ofNat n).toNat = 68*n
    rw [toNat_ofNat_lit n (by omega)]
  change 68 * (UInt256.ofNat n).toNat < UInt256.size
  rw [toNat_ofNat_lit n (by omega)]
  omega

/-- All actual drain iterations, including their overlapping memory writes,
produce the independent FIFO prefix. The source-width premise is explicit. -/
theorem drainMem_prefix (st : EvmYul.State .EVM) (head : UInt256) (n : Nat)
    (hn : n ≤ 16)
    (hsrc : ∀ i, i < n → (slotW st (Exit.base (UInt256.ofNat i) head)).toNat < 2^160) :
    (Exit.drainMem st head ByteArray.empty n).size = (if n = 0 then 0 else 68*n+16) ∧
    (bytes (Exit.drainMem st head ByteArray.empty n)).take (68*n) = fifoBytes st head n := by
  induction n with
  | zero => simp [Exit.drainMem, fifoBytes, bytes]
  | succ n ih =>
    obtain ⟨hsize, hprefix⟩ := ih (by omega) (fun i hi => hsrc i (by omega))
    let mem := Exit.drainMem st head ByteArray.empty n
    have hle : 68*n ≤ mem.size := by dsimp [mem]; rw [hsize]; split <;> omega
    have hcov : mem.size ≤ 68*n+32 := by dsimp [mem]; rw [hsize]; split <;> omega
    have hw := writeItem_bytes st mem (68*n) (Exit.base (UInt256.ofNat n) head)
      (by omega) hle hcov (hsrc n (by omega))
    rw [hprefix] at hw
    change bytes (Exit.writeItem st mem (UInt256.ofNat (68*n)) _) =
      fifoBytes st head n ++ recordAt st head n ++ _ at hw
    have hfull : bytes (Exit.drainMem st head ByteArray.empty (n+1)) =
        fifoBytes st head (n+1) ++
        (toBeBytes (slotW st (UInt256.ofNat 2 + Exit.base (UInt256.ofNat n) head)).toNat 32).drop 16 := by
      simpa only [Exit.drainMem, mul_index n (by omega), fifoBytes_succ] using hw
    constructor
    · rw [← bytes_length, hfull]
      simp only [List.length_append, fifoBytes_length, List.length_drop, length_toBeBytes]
      simp
    · rw [hfull]
      exact List.take_left' (fifoBytes_length st head (n+1))

/-- The returned slice excludes the final MSTORE overhang. -/
theorem drain_bytes (st : EvmYul.State .EVM) (head : UInt256) (n : Nat)
    (hn : n ≤ 16)
    (hsrc : ∀ i, i < n → (slotW st (Exit.base (UInt256.ofNat i) head)).toNat < 2^160) :
    bytes ((Exit.drainMem st head ByteArray.empty n).readWithPadding 0 (68*n)) =
      fifoBytes st head n := by
  obtain ⟨hs, hp⟩ := drainMem_prefix st head n hn hsrc
  by_cases hz : n = 0
  · subst n
    simp [bytes_readWithPadding_zero, fifoBytes]
  · rw [bytes_readWithPadding_prefix _ _ (by omega)
      (by omega) (by rw [hs]; simp [hz])]
    exact hp

/-- Exact FIFO identification of the buffer used by the actual exit endpoint. -/
theorem exitData_bytes (q : XiCall .exit)
    (hsrc : ∀ i, i < (Exit.drainWord q).toNat →
      (slotW (entrySt q) (Exit.base (UInt256.ofNat i) (Exit.headWord₀ q))).toNat < 2^160) :
    bytes (CommittedSystem.exitData q) =
      fifoBytes (entrySt q) (Exit.headWord₀ q) (Exit.drainWord q).toNat := by
  have hn := Exit.drainWord_le q
  have hmul : (UInt256.ofNat 68 * Exit.drainWord q).toNat = 68*(Exit.drainWord q).toNat := by
    rw [EntryReach.toNat_mul_of_lt]
    · rfl
    change 68 * (Exit.drainWord q).toNat < UInt256.size
    have : 1200 < UInt256.size := by decide
    omega
  unfold CommittedSystem.exitData
  rw [hmul, show Exit.mem₀ q = ByteArray.empty from memory_entry q]
  exact drain_bytes _ _ _ hn hsrc

open MessageCall CallBridge SystemSpec CommittedSystem
open Eip8282.Audit.Correspondence (runtimeCode)

/-- The actual complete SYSTEM call commits its control updates and returns
exactly the independent oldest-record concatenation, under the source-width
invariant. Word-indexed FIFO is not yet an initialized-history invariant. -/
theorem exit_system_fifo (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hsrc : ∀ i, i < (Exit.drainWord (codeCall c hcode steps)).toNat →
      (slotW (entrySt (codeCall c hcode steps))
        (Exit.base (UInt256.ofNat i) (Exit.headWord₀ (codeCall c hcode steps)))).toNat < 2^160) :
    let q := codeCall c hcode steps
    ∃ world created gas substate out,
      c.result = .ok (created, world, gas, substate, true, out) ∧
      bytes out = fifoBytes (entrySt q) (Exit.headWord₀ q) (Exit.drainWord q).toNat ∧
      ∀ k, worldSlot world c.target k =
        expectedSlot (entrySt q) (UInt256.ofNat 2) (Exit.drainWord q) (Exit.cdsizeWord q) k := by
  obtain ⟨world, created, gas, substate, hr, hs⟩ :=
    exit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  exact ⟨world, created, gas, substate, _, hr, exitData_bytes _ hsrc, hs⟩

#print axioms drain_bytes
#print axioms exit_system_fifo

end Eip8282.Audit.Integrator.ExitDrain
