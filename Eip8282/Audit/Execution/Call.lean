import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.Account
import EvmYul.State.ExecutionEnv
import EvmYul.Maps.AccountMap
import Eip8282.Audit.Bytecode
import EvmYul.EVM.GasConstants
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Execution.Types
import Std.Data.TreeMap.Lemmas
import EvmYul.EVM.Proof.Block
import EvmYul.EVM.Proof.MemoryStep

/-! Shared execution support, separated from historical model correspondence.
The sections retain public theorem names and isolate local proof settings. -/

section

/-! ## Context -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.EvmRunner; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.EvmRunner

open EvmYul

open EvmYul.EVM

open Eip8282.Audit.Bytecode

def toAddress (n : Nat) : AccountAddress := AccountAddress.ofNat n

def depositAddr : AccountAddress := toAddress depositAddress

def exitAddr : AccountAddress := toAddress exitAddress

/-- `SYSTEM_ADDR` of the pinned runtimes. The first four instructions of both
runtimes are `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`, so this
address is the sole key to the system subroutine. -/
def sysAddr : AccountAddress := toAddress systemAddress

abbrev RunResult :=
  Except EVM.ExecutionException
    (ExecutionResult
      (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))

end Eip8282.Audit.EvmRunner

end

section

/-! ## JumpTables -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.Step; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.Step

open EvmYul

open EvmYul.EVM

open EvmYul.Operation

open Eip8282.Audit.Bytecode

open Eip8282.Audit.Jumpdests

open GasConstants

set_option maxRecDepth 20000

theorem deposit_validJumps_eq_D_J :
    depositJumpdests = D_J depositRuntime ⟨0⟩ :=
  deposit_D_J.symm

theorem exit_validJumps_eq_D_J :
    exitJumpdests = D_J exitRuntime ⟨0⟩ :=
  exit_D_J.symm

end Eip8282.Audit.Step

end

section

/-! ## Runtime -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.Correspondence; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.Correspondence

open EvmYul (UInt256 Storage AccountAddress)

open EvmYul.Operation

open Eip8282.Audit.Bytecode

open Eip8282.Audit.Jumpdests

open Eip8282.Audit.Step

open Eip8282.Audit.Model (Kind)

open GasConstants

set_option maxRecDepth 20000

/-- Pinned runtime image. Not unfolded in theorems (`fromHex` of the full
hex is kernel-opaque); claim workers pass this to `EvmRunner`. -/
def runtimeCode : Kind → ByteArray
  | .deposit => depositRuntime
  | .exit => exitRuntime

def openingJumps : Kind → Array UInt256
  | .deposit => depositJumpdests
  | .exit => exitJumpdests

/-- The kind-indexed valid-jump table every CFG lemma steps against is the
JUMPDEST set `EvmYul.EVM.Ξ` itself derives from the pinned runtime image.
Kernel `decide` via `Jumpdests.deposit_D_J` / `exit_D_J`, so a `∀` stated
over `D_J (runtimeCode kind) ⟨0⟩` costs no `native_decide`. -/
theorem openingJumps_eq_D_J (kind : Kind) :
    openingJumps kind = EvmYul.EVM.D_J (runtimeCode kind) ⟨0⟩ := by
  cases kind
  · exact deposit_validJumps_eq_D_J
  · exact exit_validJumps_eq_D_J

end Eip8282.Audit.Correspondence

end

section

/-! ## CounterArithmetic -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.Guarantees.PControl1.Count; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.Guarantees.PControl1.Count

open Std

open EvmYul (UInt256 Storage)

open EvmYul.Operation

open Eip8282.Audit.Bytecode

open Eip8282.Audit.Jumpdests

open Eip8282.Audit.Step

open Eip8282.Audit.Correspondence

open Eip8282.Audit.Model (Kind)

open GasConstants

/-- Derived `Ord` is `(compare val).then eq`, which equals `compare val`. -/
theorem compare_val (a b : UInt256) :
    compare a b = compare a.val b.val := by
  cases a with
  | mk va =>
    cases b with
    | mk vb =>
      change (compare va vb).then Ordering.eq = compare va vb
      cases (compare va vb) <;> rfl

instance : OrientedOrd UInt256 where
  eq_swap {a b} := by
    rw [compare_val a b, compare_val b a]
    exact OrientedOrd.eq_swap (α := Fin UInt256.size)

instance : TransOrd UInt256 where
  isLE_trans {a b c} h₁ h₂ := by
    rw [compare_val a b] at h₁
    rw [compare_val b c] at h₂
    rw [compare_val a c]
    exact TransOrd.isLE_trans (α := Fin UInt256.size) h₁ h₂

instance : LawfulEqOrd UInt256 where
  eq_of_compare {a b} h := by
    have hval : compare a.val b.val = .eq := by
      rwa [← compare_val]
    exact congrArg UInt256.mk (LawfulEqOrd.eq_of_compare (α := Fin UInt256.size) hval)

end Eip8282.Audit.Guarantees.PControl1.Count

end

section

/-! ## Encoding -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.Guarantees.PDrain1.Encode; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.Guarantees.PDrain1.Encode

open EvmYul

open EvmYul.EVM

open EvmYul.Operation

open Eip8282.Audit.Bytecode

open Eip8282.Audit.Jumpdests

open Eip8282.Audit.Step

open Eip8282.Audit.Model

open Eip8282.Audit.Correspondence

open GasConstants

set_option maxRecDepth 20000

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

end Eip8282.Audit.Guarantees.PDrain1.Encode

end

section

/-! ## Support -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.XiTransport; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.XiTransport

open EvmYul EvmYul.EVM EvmYul.EVM.Proof

open Eip8282.Audit.Model

open Eip8282.Audit.Jumpdests

open Eip8282.Audit.Correspondence (runtimeCode)

def bytes (data : ByteArray) : List Nat :=
  (List.range data.size).map fun i => (data.get! i).toNat

def entryState
    (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : EVM.State :=
  { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-- The campaign's kernel-checked table, as the CFG parents step against it. -/
abbrev jumpdestsOf : Kind → Array UInt256 :=
  Eip8282.Audit.Correspondence.openingJumps

/-- The table `Ξ` derives from the code it is about to run is exactly the
kernel-checked table the CFG parents step against (`deposit_D_J` / `exit_D_J`,
both `decide +kernel` since EVMYulLean `0ff72b2`). No `native_decide`. -/
theorem Xi_validJumps_eq {kind : Kind} {I : ExecutionEnv .EVM}
    (hcode : I.code = runtimeCode kind) :
    D_J I.code ⟨0⟩ = jumpdestsOf kind := by
  rw [hcode]
  exact (Eip8282.Audit.Correspondence.openingJumps_eq_D_J kind).symm

/-- A complete `Ξ` message call into the pinned runtime for `kind`.

`code_pinned` is the only constraint: the code being executed is the pinned
image. Everything else — world, gas, substate, created accounts, block context,
calldata and value inside `env` — is universally quantified. -/
structure XiCall (kind : Kind) where
  fuel : Nat
  createdAccounts : Std.TreeSet AccountAddress compare
  genesisBlockHeader : BlockHeader
  blocks : ProcessedBlocks
  σ : AccountMap .EVM
  σ₀ : AccountMap .EVM
  gas : UInt256
  substate : Substate
  env : ExecutionEnv .EVM
  code_pinned : env.code = runtimeCode kind

namespace XiCall

variable {kind : Kind}

/-- The machine `Ξ` starts `X` from. -/
def entry (c : XiCall kind) : EVM.State :=
  entryState c.createdAccounts c.genesisBlockHeader c.blocks c.σ c.σ₀ c.gas
    c.substate c.env

/-- The complete message call. This is `EvmYul.EVM.Ξ`, the same entry point
`Eip8282.Audit.EvmRunner.run` uses for the kept kill-line traces. -/
def result (c : XiCall kind) :=
  Ξ (c.fuel + 1) c.createdAccounts c.genesisBlockHeader c.blocks c.σ c.σ₀ c.gas
    c.substate c.env

end XiCall

/-- The bytes `H` publishes at a halting opcode, as a function of the machine
rather than an existential: the requested memory slice on `RETURN` / `REVERT`,
nothing at all on `STOP` / `SELFDESTRUCT`. -/
def haltData (μ : MachineState) (op : Operation .EVM) : ByteArray :=
  if op ∈ [Operation.RETURN, Operation.REVERT] then μ.H_return else .empty

/-- At a halting opcode `H` is `some`, and what it publishes is `haltData`. This
is `H`'s definition read forwards; no run and no premise beyond `Halting`. -/
theorem H_eq_haltData {μ : MachineState} {op : Operation .EVM}
    (hop : Halting op = true) : H μ op = some (haltData μ op) := by
  by_cases h1 : op ∈ [Operation.RETURN, Operation.REVERT]
  · simp [H, haltData, h1]
  · have h2 : op ∈ [Operation.STOP, Operation.SELFDESTRUCT] := by
      simpa [Halting, h1] using hop
    simp [H, haltData, h1, h2]

/-- **The exit instruction halts — derived from the run.** A `RunUntil` against
the halting stop condition that stopped with fuel remaining records *why* it
stopped, and the only available reason is that the decoded opcode halts. -/
theorem exit_halting {kind : Kind} {c : XiCall kind} {rem : Nat}
    {trace : List Labelled} {exit : EVM.State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg)) :
    Halting op = true := by
  have h := hrun.stop_of_rem_pos (Nat.succ_ne_zero rem)
  rw [hdec] at h
  simpa [stopOrHalting] using h

/-- **`H` at the exit, with no premise at all.** The caller of every statement
below supplies the run; the halting data follows. -/
theorem exit_H {kind : Kind} {c : XiCall kind} {rem : Nat}
    {trace : List Labelled} {exit : EVM.State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
      trace (rem + 1) exit)
    (hdec : decodeAt exit = (op, arg)) (μ : MachineState) :
    H μ op = some (haltData μ op) :=
  H_eq_haltData (exit_halting hrun hdec)

/-- `zeroes` is an `@[extern] def`, not `opaque`, so the empty padding reduces. -/
theorem zeroes_zero : ffi.ByteArray.zeroes 0 = ByteArray.empty := rfl

/-- A zero-length read is empty regardless of source and offset: the unpadded
read is an empty `extract` and the padding is `zeroes 0`. -/
theorem readWithPadding_size_zero (source : ByteArray) (addr : Nat) :
    (ByteArray.readWithPadding source addr 0).size = 0 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp [zeroes_zero]

/-- ... hence it publishes no bytes. -/
theorem bytes_readWithPadding_zero (source : ByteArray) (addr : Nat) :
    bytes (source.readWithPadding addr 0) = [] := by
  simp [bytes, readWithPadding_size_zero]

/-- `bytes` enumerates a `ByteArray` index by index, so it is exactly as long. -/
theorem bytes_length (b : ByteArray) : (bytes b).length = b.size := by
  simp [bytes]

/-- `toLeBytes` produces exactly `w` bytes. -/
@[simp] theorem length_toLeBytes (n w : Nat) : (toLeBytes n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLeBytes, ih]

/-- **Every digit of the model's little-endian expansion, in closed form.** The
same statement EVMYulLean's `getElem_toLeBytesFixed` makes about its own encoder,
proved the same way; the two recursions differ only in landing in `UInt8` rather
than `Byte := Nat`. -/
theorem getElem_toLeBytes (n w i : Nat) (h : i < (toLeBytes n w).length) :
    (toLeBytes n w)[i] = n / 256 ^ i % 256 := by
  induction w generalizing n i with
  | zero => simp at h
  | succ w ih =>
    match i with
    | 0 => simp [toLeBytes]
    | i + 1 =>
      have h' : i < (toLeBytes (n / 256) w).length := by
        simp only [length_toLeBytes] at h ⊢; omega
      have : n / 256 / 256 ^ i = n / 256 ^ (i + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simpa [toLeBytes, this] using ih (n / 256) i h'

/-- **The model's big-endian encoder in the shape a `List ℕ` observation takes.**
Index `i` counts from the most significant end, so it names the `w - 1 - i`-th
base-256 digit. This is the right-hand side of
`UInt256.map_toNat_get!_toByteArray`, verbatim. -/
theorem toBeBytes_eq_map_range (n w : Nat) :
    toBeBytes n w = (List.range w).map (fun i => n / 256 ^ (w - 1 - i) % 256) := by
  refine List.ext_getElem (by simp [toBeBytes]) fun i h₁ _ => ?_
  have hi : i < w := by simpa [toBeBytes] using h₁
  simp only [List.getElem_map, List.getElem_range]
  show (toLeBytes n w).reverse[i]'(by simpa using hi) = _
  rw [List.getElem_reverse (by simp; omega), getElem_toLeBytes]
  simp only [length_toLeBytes]

/-- **The two encoders agree.** The bytes this file publishes for a stored EVM
word are the model's 32-byte big-endian encoding of that word's value.

This is the equation the campaign has been missing. `bytes` is how `observe`
reads return data; `toBeBytes` is how the abstract model writes it; and #9's
`UInt256.map_toNat_get!_toByteArray` — which reaches the base-256 digits through
`toBeBytesFixed`, never through the private `toBytes'` — is what makes them the
same list. -/
theorem bytes_toByteArray (v : UInt256) :
    bytes (UInt256.toByteArray v) = toBeBytes v.toNat 32 := by
  show (List.range (UInt256.toByteArray v).size).map
      (fun i => ((UInt256.toByteArray v).get! i).toNat) = _
  rw [toBeBytes_eq_map_range]
  exact EvmYul.UInt256.map_toNat_get!_toByteArray v

theorem bytes_eq_map_data (b : ByteArray) :
    bytes b = b.data.toList.map UInt8.toNat := by
  refine List.ext_getElem (by simp [bytes]) fun i h₁ h₂ => ?_
  have hi : i < b.size := by simpa [bytes] using h₁
  have hi' : i < b.data.size := by simpa [ByteArray.size_data] using hi
  simp only [bytes, List.getElem_map, List.getElem_range, ByteArray.get!,
    Array.getElem_toList]
  rw [getElem!_pos b.data i hi']

theorem bytes_append (a b : ByteArray) : bytes (a ++ b) = bytes a ++ bytes b := by
  simp [bytes_eq_map_data, ByteArray.data_append]

theorem bytes_extract_zero (b : ByteArray) (d : Nat) :
    bytes (b.extract 0 d) = (bytes b).take d := by
  rw [bytes_eq_map_data, bytes_eq_map_data, ← List.map_take]
  congr 1
  simp [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem bytes_readWithPadding_prefix (b : ByteArray) (L : Nat)
    (hpos : 0 < L) (h64 : L < 2 ^ 64) (hfit : L ≤ b.size) :
    bytes (b.readWithPadding 0 L) = (bytes b).take L := by
  rw [ByteArray.readWithPadding_eq_extract b 0 L hpos h64 (by omega), Nat.zero_add,
    bytes_extract_zero]

theorem memory_mstore_overwrite (μ : MachineState) (spos sval : UInt256)
    (hle : spos.toNat ≤ μ.memory.size) (hcov : μ.memory.size ≤ spos.toNat + 32) :
    (μ.mstore spos sval).memory = μ.memory.extract 0 spos.toNat ++ sval.toByteArray := by
  show ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32 = _
  rw [ByteArray.write_eq_of_grows _ _ _ _ (by norm_num)
      (EvmYul.UInt256.size_toByteArray sval) (by omega)
      (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)]
  ext1
  simp [ByteArray.data_append, ByteArray.data_extract,
    show spos.toNat - μ.memory.size = 0 from by omega]

theorem toBeBytes_succ (n w : Nat) :
    toBeBytes n (w + 1) = toBeBytes (n / 256) w ++ [n % 256] := by
  simp [toBeBytes, toLeBytes]

theorem toLeBytes_mul_pow (n k w : Nat) :
    toLeBytes (n * 256 ^ k) (k + w) = List.replicate k 0 ++ toLeBytes n w := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hmod : n * 256 ^ (k + 1) % 256 = 0 := by
      rw [pow_succ, ← Nat.mul_assoc]; simp
    have hdiv : n * 256 ^ (k + 1) / 256 = n * 256 ^ k := by
      rw [pow_succ, ← Nat.mul_assoc]; simp
    rw [show k + 1 + w = (k + w) + 1 from by omega, toLeBytes, hmod, hdiv, ih]
    simp [List.replicate_succ]

theorem toBeBytes_mul_pow (n k w : Nat) :
    toBeBytes (n * 256 ^ k) (k + w) = toBeBytes n w ++ List.replicate k 0 := by
  rw [toBeBytes, toLeBytes_mul_pow, List.reverse_append]
  simp [toBeBytes]

theorem beBytes_append_singleton (bs : List Byte) (b : Byte) :
    beBytes (bs ++ [b]) = beBytes bs * 256 + b := by
  simp [beBytes]

theorem toBeBytes_beBytes (bs : List Byte) (hok : ∀ b ∈ bs, b < 256) :
    toBeBytes (beBytes bs) bs.length = bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    have hb : b < 256 := hok b (by simp)
    have hdiv : (beBytes bs * 256 + b) / 256 = beBytes bs := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num : 0 < 256),
        Nat.div_eq_of_lt hb, Nat.zero_add]
    have hmod : (beBytes bs * 256 + b) % 256 = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    rw [List.length_append, List.length_cons, List.length_nil,
      show bs.length + (0 + 1) = bs.length + 1 from by omega, toBeBytes_succ,
      beBytes_append_singleton, hdiv, hmod, ih fun x hx => hok x (by simp [hx])]

@[simp] theorem length_toBeBytes (n w : Nat) : (toBeBytes n w).length = w := by
  simp [toBeBytes]

theorem memory_mstore8_eq (μ : MachineState) (spos sval : UInt256) :
    (μ.mstore8 spos sval).memory
      = ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1 := rfl

/-- **Read-over-`MSTORE8`.** One `MSTORE8` inside the already-written region
replaces exactly one byte and leaves every other byte alone. -/
theorem bytes_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    bytes (μ.mstore8 spos sval).memory
      = (bytes μ.memory).take spos.toNat
        ++ (sval.toNat % 256) :: (bytes μ.memory).drop (spos.toNat + 1) := by
  rw [memory_mstore8_eq,
    ByteArray.write_eq_of_fits ⟨#[UInt8.ofNat sval.toNat]⟩ μ.memory spos.toNat 1
      (by norm_num) (by rfl) hfit]
  rw [bytes_eq_map_data, bytes_eq_map_data]
  simp [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.map_take, List.map_drop]

theorem toLeBytes_lt (n w : Nat) : ∀ x ∈ toLeBytes n w, x < 256 := by
  induction w generalizing n with
  | zero => simp [toLeBytes]
  | succ w ih =>
    intro x hx
    rw [toLeBytes] at hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact Nat.mod_lt _ (by norm_num)
    · exact ih (n / 256) x h

section

set_option autoImplicit false

@[simp] theorem toNat_zero : (⟨0⟩ : UInt256).toNat = 0 := by
  show (0 : Fin UInt256.size).val = 0
  simp

/-- **An `XRuns` prefix extends a halting `RunUntil`.** Whatever the run did
before it arrived, none of those steps halted — that is what `XStepAt` carries —
so the whole thing is still a `RunUntil` against the halting stop condition. -/
theorem runUntil_of_xRuns {validJumps : Array UInt256} {fuel rem rem' : Nat}
    {trace₁ trace₂ : List Labelled} {pre mid post : EVM.State}
    (h₁ : XRuns validJumps fuel pre trace₁ rem mid)
    (h₂ : RunUntil (fun w => Halting w) validJumps rem mid trace₂ rem' post) :
    RunUntil (fun w => Halting w) validJumps fuel pre (trace₁ ++ trace₂) rem' post := by
  induction h₁ with
  | refl => simpa using h₂
  | cons hstep _ ih =>
      obtain ⟨_, _, _, hH⟩ := id hstep
      exact RunUntil.step (by simp [stopOrHalting, H_eq_none_iff.mp hH]) hstep (ih h₂)

end

section

set_option autoImplicit false

theorem ofNat_add_ofNat (m n : Nat) :
    UInt256.ofNat m + UInt256.ofNat n = UInt256.ofNat (m + n) := by
  have h : ((UInt256.ofNat m + UInt256.ofNat n).val : Fin UInt256.size)
      = (UInt256.ofNat (m + n)).val := by
    apply Fin.ext
    show (m % UInt256.size + n % UInt256.size) % UInt256.size = (m + n) % UInt256.size
    exact (Nat.add_mod m n UInt256.size).symm
  cases hx : UInt256.ofNat m + UInt256.ofNat n
  cases hy : UInt256.ofNat (m + n)
  simp_all

end

end Eip8282.Audit.XiTransport

end

section

/-! ## HaltWitness -/

/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.UniversalBoundary; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.UniversalBoundary

open EvmYul EvmYul.EVM EvmYul.EVM.Proof

open Eip8282.Audit.Model (Kind)

open Eip8282.Audit.XiTransport

/-- **A halting witness for a complete `Ξ` call.** The non-halting prefix runs
to `exit` with fuel to spare, `exit` decodes to `op`, `op` is charged, and it
steps to `post`.

This is the R2/R3/R4 run decomposition packaged as data so that it can be
quantified over. No theorem in this repository produces one for an arbitrary
admissible call; that is recorded separately by `TerminationClosure`. -/
structure XiHalts {kind : Kind} (c : XiCall kind) where
  /-- Fuel left over when the run stopped; positivity is what records *why*. -/
  rem : Nat
  gasCost : Nat
  trace : List Labelled
  exit : EVM.State
  mid : EVM.State
  post : EVM.State
  op : Operation .EVM
  arg : Option (UInt256 × Nat)
  run : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
    trace (rem + 1) exit
  decode : decodeAt exit = (op, arg)
  charge : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost)
  stepOk : StepOk rem gasCost (op, arg) mid post

end Eip8282.Audit.UniversalBoundary

end
