import Eip8282.Audit.WellFormed
import Eip8282.Audit.Step

/-!
D2 — FIFO drain (`accum_loop`): pointer algebra first, then cap immediates.

**Load-bearing `∀` (1)–(4).** Under `WellFormed`, queue length is `tail - head`.
The drain takes the oldest `n = min length (capOf kind)` records, with
`capOf .deposit = 64` and `capOf .exit = 16`. HEAD advances by `n`, or both
pointers reset to `0` on a full drain. That pointer update reconstructs
`Model.systemCall`'s `drop cap` leftover (and `take cap` is the returned
window). Opcode-at-PC pins the kill-line `PUSH1 64` / `PUSH1 16` clamp
immediates and the `GT` that implements `min`.

**Fragment (5).** `i` from `0` to `n` is the `accum_loop` counter: the
`EQ; PUSH update_head; JUMPI` at the top of the loop fires iff `i = n`.
The loop body (storage → return encoding) is D3; this module does not
expand it.

CFG here is opcode-at-PC on closed hex *windows* of the pinned runtimes —
the same slice `fromHex` style as F3. Windows start at the clamp `PUSH1`,
so local PC `0` is runtime `295` (deposit) / `236` (exit). Jump dests in
those windows are the *runtime* PCs (`begin_loop` `305`/`245`,
`update_head` `471`/`301`). Full `fromHex` of either runtime is
kernel-opaque; byte-at-offset of the whole image is the mutant module's
`native_decide` fact and is not repeated here.

No `sorry`. No `axiom`. No `native_decide`.
-/

namespace Eip8282.Audit.Guarantees.PDrain1.Fifo

open EvmYul
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Model
open Eip8282.Audit.Step

set_option maxRecDepth 20000

/-! ## Caps (both named) -/

@[simp] theorem capOf_deposit : capOf .deposit = 64 := rfl
@[simp] theorem capOf_exit : capOf .exit = 16 := rfl

@[simp] theorem capOf_deposit_eq_max : capOf .deposit = maxDepositPerBlock := rfl
@[simp] theorem capOf_exit_eq_max : capOf .exit = maxExitPerBlock := rfl

theorem maxDepositPerBlock_eq : maxDepositPerBlock = 64 := rfl
theorem maxExitPerBlock_eq : maxExitPerBlock = 16 := rfl

/-- Kill-line clamp immediates. Deposit `PUSH1 64` operand; exit `PUSH1 16`
operand. Comparison immediates at 296 / 237 are a different `PUSH1` and
are not the mutant. -/
def depositCapImmPc : Nat := 304
def exitCapImmPc : Nat := 244

theorem depositCapImmPc_eq : depositCapImmPc = 304 := rfl
theorem exitCapImmPc_eq : exitCapImmPc = 244 := rfl

/-! ## Named drain PCs (F1 tables) -/

theorem deposit_begin_loop_pc : Deposit.begin_loop = 305 := rfl
theorem deposit_accum_loop_pc : Deposit.accum_loop = 307 := rfl
theorem deposit_update_head_pc : Deposit.update_head = 471 := rfl
theorem deposit_reset_queue_pc : Deposit.reset_queue = 489 := rfl

theorem exit_begin_loop_pc : Exit.begin_loop = 245 := rfl
theorem exit_accum_loop_pc : Exit.accum_loop = 247 := rfl
theorem exit_update_head_pc : Exit.update_head = 301 := rfl
theorem exit_reset_queue_pc : Exit.reset_queue = 319 := rfl

/-! ## Pointer algebra (load-bearing `∀`) -/

/-- Live queue length under the packed-FIFO invariant. -/
def length (head tail : Nat) : Nat := tail - head

/-- Records the system path actually drains: `min(length, cap)`. -/
def drainCount (kind : Kind) (head tail : Nat) : Nat :=
  min (length head tail) (capOf kind)

/-- Post-drain `QUEUE_HEAD`. Full drain (every live record returned) zeroes
both pointers; otherwise HEAD advances by the clamped count. -/
def nextHead (kind : Kind) (head tail : Nat) : Nat :=
  if drainCount kind head tail = length head tail then 0
  else head + drainCount kind head tail

/-- Post-drain `QUEUE_TAIL`. Zeroed together with HEAD on a full drain;
unchanged on a partial drain. -/
def nextTail (kind : Kind) (head tail : Nat) : Nat :=
  if drainCount kind head tail = length head tail then 0 else tail

theorem length_of_le {head tail : Nat} (_hle : head ≤ tail) :
    length head tail = tail - head :=
  rfl

theorem drainCount_le_length (kind : Kind) (head tail : Nat) :
    drainCount kind head tail ≤ length head tail :=
  Nat.min_le_left _ _

theorem drainCount_le_cap (kind : Kind) (head tail : Nat) :
    drainCount kind head tail ≤ capOf kind :=
  Nat.min_le_right _ _

private theorem min_eq_left_iff {a b : Nat} : min a b = a ↔ a ≤ b := by
  constructor
  · intro h
    have : min a b ≤ b := Nat.min_le_right a b
    rwa [h] at this
  · intro h
    exact Nat.min_eq_left h

theorem drainCount_eq_length_iff (kind : Kind) (head tail : Nat) :
    drainCount kind head tail = length head tail ↔
      length head tail ≤ capOf kind :=
  min_eq_left_iff

theorem drainCount_eq_cap_of_lt (kind : Kind) {head tail : Nat}
    (h : capOf kind < length head tail) :
    drainCount kind head tail = capOf kind :=
  Nat.min_eq_right (Nat.le_of_lt h)

theorem head_add_drainCount_le_tail (kind : Kind) {head tail : Nat}
    (hle : head ≤ tail) :
    head + drainCount kind head tail ≤ tail := by
  have := drainCount_le_length kind head tail
  unfold length at *
  omega

theorem next_full (kind : Kind) {head tail : Nat}
    (hleCap : length head tail ≤ capOf kind) :
    nextHead kind head tail = 0 ∧ nextTail kind head tail = 0 := by
  unfold nextHead nextTail
  have hn : drainCount kind head tail = length head tail :=
    (drainCount_eq_length_iff kind head tail).mpr hleCap
  simp [hn]

/-- Partial drain: more live records than the cap. HEAD advances by the cap;
TAIL is unchanged. -/
theorem next_partial (kind : Kind) {head tail : Nat}
    (h : capOf kind < length head tail) :
    nextHead kind head tail = head + capOf kind ∧
      nextTail kind head tail = tail := by
  have hn : drainCount kind head tail = capOf kind :=
    drainCount_eq_cap_of_lt kind h
  have hne : drainCount kind head tail ≠ length head tail := by
    rw [hn]
    exact Nat.ne_of_lt h
  unfold nextHead nextTail
  split_ifs with hif
  · exact (hne hif).elim
  · exact ⟨hn ▸ rfl, rfl⟩

theorem next_partial_head_add (kind : Kind) {head tail : Nat}
    (h : capOf kind < length head tail) :
    nextHead kind head tail = head + drainCount kind head tail := by
  have := next_partial kind h
  have hn : drainCount kind head tail = capOf kind :=
    drainCount_eq_cap_of_lt kind h
  omega

/-- Full drain iff the live window fits in the per-block cap. Both pointers
go to `0`. -/
theorem next_full_iff (kind : Kind) {head tail : Nat} (_hle : head ≤ tail) :
    nextHead kind head tail = 0 ∧ nextTail kind head tail = 0 ↔
      length head tail ≤ capOf kind := by
  constructor
  · intro h
    by_contra hcap
    have hlt : capOf kind < length head tail := Nat.not_le.mp hcap
    have hh : nextHead kind head tail = head + capOf kind := (next_partial kind hlt).1
    have : head + capOf kind = 0 := by rw [← hh]; exact h.1
    have hz : capOf kind = 0 := by omega
    cases kind with
    | deposit => simp [capOf_deposit] at hz
    | exit => simp [capOf_exit] at hz
  · intro hleCap
    exact next_full kind hleCap

/-! ### WellFormed transport -/

theorem length_eq_queueOf {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    length (queueHead σ) (queueTail σ) = (queueOf kind σ).length := by
  rw [queueOf_length wf]
  rfl

theorem drainCount_eq_min {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    drainCount kind (queueHead σ) (queueTail σ) =
      min (queueOf kind σ).length (capOf kind) := by
  rw [drainCount, length_eq_queueOf wf]

theorem drainCount_eq_take_length {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    ((queueOf kind σ).take (capOf kind)).length =
      drainCount kind (queueHead σ) (queueTail σ) := by
  rw [List.length_take, drainCount_eq_min wf, Nat.min_comm]

theorem leftover_length {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    ((queueOf kind σ).drop (capOf kind)).length =
      (queueOf kind σ).length - drainCount kind (queueHead σ) (queueTail σ) := by
  rw [List.length_drop, drainCount_eq_min wf, Nat.min_comm]
  omega

theorem next_wellFormed {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    IsWellFormed kind
      (nextHead kind (queueHead σ) (queueTail σ))
      (nextTail kind (queueHead σ) (queueTail σ)) := by
  have hle := head_le_tail wf
  have tlt := tail_lt_2_64 wf
  have nb := item_base_no_wrap wf
  by_cases hcap : length (queueHead σ) (queueTail σ) ≤ capOf kind
  · have ⟨h0, t0⟩ := next_full kind hcap
    rw [h0, t0]
    exact empty_queue_pointers kind
  · have hlt : capOf kind < length (queueHead σ) (queueTail σ) := Nat.not_le.mp hcap
    have ⟨hh, ht⟩ := next_partial kind hlt
    rw [hh, ht]
    refine ⟨?_, tlt, nb⟩
    have hn : drainCount kind (queueHead σ) (queueTail σ) = capOf kind :=
      drainCount_eq_cap_of_lt kind hlt
    have := head_add_drainCount_le_tail kind hle
    simpa [hn] using this

/-! ### `queueFrom` — leftover window at the updated pointers -/

/-- Logical FIFO on an explicit `[head, tail)` window of packed items.
Agrees with `queueOf` on the stored pointers. -/
def queueFrom (kind : Kind) (σ : Storage) (head tail : Nat) : List Record :=
  if head ≤ tail then
    (List.range (tail - head)).map (fun i => decodeItem kind σ (head + i))
  else
    []

theorem queueOf_eq_queueFrom (kind : Kind) (σ : Storage) :
    queueOf kind σ = queueFrom kind σ (queueHead σ) (queueTail σ) :=
  rfl

private theorem take_map {α β} (f : α → β) : ∀ (n : Nat) (l : List α),
    (l.map f).take n = (l.take n).map f
  | 0, _ => by simp
  | _ + 1, [] => by simp
  | n + 1, a :: as => by
      change f a :: (as.map f).take n = f a :: (as.take n).map f
      rw [take_map f n as]

private theorem drop_map {α β} (f : α → β) : ∀ (n : Nat) (l : List α),
    (l.map f).drop n = (l.drop n).map f
  | 0, l => by simp
  | _ + 1, [] => by simp
  | n + 1, _ :: as => by
      change (as.map f).drop n = (as.drop n).map f
      exact drop_map f n as

private theorem range_succ_eq_map (m : Nat) :
    List.range (m + 1) = 0 :: (List.range m).map Nat.succ := by
  induction m with
  | zero =>
    rw [List.range_succ]
    simp
  | succ m ih =>
    rw [List.range_succ]
    conv_lhs => rw [ih]
    rw [List.cons_append]
    congr 1
    rw [List.range_succ, List.map_append]
    simp

private theorem take_range : ∀ (n m : Nat),
    (List.range m).take n = List.range (min n m)
  | _, 0 => by simp
  | 0, _m + 1 => by simp
  | n + 1, m + 1 => by
      have hmin : min (n + 1) (m + 1) = min n m + 1 := by omega
      rw [range_succ_eq_map, hmin, range_succ_eq_map]
      change 0 :: ((List.range m).map Nat.succ).take n =
        0 :: (List.range (min n m)).map Nat.succ
      rw [take_map, take_range n m]

private theorem drop_range : ∀ (n m : Nat),
    (List.range m).drop n = (List.range (m - n)).map (fun i => n + i)
  | 0, m => by
      show List.range m = (List.range m).map (fun i => 0 + i)
      refine (List.map_id (List.range m)).symm.trans ?_
      exact List.map_congr_left (fun i _ => (Nat.zero_add i).symm)
  | _n + 1, 0 => by simp
  | n + 1, m + 1 => by
      rw [range_succ_eq_map]
      simp only [List.drop]
      rw [drop_map, drop_range n m, List.map_map, Nat.succ_sub_succ]
      exact List.map_congr_left (fun i _ => by
        simp only [Function.comp, Nat.succ_eq_add_one]
        omega)

/-- Oldest `min(length, cap)` records: packed items `head .. head+n-1`. -/
theorem oldest_eq_take {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    (queueOf kind σ).take (capOf kind) =
      (List.range (drainCount kind (queueHead σ) (queueTail σ))).map
        (fun i => decodeItem kind σ (queueHead σ + i)) := by
  have hle := head_le_tail wf
  unfold queueOf
  simp [hle]
  rw [take_map, take_range]
  congr 1
  unfold drainCount length
  rw [Nat.min_comm]

/-- Leftover after the drain: packed items `head+n .. tail-1`, or `[]` on a
full drain. Matches `queueFrom` at the updated pointers. -/
theorem leftover_eq_queueFrom {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    queueFrom kind σ
        (nextHead kind (queueHead σ) (queueTail σ))
        (nextTail kind (queueHead σ) (queueTail σ)) =
      (queueOf kind σ).drop (capOf kind) := by
  have hle := head_le_tail wf
  unfold queueOf
  simp only [hle, ite_true]
  by_cases hcap : length (queueHead σ) (queueTail σ) ≤ capOf kind
  · have ⟨h0, t0⟩ := next_full kind hcap
    rw [h0, t0]
    simp only [queueFrom, Nat.zero_le, ite_true, Nat.sub_self, List.range_zero,
      List.map_nil]
    refine Eq.symm (List.drop_eq_nil_of_le ?_)
    simp only [List.length_map, List.length_range]
    simpa [length] using hcap
  · have hlt : capOf kind < length (queueHead σ) (queueTail σ) :=
      Nat.not_le.mp hcap
    have ⟨hh, ht⟩ := next_partial kind hlt
    have hn : drainCount kind (queueHead σ) (queueTail σ) = capOf kind :=
      drainCount_eq_cap_of_lt kind hlt
    have hle2 : queueHead σ + capOf kind ≤ queueTail σ := by
      have := head_add_drainCount_le_tail kind hle
      simpa [hn] using this
    rw [hh, ht]
    unfold queueFrom
    simp only [hle2, ite_true]
    rw [Nat.sub_add_eq, drop_map, drop_range, List.map_map]
    refine List.map_congr_left ?_
    intro i _hi
    simp only [Function.comp]
    rw [Nat.add_assoc]

/-! ### Match `Model.systemCall` (`drop cap` / `take cap`) -/

theorem systemCall_queue (s : State) (b : Bool) :
    (systemCall s b).state.queue = s.queue.drop (capOf s.kind) :=
  rfl

theorem systemCall_return_take (s : State) (b : Bool) :
    systemCall s b =
      .success (systemCall s b).state
        (concatReturned (s.queue.take (capOf s.kind))) := by
  unfold systemCall
  simp

/-- `drop cap` length equals leftover under the pointer update. Does not
unfold `encodeReturned` (D3). -/
theorem systemCall_leftover_of_toModel {kind : Kind} {σ : Storage}
    (bal : Wei) (b : Bool) (wf : WellFormed kind σ) :
    (systemCall (toModel kind σ bal) b).state.queue =
      queueFrom kind σ
        (nextHead kind (queueHead σ) (queueTail σ))
        (nextTail kind (queueHead σ) (queueTail σ)) := by
  rw [systemCall_queue, toModel_queue]
  exact (leftover_eq_queueFrom wf).symm

theorem systemCall_take_of_toModel {kind : Kind} {σ : Storage}
    (bal : Wei) (_b : Bool) (wf : WellFormed kind σ) :
    (toModel kind σ bal).queue.take (capOf kind) =
      (List.range (drainCount kind (queueHead σ) (queueTail σ))).map
        (fun i => decodeItem kind σ (queueHead σ + i)) := by
  rw [toModel_queue]
  simpa using oldest_eq_take wf

theorem systemCall_full_drain {kind : Kind} {σ : Storage}
    (bal : Wei) (b : Bool) (wf : WellFormed kind σ)
    (h : (queueOf kind σ).length ≤ capOf kind) :
    (systemCall (toModel kind σ bal) b).state.queue = [] ∧
      nextHead kind (queueHead σ) (queueTail σ) = 0 ∧
      nextTail kind (queueHead σ) (queueTail σ) = 0 := by
  have hlen := length_eq_queueOf wf
  have hleCap : length (queueHead σ) (queueTail σ) ≤ capOf kind := by
    rwa [hlen]
  refine ⟨?_, next_full kind hleCap⟩
  rw [systemCall_queue, toModel_queue]
  exact List.drop_eq_nil_of_le h

theorem systemCall_partial_drain {kind : Kind} {σ : Storage}
    (bal : Wei) (b : Bool) (wf : WellFormed kind σ)
    (h : capOf kind < (queueOf kind σ).length) :
    nextHead kind (queueHead σ) (queueTail σ) =
        queueHead σ + capOf kind ∧
      nextTail kind (queueHead σ) (queueTail σ) = queueTail σ ∧
      (systemCall (toModel kind σ bal) b).state.queue.length =
        (queueOf kind σ).length - capOf kind := by
  have hlen := length_eq_queueOf wf
  have hlt : capOf kind < length (queueHead σ) (queueTail σ) := by
    rwa [hlen]
  have ⟨hh, ht⟩ := next_partial kind hlt
  refine ⟨hh, ht, ?_⟩
  rw [systemCall_queue, toModel_queue, List.length_drop, toModel_kind]

/-! ## CFG: clamp `GT` / `PUSH1 cap` (kill-line bytes)

Windows are the pinned hex slices that start at the *comparison* `PUSH1`
of `MAX_PER_BLOCK`. Local PC `0` is runtime `295` (deposit) / `236` (exit).
The clamp immediate — the kill-line byte — is the second `PUSH1` operand
in each window (deposit local `9` = runtime `304`; exit local `8` = `244`).
-/

/-- Deposit bytes `[295, 315)`: `PUSH1 64; GT; PUSH2 begin_loop; JUMPI;
POP; PUSH1 64; JUMPDEST begin_loop; PUSH0; JUMPDEST accum_loop;
DUP2; DUP2; EQ; PUSH2 update_head; JUMPI`. -/
def depositClampHex : String :=
  "604011610131575060405b5f5b8181146101d757"

def depositClampWindow : ByteArray := fromHex depositClampHex

/-- Runtime offset of local PC `0` in `depositClampWindow`. -/
def depositClampBase : Nat := 295

/-- Exit bytes `[236, 255)`: `PUSH1 16; GT; PUSH1 begin_loop; JUMPI;
POP; PUSH1 16; JUMPDEST begin_loop; PUSH0; JUMPDEST accum_loop;
DUP2; DUP2; EQ; PUSH2 update_head; JUMPI`. -/
def exitClampHex : String :=
  "60101160f5575060105b5f5b81811461012d57"

def exitClampWindow : ByteArray := fromHex exitClampHex

def exitClampBase : Nat := 236

theorem depositClampBase_add_imm : depositClampBase + 9 = depositCapImmPc :=
  rfl

theorem exitClampBase_add_imm : exitClampBase + 8 = exitCapImmPc :=
  rfl

theorem deposit_begin_loop_local : depositClampBase + 10 = Deposit.begin_loop :=
  rfl

theorem deposit_accum_loop_local : depositClampBase + 12 = Deposit.accum_loop :=
  rfl

theorem exit_begin_loop_local : exitClampBase + 9 = Exit.begin_loop :=
  rfl

theorem exit_accum_loop_local : exitClampBase + 11 = Exit.accum_loop :=
  rfl

/-! ### Deposit opcode-at-PC (closed 20-byte window) -/

theorem deposit_opcode_cmp_PUSH1 :
    opcodeAt depositClampWindow 0 =
      some (.PUSH1, some (UInt256.ofNat 64, 1)) :=
  rfl

theorem deposit_opcode_GT :
    opcodeAt depositClampWindow 2 = some (.GT, none) :=
  rfl

theorem deposit_opcode_push_begin_loop :
    opcodeAt depositClampWindow 3 =
      some (.PUSH2, some (UInt256.ofNat Deposit.begin_loop, 2)) :=
  rfl

theorem deposit_opcode_clamp_JUMPI :
    opcodeAt depositClampWindow 6 = some (.JUMPI, none) :=
  rfl

theorem deposit_opcode_POP :
    opcodeAt depositClampWindow 7 = some (.POP, none) :=
  rfl

/-- Kill-line `PUSH1 64` at runtime 303; immediate sits at 304. -/
theorem deposit_opcode_clamp_PUSH1 :
    opcodeAt depositClampWindow 8 =
      some (.PUSH1, some (UInt256.ofNat 64, 1)) :=
  rfl

theorem deposit_opcode_begin_loop_JUMPDEST :
    opcodeAt depositClampWindow 10 = some (.JUMPDEST, none) :=
  rfl

theorem deposit_opcode_PUSH0 :
    opcodeAt depositClampWindow 11 = some (.PUSH0, none) :=
  rfl

theorem deposit_opcode_accum_loop_JUMPDEST :
    opcodeAt depositClampWindow 12 = some (.JUMPDEST, none) :=
  rfl

theorem deposit_opcode_loop_DUP2 :
    opcodeAt depositClampWindow 13 = some (.DUP2, none) :=
  rfl

theorem deposit_opcode_loop_DUP2' :
    opcodeAt depositClampWindow 14 = some (.DUP2, none) :=
  rfl

theorem deposit_opcode_loop_EQ :
    opcodeAt depositClampWindow 15 = some (.EQ, none) :=
  rfl

theorem deposit_opcode_push_update_head :
    opcodeAt depositClampWindow 16 =
      some (.PUSH2, some (UInt256.ofNat Deposit.update_head, 2)) :=
  rfl

theorem deposit_opcode_loop_JUMPI :
    opcodeAt depositClampWindow 19 = some (.JUMPI, none) :=
  rfl

/-! ### Exit opcode-at-PC (closed 19-byte window) -/

theorem exit_opcode_cmp_PUSH1 :
    opcodeAt exitClampWindow 0 =
      some (.PUSH1, some (UInt256.ofNat 16, 1)) :=
  rfl

theorem exit_opcode_GT :
    opcodeAt exitClampWindow 2 = some (.GT, none) :=
  rfl

theorem exit_opcode_push_begin_loop :
    opcodeAt exitClampWindow 3 =
      some (.PUSH1, some (UInt256.ofNat Exit.begin_loop, 1)) :=
  rfl

theorem exit_opcode_clamp_JUMPI :
    opcodeAt exitClampWindow 5 = some (.JUMPI, none) :=
  rfl

theorem exit_opcode_POP :
    opcodeAt exitClampWindow 6 = some (.POP, none) :=
  rfl

/-- Kill-line `PUSH1 16` at runtime 243; immediate sits at 244. -/
theorem exit_opcode_clamp_PUSH1 :
    opcodeAt exitClampWindow 7 =
      some (.PUSH1, some (UInt256.ofNat 16, 1)) :=
  rfl

theorem exit_opcode_begin_loop_JUMPDEST :
    opcodeAt exitClampWindow 9 = some (.JUMPDEST, none) :=
  rfl

theorem exit_opcode_PUSH0 :
    opcodeAt exitClampWindow 10 = some (.PUSH0, none) :=
  rfl

theorem exit_opcode_accum_loop_JUMPDEST :
    opcodeAt exitClampWindow 11 = some (.JUMPDEST, none) :=
  rfl

theorem exit_opcode_loop_DUP2 :
    opcodeAt exitClampWindow 12 = some (.DUP2, none) :=
  rfl

theorem exit_opcode_loop_DUP2' :
    opcodeAt exitClampWindow 13 = some (.DUP2, none) :=
  rfl

theorem exit_opcode_loop_EQ :
    opcodeAt exitClampWindow 14 = some (.EQ, none) :=
  rfl

theorem exit_opcode_push_update_head :
    opcodeAt exitClampWindow 15 =
      some (.PUSH2, some (UInt256.ofNat Exit.update_head, 2)) :=
  rfl

theorem exit_opcode_loop_JUMPI :
    opcodeAt exitClampWindow 18 = some (.JUMPI, none) :=
  rfl

/-- Both kill-line clamp `PUSH1`s, both `GT`s, both `begin_loop` dests. -/
theorem both_caps_pinned :
    opcodeAt depositClampWindow 8 =
        some (.PUSH1, some (UInt256.ofNat (capOf .deposit), 1)) ∧
      opcodeAt exitClampWindow 7 =
        some (.PUSH1, some (UInt256.ofNat (capOf .exit), 1)) ∧
      opcodeAt depositClampWindow 0 =
        some (.PUSH1, some (UInt256.ofNat (capOf .deposit), 1)) ∧
      opcodeAt exitClampWindow 0 =
        some (.PUSH1, some (UInt256.ofNat (capOf .exit), 1)) ∧
      opcodeAt depositClampWindow 2 = some (.GT, none) ∧
      opcodeAt exitClampWindow 2 = some (.GT, none) ∧
      opcodeAt depositClampWindow 3 =
        some (.PUSH2, some (UInt256.ofNat Deposit.begin_loop, 2)) ∧
      opcodeAt exitClampWindow 3 =
        some (.PUSH1, some (UInt256.ofNat Exit.begin_loop, 1)) :=
  ⟨deposit_opcode_clamp_PUSH1, exit_opcode_clamp_PUSH1,
    deposit_opcode_cmp_PUSH1, exit_opcode_cmp_PUSH1,
    deposit_opcode_GT, exit_opcode_GT,
    deposit_opcode_push_begin_loop, exit_opcode_push_begin_loop⟩

/-! ### Clamp `GT` implements `min` (symbolic, any length) -/

theorem toNat_ofNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size :=
  rfl

theorem ofNat_eq_of_lt {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem ofNat_inj {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have := congrArg UInt256.toNat h
  rw [ofNat_eq_of_lt ha, ofNat_eq_of_lt hb] at this
  exact this

private theorem ofNat_zero_ne_one :
    UInt256.ofNat 0 ≠ UInt256.ofNat 1 := by
  intro h
  have := ofNat_inj (by decide) (by decide) h
  cases this

theorem gt_eq_one_iff (a b : UInt256) :
    UInt256.gt a b = UInt256.ofNat 1 ↔ a > b := by
  simp only [UInt256.gt, UInt256.fromBool, Bool.toUInt256]
  by_cases h : a > b
  · simp [h]
  · simp [h]
    intro heq
    exact (ofNat_zero_ne_one heq).elim

theorem eq_eq_one_iff (a b : UInt256) :
    UInt256.eq a b = UInt256.ofNat 1 ↔ a = b := by
  simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256]
  by_cases h : a = b
  · simp [h]
  · simp [h]
    intro heq
    exact (ofNat_zero_ne_one heq).elim

theorem ofNat_lt_iff {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) :
    UInt256.ofNat a > UInt256.ofNat b ↔ a > b := by
  constructor
  · intro h
    have ha' := ofNat_eq_of_lt ha
    have hb' := ofNat_eq_of_lt hb
    have : (UInt256.ofNat b).toNat < (UInt256.ofNat a).toNat := h
    rw [ha', hb'] at this
    exact this
  · intro h
    have ha' := ofNat_eq_of_lt ha
    have hb' := ofNat_eq_of_lt hb
    show (UInt256.ofNat b).toNat < (UInt256.ofNat a).toNat
    rw [ha', hb']
    exact h

/-- Assembly `GT` of `cap` vs live length: jump to `begin_loop` keeping
`length` iff `cap > length`; else `POP; PUSH cap`. That is `min`. -/
def clampCount (cap len : Nat) : Nat :=
  if cap > len then len else cap

theorem clampCount_eq_min (cap len : Nat) :
    clampCount cap len = min len cap := by
  unfold clampCount
  split_ifs with h
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · exact (Nat.min_eq_right (Nat.le_of_not_gt h)).symm

theorem drainCount_eq_clamp (kind : Kind) (head tail : Nat) :
    drainCount kind head tail =
      clampCount (capOf kind) (length head tail) := by
  rw [drainCount, clampCount_eq_min]

/-- `GT` of the named cap against a well-formed length is `1` iff the
undercap branch is taken. Length and cap both sit far below `2^256`. -/
theorem gt_cap_length {kind : Kind} {head tail : Nat}
    (tlt : tail < 2 ^ 64) (_hle : head ≤ tail) :
    UInt256.gt (UInt256.ofNat (capOf kind)) (UInt256.ofNat (length head tail)) =
        UInt256.ofNat 1 ↔
      capOf kind > length head tail := by
  have hlen : length head tail < UInt256.size := by
    unfold length
    have : tail - head ≤ tail := Nat.sub_le _ _
    have : tail < UInt256.size := Nat.lt_trans tlt (by decide)
    omega
  have hcap : capOf kind < UInt256.size := by
    cases kind <;> decide
  rw [gt_eq_one_iff, ofNat_lt_iff hcap hlen]

theorem clamp_gt_branch {kind : Kind} {head tail : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail) :
    (UInt256.gt (UInt256.ofNat (capOf kind))
        (UInt256.ofNat (length head tail)) = UInt256.ofNat 1 →
      drainCount kind head tail = length head tail) ∧
      (UInt256.gt (UInt256.ofNat (capOf kind))
        (UInt256.ofNat (length head tail)) = UInt256.ofNat 0 →
      drainCount kind head tail = capOf kind) := by
  have hiff := gt_cap_length (kind := kind) tlt hle
  constructor
  · intro hgt
    have : capOf kind > length head tail := hiff.mp hgt
    exact (drainCount_eq_length_iff kind head tail).mpr (Nat.le_of_lt this)
  · intro hgt
    have hne : ¬ capOf kind > length head tail := by
      intro ht
      have : UInt256.gt (UInt256.ofNat (capOf kind))
          (UInt256.ofNat (length head tail)) = UInt256.ofNat 1 := hiff.mpr ht
      rw [this] at hgt
      exact ofNat_zero_ne_one hgt.symm
    have : capOf kind ≤ length head tail := Nat.le_of_not_gt hne
    unfold drainCount
    exact Nat.min_eq_right this

/-! ## Loop-counter fragment (5)

At `accum_loop` the stack is `[i, n, head, tail]`. The body is D3 encode
and is not unfolded. What this module closes: the `EQ` of `i` against `n`
is the loop-exit condition, and the `JUMPI` dest is `update_head`.
Counter `i` starts at `0` (`PUSH0` after `begin_loop`) and would increment
by `1` at the unexpanded body tail.
-/

theorem loop_eq_iff {i n : Nat}
    (hi : i < UInt256.size) (hn : n < UInt256.size) :
    UInt256.eq (UInt256.ofNat i) (UInt256.ofNat n) = UInt256.ofNat 1 ↔
      i = n := by
  rw [eq_eq_one_iff]
  constructor
  · intro h
    exact ofNat_inj hi hn h
  · intro h
    rw [h]

/-- Under `WellFormed`, every loop index `i ≤ n` fits in `UInt256`. -/
theorem drainCount_lt_size {kind : Kind} {head tail : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail) :
    drainCount kind head tail < UInt256.size := by
  have := drainCount_le_length kind head tail
  unfold length at *
  have : tail < UInt256.size := Nat.lt_trans tlt (by decide)
  omega

theorem loop_index_lt_size {kind : Kind} {head tail i : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail)
    (hi : i ≤ drainCount kind head tail) :
    i < UInt256.size :=
  Nat.lt_of_le_of_lt hi (drainCount_lt_size tlt hle)

/-- Exit the drain loop iff the counter has reached the clamped count.
Does not claim the body ran; this is the `JUMPI @update_head` condition. -/
theorem loop_exit_iff {kind : Kind} {head tail i : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail)
    (hi : i ≤ drainCount kind head tail) :
    UInt256.eq (UInt256.ofNat i)
        (UInt256.ofNat (drainCount kind head tail)) = UInt256.ofNat 1 ↔
      i = drainCount kind head tail :=
  loop_eq_iff (loop_index_lt_size tlt hle hi) (drainCount_lt_size tlt hle)

theorem loop_continues {kind : Kind} {head tail i : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail)
    (hi : i < drainCount kind head tail) :
    UInt256.eq (UInt256.ofNat i)
        (UInt256.ofNat (drainCount kind head tail)) = UInt256.ofNat 0 := by
  have hle' : i ≤ drainCount kind head tail := Nat.le_of_lt hi
  have hiff := loop_exit_iff (kind := kind) tlt hle hle'
  by_cases heq : i = drainCount kind head tail
  · omega
  · have : UInt256.eq (UInt256.ofNat i)
        (UInt256.ofNat (drainCount kind head tail)) ≠ UInt256.ofNat 1 :=
      fun h => heq (hiff.mp h)
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256] at this ⊢
    split_ifs at this ⊢ with h
    · exact (this rfl).elim
    · rfl

theorem loop_done {kind : Kind} {head tail : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail) :
    UInt256.eq (UInt256.ofNat (drainCount kind head tail))
        (UInt256.ofNat (drainCount kind head tail)) = UInt256.ofNat 1 :=
  (loop_exit_iff (kind := kind) (i := drainCount kind head tail) tlt hle
      (Nat.le_refl _)).mpr rfl

/-- `i = 0` is the `PUSH0` that follows `begin_loop`. -/
theorem loop_starts_at_zero :
    opcodeAt depositClampWindow 11 = some (.PUSH0, none) ∧
      opcodeAt exitClampWindow 10 = some (.PUSH0, none) :=
  ⟨deposit_opcode_PUSH0, exit_opcode_PUSH0⟩

/-- `JUMPI` dest at the loop head is `update_head` for both runtimes. -/
theorem loop_jumpi_dest_update_head :
    opcodeAt depositClampWindow 16 =
        some (.PUSH2, some (UInt256.ofNat Deposit.update_head, 2)) ∧
      opcodeAt exitClampWindow 15 =
        some (.PUSH2, some (UInt256.ofNat Exit.update_head, 2)) ∧
      opcodeAt depositClampWindow 19 = some (.JUMPI, none) ∧
      opcodeAt exitClampWindow 18 = some (.JUMPI, none) :=
  ⟨deposit_opcode_push_update_head, exit_opcode_push_update_head,
    deposit_opcode_loop_JUMPI, exit_opcode_loop_JUMPI⟩

/-! ### `update_head` / `reset_queue` windows (pointer-write CFG, no body) -/

/-- Deposit bytes `[471, 500)`: `JUMPDEST update_head; SWAP2; ADD; DUP1;
SWAP3; EQ; PUSH2 reset_queue; JUMPI; … JUMPDEST reset_queue`. -/
def depositHeadHex : String :=
  "5b91018092146101e957906002556101f4565b90505f6002555f600355"

def depositHeadWindow : ByteArray := fromHex depositHeadHex

def depositHeadBase : Nat := 471

theorem depositHeadBase_eq : depositHeadBase = Deposit.update_head := rfl

theorem deposit_opcode_update_head_JUMPDEST :
    opcodeAt depositHeadWindow 0 = some (.JUMPDEST, none) :=
  rfl

theorem deposit_opcode_reset_eq :
    opcodeAt depositHeadWindow 5 = some (.EQ, none) :=
  rfl

theorem deposit_opcode_push_reset_queue :
    opcodeAt depositHeadWindow 6 =
      some (.PUSH2, some (UInt256.ofNat Deposit.reset_queue, 2)) :=
  rfl

theorem deposit_opcode_reset_JUMPI :
    opcodeAt depositHeadWindow 9 = some (.JUMPI, none) :=
  rfl

theorem deposit_head_reset_local : depositHeadBase + 18 = Deposit.reset_queue :=
  rfl

theorem deposit_opcode_reset_queue_JUMPDEST :
    opcodeAt depositHeadWindow 18 = some (.JUMPDEST, none) :=
  rfl

/-- Exit bytes `[301, 330)`: same shape as the deposit head/reset pair. -/
def exitHeadHex : String :=
  "5b910180921461013f579060025561014a565b90505f6002555f600355"

def exitHeadWindow : ByteArray := fromHex exitHeadHex

def exitHeadBase : Nat := 301

theorem exitHeadBase_eq : exitHeadBase = Exit.update_head := rfl

theorem exit_opcode_update_head_JUMPDEST :
    opcodeAt exitHeadWindow 0 = some (.JUMPDEST, none) :=
  rfl

theorem exit_opcode_reset_eq :
    opcodeAt exitHeadWindow 5 = some (.EQ, none) :=
  rfl

theorem exit_opcode_push_reset_queue :
    opcodeAt exitHeadWindow 6 =
      some (.PUSH2, some (UInt256.ofNat Exit.reset_queue, 2)) :=
  rfl

theorem exit_opcode_reset_JUMPI :
    opcodeAt exitHeadWindow 9 = some (.JUMPI, none) :=
  rfl

theorem exit_head_reset_local : exitHeadBase + 18 = Exit.reset_queue :=
  rfl

theorem exit_opcode_reset_queue_JUMPDEST :
    opcodeAt exitHeadWindow 18 = some (.JUMPDEST, none) :=
  rfl

/-- Full-drain reset: `new_head == tail` (i.e. `n = length`) jumps to
`reset_queue`, which zeroes both pointers. Partial drain falls through
and `SSTORE`s the advanced HEAD. Algebra in `next_full` / `next_partial`. -/
theorem reset_eq_iff_full {kind : Kind} {head tail : Nat}
    (tlt : tail < 2 ^ 64) (hle : head ≤ tail) :
    UInt256.eq
        (UInt256.ofNat (head + drainCount kind head tail))
        (UInt256.ofNat tail) = UInt256.ofNat 1 ↔
      length head tail ≤ capOf kind := by
  have hsum : head + drainCount kind head tail < UInt256.size := by
    have := head_add_drainCount_le_tail kind hle
    have : tail < UInt256.size := Nat.lt_trans tlt (by decide)
    omega
  have ht : tail < UInt256.size := Nat.lt_trans tlt (by decide)
  rw [loop_eq_iff hsum ht]
  constructor
  · intro h
    have : drainCount kind head tail = length head tail := by
      unfold length at *
      omega
    exact (drainCount_eq_length_iff kind head tail).mp this
  · intro hleCap
    have hn : drainCount kind head tail = length head tail :=
      (drainCount_eq_length_iff kind head tail).mpr hleCap
    unfold length at *
    omega

/-! ## Summary -/

/-- Load-bearing `∀` conjunction: both caps, oldest-`n` window, leftover
pointers match `systemCall` `drop`/`take`, clamp `GT` is `min`. -/
theorem fifo_forall {kind : Kind} {σ : Storage} (wf : WellFormed kind σ)
    (bal : Wei) (b : Bool) :
    capOf .deposit = 64 ∧
      capOf .exit = 16 ∧
      drainCount kind (queueHead σ) (queueTail σ) =
        min (queueOf kind σ).length (capOf kind) ∧
      (queueOf kind σ).take (capOf kind) =
        (List.range (drainCount kind (queueHead σ) (queueTail σ))).map
          (fun i => decodeItem kind σ (queueHead σ + i)) ∧
      (systemCall (toModel kind σ bal) b).state.queue =
        queueFrom kind σ
          (nextHead kind (queueHead σ) (queueTail σ))
          (nextTail kind (queueHead σ) (queueTail σ)) ∧
      (length (queueHead σ) (queueTail σ) ≤ capOf kind →
        nextHead kind (queueHead σ) (queueTail σ) = 0 ∧
          nextTail kind (queueHead σ) (queueTail σ) = 0) ∧
      (capOf kind < length (queueHead σ) (queueTail σ) →
        nextHead kind (queueHead σ) (queueTail σ) =
            queueHead σ + capOf kind ∧
          nextTail kind (queueHead σ) (queueTail σ) = queueTail σ) :=
  ⟨capOf_deposit, capOf_exit, drainCount_eq_min wf, oldest_eq_take wf,
    systemCall_leftover_of_toModel bal b wf,
    fun h => next_full kind h,
    fun h => next_partial kind h⟩

end Eip8282.Audit.Guarantees.PDrain1.Fifo
