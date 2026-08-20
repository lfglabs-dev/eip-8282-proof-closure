import Eip8282.Audit.Correspondence
import Eip8282.Audit.WellFormed
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Model

/-!
# D2 — FIFO drain (`accum_loop`, pointer motion, caps 64 and 16)

P-DRAIN-1 claim worker D2. Owns **how many** records a system drain
returns and how `QUEUE_HEAD` / `QUEUE_TAIL` move. D1 owns the SSTORE key
set (stale-slot non-erasure). D3 owns BE→LE amount rewrite.

## What is `∀` here

Under `WellFormed` (`head ≤ tail`, `tail < 2^64`) and `CallHyp`
`isUser = false` (system path):

* `n = min(tail - head, capOf kind)` in `Nat` (no `UInt256` wrap on `SUB`);
* `accum_loop` runs `n` iterations (`i = 0,1,…,n-1`), then `i = n`;
* the returned window is the oldest `n` packed items `[head, head+n)`;
* after the drain: if `n = tail - head` (full) then both pointers are
  stored `0`, else `HEAD := HEAD + n` and `TAIL` is unchanged.

This generalises Wave 5/6 sampled tails `{2, 17, 65}`; those are
instances of the `∀`, not extra `Ξ` traces.

## Fragment (not claimed)

Not a reduction of `EvmYul.EVM.Ξ` / `X`. The encode body of each
iteration is treated as “advance `i` by 1 and copy `RECORD_SIZE` bytes”
(D3 owns the amount rewrite). CFG facts are opcode-at-PC on the drain
snippets plus a stack machine that matches `SUB` / `GT` / clamp /
`update_head` vs `reset_queue`.

## Kill-line

The over-cap path loads a **PUSH1 cap** immediate:

* deposit offset **304** (`PUSH1 64`);
* exit offset **244** (`PUSH1 16`).

A one-byte cut of that immediate (64→32 / 16→8) makes
`n = min(length, capOf kind)` false on any queue longer than the mutated
cap. The comparison immediate (deposit 296 / exit 237) is a different
byte; under-cap drains never load the clamp PUSH1.
-/

namespace Eip8282.Audit.Guarantees.PDrain1.Fifo

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model
open Eip8282.Audit.Step

/-! ## Named caps (kill-line PUSH1 immediates) -/

/-- Deposit `MAX_PER_BLOCK`. The over-cap `PUSH1` immediate sits at
runtime offset 304 (`Jumpdests`: clamp byte; F1 `begin_loop` is 305). -/
def depositCap : Nat := 64

/-- Exit `MAX_PER_BLOCK`. The over-cap `PUSH1` immediate sits at
runtime offset 244 (`Jumpdests`: clamp byte; F1 `begin_loop` is 245). -/
def exitCap : Nat := 16

/-- Absolute offset of the deposit clamp `PUSH1 64` immediate. -/
def depositCapOffset : Nat := 304

/-- Absolute offset of the exit clamp `PUSH1 16` immediate. -/
def exitCapOffset : Nat := 244

/-- Comparison `PUSH1` (not the kill-line): deposit `MAX > count`. -/
def depositCapCmpOffset : Nat := 296

/-- Comparison `PUSH1` (not the kill-line): exit `MAX > count`. -/
def exitCapCmpOffset : Nat := 237

theorem capOf_deposit : capOf .deposit = depositCap := rfl
theorem capOf_exit : capOf .exit = exitCap := rfl

theorem capOf_eq (kind : Kind) :
    capOf kind = match kind with | .deposit => depositCap | .exit => exitCap := by
  cases kind <;> rfl

theorem depositCap_eq_maxDepositPerBlock : depositCap = maxDepositPerBlock := rfl
theorem exitCap_eq_maxExitPerBlock : exitCap = maxExitPerBlock := rfl

theorem depositCapOffset_pred_begin_loop :
    depositCapOffset + 1 = Deposit.begin_loop := rfl

theorem exitCapOffset_pred_begin_loop :
    exitCapOffset + 1 = Exit.begin_loop := rfl

theorem deposit_drain_pcs :
    Deposit.read_requests = 284 ∧
      Deposit.begin_loop = 305 ∧
      Deposit.accum_loop = 307 ∧
      Deposit.update_head = 471 ∧
      Deposit.reset_queue = 489 ∧
      depositCapOffset = 304 := by
  decide

theorem exit_drain_pcs :
    Exit.read_requests = 225 ∧
      Exit.begin_loop = 245 ∧
      Exit.accum_loop = 247 ∧
      Exit.update_head = 301 ∧
      Exit.reset_queue = 319 ∧
      exitCapOffset = 244 := by
  decide

/-- Both PUSH1 caps, named so a one-byte cut of offset 304 or 244
falsifies `drainN = min(length, capOf kind)`. -/
theorem caps_named :
    capOf .deposit = 64 ∧ capOf .exit = 16 ∧
      depositCap = 64 ∧ exitCap = 16 ∧
      depositCapOffset = 304 ∧ exitCapOffset = 244 := by
  decide

/-- System-return record width. Not D3's amount rewrite: this is the
`n * RECORD_SIZE` byte budget of the drain loop / `RETURN`. -/
def recordSize : Kind → Nat
  | .deposit => 184
  | .exit => 68

theorem recordSize_deposit : recordSize .deposit = 184 := rfl
theorem recordSize_exit : recordSize .exit = 68 := rfl

/-! ## `n = min(length, cap)` (Nat, no wrap) -/

/-- Live queue length. `WellFormed` gives `head ≤ tail`, so this is
`tail - head` with no underflow; `tail < 2^64` blocks `UInt256` wrap. -/
def queueLength (head tail : Nat) : Nat := tail - head

/-- Records the system path drains: `min(length, MAX_PER_BLOCK)`. -/
def drainN (kind : Kind) (head tail : Nat) : Nat :=
  min (queueLength head tail) (capOf kind)

theorem drainN_eq_min (kind : Kind) (head tail : Nat) :
    drainN kind head tail = min (tail - head) (capOf kind) :=
  rfl

/-- Assembly clamp: `GT` is `cap > length`; taken `JUMPI @begin_loop`
keeps `SUB` count, else `POP; PUSH1 cap`. Strict `GT`, so `length = cap`
falls through to `PUSH1 cap` and still yields `cap`. -/
def cfgClamp (length cap : Nat) : Nat :=
  if cap > length then length else cap

theorem cfgClamp_eq_min (length cap : Nat) :
    cfgClamp length cap = min length cap := by
  unfold cfgClamp
  by_cases h : cap > length
  · rw [if_pos h, Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [if_neg h, Nat.min_eq_right (Nat.not_lt.mp h)]

theorem drainN_eq_cfgClamp (kind : Kind) (head tail : Nat) :
    drainN kind head tail = cfgClamp (tail - head) (capOf kind) := by
  rw [drainN_eq_min, cfgClamp_eq_min]

theorem drainN_le_length (kind : Kind) (head tail : Nat) :
    drainN kind head tail ≤ tail - head :=
  Nat.min_le_left _ _

theorem drainN_le_cap (kind : Kind) (head tail : Nat) :
    drainN kind head tail ≤ capOf kind :=
  Nat.min_le_right _ _

theorem drainN_le_depositCap (head tail : Nat) :
    drainN .deposit head tail ≤ depositCap :=
  drainN_le_cap .deposit head tail

theorem drainN_le_exitCap (head tail : Nat) :
    drainN .exit head tail ≤ exitCap :=
  drainN_le_cap .exit head tail

/-- Full drain iff live length fits in the PUSH1 cap. -/
theorem full_drain_iff (kind : Kind) {head tail : Nat} (_hle : head ≤ tail) :
    drainN kind head tail = tail - head ↔
      tail - head ≤ capOf kind := by
  unfold drainN queueLength
  constructor
  · intro h
    exact h ▸ Nat.min_le_right _ _
  · intro h
    exact Nat.min_eq_left h

/-- Partial drain iff the queue is strictly longer than the PUSH1 cap.
Then `n` is exactly that cap (64 or 16). -/
theorem partial_drain_iff (kind : Kind) {head tail : Nat} (_hle : head ≤ tail) :
    capOf kind < tail - head ↔
      drainN kind head tail = capOf kind ∧ drainN kind head tail ≠ tail - head := by
  unfold drainN queueLength
  constructor
  · intro hlt
    constructor
    · exact Nat.min_eq_right (Nat.le_of_lt hlt)
    · rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
      exact Ne.symm (Nat.ne_of_gt hlt)
  · intro ⟨heq, hne⟩
    have hle_cap : capOf kind ≤ tail - head := by
      rw [← heq]
      exact Nat.min_le_left _ _
    refine Nat.lt_of_le_of_ne hle_cap ?_
    intro hEq
    apply hne
    rw [heq, hEq]

/-! A one-byte cut of the clamp PUSH1 falsifies `n = min(length, capOf)`
on an over-cap queue. Wave-6 images: deposit tail 65, exit tail 17. -/

theorem deposit_over_cap_uses_64 :
    drainN .deposit 0 65 = depositCap := by
  decide

theorem exit_over_cap_uses_16 :
    drainN .exit 0 17 = exitCap := by
  decide

theorem deposit_under_cap_uses_length :
    drainN .deposit 0 2 = 2 := by
  decide

theorem exit_under_cap_uses_length :
    drainN .exit 0 2 = 2 := by
  decide

/-- Mutating the deposit PUSH1 64→32 would drain 32, not `capOf .deposit`. -/
theorem deposit_cap_cut_32_ne :
    min (65 : Nat) 32 = 32 ∧ 32 ≠ depositCap := by
  decide

/-- Mutating the exit PUSH1 16→8 would drain 8, not `capOf .exit`. -/
theorem exit_cap_cut_8_ne :
    min (17 : Nat) 8 = 8 ∧ 8 ≠ exitCap := by
  decide

/-! ## Pointer motion -/

/-- Post-state of `update_head` / `reset_queue`.
`n = tail - head` → both stored 0; otherwise `HEAD := HEAD + n`, TAIL
unchanged. Empty queues take the reset (`head + 0 = tail`). -/
def pointerAfter (head tail n : Nat) : Nat × Nat :=
  if n = tail - head then (0, 0) else (head + n, tail)

theorem pointerAfter_full {head tail n : Nat}
    (_hle : head ≤ tail) (hfull : n = tail - head) :
    pointerAfter head tail n = (0, 0) := by
  simp [pointerAfter, hfull]

theorem pointerAfter_partial {head tail n : Nat}
    (_hle : head ≤ tail) (hpart : n ≠ tail - head) :
    pointerAfter head tail n = (head + n, tail) := by
  simp [pointerAfter, hpart]

theorem pointerAfter_drainN (kind : Kind) {head tail : Nat}
    (_hle : head ≤ tail) :
    pointerAfter head tail (drainN kind head tail) =
      if tail - head ≤ capOf kind then (0, 0)
      else (head + capOf kind, tail) := by
  unfold pointerAfter drainN queueLength
  by_cases hle' : tail - head ≤ capOf kind
  · rw [if_pos hle', Nat.min_eq_left hle', if_pos rfl]
  · rw [if_neg hle']
    have hlt : capOf kind < tail - head := Nat.gt_of_not_le hle'
    rw [Nat.min_eq_right (Nat.le_of_lt hlt), if_neg (Ne.symm (Nat.ne_of_gt hlt))]

/-- Assembly `update_head`: stack `[i, n, head, tail]` with `i = n`,
`SWAP2; ADD` yields `head + n`. Then `EQ` vs `tail` selects reset vs
partial `SSTORE QUEUE_HEAD`. -/
def updateHeadOps (n head tail : Nat) : Nat × Nat :=
  let newHead := head + n
  if newHead = tail then (0, 0) else (newHead, tail)

theorem updateHeadOps_eq_pointerAfter {n head tail : Nat}
    (hle : head ≤ tail) (hn : n ≤ tail - head) :
    updateHeadOps n head tail = pointerAfter head tail n := by
  unfold updateHeadOps pointerAfter
  have : head + n = tail ↔ n = tail - head := by omega
  simp [this]

theorem drain_pointers (kind : Kind) {head tail : Nat} (hle : head ≤ tail) :
    let n := drainN kind head tail
    (n = tail - head → pointerAfter head tail n = (0, 0)) ∧
      (n ≠ tail - head → pointerAfter head tail n = (head + n, tail)) :=
  ⟨pointerAfter_full hle, pointerAfter_partial hle⟩

/-! ## `accum_loop` visits `n` iterations -/

/-- One `accum_loop` tick: `DUP2; DUP2; EQ; JUMPI @update_head`. If
`i = n` the loop exits; otherwise the encode body copies `RECORD_SIZE`
bytes (opaque to D2) and `PUSH1 1; ADD; JUMP @accum_loop`. -/
def accumTick (i n : Nat) : Option Nat :=
  if i = n then none else some (i + 1)

/-- Fuelled walk of `accum_loop` from `i`. -/
def accumGo : Nat → Nat → Nat → Nat
  | 0, i, _ => i
  | fuel + 1, i, n => if i = n then i else accumGo fuel (i + 1) n

theorem accumGo_at_n (fuel n : Nat) :
    accumGo fuel n n = n := by
  cases fuel <;> simp [accumGo]

theorem accumGo_reaches {fuel i n : Nat}
    (hle : i ≤ n) (hfuel : n - i ≤ fuel) :
    accumGo fuel i n = n := by
  induction fuel generalizing i with
  | zero =>
      have : i = n := by omega
      simp [accumGo, this]
  | succ f ih =>
      unfold accumGo
      split
      · next heq => exact heq
      · next hne =>
          have hlt : i < n := Nat.lt_of_le_of_ne hle hne
          exact ih (Nat.succ_le_of_lt hlt) (by omega)

/-- Starting at `i = 0` (`begin_loop; PUSH0`), `n` successful body
ticks plus the exiting `i = n` check reach `update_head`. -/
theorem accum_loop_visits (n : Nat) :
    accumGo (n + 1) 0 n = n :=
  accumGo_reaches (Nat.zero_le n) (by omega)

theorem accumTick_body {i n : Nat} (h : i ≠ n) :
    accumTick i n = some (i + 1) := by
  simp [accumTick, h]

theorem accumTick_exit (n : Nat) :
    accumTick n n = none := by
  simp [accumTick]

/-- Exactly `n` body ticks occur before the exit. -/
def accumIters : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, i, n => if i = n then 0 else 1 + accumIters fuel (i + 1) n

theorem accumIters_eq {fuel i n : Nat}
    (hle : i ≤ n) (hfuel : n - i ≤ fuel) :
    accumIters fuel i n = n - i := by
  induction fuel generalizing i with
  | zero =>
      have : n - i = 0 := by omega
      simp [accumIters, this]
  | succ f ih =>
      unfold accumIters
      split
      · next heq => simp [heq]
      · next hne =>
          have hlt : i < n := Nat.lt_of_le_of_ne hle hne
          rw [ih (Nat.succ_le_of_lt hlt) (by omega)]
          omega

theorem accum_loop_iter_count (n : Nat) :
    accumIters (n + 1) 0 n = n :=
  accumIters_eq (Nat.zero_le n) (by omega)

/-- Body iteration `i` reads packed item `head + i` (oldest first). -/
def visitedIndex (head i : Nat) : Nat := head + i

theorem visited_window (head n : Nat) :
    (List.range n).map (visitedIndex head) =
      (List.range n).map (fun i => head + i) :=
  rfl

/-! ## Oldest window `[head, head+n)` -/

theorem take_range_of_le {k n : Nat} (h : k ≤ n) :
    (List.range n).take k = List.range k := by
  rw [List.take_range, Nat.min_eq_left h]

theorem drop_range_map (n k : Nat) :
    (List.range n).drop k = (List.range (n - k)).map (fun i => k + i) := by
  rw [List.range_eq_range', List.drop_range']
  simp [List.range'_eq_map_range]

theorem take_eq_take_min_length {α} (l : List α) (cap : Nat) :
    l.take (min l.length cap) = l.take cap := by
  by_cases h : l.length ≤ cap
  · have hcap : l.length ≤ cap := h
    rw [Nat.min_eq_left h, List.take_of_length_le (Nat.le_refl _),
        List.take_of_length_le hcap]
  · rw [Nat.min_eq_right (Nat.le_of_not_le h)]

theorem queueOf_take_oldest {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    let h := queueHead σ
    let t := queueTail σ
    let n := drainN kind h t
    (queueOf kind σ).take n =
      (List.range n).map (fun i => decodeItem kind σ (h + i)) := by
  have hle := head_le_tail wf
  have hn : drainN kind (queueHead σ) (queueTail σ) ≤
      queueTail σ - queueHead σ := drainN_le_length kind _ _
  unfold queueOf
  simp [hle]
  rw [← List.map_take, take_range_of_le hn]

theorem queueOf_drop_rest {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    let h := queueHead σ
    let t := queueTail σ
    let n := drainN kind h t
    (queueOf kind σ).drop n =
      (List.range (t - h - n)).map (fun i => decodeItem kind σ (h + n + i)) := by
  have hle := head_le_tail wf
  unfold queueOf
  simp [hle]
  rw [← List.map_drop, drop_range_map]
  simp [Function.comp, Nat.add_assoc]

/-- Model `systemCall` drops `capOf` and returns `take capOf`. That is
the same window as `take drainN` because `drainN = min(length, cap)`. -/
theorem take_drainN_eq_take_cap {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    (queueOf kind σ).take (drainN kind (queueHead σ) (queueTail σ)) =
      (queueOf kind σ).take (capOf kind) := by
  have hlen := queueOf_length wf
  unfold drainN queueLength
  rw [← hlen]
  exact take_eq_take_min_length (queueOf kind σ) (capOf kind)

theorem drop_drainN_eq_drop_cap {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    (queueOf kind σ).drop (drainN kind (queueHead σ) (queueTail σ)) =
      (queueOf kind σ).drop (capOf kind) := by
  have hlen := queueOf_length wf
  unfold drainN queueLength
  rw [← hlen]
  by_cases h : (queueOf kind σ).length ≤ capOf kind
  · rw [Nat.min_eq_left h, List.drop_eq_nil_of_le (Nat.le_refl _),
        List.drop_eq_nil_of_le h]
  · rw [Nat.min_eq_right (Nat.le_of_not_le h)]

/-! ## `UInt256` `SUB` / `ADD` do not wrap under `WellFormed` -/

theorem pow64_lt_uint256_size : 2 ^ 64 < UInt256.size := by
  unfold UInt256.size
  decide

theorem ofNat_toNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

theorem lt_size_of_lt_pow64 {n : Nat} (h : n < 2 ^ 64) :
    n < UInt256.size :=
  Nat.lt_trans h pow64_lt_uint256_size

theorem sub_toNat_of_le {a b : Nat} (hle : b ≤ a) (ha : a < UInt256.size) :
    (UInt256.ofNat a - UInt256.ofNat b).toNat = a - b := by
  have hb : b < UInt256.size := Nat.lt_of_le_of_lt hle ha
  have ha' : (UInt256.ofNat a).toNat = a := ofNat_toNat_of_lt ha
  have hb' : (UInt256.ofNat b).toNat = b := ofNat_toNat_of_lt hb
  have hFin : (UInt256.ofNat b).val ≤ (UInt256.ofNat a).val := by
    change (UInt256.ofNat b).toNat ≤ (UInt256.ofNat a).toNat
    omega
  have hsub : ((UInt256.ofNat a).val - (UInt256.ofNat b).val).val =
      (UInt256.ofNat a).val.val - (UInt256.ofNat b).val.val :=
    Fin.sub_val_of_le hFin
  change ((UInt256.ofNat a).val - (UInt256.ofNat b).val).val = a - b
  rw [hsub]
  simp [UInt256.toNat] at ha' hb'
  rw [ha', hb']

/-- `SUB` of TAIL−HEAD is Nat subtraction. Assembly: `DUP1; DUP3; SUB`. -/
theorem sub_no_wrap {head tail : Nat}
    (hle : head ≤ tail) (ht : tail < 2 ^ 64) :
    (UInt256.ofNat tail - UInt256.ofNat head).toNat = tail - head :=
  sub_toNat_of_le hle (lt_size_of_lt_pow64 ht)

theorem add_toNat_of_lt {a b : Nat} (h : a + b < UInt256.size) :
    (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b := by
  have ha : a < UInt256.size := Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < UInt256.size := Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
  have ha' : (UInt256.ofNat a).toNat = a := ofNat_toNat_of_lt ha
  have hb' : (UInt256.ofNat b).toNat = b := ofNat_toNat_of_lt hb
  have ha'' : (UInt256.ofNat a).val.val = a := by
    simpa [UInt256.toNat] using ha'
  have hb'' : (UInt256.ofNat b).val.val = b := by
    simpa [UInt256.toNat] using hb'
  have hsum : (UInt256.ofNat a).val.val + (UInt256.ofNat b).val.val < UInt256.size := by
    rw [ha'', hb'']; exact h
  have hadd := Fin.val_add_eq_of_add_lt (a := (UInt256.ofNat a).val) (b := (UInt256.ofNat b).val) hsum
  change ((UInt256.ofNat a).val + (UInt256.ofNat b).val).val = a + b
  rw [hadd, ha'', hb'']

/-- `ADD` of HEAD+n does not wrap: `n ≤ cap ≤ 64` and `tail < 2^64`. -/
theorem add_no_wrap {head n : Nat}
    (h : head + n < 2 ^ 64) :
    (UInt256.ofNat head + UInt256.ofNat n).toNat = head + n :=
  add_toNat_of_lt (lt_size_of_lt_pow64 h)

theorem wellFormed_sub_no_wrap {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    (UInt256.ofNat (queueTail σ) - UInt256.ofNat (queueHead σ)).toNat =
      queueTail σ - queueHead σ :=
  sub_no_wrap (head_le_tail wf) (tail_lt_2_64 wf)

theorem wellFormed_add_no_wrap {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    let head := queueHead σ
    let n := drainN kind head (queueTail σ)
    head + n < 2 ^ 64 ∧
      (UInt256.ofNat head + UInt256.ofNat n).toNat = head + n := by
  intro head n
  have hle := head_le_tail wf
  have ht := tail_lt_2_64 wf
  have hn : n ≤ queueTail σ - head := drainN_le_length kind head (queueTail σ)
  have hsum : head + n ≤ queueTail σ := by omega
  have hlt : head + n < 2 ^ 64 := Nat.lt_of_le_of_lt hsum ht
  exact ⟨hlt, add_no_wrap hlt⟩

theorem ofNat_gt_iff {a b : Nat} (ha : a < UInt256.size) (hb : b < UInt256.size) :
    (UInt256.ofNat a > UInt256.ofNat b) ↔ a > b := by
  have ha' := ofNat_toNat_of_lt ha
  have hb' := ofNat_toNat_of_lt hb
  constructor
  · intro h
    change (UInt256.ofNat b).toNat < (UInt256.ofNat a).toNat at h
    omega
  · intro h
    change (UInt256.ofNat b).toNat < (UInt256.ofNat a).toNat
    omega

/-- `GT` of the PUSH1 cap vs `SUB` count agrees with Nat `>`. -/
theorem gt_cap_iff (kind : Kind) {head tail : Nat}
    (_hle : head ≤ tail) (ht : tail < 2 ^ 64) :
    (UInt256.ofNat (capOf kind) > UInt256.ofNat (tail - head)) ↔
      capOf kind > tail - head := by
  have hcap : capOf kind < 2 ^ 64 := by
    cases kind <;> decide
  have hlen : tail - head < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) ht
  exact ofNat_gt_iff (lt_size_of_lt_pow64 hcap) (lt_size_of_lt_pow64 hlen)

/-! ## Return size = `n * RECORD_SIZE` (no amount rewrite) -/

theorem toLeBytes_length (n w : Nat) : (toLeBytes n w).length = w := by
  induction w generalizing n with
  | zero => simp [toLeBytes]
  | succ w ih => simp [toLeBytes, ih]

theorem toBeBytes_length (n w : Nat) : (toBeBytes n w).length = w := by
  simp [toBeBytes, toLeBytes_length]

theorem wordToBytesBE_length (w : Nat) : (wordToBytesBE w).length = 32 := by
  simp [wordToBytesBE]

theorem length_flatMap_wordToBytesBE (ws : List Nat) :
    (ws.flatMap wordToBytesBE).length = ws.length * 32 := by
  induction ws with
  | nil => simp
  | cons _w ws ih =>
      simp [wordToBytesBE_length, ih]
      omega

theorem loadItemWords_length (kind : Kind) (σ : Storage) (idx : Nat) :
    (loadItemWords kind σ idx).length = slotsPerItem kind := by
  simp [loadItemWords]

theorem decodeDepositCalldata_length (σ : Storage) (idx : Nat) :
    (decodeDepositCalldata σ idx).length = 184 := by
  unfold decodeDepositCalldata wordsToBytes
  have hws : (loadItemWords .deposit σ idx).length = 6 :=
    loadItemWords_length .deposit σ idx
  have hflat : ((loadItemWords .deposit σ idx).flatMap wordToBytesBE).length = 192 := by
    rw [length_flatMap_wordToBytesBE, hws]
  rw [List.length_take, hflat]
  decide

theorem decodeExitPubkey_length (σ : Storage) (idx : Nat) :
    (decodeExitPubkey σ idx).length = 48 := by
  unfold decodeExitPubkey wordsToBytes
  have hws : (loadItemWords .exit σ idx).length = 3 :=
    loadItemWords_length .exit σ idx
  have hdrop : ((loadItemWords .exit σ idx).drop 1).length = 2 := by
    rw [List.length_drop, hws]
  have hflat :
      (((loadItemWords .exit σ idx).drop 1).flatMap wordToBytesBE).length = 64 := by
    rw [length_flatMap_wordToBytesBE, hdrop]
  rw [List.length_take, hflat]
  decide

theorem encodeReturned_decodeItem (kind : Kind) (σ : Storage) (idx : Nat) :
    (encodeReturned (decodeItem kind σ idx)).length = recordSize kind := by
  cases kind with
  | deposit =>
      simp only [decodeItem, encodeReturned, recordSize]
      set cd := decodeDepositCalldata σ idx
      have hcd : cd.length = 184 := decodeDepositCalldata_length σ idx
      rw [List.length_append, List.length_append, List.length_take, List.length_drop,
          toLeBytes_length, hcd]
      decide
  | exit =>
      simp only [decodeItem, encodeReturned, recordSize]
      rw [List.length_append, toBeBytes_length, decodeExitPubkey_length]

theorem concatReturned_length_const (rs : List Record) (k : Nat)
    (h : ∀ r ∈ rs, (encodeReturned r).length = k) :
    (concatReturned rs).length = rs.length * k := by
  unfold concatReturned
  induction rs with
  | nil => simp
  | cons r rs ih =>
      have hr : (encodeReturned r).length = k := h r (by simp)
      have hrs : ∀ x ∈ rs, (encodeReturned x).length = k := fun x hx =>
        h x (List.mem_cons.mpr (Or.inr hx))
      rw [List.map_cons, List.flatten_cons, List.length_append, hr, ih hrs]
      have hlen : (r :: rs).length = rs.length + 1 := rfl
      rw [hlen, Nat.add_comm k, Nat.succ_mul]

theorem concatReturned_oldest_length {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    (concatReturned
        ((queueOf kind σ).take (drainN kind (queueHead σ) (queueTail σ)))).length =
      drainN kind (queueHead σ) (queueTail σ) * recordSize kind := by
  set n := drainN kind (queueHead σ) (queueTail σ)
  have hlen : ((queueOf kind σ).take n).length = n := by
    rw [List.length_take, queueOf_length wf, Nat.min_eq_left (drainN_le_length _ _ _)]
  have hconst :
      (concatReturned ((queueOf kind σ).take n)).length =
        ((queueOf kind σ).take n).length * recordSize kind := by
    refine concatReturned_length_const _ (recordSize kind) ?_
    intro r hr
    have htake := queueOf_take_oldest wf
    simp at htake
    rw [htake] at hr
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hr
    exact encodeReturned_decodeItem kind σ (queueHead σ + i)
  rw [hlen] at hconst
  exact hconst

/-! ## Model transport (`systemCall` = drop/take `capOf` = drainN window) -/

theorem model_system_queue (s : Model.State) (b : Bool) :
    (systemCall s b).state.queue = s.queue.drop (capOf s.kind) := by
  unfold systemCall
  rfl

theorem model_system_return (s : Model.State) (b : Bool) :
    systemCall s b =
      .success (systemCall s b).state
        (concatReturned (s.queue.take (capOf s.kind))) := by
  unfold systemCall
  rfl

theorem modelCall_system_take {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei) :
    (modelCall kind false σ balance caller calldata value).state.queue =
      (queueOf kind σ).drop (drainN kind (queueHead σ) (queueTail σ)) ∧
      (match modelCall kind false σ balance caller calldata value with
       | .success _ d =>
           d = concatReturned
             ((queueOf kind σ).take (drainN kind (queueHead σ) (queueTail σ)))
       | .revert _ => False) := by
  simp only [modelCall_system, systemCall, Outcome.state_success, toModel_queue,
    toModel_kind]
  constructor
  · exact (drop_drainN_eq_drop_cap wf).symm
  · exact congrArg concatReturned (take_drainN_eq_take_cap wf).symm

/-! ## Drain snippets (CFG-direct on clamp / loop bound / pointer ops) -/

/-- Deposit `read_requests` … `accum_loop` bound-check `JUMPI`.
Relative PC 0 is absolute 284. Kill-line cap immediate is relative 20. -/
def depositClampHex : String :=
  "5b60035460025480820380604011610131575060405b5f5b8181146101d757"

/-- Exit `read_requests` … `accum_loop` bound-check `JUMPI`.
Relative PC 0 is absolute 225. Kill-line cap immediate is relative 19. -/
def exitClampHex : String :=
  "5b6003546002548082038060101160f5575060105b5f5b81811461012d57"

def depositClamp : ByteArray := fromHex depositClampHex
def exitClamp : ByteArray := fromHex exitClampHex

theorem deposit_clamp_rel_cap :
    Deposit.read_requests + 20 = depositCapOffset := rfl

theorem exit_clamp_rel_cap :
    Exit.read_requests + 19 = exitCapOffset := rfl

theorem deposit_clamp_rel_cmp :
    Deposit.read_requests + 12 = depositCapCmpOffset := rfl

theorem exit_clamp_rel_cmp :
    Exit.read_requests + 12 = exitCapCmpOffset := rfl

/-- Deposit clamp snippet: PUSH1 cap (kill-line) at relative 19, immediate
byte 64 at relative 20. -/
theorem deposit_clamp_opcode_PUSH1_cap :
    opcodeAt depositClamp 19 =
      some (.PUSH1, some (UInt256.ofNat depositCap, 1)) :=
  rfl

theorem deposit_clamp_opcode_PUSH1_cmp :
    opcodeAt depositClamp 11 =
      some (.PUSH1, some (UInt256.ofNat depositCap, 1)) :=
  rfl

theorem deposit_clamp_opcode_GT :
    opcodeAt depositClamp 13 = some (.GT, none) :=
  rfl

theorem deposit_clamp_opcode_JUMPI_begin :
    opcodeAt depositClamp 14 =
      some (.PUSH2, some (UInt256.ofNat Deposit.begin_loop, 2)) :=
  rfl

theorem deposit_clamp_opcode_begin_loop :
    opcodeAt depositClamp 21 = some (.JUMPDEST, none) :=
  rfl

theorem deposit_clamp_opcode_PUSH0 :
    opcodeAt depositClamp 22 = some (.PUSH0, none) :=
  rfl

theorem deposit_clamp_opcode_accum :
    opcodeAt depositClamp 23 = some (.JUMPDEST, none) :=
  rfl

theorem deposit_clamp_rel_begin :
    Deposit.read_requests + 21 = Deposit.begin_loop := rfl

theorem deposit_clamp_rel_accum :
    Deposit.read_requests + 23 = Deposit.accum_loop := rfl

/-- Exit clamp snippet: PUSH1 cap (kill-line) at relative 18, immediate
byte 16 at relative 19. -/
theorem exit_clamp_opcode_PUSH1_cap :
    opcodeAt exitClamp 18 =
      some (.PUSH1, some (UInt256.ofNat exitCap, 1)) :=
  rfl

theorem exit_clamp_opcode_PUSH1_cmp :
    opcodeAt exitClamp 11 =
      some (.PUSH1, some (UInt256.ofNat exitCap, 1)) :=
  rfl

theorem exit_clamp_opcode_GT :
    opcodeAt exitClamp 13 = some (.GT, none) :=
  rfl

theorem exit_clamp_opcode_PUSH1_begin :
    opcodeAt exitClamp 14 =
      some (.PUSH1, some (UInt256.ofNat Exit.begin_loop, 1)) :=
  rfl

theorem exit_clamp_opcode_begin_loop :
    opcodeAt exitClamp 20 = some (.JUMPDEST, none) :=
  rfl

theorem exit_clamp_opcode_PUSH0 :
    opcodeAt exitClamp 21 = some (.PUSH0, none) :=
  rfl

theorem exit_clamp_opcode_accum :
    opcodeAt exitClamp 22 = some (.JUMPDEST, none) :=
  rfl

theorem exit_clamp_rel_begin :
    Exit.read_requests + 20 = Exit.begin_loop := rfl

theorem exit_clamp_rel_accum :
    Exit.read_requests + 22 = Exit.accum_loop := rfl

/-- Deposit `update_head` / `reset_queue` through both pointer `SSTORE`s. -/
def depositPointerHex : String :=
  "5b91018092146101e957906002556101f4565b90505f6002555f600355"

/-- Exit `update_head` / `reset_queue` through both pointer `SSTORE`s. -/
def exitPointerHex : String :=
  "5b910180921461013f579060025561014a565b90505f6002555f600355"

def depositPointer : ByteArray := fromHex depositPointerHex
def exitPointer : ByteArray := fromHex exitPointerHex

theorem deposit_pointer_opcode_SWAP2 :
    opcodeAt depositPointer 1 = some (.SWAP2, none) :=
  rfl

theorem deposit_pointer_opcode_ADD :
    opcodeAt depositPointer 2 = some (.ADD, none) :=
  rfl

theorem deposit_pointer_opcode_EQ :
    opcodeAt depositPointer 5 = some (.EQ, none) :=
  rfl

theorem deposit_pointer_opcode_PUSH2_reset :
    opcodeAt depositPointer 6 =
      some (.PUSH2, some (UInt256.ofNat Deposit.reset_queue, 2)) :=
  rfl

theorem deposit_pointer_opcode_PUSH1_HEAD :
    opcodeAt depositPointer 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) :=
  rfl

theorem deposit_pointer_opcode_SSTORE :
    opcodeAt depositPointer 13 = some (.SSTORE, none) :=
  rfl

theorem deposit_pointer_rel :
    Deposit.update_head + 0 = Deposit.update_head ∧
      Deposit.update_head + 18 = Deposit.reset_queue := by
  decide

theorem exit_pointer_opcode_SWAP2 :
    opcodeAt exitPointer 1 = some (.SWAP2, none) :=
  rfl

theorem exit_pointer_opcode_ADD :
    opcodeAt exitPointer 2 = some (.ADD, none) :=
  rfl

theorem exit_pointer_opcode_EQ :
    opcodeAt exitPointer 5 = some (.EQ, none) :=
  rfl

theorem exit_pointer_opcode_PUSH2_reset :
    opcodeAt exitPointer 6 =
      some (.PUSH2, some (UInt256.ofNat Exit.reset_queue, 2)) :=
  rfl

theorem exit_pointer_opcode_PUSH1_HEAD :
    opcodeAt exitPointer 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) :=
  rfl

theorem exit_pointer_opcode_SSTORE :
    opcodeAt exitPointer 13 = some (.SSTORE, none) :=
  rfl

theorem exit_pointer_rel :
    Exit.update_head + 0 = Exit.update_head ∧
      Exit.update_head + 18 = Exit.reset_queue := by
  decide

/-- Opening of `read_requests`: `PUSH1 QUEUE_TAIL; SLOAD; PUSH1 QUEUE_HEAD; SLOAD`. -/
theorem deposit_clamp_opcode_TAIL :
    opcodeAt depositClamp 1 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_TAIL, 1)) :=
  rfl

theorem deposit_clamp_opcode_HEAD :
    opcodeAt depositClamp 4 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) :=
  rfl

theorem deposit_clamp_opcode_SUB :
    opcodeAt depositClamp 9 = some (.SUB, none) :=
  rfl

theorem exit_clamp_opcode_TAIL :
    opcodeAt exitClamp 1 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_TAIL, 1)) :=
  rfl

theorem exit_clamp_opcode_HEAD :
    opcodeAt exitClamp 4 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) :=
  rfl

theorem exit_clamp_opcode_SUB :
    opcodeAt exitClamp 9 = some (.SUB, none) :=
  rfl

/-- Loop bound: `DUP2; DUP2; EQ` then `JUMPI @update_head`. -/
theorem deposit_accum_opcode_EQ :
    opcodeAt depositClamp 26 = some (.EQ, none) :=
  rfl

theorem deposit_accum_opcode_PUSH2_update_head :
    opcodeAt depositClamp 27 =
      some (.PUSH2, some (UInt256.ofNat Deposit.update_head, 2)) :=
  rfl

theorem exit_accum_opcode_EQ :
    opcodeAt exitClamp 25 = some (.EQ, none) :=
  rfl

theorem exit_accum_opcode_PUSH2_update_head :
    opcodeAt exitClamp 26 =
      some (.PUSH2, some (UInt256.ofNat Exit.update_head, 2)) :=
  rfl

/-! ## `CallHyp` system-path `∀` -/

theorem drainN_eq_queue_min {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    drainN kind (queueHead σ) (queueTail σ) =
      min (queueOf kind σ).length (capOf kind) := by
  rw [drainN_eq_min, queueOf_length wf]

/-- System-path FIFO: count, oldest window, pointer motion, both caps.
Hypotheses: `WellFormed`, `CallHyp.isUser = false`. Not a `Ξ` reduction. -/
theorem fifo_system_spec {kind : Kind} {σ : Storage}
    (h : CallHyp kind σ) (_hsys : h.isUser = false) :
    let head := queueHead σ
    let tail := queueTail σ
    let n := drainN kind head tail
    n = min (queueOf kind σ).length (capOf kind) ∧
      n = cfgClamp (tail - head) (capOf kind) ∧
      n ≤ capOf kind ∧
      (kind = .deposit → n ≤ depositCap) ∧
      (kind = .exit → n ≤ exitCap) ∧
      accumIters (n + 1) 0 n = n ∧
      (queueOf kind σ).take n =
        (List.range n).map (fun i => decodeItem kind σ (head + i)) ∧
      pointerAfter head tail n =
        (if (queueOf kind σ).length ≤ capOf kind then (0, 0)
         else (head + n, tail)) ∧
      (UInt256.ofNat tail - UInt256.ofNat head).toNat = tail - head := by
  intro head tail n
  have wf := h.wellFormed
  have hle := head_le_tail wf
  refine ⟨drainN_eq_queue_min wf, drainN_eq_cfgClamp kind head tail,
      drainN_le_cap kind head tail, ?_, ?_,
      accum_loop_iter_count n, queueOf_take_oldest wf, ?_,
      wellFormed_sub_no_wrap wf⟩
  · intro hk; cases hk; exact drainN_le_depositCap head tail
  · intro hk; cases hk; exact drainN_le_exitCap head tail
  · have hlen := queueOf_length wf
    change pointerAfter (queueHead σ) (queueTail σ)
        (drainN kind (queueHead σ) (queueTail σ)) =
      (if (queueOf kind σ).length ≤ capOf kind then (0, 0)
       else (queueHead σ + drainN kind (queueHead σ) (queueTail σ),
             queueTail σ))
    rw [pointerAfter_drainN kind hle, hlen]
    split_ifs with hle'
    · rfl
    · have hncap : drainN kind (queueHead σ) (queueTail σ) = capOf kind :=
        (partial_drain_iff kind hle).mp (Nat.gt_of_not_le hle') |>.1
      rw [hncap]

theorem fifo_system_spec_deposit {σ : Storage}
    (h : CallHyp .deposit σ) (_ : h.isUser = false) :
    drainN .deposit (queueHead σ) (queueTail σ) ≤ depositCap :=
  drainN_le_depositCap _ _

theorem fifo_system_spec_exit {σ : Storage}
    (h : CallHyp .exit σ) (_ : h.isUser = false) :
    drainN .exit (queueHead σ) (queueTail σ) ≤ exitCap :=
  drainN_le_exitCap _ _

/-- Both kinds: full drain zeroes both pointers; partial advances HEAD by
the PUSH1 cap. -/
theorem fifo_pointers_both_kinds {kind : Kind} {σ : Storage}
    (h : CallHyp kind σ) (_hsys : h.isUser = false) :
    let head := queueHead σ
    let tail := queueTail σ
    let n := drainN kind head tail
    (n = tail - head → pointerAfter head tail n = (0, 0)) ∧
      (n ≠ tail - head →
        pointerAfter head tail n = (head + n, tail) ∧ n = capOf kind) := by
  intro head tail n
  have hle := head_le_tail h.wellFormed
  constructor
  · exact pointerAfter_full hle
  · intro hne
    refine ⟨pointerAfter_partial hle hne, ?_⟩
    have := partial_drain_iff kind hle
    have hlt : capOf kind < tail - head := by
      by_contra hle'
      exact hne ((full_drain_iff kind hle).mpr (Nat.not_lt.mp hle'))
    exact (this.mp hlt).1

end Eip8282.Audit.Guarantees.PDrain1.Fifo
