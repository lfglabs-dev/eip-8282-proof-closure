import Eip8282.Audit.WellFormed
import Eip8282.Audit.Model
import Eip8282.Audit.Correspondence
import Eip8282.Audit.Guarantees.PControl1.Ctor

/-!
# Reachable packed-storage images

`Eip8282.Audit.WellFormed.WellFormed` is the hypothesis every registered `∀`
parent carries. On its own it is a shape predicate: it says slots 0–3 are the
control words and `head ≤ tail`, but not that the image was *built* by the
pinned constructors and the two calls. `A-REACHABLE` named exactly that gap.

This module closes the coverage direction of that gap, entirely inside the
packed-storage layer and the abstract model — it never runs `Ξ`:

* `ctorStorage` is the storage post-image of the pinned init programs. It is
  not a fresh assumption: it is `PControl1.Ctor.depositPost` / `exitPost`
  applied to the empty map, i.e. what `runDepositCtor` / `runExitCtor` return
  in `Ctor.ctor_posts_from_empty`, a CFG run of the pinned init bytes.
* `applyUser` and `applySystem` are the storage transitions: a successful
  submission writes the packed item at `QUEUE_TAIL` and bumps `SLOT_COUNT` /
  `QUEUE_TAIL`; a system call rewrites `SLOT_EXCESS`, zeroes `SLOT_COUNT`,
  advances `QUEUE_HEAD` by the drained count and resets both pointers to `0`
  when the queue empties.
* `ReachableStorage` is the inductive closure of `ctorStorage` under those two.
* `ReachableStorage.wellFormed` proves every reachable image is `WellFormed`,
  so the registered parents' `∀ σ, WellFormed kind σ → …` covers all of them.
* `ReachableStorage.model_reachable` proves each reachable image abstracts
  under `toModel` to a `Model.Reachable` state, derived from the constructors
  rather than assumed.
* `ReachableStorage.callHyp` hands a reachable image to the exact
  `Correspondence.CallHyp` the three parents quantify over.

The pointer reset on full drain is not invented here: the kept `Ξ` trace in
`pdrain1_bytecode_parent` observes slots `(103, 0, 0, 0)` after a two-item
exit queue is drained, and `(_, 0, 16, 17)` after a 17-item queue is drained
at cap 16.

## What this does not close

`applyUser` / `applySystem` are *stated* storage transitions, not
`EvmYul.EVM.Ξ`. That `Ξ` on the pinned runtimes implements them is
`A-ABSTRACT-TX`, which stays open. So this module turns "the parents may not
be about the predeploys" into "the parents cover every image reachable under
the modelled transition; whether `Ξ` realises that transition is
`A-ABSTRACT-TX`".

Two side conditions are carried explicitly rather than hidden:

* `QUEUE_TAIL` must stay below `2 ^ 64` across an append. The assembly has no
  such check; `WellFormed` is where the bound lives, so images past `2 ^ 64`
  successful submissions are outside the registered parents by construction.
* `SLOT_EXCESS + SLOT_COUNT` must not wrap a 256-bit word across a system
  call. `Model.nextExcess` is unbounded `Nat`; `SSTORE` is `mod 2 ^ 256`.
  Where the sum wraps, the storage transition is not a refinement of the
  model, and the hypothesis says so.
-/

namespace Eip8282.Audit.Reachable

open EvmYul (UInt256 Storage)
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Model
open Eip8282.Audit.Step (isUserCaller campaignGasBound)
open Eip8282.Audit.Correspondence (CallHyp campaignFuelBound)
open Eip8282.Audit.Guarantees.PControl1.Ctor (depositPost exitPost)

/-! ## Slot algebra

`Storage` is `Std.TreeMap UInt256 UInt256 compare`, so one `SSTORE` is
`TreeMap.insert` and reading a slot back is `getD_insert`. Everything below
needs exactly one fact about key comparison: two `UInt256.ofNat` keys compare
`.eq` iff the naturals agree mod `2 ^ 256`.
-/

/-- One `SSTORE` of a natural value at a natural slot. -/
def setSlot (σ : Storage) (slot value : Nat) : Storage :=
  σ.insert (UInt256.ofNat slot) (UInt256.ofNat value)

theorem toNat_ofNat_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n :=
  Eip8282.Audit.Guarantees.PControl1.Ctor.toNat_ofNat_lt h

private theorem ordering_then_eq (o : Ordering) : o.then .eq = o := by
  cases o <;> rfl

/-- `UInt256`'s derived `Ord` is `Ord` on its single `val` field. -/
theorem u256_compare_val (a b : UInt256) :
    compare a b = compare a.val b.val := by
  cases a; cases b
  change Ordering.then (compare _ _) .eq = _
  exact ordering_then_eq _

theorem compare_ofNat (p q : Nat) :
    compare (UInt256.ofNat p) (UInt256.ofNat q) =
      compare (p % UInt256.size) (q % UInt256.size) := by
  rw [u256_compare_val]
  rfl

theorem compare_ofNat_eq_iff {p q : Nat} (hp : p < UInt256.size)
    (hq : q < UInt256.size) :
    compare (UInt256.ofNat p) (UInt256.ofNat q) = .eq ↔ p = q := by
  rw [compare_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  exact Nat.compare_eq_eq

/-- Reading any slot after one `SSTORE`. -/
theorem loadNat_setSlot {σ : Storage} {slot value q : Nat}
    (hslot : slot < UInt256.size) (hq : q < UInt256.size)
    (hvalue : value < UInt256.size) :
    loadNat (setSlot σ slot value) q =
      if q = slot then value else loadNat σ q := by
  unfold loadNat loadU256 setSlot
  by_cases h : q = slot
  · subst h
    rw [Std.TreeMap.getD_insert_self]
    simp [toNat_ofNat_lt hvalue]
  · rw [Std.TreeMap.getD_insert]
    have hne : ¬ (compare (UInt256.ofNat slot) (UInt256.ofNat q) = .eq) := by
      rw [compare_ofNat_eq_iff hslot hq]
      exact fun hs => h hs.symm
    simp [hne, h]

theorem loadNat_setSlot_ne {σ : Storage} {slot value q : Nat}
    (hslot : slot < UInt256.size) (hq : q < UInt256.size)
    (hvalue : value < UInt256.size) (hne : q ≠ slot) :
    loadNat (setSlot σ slot value) q = loadNat σ q := by
  rw [loadNat_setSlot hslot hq hvalue, if_neg hne]

theorem loadNat_setSlot_self {σ : Storage} {slot value : Nat}
    (hslot : slot < UInt256.size) (hvalue : value < UInt256.size) :
    loadNat (setSlot σ slot value) slot = value := by
  rw [loadNat_setSlot hslot hslot hvalue, if_pos rfl]

/-- Write consecutive words starting at `base`. This is the packed-item store
the assembly performs on a successful submission. -/
def writeWords (σ : Storage) (base : Nat) : List Nat → Storage
  | [] => σ
  | w :: ws => writeWords (setSlot σ base w) (base + 1) ws

/-- Slots outside `[base, base + ws.length)` survive the packed-item store. -/
theorem loadNat_writeWords_outside :
    ∀ (ws : List Nat) (σ : Storage) (base q : Nat),
      base + ws.length < UInt256.size →
      q < UInt256.size →
      (∀ w ∈ ws, w < UInt256.size) →
      (q < base ∨ base + ws.length ≤ q) →
      loadNat (writeWords σ base ws) q = loadNat σ q
  | [], _, _, _, _, _, _, _ => rfl
  | w :: ws, σ, base, q, hbase, hq, hws, hout => by
      have hbase' : base + 1 + ws.length < UInt256.size := by
        simp [List.length_cons] at hbase; omega
      have hwlt : w < UInt256.size := hws w (List.mem_cons_self)
      have hws' : ∀ u ∈ ws, u < UInt256.size := fun u hu =>
        hws u (List.mem_cons_of_mem _ hu)
      have hbaselt : base < UInt256.size := by
        simp [List.length_cons] at hbase; omega
      have hne : q ≠ base := by
        rcases hout with h | h
        · omega
        · simp [List.length_cons] at h; omega
      have hout' : q < base + 1 ∨ base + 1 + ws.length ≤ q := by
        rcases hout with h | h
        · exact Or.inl (by omega)
        · simp [List.length_cons] at h; exact Or.inr (by omega)
      show loadNat (writeWords (setSlot σ base w) (base + 1) ws) q = loadNat σ q
      rw [loadNat_writeWords_outside ws (setSlot σ base w) (base + 1) q hbase' hq
        hws' hout']
      exact loadNat_setSlot_ne hbaselt hq hwlt hne

/-! ## Slot bounds

Control slots are 0–3; item slots start at `QUEUE_OFFSET = 4`. A `WellFormed`
image has `tail < 2 ^ 64` and at most six slots per item, so every item slot
in play sits below `2 ^ 67` — far inside a 256-bit word.
-/

theorem slotsPerItem_le_six (kind : Kind) : slotsPerItem kind ≤ 6 := by
  cases kind <;> decide

theorem slotsPerItem_pos (kind : Kind) : 0 < slotsPerItem kind := by
  cases kind <;> decide

theorem control_slots_lt_size :
    SLOT_EXCESS < UInt256.size ∧ SLOT_COUNT < UInt256.size ∧
      QUEUE_HEAD < UInt256.size ∧ QUEUE_TAIL < UInt256.size := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD,
    QUEUE_TAIL, UInt256.size]

/-- Whole item window of index `idx` is inside a 256-bit word. -/
theorem itemWindow_lt_size {kind : Kind} {idx : Nat} (hidx : idx < 2 ^ 64) :
    itemBase kind idx + slotsPerItem kind < UInt256.size := by
  have hspi := slotsPerItem_le_six kind
  have h1 : idx * slotsPerItem kind ≤ idx * 6 :=
    Nat.mul_le_mul_left idx hspi
  have h2 : idx * 6 ≤ 2 ^ 64 * 6 :=
    Nat.mul_le_mul_right 6 (Nat.le_of_lt hidx)
  have h3 : 2 ^ 64 * 6 + 10 < UInt256.size := by
    simp [UInt256.size]
  unfold itemBase QUEUE_OFFSET
  omega

theorem itemSlot_lt_size {kind : Kind} {idx j : Nat} (hidx : idx < 2 ^ 64)
    (hj : j < slotsPerItem kind) : itemBase kind idx + j < UInt256.size :=
  Nat.lt_trans (Nat.add_lt_add_left hj _) (itemWindow_lt_size hidx)

theorem four_le_itemBase (kind : Kind) (idx : Nat) : 4 ≤ itemBase kind idx := by
  unfold itemBase QUEUE_OFFSET
  omega

/-- Item windows are laid out in increasing index order and do not overlap. -/
theorem itemWindow_le_of_lt {kind : Kind} {idx t : Nat} (h : idx < t) :
    itemBase kind idx + slotsPerItem kind ≤ itemBase kind t := by
  have : (idx + 1) * slotsPerItem kind ≤ t * slotsPerItem kind :=
    Nat.mul_le_mul_right _ h
  unfold itemBase
  have hexp : (idx + 1) * slotsPerItem kind =
      idx * slotsPerItem kind + slotsPerItem kind := by ring
  omega

/-! ## Reading `queueOf` -/

theorem queueOf_eq (kind : Kind) {σ : Storage}
    (h : queueHead σ ≤ queueTail σ) :
    queueOf kind σ =
      (List.range (queueTail σ - queueHead σ)).map
        (fun i => decodeItem kind σ (queueHead σ + i)) := by
  unfold queueOf
  simp [h]

/-- `decodeItem` only reads the item's own window. -/
theorem decodeItem_congr (kind : Kind) {σ τ : Storage} {idx : Nat}
    (h : ∀ j, j < slotsPerItem kind →
      loadNat σ (itemBase kind idx + j) = loadNat τ (itemBase kind idx + j)) :
    decodeItem kind σ idx = decodeItem kind τ idx := by
  have hwords : loadItemWords kind σ idx = loadItemWords kind τ idx := by
    unfold loadItemWords
    refine List.map_congr_left ?_
    intro j hj
    exact h j (List.mem_range.mp hj)
  cases kind with
  | deposit =>
      unfold decodeItem decodeDepositCalldata
      rw [hwords]
  | exit =>
      have h0 : loadNat σ (itemBase .exit idx) = loadNat τ (itemBase .exit idx) := by
        have := h 0 (by decide)
        simpa using this
      unfold decodeItem decodeExitSource decodeExitPubkey
      rw [hwords, h0]

/-! ## Constructor images

`depositPost` / `exitPost` are `PControl1.Ctor`'s post-images of the two
pinned init programs; `Ctor.ctor_posts_from_empty` is the CFG run that
produces them from the empty map.
-/

def ctorStorage : Kind → Storage
  | .deposit => depositPost default
  | .exit => exitPost default

theorem ctorStorage_deposit : ctorStorage .deposit = (default : Storage) := rfl

theorem ctorStorage_head (kind : Kind) : queueHead (ctorStorage kind) = 0 := by
  cases kind with
  | deposit => rfl
  | exit =>
      show loadNat (setSlot (default : Storage) 0 inhibitor) QUEUE_HEAD = 0
      rw [loadNat_setSlot_ne (by simp [UInt256.size])
        (by simp [QUEUE_HEAD, UInt256.size]) (by simp [inhibitor, UInt256.size])
        (by decide)]
      rfl

theorem ctorStorage_tail (kind : Kind) : queueTail (ctorStorage kind) = 0 := by
  cases kind with
  | deposit => rfl
  | exit =>
      show loadNat (setSlot (default : Storage) 0 inhibitor) QUEUE_TAIL = 0
      rw [loadNat_setSlot_ne (by simp [UInt256.size])
        (by simp [QUEUE_TAIL, UInt256.size]) (by simp [inhibitor, UInt256.size])
        (by decide)]
      rfl

theorem ctorStorage_count (kind : Kind) : slotCount (ctorStorage kind) = 0 := by
  cases kind with
  | deposit => rfl
  | exit =>
      show loadNat (setSlot (default : Storage) 0 inhibitor) SLOT_COUNT = 0
      rw [loadNat_setSlot_ne (by simp [UInt256.size])
        (by simp [SLOT_COUNT, UInt256.size]) (by simp [inhibitor, UInt256.size])
        (by decide)]
      rfl

theorem ctorStorage_excess_deposit : slotExcess (ctorStorage .deposit) = 0 :=
  Eip8282.Audit.Guarantees.PControl1.Ctor.slotExcess_default

theorem ctorStorage_excess_exit :
    slotExcess (ctorStorage .exit) = inhibitor :=
  Eip8282.Audit.Guarantees.PControl1.Ctor.slotExcess_exitPost _

/-- Both constructor post-images are `WellFormed`: pointers start at `0`. -/
theorem ctorStorage_wellFormed (kind : Kind) :
    WellFormed kind (ctorStorage kind) := by
  rw [wellFormed_iff, ctorStorage_head, ctorStorage_tail]
  exact empty_queue_pointers kind

theorem ctorStorage_queue (kind : Kind) : queueOf kind (ctorStorage kind) = [] :=
  queueOf_empty_of_eq kind _ (by rw [ctorStorage_head, ctorStorage_tail])

/-- The deposit constructor deploys `Model.initialDeposit`, and the exit
constructor deploys `Model.initialExit`. Both are *derived* from the pinned
init programs' storage post-images, not posited. -/
theorem ctorStorage_toModel (kind : Kind) :
    toModel kind (ctorStorage kind) 0 =
      match kind with
      | .deposit => initialDeposit
      | .exit => initialExit := by
  cases kind with
  | deposit =>
      unfold toModel initialDeposit
      rw [ctorStorage_excess_deposit, ctorStorage_count, ctorStorage_queue]
  | exit =>
      unfold toModel initialExit
      rw [ctorStorage_excess_exit, ctorStorage_count, ctorStorage_queue]

theorem ctorStorage_reachable (kind : Kind) :
    Reachable (toModel kind (ctorStorage kind) 0) := by
  cases kind with
  | deposit => rw [ctorStorage_toModel .deposit]; exact Reachable.deposit
  | exit => rw [ctorStorage_toModel .exit]; exact Reachable.exit

/-! ## User submission: the packed append -/

/-- Storage effect of a successful user submission: the packed item words
land at `QUEUE_TAIL`, then `SLOT_COUNT` and `QUEUE_TAIL` increment. -/
def applyUser (kind : Kind) (σ : Storage) (ws : List Nat) : Storage :=
  setSlot
    (setSlot (writeWords σ (itemBase kind (queueTail σ)) ws)
      SLOT_COUNT (slotCount σ + 1))
    QUEUE_TAIL (queueTail σ + 1)

/-- The record the freshly written window decodes to. Reading it back out of
the post-image is what makes this a theorem about *whatever* the assembly
wrote, not about an assumed encoding. -/
def appendedRecord (kind : Kind) (σ : Storage) (ws : List Nat) : Record :=
  decodeItem kind (applyUser kind σ ws) (queueTail σ)

def appendedCalldata (kind : Kind) (σ : Storage) (ws : List Nat) : List Byte :=
  match kind with
  | .deposit => decodeDepositCalldata (applyUser kind σ ws) (queueTail σ)
  | .exit => decodeExitPubkey (applyUser kind σ ws) (queueTail σ)

def appendedCaller (kind : Kind) (σ : Storage) (ws : List Nat) : Address :=
  match kind with
  | .deposit => 0
  | .exit => decodeExitSource (applyUser kind σ ws) (queueTail σ)

section UserLemmas

variable {kind : Kind} {σ : Storage} {ws : List Nat}

/-- Campaign-side conditions for one packed append. -/
structure AppendHyp (kind : Kind) (σ : Storage) (ws : List Nat) : Prop where
  wellFormed : WellFormed kind σ
  len : ws.length = slotsPerItem kind
  words : ∀ w ∈ ws, w < UInt256.size
  count : slotCount σ + 1 < UInt256.size
  tail : queueTail σ + 1 < 2 ^ 64

private theorem window_bound (h : AppendHyp kind σ ws) :
    itemBase kind (queueTail σ) + ws.length < UInt256.size := by
  rw [h.len]
  exact itemWindow_lt_size (Nat.lt_of_succ_lt h.tail)

/-- The bumped `QUEUE_TAIL` still fits a 256-bit word. `omega` cannot project
this out of `AppendHyp` on its own, so it is named once here. -/
private theorem tail_succ_lt_size (h : AppendHyp kind σ ws) :
    queueTail σ + 1 < UInt256.size := by
  have ht := h.tail
  have : (2:Nat) ^ 64 < UInt256.size := by simp [UInt256.size]
  omega

/-- Control slots survive the packed-item store: item windows start at 4. -/
private theorem load_control_writeWords (h : AppendHyp kind σ ws) {q : Nat}
    (hq : q < 4) :
    loadNat (writeWords σ (itemBase kind (queueTail σ)) ws) q = loadNat σ q := by
  have hbase := four_le_itemBase kind (queueTail σ)
  exact loadNat_writeWords_outside ws σ _ q (window_bound h)
    (by simp [UInt256.size]; omega) h.words (Or.inl (by omega))

theorem applyUser_tail (h : AppendHyp kind σ ws) :
    queueTail (applyUser kind σ ws) = queueTail σ + 1 := by
  have hlt : queueTail σ + 1 < UInt256.size := tail_succ_lt_size h
  exact loadNat_setSlot_self (by simp [QUEUE_TAIL, UInt256.size]) hlt

theorem applyUser_count (h : AppendHyp kind σ ws) :
    slotCount (applyUser kind σ ws) = slotCount σ + 1 := by
  have hlt : queueTail σ + 1 < UInt256.size := tail_succ_lt_size h
  unfold applyUser slotCount
  rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
      (by simp [SLOT_COUNT, UInt256.size]) hlt (by decide)]
  exact loadNat_setSlot_self (by simp [SLOT_COUNT, UInt256.size]) h.count

theorem applyUser_head (h : AppendHyp kind σ ws) :
    queueHead (applyUser kind σ ws) = queueHead σ := by
  have hlt : queueTail σ + 1 < UInt256.size := tail_succ_lt_size h
  unfold applyUser queueHead
  rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
      (by simp [QUEUE_HEAD, UInt256.size]) hlt (by decide),
    loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size])
      (by simp [QUEUE_HEAD, UInt256.size]) h.count (by decide)]
  exact load_control_writeWords h (by simp [QUEUE_HEAD])

theorem applyUser_excess (h : AppendHyp kind σ ws) :
    slotExcess (applyUser kind σ ws) = slotExcess σ := by
  have hlt : queueTail σ + 1 < UInt256.size := tail_succ_lt_size h
  unfold applyUser slotExcess
  rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
      (by simp [SLOT_EXCESS, UInt256.size]) hlt (by decide),
    loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size])
      (by simp [SLOT_EXCESS, UInt256.size]) h.count (by decide)]
  exact load_control_writeWords h (by simp [SLOT_EXCESS])

/-- Already-queued items are untouched by the append. -/
theorem applyUser_old_item (h : AppendHyp kind σ ws) {idx j : Nat}
    (hidx : idx < queueTail σ) (hj : j < slotsPerItem kind) :
    loadNat (applyUser kind σ ws) (itemBase kind idx + j) =
      loadNat σ (itemBase kind idx + j) := by
  have htail64 : queueTail σ < 2 ^ 64 := Nat.lt_of_succ_lt h.tail
  have hidx64 : idx < 2 ^ 64 := Nat.lt_trans hidx htail64
  have hqlt : itemBase kind idx + j < UInt256.size := itemSlot_lt_size hidx64 hj
  have hlt : queueTail σ + 1 < UInt256.size := tail_succ_lt_size h
  have hbase := four_le_itemBase kind idx
  have hbelow : itemBase kind idx + j < itemBase kind (queueTail σ) := by
    have := itemWindow_le_of_lt (kind := kind) hidx
    omega
  unfold applyUser
  rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size]) hqlt hlt
      (by simp [QUEUE_TAIL]; omega),
    loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size]) hqlt h.count
      (by simp [SLOT_COUNT]; omega)]
  exact loadNat_writeWords_outside ws σ _ _ (window_bound h) hqlt h.words
    (Or.inl hbelow)

/-- The queue grows by exactly the record the new window decodes to. -/
theorem queueOf_applyUser (h : AppendHyp kind σ ws) :
    queueOf kind (applyUser kind σ ws) =
      queueOf kind σ ++ [appendedRecord kind σ ws] := by
  have hle := head_le_tail h.wellFormed
  have hhead := applyUser_head h
  have htail := applyUser_tail h
  have hle' : queueHead (applyUser kind σ ws) ≤ queueTail (applyUser kind σ ws) := by
    rw [hhead, htail]; omega
  rw [queueOf_eq kind hle', queueOf_eq kind hle, hhead, htail]
  have hsub : queueTail σ + 1 - queueHead σ = (queueTail σ - queueHead σ) + 1 := by
    omega
  rw [hsub, List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left ?_
    intro i hi
    have hi' : i < queueTail σ - queueHead σ := List.mem_range.mp hi
    refine decodeItem_congr kind ?_
    intro j hj
    exact applyUser_old_item h (by omega) hj
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    unfold appendedRecord
    congr 1
    omega

end UserLemmas

/-! ## System call: the bounded drain -/

def drainCount (kind : Kind) (σ : Storage) : Nat :=
  min (capOf kind) (queueTail σ - queueHead σ)

/-- `Model.nextExcess` reads only kind, `SLOT_EXCESS` and `SLOT_COUNT`. -/
def nextExcessOf (kind : Kind) (σ : Storage) (calldataNonempty : Bool) : Nat :=
  nextExcess (toModel kind σ 0) calldataNonempty

theorem nextExcess_toModel (kind : Kind) (σ : Storage) (bal : Wei) (b : Bool) :
    nextExcess (toModel kind σ bal) b = nextExcessOf kind σ b := rfl

/-- The two control-word `SSTORE`s a system call always performs. -/
def systemControlWrite (kind : Kind) (σ : Storage) (calldataNonempty : Bool) : Storage :=
  setSlot (setSlot σ SLOT_EXCESS (nextExcessOf kind σ calldataNonempty)) SLOT_COUNT 0

/-- Storage effect of a system call: rewrite `SLOT_EXCESS`, zero
`SLOT_COUNT`, advance `QUEUE_HEAD` past the drained items, and reset both
pointers to `0` when that empties the queue. -/
def applySystem (kind : Kind) (σ : Storage) (calldataNonempty : Bool) : Storage :=
  if queueHead σ + drainCount kind σ = queueTail σ then
    setSlot (setSlot (systemControlWrite kind σ calldataNonempty) QUEUE_HEAD 0)
      QUEUE_TAIL 0
  else
    setSlot (systemControlWrite kind σ calldataNonempty) QUEUE_HEAD
      (queueHead σ + drainCount kind σ)

section SystemLemmas

variable {kind : Kind} {σ : Storage} {b : Bool}

/-- Campaign-side conditions for one system drain. -/
structure DrainHyp (kind : Kind) (σ : Storage) : Prop where
  wellFormed : WellFormed kind σ
  noWrap : slotExcess σ + slotCount σ < UInt256.size

private theorem nextExcess_lt_size (h : DrainHyp kind σ) (b : Bool) :
    nextExcessOf kind σ b < UInt256.size := by
  have hinh : inhibitor < UInt256.size := by simp [inhibitor, UInt256.size]
  unfold nextExcessOf nextExcess
  split
  · exact hinh
  · split
    · simp [UInt256.size]
    · split
      · have := h.noWrap
        simp only [toModel_excess, toModel_count]
        omega
      · simp [UInt256.size]

private theorem head_lt_size (h : DrainHyp kind σ) :
    queueHead σ + drainCount kind σ < UInt256.size := by
  have ht := tail_lt_2_64 h.wellFormed
  have hle := head_le_tail h.wellFormed
  have hd : drainCount kind σ ≤ queueTail σ - queueHead σ :=
    Nat.min_le_right _ _
  have : (2:Nat) ^ 64 < UInt256.size := by simp [UInt256.size]
  omega

private theorem load_item_applySystem (h : DrainHyp kind σ) {q : Nat}
    (hq4 : 4 ≤ q) (hqlt : q < UInt256.size) :
    loadNat (applySystem kind σ b) q = loadNat σ q := by
  have hE := nextExcess_lt_size h b
  have hH := head_lt_size h
  unfold applySystem systemControlWrite
  split
  · rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size]) hqlt
        (by simp [UInt256.size]) (by simp [QUEUE_TAIL]; omega),
      loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size]) hqlt
        (by simp [UInt256.size]) (by simp [QUEUE_HEAD]; omega),
      loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size]) hqlt
        (by simp [UInt256.size]) (by simp [SLOT_COUNT]; omega),
      loadNat_setSlot_ne (by simp [SLOT_EXCESS, UInt256.size]) hqlt hE
        (by simp [SLOT_EXCESS]; omega)]
  · rw [loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size]) hqlt hH
        (by simp [QUEUE_HEAD]; omega),
      loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size]) hqlt
        (by simp [UInt256.size]) (by simp [SLOT_COUNT]; omega),
      loadNat_setSlot_ne (by simp [SLOT_EXCESS, UInt256.size]) hqlt hE
        (by simp [SLOT_EXCESS]; omega)]

theorem applySystem_excess (h : DrainHyp kind σ) :
    slotExcess (applySystem kind σ b) = nextExcessOf kind σ b := by
  have hE := nextExcess_lt_size h b
  have hH := head_lt_size h
  unfold applySystem systemControlWrite slotExcess
  split
  · rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
        (by simp [SLOT_EXCESS, UInt256.size]) (by simp [UInt256.size]) (by decide),
      loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size])
        (by simp [SLOT_EXCESS, UInt256.size]) (by simp [UInt256.size]) (by decide),
      loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size])
        (by simp [SLOT_EXCESS, UInt256.size]) (by simp [UInt256.size]) (by decide)]
    exact loadNat_setSlot_self (by simp [SLOT_EXCESS, UInt256.size]) hE
  · rw [loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size])
        (by simp [SLOT_EXCESS, UInt256.size]) hH (by decide),
      loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size])
        (by simp [SLOT_EXCESS, UInt256.size]) (by simp [UInt256.size]) (by decide)]
    exact loadNat_setSlot_self (by simp [SLOT_EXCESS, UInt256.size]) hE

theorem applySystem_count (h : DrainHyp kind σ) :
    slotCount (applySystem kind σ b) = 0 := by
  have hH := head_lt_size h
  unfold applySystem systemControlWrite slotCount
  split
  · rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
        (by simp [SLOT_COUNT, UInt256.size]) (by simp [UInt256.size]) (by decide),
      loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size])
        (by simp [SLOT_COUNT, UInt256.size]) (by simp [UInt256.size]) (by decide)]
    exact loadNat_setSlot_self (by simp [SLOT_COUNT, UInt256.size])
      (by simp [UInt256.size])
  · rw [loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size])
        (by simp [SLOT_COUNT, UInt256.size]) hH (by decide)]
    exact loadNat_setSlot_self (by simp [SLOT_COUNT, UInt256.size])
      (by simp [UInt256.size])

theorem applySystem_pointers (h : DrainHyp kind σ) :
    if queueHead σ + drainCount kind σ = queueTail σ then
      queueHead (applySystem kind σ b) = 0 ∧ queueTail (applySystem kind σ b) = 0
    else
      queueHead (applySystem kind σ b) = queueHead σ + drainCount kind σ ∧
        queueTail (applySystem kind σ b) = queueTail σ := by
  have hE := nextExcess_lt_size h b
  have hH := head_lt_size h
  have htlt : queueTail σ < UInt256.size := by
    have := tail_lt_2_64 h.wellFormed
    have : (2:Nat) ^ 64 < UInt256.size := by simp [UInt256.size]
    omega
  by_cases hreset : queueHead σ + drainCount kind σ = queueTail σ
  · rw [if_pos hreset]
    have hEq : applySystem kind σ b =
        setSlot (setSlot (systemControlWrite kind σ b) QUEUE_HEAD 0) QUEUE_TAIL 0 := by
      unfold applySystem
      rw [if_pos hreset]
    rw [hEq]
    constructor
    · show loadNat _ QUEUE_HEAD = 0
      rw [loadNat_setSlot_ne (by simp [QUEUE_TAIL, UInt256.size])
        (by simp [QUEUE_HEAD, UInt256.size]) (by simp [UInt256.size]) (by decide)]
      exact loadNat_setSlot_self (by simp [QUEUE_HEAD, UInt256.size])
        (by simp [UInt256.size])
    · show loadNat _ QUEUE_TAIL = 0
      exact loadNat_setSlot_self (by simp [QUEUE_TAIL, UInt256.size])
        (by simp [UInt256.size])
  · rw [if_neg hreset]
    have hEq : applySystem kind σ b =
        setSlot (systemControlWrite kind σ b) QUEUE_HEAD
          (queueHead σ + drainCount kind σ) := by
      unfold applySystem
      rw [if_neg hreset]
    rw [hEq]
    constructor
    · show loadNat _ QUEUE_HEAD = _
      exact loadNat_setSlot_self (by simp [QUEUE_HEAD, UInt256.size]) hH
    · show loadNat _ QUEUE_TAIL = _
      unfold systemControlWrite
      rw [loadNat_setSlot_ne (by simp [QUEUE_HEAD, UInt256.size])
          (by simp [QUEUE_TAIL, UInt256.size]) hH (by decide),
        loadNat_setSlot_ne (by simp [SLOT_COUNT, UInt256.size])
          (by simp [QUEUE_TAIL, UInt256.size]) (by simp [UInt256.size]) (by decide),
        loadNat_setSlot_ne (by simp [SLOT_EXCESS, UInt256.size])
          (by simp [QUEUE_TAIL, UInt256.size]) hE (by decide)]
      rfl

theorem applySystem_wellFormed (h : DrainHyp kind σ) :
    WellFormed kind (applySystem kind σ b) := by
  have hptr := applySystem_pointers (kind := kind) (σ := σ) (b := b) h
  have hle := head_le_tail h.wellFormed
  have ht64 := tail_lt_2_64 h.wellFormed
  have hnb := item_base_no_wrap h.wellFormed
  rw [wellFormed_iff]
  by_cases hreset : queueHead σ + drainCount kind σ = queueTail σ
  · rw [if_pos hreset] at hptr
    rw [hptr.1, hptr.2]
    exact empty_queue_pointers kind
  · rw [if_neg hreset] at hptr
    rw [hptr.1, hptr.2]
    have hd : drainCount kind σ ≤ queueTail σ - queueHead σ := Nat.min_le_right _ _
    exact ⟨by omega, ht64, hnb⟩

private theorem map_range_drop {α : Type} :
    ∀ (n m : Nat) (f : Nat → α),
      ((List.range m).map f).drop n = (List.range (m - n)).map (fun i => f (n + i))
  | 0, m, f => by simp
  | _ + 1, 0, _ => by simp
  | n + 1, m + 1, f => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.drop_succ_cons,
        map_range_drop n m (f ∘ Nat.succ)]
      have hr : m + 1 - (n + 1) = m - n := by omega
      rw [hr]
      refine List.map_congr_left ?_
      intro i _
      show f (Nat.succ (n + i)) = f (n + 1 + i)
      congr 1
      omega

theorem queueOf_applySystem (h : DrainHyp kind σ) :
    queueOf kind (applySystem kind σ b) =
      (queueOf kind σ).drop (capOf kind) := by
  have hptr := applySystem_pointers (kind := kind) (σ := σ) (b := b) h
  have hle := head_le_tail h.wellFormed
  have ht64 := tail_lt_2_64 h.wellFormed
  have hsame : ∀ idx j, idx < queueTail σ → j < slotsPerItem kind →
      loadNat (applySystem kind σ b) (itemBase kind idx + j) =
        loadNat σ (itemBase kind idx + j) := by
    intro idx j hidx hj
    have hidx64 : idx < 2 ^ 64 := Nat.lt_trans hidx ht64
    exact load_item_applySystem h (by have := four_le_itemBase kind idx; omega)
      (itemSlot_lt_size hidx64 hj)
  rw [queueOf_eq kind hle]
  by_cases hreset : queueHead σ + drainCount kind σ = queueTail σ
  · rw [if_pos hreset] at hptr
    have hempty : queueOf kind (applySystem kind σ b) = [] :=
      queueOf_empty_of_eq kind _ (by rw [hptr.1, hptr.2])
    rw [hempty]
    have hd : drainCount kind σ = queueTail σ - queueHead σ := by omega
    have hcap : queueTail σ - queueHead σ ≤ capOf kind := by
      have := Nat.min_le_left (capOf kind) (queueTail σ - queueHead σ)
      unfold drainCount at hd
      omega
    symm
    refine List.drop_eq_nil_of_le ?_
    simpa using hcap
  · rw [if_neg hreset] at hptr
    have hd : drainCount kind σ = capOf kind := by
      unfold drainCount at hreset ⊢
      omega
    have hcaple : queueHead σ + capOf kind ≤ queueTail σ := by
      have hmin : drainCount kind σ ≤ queueTail σ - queueHead σ :=
        Nat.min_le_right _ _
      omega
    rw [queueOf_eq kind (by rw [hptr.1, hptr.2, hd]; exact hcaple), hptr.1, hptr.2, hd,
      map_range_drop]
    have hlen : queueTail σ - (queueHead σ + capOf kind) =
        queueTail σ - queueHead σ - capOf kind := by omega
    rw [hlen]
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < queueTail σ - queueHead σ - capOf kind := List.mem_range.mp hi
    have heq : queueHead σ + capOf kind + i = queueHead σ + (capOf kind + i) := by
      omega
    rw [heq]
    refine decodeItem_congr kind ?_
    intro j hj
    exact hsame _ j (by omega) hj

end SystemLemmas

/-! ## Refinement: the storage transitions are the model's calls -/

theorem toModel_applyUser {kind : Kind} {σ : Storage} {ws : List Nat}
    (h : AppendHyp kind σ ws) (bal value : Wei) :
    toModel kind (applyUser kind σ ws) (bal + value) =
      appendRecord (toModel kind σ bal) (appendedCaller kind σ ws)
        (appendedCalldata kind σ ws) value := by
  unfold toModel appendRecord
  rw [applyUser_excess h, applyUser_count h, queueOf_applyUser h]
  cases kind with
  | deposit =>
      simp only [appendedRecord, appendedCalldata, decodeItem]
  | exit =>
      simp only [appendedRecord, appendedCalldata, appendedCaller, decodeItem]

/-- A successful submission on a reachable image is exactly `Model.userCall`. -/
theorem toModel_applyUser_eq_userCall {kind : Kind} {σ : Storage} {ws : List Nat}
    (h : AppendHyp kind σ ws) (bal value : Wei)
    (hInh : inhibited (toModel kind σ bal) = false)
    (hne : appendedCalldata kind σ ws ≠ [])
    (hAdm : admissible (toModel kind σ bal) (appendedCalldata kind σ ws) value = true) :
    toModel kind (applyUser kind σ ws) (bal + value) =
      (userCall (toModel kind σ bal) (appendedCaller kind σ ws)
        (appendedCalldata kind σ ws) value).state := by
  rw [toModel_applyUser h bal value]
  unfold userCall
  simp [hInh, hne, hAdm]

theorem toModel_applySystem {kind : Kind} {σ : Storage} {b : Bool}
    (h : DrainHyp kind σ) (bal : Wei) :
    toModel kind (applySystem kind σ b) bal =
      (systemCall (toModel kind σ bal) b).state := by
  unfold systemCall toModel
  rw [applySystem_excess h, applySystem_count h, queueOf_applySystem h]
  rfl

/-- Appending preserves `WellFormed`. -/
theorem applyUser_wellFormed {kind : Kind} {σ : Storage} {ws : List Nat}
    (h : AppendHyp kind σ ws) : WellFormed kind (applyUser kind σ ws) := by
  have hle := head_le_tail h.wellFormed
  rw [wellFormed_iff, applyUser_head h, applyUser_tail h]
  refine ⟨by omega, h.tail, ?_⟩
  have hspi := slotsPerItem_le_six kind
  have h1 : (queueTail σ + 1) * slotsPerItem kind ≤ (queueTail σ + 1) * 6 :=
    Nat.mul_le_mul_left _ hspi
  have h2 : (queueTail σ + 1) * 6 ≤ 2 ^ 64 * 6 :=
    Nat.mul_le_mul_right 6 (Nat.le_of_lt h.tail)
  have h3 : 2 ^ 64 * 6 + 10 < UInt256.size := by simp [UInt256.size]
  unfold QUEUE_OFFSET
  omega

/-! ## Reachable storage images -/

/-- Storage images built from the pinned constructor post-image by successful
submissions and system drains. Balance is tracked alongside because
`Model.State` carries it and `Storage` does not. -/
inductive ReachableStorage (kind : Kind) : Storage → Wei → Prop where
  | ctor : ReachableStorage kind (ctorStorage kind) 0
  | user {σ : Storage} {bal : Wei} (h : ReachableStorage kind σ bal)
      (ws : List Nat) (value : Wei)
      (len : ws.length = slotsPerItem kind)
      (words : ∀ w ∈ ws, w < UInt256.size)
      (count : slotCount σ + 1 < UInt256.size)
      (tail : queueTail σ + 1 < 2 ^ 64)
      (notInhibited : inhibited (toModel kind σ bal) = false)
      (nonempty : appendedCalldata kind σ ws ≠ [])
      (adm : admissible (toModel kind σ bal) (appendedCalldata kind σ ws) value = true) :
      ReachableStorage kind (applyUser kind σ ws) (bal + value)
  | system {σ : Storage} {bal : Wei} (h : ReachableStorage kind σ bal) (b : Bool)
      (noWrap : slotExcess σ + slotCount σ < UInt256.size) :
      ReachableStorage kind (applySystem kind σ b) bal

/-- Every reachable image is `WellFormed`, so the `∀ σ, WellFormed kind σ → …`
of the three registered parents covers all of them. -/
theorem ReachableStorage.wellFormed {kind : Kind} {σ : Storage} {bal : Wei}
    (h : ReachableStorage kind σ bal) : WellFormed kind σ := by
  induction h with
  | ctor => exact ctorStorage_wellFormed kind
  | user _ ws _ len words count tail _ _ _ ih =>
      exact applyUser_wellFormed ⟨ih, len, words, count, tail⟩
  | system _ _ noWrap ih => exact applySystem_wellFormed ⟨ih, noWrap⟩

/-- Every reachable image abstracts to a `Model.Reachable` state. Derived from
the two constructors and the two calls, not assumed. -/
theorem ReachableStorage.model_reachable {kind : Kind} {σ : Storage} {bal : Wei}
    (h : ReachableStorage kind σ bal) : Reachable (toModel kind σ bal) := by
  induction h with
  | ctor => exact ctorStorage_reachable kind
  | @user σ bal hr ws value len words count tail notInhibited nonempty adm ih =>
      refine Reachable.step ih
        (.user (appendedCaller kind σ ws) (appendedCalldata kind σ ws) value) ?_
      exact toModel_applyUser_eq_userCall
        ⟨hr.wellFormed, len, words, count, tail⟩ bal value notInhibited nonempty adm
  | @system σ bal hr b noWrap ih =>
      refine Reachable.step ih (.system b) ?_
      exact toModel_applySystem ⟨hr.wellFormed, noWrap⟩ bal

/-- A reachable image supplies the `CallHyp` the three registered parents
quantify over, at any campaign-legal gas, fuel and caller. -/
def ReachableStorage.callHyp {kind : Kind} {σ : Storage} {bal : Wei}
    (h : ReachableStorage kind σ bal) (gas fuel : Nat)
    (hgas : gas ≥ campaignGasBound) (hfuel : fuel ≥ campaignFuelBound)
    (caller : UInt256) : CallHyp kind σ where
  wellFormed := h.wellFormed
  gas := gas
  gas_ge := hgas
  fuel := fuel
  fuel_ge := hfuel
  caller := caller
  isUser := decide (isUserCaller caller)
  caller_class := by simp

/-- The registered parents are not vacuous on the deployed images: both
constructor post-images are reachable, `WellFormed`, and abstract to the
specified initial states. -/
theorem ctorStorage_reachableStorage (kind : Kind) :
    ReachableStorage kind (ctorStorage kind) 0 :=
  ReachableStorage.ctor

end Eip8282.Audit.Reachable
