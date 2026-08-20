import EvmYul.Maps.StorageMap
import Eip8282.Audit.Model

/-!
Packed EIP-8282 storage shape used by every `∀` parent.

`∀` over raw EVM storage is the wrong theorem. The assembly treats slots 0–3 as
the control words and `[QUEUE_HEAD, QUEUE_TAIL)` as a dense packed FIFO.
Stale words *outside* that window are unconstrained (P-DRAIN-1).

This module is the F2 foundation artifact. It does not execute `Ξ`.
-/

namespace Eip8282.Audit.WellFormed

open EvmYul
open Eip8282.Audit.Model

/-- `QUEUE_OFFSET` in both pinned runtimes. -/
def QUEUE_OFFSET : Nat := 4

def SLOT_EXCESS : Nat := 0
def SLOT_COUNT : Nat := 1
def QUEUE_HEAD : Nat := 2
def QUEUE_TAIL : Nat := 3

def slotsPerItem : Kind → Nat
  | .deposit => 6
  | .exit => 3

def itemBytes : Kind → Nat
  | .deposit => 184
  | .exit => 48

/-- Big-endian byte `i` of a 32-byte word (`i = 0` is the MSB). -/
def byteAtBE (w i : Nat) : Nat :=
  if i ≥ 32 then 0 else (w / 256 ^ (31 - i)) % 256

def wordToBytesBE (w : Nat) : List Byte :=
  (List.range 32).map (fun i => byteAtBE w i)

/-- Concatenate 32-byte words and take the first `n` bytes. -/
def wordsToBytes (words : List Nat) (n : Nat) : List Byte :=
  (words.flatMap wordToBytesBE).take n

def loadU256 (σ : Storage) (slot : Nat) : UInt256 :=
  σ.getD (UInt256.ofNat slot) (UInt256.ofNat 0)

def loadNat (σ : Storage) (slot : Nat) : Nat :=
  (loadU256 σ slot).toNat

def slotExcess (σ : Storage) : Nat := loadNat σ SLOT_EXCESS
def slotCount (σ : Storage) : Nat := loadNat σ SLOT_COUNT
def queueHead (σ : Storage) : Nat := loadNat σ QUEUE_HEAD
def queueTail (σ : Storage) : Nat := loadNat σ QUEUE_TAIL

/-- Base slot of packed item `idx` (the assembly uses `QUEUE_OFFSET + idx * SLOTS_PER_ITEM`). -/
def itemBase (kind : Kind) (idx : Nat) : Nat :=
  QUEUE_OFFSET + idx * slotsPerItem kind

def loadItemWords (kind : Kind) (σ : Storage) (idx : Nat) : List Nat :=
  (List.range (slotsPerItem kind)).map (fun j => loadNat σ (itemBase kind idx + j))

/-- 184-byte deposit calldata recovered from six `CALLDATALOAD` words. -/
def decodeDepositCalldata (σ : Storage) (idx : Nat) : List Byte :=
  wordsToBytes (loadItemWords .deposit σ idx) 184

/-- 48-byte exit pubkey recovered from the two pubkey words (source sits in word 0). -/
def decodeExitPubkey (σ : Storage) (idx : Nat) : List Byte :=
  let ws := loadItemWords .exit σ idx
  wordsToBytes (ws.drop 1) 48

/-- 20-byte source is the low 160 bits of the first packed exit word. -/
def decodeExitSource (σ : Storage) (idx : Nat) : Address :=
  loadNat σ (itemBase .exit idx) % 256 ^ 20

def decodeItem (kind : Kind) (σ : Storage) (idx : Nat) : Record :=
  match kind with
  | .deposit =>
      let cd := decodeDepositCalldata σ idx
      .deposit cd (depositAmount cd)
  | .exit =>
      .exit (decodeExitSource σ idx) (decodeExitPubkey σ idx)

/-- Logical FIFO: packed items `head .. tail-1`. Empty when `head = tail`.
If the pointer invariant is broken (`tail < head`) this returns `[]` rather
than wrapping — the assembly is not a ring buffer. -/
def queueOf (kind : Kind) (σ : Storage) : List Record :=
  let h := queueHead σ
  let t := queueTail σ
  if h ≤ t then
    (List.range (t - h)).map (fun i => decodeItem kind σ (h + i))
  else
    []

def toModel (kind : Kind) (σ : Storage) (balance : Wei := 0) : State :=
  { kind := kind
    storedExcess := slotExcess σ
    count := slotCount σ
    queue := queueOf kind σ
    balance := balance }

/-- Pointer invariant plus a bound that keeps `QUEUE_OFFSET + tail * slotsPerItem`
inside `UInt256` (so item bases cannot wrap). `2^64` is far above the Wave-5
`tail = 65` image and far below `2^256 / 6`. -/
def wellFormedB (kind : Kind) (σ : Storage) : Bool :=
  let h := queueHead σ
  let t := queueTail σ
  decide (h ≤ t) &&
    decide (t < 2 ^ 64) &&
    decide (QUEUE_OFFSET + t * slotsPerItem kind < UInt256.size)

/-- Pointer invariant on the decoded control words. Preferred form for `∀` hypotheses. -/
def IsWellFormed (kind : Kind) (head tail : Nat) : Prop :=
  head ≤ tail ∧
    tail < 2 ^ 64 ∧
    QUEUE_OFFSET + tail * slotsPerItem kind < UInt256.size

instance (kind : Kind) (head tail : Nat) : Decidable (IsWellFormed kind head tail) := by
  unfold IsWellFormed
  infer_instance

set_option linter.dupNamespace false in
/-- Packed-queue well-formedness of an EVM storage image. -/
def WellFormed (kind : Kind) (σ : Storage) : Prop :=
  wellFormedB kind σ = true

instance (kind : Kind) (σ : Storage) : Decidable (WellFormed kind σ) :=
  inferInstanceAs (Decidable (_ = true))

theorem isWellFormed_of_le (kind : Kind) {head tail : Nat}
    (hle : head ≤ tail) (tlt : tail < 2 ^ 64)
    (nb : QUEUE_OFFSET + tail * slotsPerItem kind < UInt256.size) :
    IsWellFormed kind head tail :=
  ⟨hle, tlt, nb⟩

theorem wellFormedB_iff (kind : Kind) (σ : Storage) :
    wellFormedB kind σ = true ↔
      IsWellFormed kind (queueHead σ) (queueTail σ) := by
  unfold wellFormedB IsWellFormed
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem wellFormed_iff (kind : Kind) (σ : Storage) :
    WellFormed kind σ ↔ IsWellFormed kind (queueHead σ) (queueTail σ) := by
  unfold WellFormed
  exact wellFormedB_iff kind σ

theorem head_le_tail {kind : Kind} {σ : Storage} (h : WellFormed kind σ) :
    queueHead σ ≤ queueTail σ :=
  (wellFormed_iff kind σ).mp h |>.1

theorem tail_lt_2_64 {kind : Kind} {σ : Storage} (h : WellFormed kind σ) :
    queueTail σ < 2 ^ 64 :=
  (wellFormed_iff kind σ).mp h |>.2.1

theorem item_base_no_wrap {kind : Kind} {σ : Storage} (h : WellFormed kind σ) :
    QUEUE_OFFSET + queueTail σ * slotsPerItem kind < UInt256.size :=
  (wellFormed_iff kind σ).mp h |>.2.2

@[simp] theorem toModel_kind (kind : Kind) (σ : Storage) (b : Wei) :
    (toModel kind σ b).kind = kind := rfl

@[simp] theorem toModel_excess (kind : Kind) (σ : Storage) (b : Wei) :
    (toModel kind σ b).storedExcess = slotExcess σ := rfl

@[simp] theorem toModel_count (kind : Kind) (σ : Storage) (b : Wei) :
    (toModel kind σ b).count = slotCount σ := rfl

@[simp] theorem toModel_queue (kind : Kind) (σ : Storage) (b : Wei) :
    (toModel kind σ b).queue = queueOf kind σ := rfl

@[simp] theorem toModel_balance (kind : Kind) (σ : Storage) (b : Wei) :
    (toModel kind σ b).balance = b := rfl

theorem inhibited_iff (kind : Kind) (σ : Storage) (b : Wei) :
    inhibited (toModel kind σ b) = true ↔ slotExcess σ = inhibitor := by
  unfold inhibited
  simp

theorem queueOf_empty_of_eq (kind : Kind) (σ : Storage)
    (h : queueHead σ = queueTail σ) :
    queueOf kind σ = [] := by
  unfold queueOf
  simp [h]

theorem queueOf_length {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    (queueOf kind σ).length = queueTail σ - queueHead σ := by
  have hle := head_le_tail wf
  unfold queueOf
  simp [hle]

/-- Helper matching `EvmRunner.storageFromList`, kept here so this module does
not depend on `Ξ`. -/
def storageFromList (pairs : List (Nat × Nat)) : Storage :=
  pairs.foldl
    (fun acc (k, v) => acc.insert (UInt256.ofNat k) (UInt256.ofNat v))
    default

/-- P-CONTROL-1 empty-queue image. -/
def ctlStorage (excess count : Nat) : Storage :=
  storageFromList [(0, excess), (1, count), (2, 0), (3, 0)]

/-- P-SUBMIT-1 live image (`head = 7`, `tail = 9`). -/
def liveStorage : Storage :=
  storageFromList [(0, 100), (1, 5), (2, 7), (3, 9)]

/-- P-SUBMIT-1 second image (`head = 2`, `tail = 6`). -/
def altStorage : Storage :=
  storageFromList [(0, 50), (1, 3), (2, 2), (3, 6)]

/-- Inhibited, reachable-shaped pointers. -/
def inhibitedStorage : Storage :=
  storageFromList [(0, 2 ^ 256 - 1), (1, 5), (2, 7), (3, 9)]

/-- Wave-5 / P-DRAIN-1 over-cap deposit image (`tail = 65`). -/
def depositQueue65Pointers : Storage :=
  storageFromList [(0, 100), (1, 5), (2, 0), (3, 65)]

/-- Empty storage: both pointers zero. Holds for either predeploy. -/
theorem default_wellFormed (kind : Kind) : WellFormed kind (default : Storage) := by
  cases kind <;> decide

/-- Pointer-only well-formedness of the campaign's concrete images. -/
theorem ctl_pointers : IsWellFormed .deposit 0 0 := by decide
theorem live_pointers : IsWellFormed .deposit 7 9 := by decide
theorem alt_pointers : IsWellFormed .deposit 2 6 := by decide
theorem inhibited_pointers : IsWellFormed .deposit 7 9 := by decide
theorem depositQueue65_pointers : IsWellFormed .deposit 0 65 := by decide
theorem exitOverCap_pointers : IsWellFormed .exit 0 17 := by decide

theorem empty_queue_pointers (kind : Kind) : IsWellFormed kind 0 0 := by
  cases kind <;> decide

end Eip8282.Audit.WellFormed
