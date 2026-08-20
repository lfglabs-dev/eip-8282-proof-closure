import Eip8282.Audit.Correspondence
import Eip8282.Audit.WellFormed
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Step

/-!
P-DRAIN-1 D1: system-path SSTORE footprint.

F4 left `A-ABSTRACT-TX` open; this module does **not** run `Ξ`. The system
caller lands at `read_requests` (F3). From there the only `SSTORE`s sit at
the F1 labels `update_head`, `reset_queue`, and `store_excess`; their keys
are the PUSH immediates `{SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL}`
= `{0,1,2,3}`. `accum_loop` is SLOAD/MSTORE of the return buffer.

Kill-line: deposit offset 483 / exit offset 313 is the `PUSH1 QUEUE_HEAD`
immediate of the partial-drain `SSTORE`. Retargeting that byte onto a queue
word makes the `PUSH1` immediate leave `{0,1,2,3}`, so
`system_sstore_keys_subset` is false of that mutant.
-/

namespace Eip8282.Audit.Guarantees.PDrain1.Footprint

open EvmYul
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model (Kind)

set_option maxRecDepth 20000

/-! ## Control slots -/

/-- System-path `SSTORE` keys. Same four words as `WellFormed`. -/
def controlKeys : List Nat :=
  [SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL]

theorem controlKeys_eq :
    controlKeys = [0, 1, 2, 3] := rfl

theorem mem_controlKeys_iff {k : Nat} :
    k ∈ controlKeys ↔
      k = SLOT_EXCESS ∨ k = SLOT_COUNT ∨ k = QUEUE_HEAD ∨ k = QUEUE_TAIL := by
  simp [controlKeys]

theorem controlKey_lt_offset {k : Nat} (h : k ∈ controlKeys) :
    k < QUEUE_OFFSET := by
  simp [controlKeys, SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL] at h
  unfold QUEUE_OFFSET
  omega

/-! ## System caller → `read_requests` (F3) -/

/-- Under `CallHyp` with `isUser = false`, the opening JUMPI lands on the
system subroutine. CFG-level; not a reduction of `X`. -/
theorem system_path_pc
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (hsys : h.isUser = false) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = readRequestsPc kind :=
  (callHyp_dispatch h hrun).1.mpr hsys

/-! ## Pinned windows at F1 labels

Small `fromHex` slices starting at the named JUMPDEST, matching the later
chunks of `depositRuntimeHex` / `exitRuntimeHex`. `opcodeAt` of the full
runtime does not unfold (`fromHexGo` is private).
-/

/-- `update_head` through the partial-drain `PUSH1 QUEUE_HEAD; SSTORE; JUMP`. -/
def depositUpdateHeadHex : String :=
  "5b91018092146101e957906002556101f456"

def exitUpdateHeadHex : String :=
  "5b910180921461013f579060025561014a56"

/-- `reset_queue` through both pointer `SSTORE`s and the `update_excess` JUMPDEST. -/
def depositResetQueueHex : String :=
  "5b90505f6002555f6003555b"

def exitResetQueueHex : String :=
  "5b90505f6002555f6003555b"

/-- `store_excess` through `RETURN`. -/
def depositStoreExcessHex : String :=
  "5b5f555f60015560b8025ff3"

def exitStoreExcessHex : String :=
  "5b5f555f6001556044025ff3"

def depositUpdateHeadWindow : ByteArray := fromHex depositUpdateHeadHex
def exitUpdateHeadWindow : ByteArray := fromHex exitUpdateHeadHex
def depositResetQueueWindow : ByteArray := fromHex depositResetQueueHex
def exitResetQueueWindow : ByteArray := fromHex exitResetQueueHex
def depositStoreExcessWindow : ByteArray := fromHex depositStoreExcessHex
def exitStoreExcessWindow : ByteArray := fromHex exitStoreExcessHex

/-- Windows start at the F1 JUMPDEST. -/
theorem deposit_update_head_window_pc : Deposit.update_head = 471 := rfl
theorem deposit_reset_queue_window_pc : Deposit.reset_queue = 489 := rfl
theorem deposit_store_excess_window_pc : Deposit.store_excess = 612 := rfl
theorem exit_update_head_window_pc : Exit.update_head = 301 := rfl
theorem exit_reset_queue_window_pc : Exit.reset_queue = 319 := rfl
theorem exit_store_excess_window_pc : Exit.store_excess = 442 := rfl

/-- Wave-6 kill-line: the `PUSH1 QUEUE_HEAD` immediate of the partial-drain
`SSTORE`. -/
theorem deposit_kill_line_immediate_pc :
    Deposit.update_head + 12 = 483 := rfl

theorem exit_kill_line_immediate_pc :
    Exit.update_head + 12 = 313 := rfl

/-! ### `update_head`: `PUSH1 QUEUE_HEAD; SSTORE` -/

theorem deposit_update_head_JUMPDEST :
    opcodeAt depositUpdateHeadWindow 0 = some (.JUMPDEST, none) := rfl

theorem deposit_update_head_PUSH1_QUEUE_HEAD :
    opcodeAt depositUpdateHeadWindow 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) := rfl

theorem deposit_update_head_SSTORE :
    opcodeAt depositUpdateHeadWindow 13 = some (.SSTORE, none) := rfl

theorem exit_update_head_JUMPDEST :
    opcodeAt exitUpdateHeadWindow 0 = some (.JUMPDEST, none) := rfl

theorem exit_update_head_PUSH1_QUEUE_HEAD :
    opcodeAt exitUpdateHeadWindow 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) := rfl

theorem exit_update_head_SSTORE :
    opcodeAt exitUpdateHeadWindow 13 = some (.SSTORE, none) := rfl

/-- The partial-drain `SSTORE` key is `QUEUE_HEAD` (= 2), both predeploys. -/
theorem update_head_sstore_key (kind : Kind) :
    opcodeAt (match kind with
        | .deposit => depositUpdateHeadWindow
        | .exit => exitUpdateHeadWindow) 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
    opcodeAt (match kind with
        | .deposit => depositUpdateHeadWindow
        | .exit => exitUpdateHeadWindow) 13 =
      some (.SSTORE, none) := by
  cases kind with
  | deposit =>
      exact ⟨deposit_update_head_PUSH1_QUEUE_HEAD, deposit_update_head_SSTORE⟩
  | exit =>
      exact ⟨exit_update_head_PUSH1_QUEUE_HEAD, exit_update_head_SSTORE⟩

/-! ### `reset_queue`: `PUSH0; PUSH1 QUEUE_HEAD; SSTORE` and
`PUSH0; PUSH1 QUEUE_TAIL; SSTORE` -/

theorem deposit_reset_queue_JUMPDEST :
    opcodeAt depositResetQueueWindow 0 = some (.JUMPDEST, none) := rfl

theorem deposit_reset_queue_PUSH0_head :
    opcodeAt depositResetQueueWindow 3 = some (.PUSH0, none) := rfl

theorem deposit_reset_queue_PUSH1_QUEUE_HEAD :
    opcodeAt depositResetQueueWindow 4 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) := rfl

theorem deposit_reset_queue_SSTORE_head :
    opcodeAt depositResetQueueWindow 6 = some (.SSTORE, none) := rfl

theorem deposit_reset_queue_PUSH0_tail :
    opcodeAt depositResetQueueWindow 7 = some (.PUSH0, none) := rfl

theorem deposit_reset_queue_PUSH1_QUEUE_TAIL :
    opcodeAt depositResetQueueWindow 8 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_TAIL, 1)) := rfl

theorem deposit_reset_queue_SSTORE_tail :
    opcodeAt depositResetQueueWindow 10 = some (.SSTORE, none) := rfl

theorem exit_reset_queue_JUMPDEST :
    opcodeAt exitResetQueueWindow 0 = some (.JUMPDEST, none) := rfl

theorem exit_reset_queue_PUSH0_head :
    opcodeAt exitResetQueueWindow 3 = some (.PUSH0, none) := rfl

theorem exit_reset_queue_PUSH1_QUEUE_HEAD :
    opcodeAt exitResetQueueWindow 4 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) := rfl

theorem exit_reset_queue_SSTORE_head :
    opcodeAt exitResetQueueWindow 6 = some (.SSTORE, none) := rfl

theorem exit_reset_queue_PUSH0_tail :
    opcodeAt exitResetQueueWindow 7 = some (.PUSH0, none) := rfl

theorem exit_reset_queue_PUSH1_QUEUE_TAIL :
    opcodeAt exitResetQueueWindow 8 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_TAIL, 1)) := rfl

theorem exit_reset_queue_SSTORE_tail :
    opcodeAt exitResetQueueWindow 10 = some (.SSTORE, none) := rfl

/-! ### `store_excess`: `PUSH0; SSTORE` (slot 0) and `PUSH0; PUSH1 1; SSTORE` -/

theorem deposit_store_excess_JUMPDEST :
    opcodeAt depositStoreExcessWindow 0 = some (.JUMPDEST, none) := rfl

theorem deposit_store_excess_PUSH0_SLOT_EXCESS :
    opcodeAt depositStoreExcessWindow 1 = some (.PUSH0, none) := rfl

theorem deposit_store_excess_SSTORE_excess :
    opcodeAt depositStoreExcessWindow 2 = some (.SSTORE, none) := rfl

theorem deposit_store_excess_PUSH0_value :
    opcodeAt depositStoreExcessWindow 3 = some (.PUSH0, none) := rfl

theorem deposit_store_excess_PUSH1_SLOT_COUNT :
    opcodeAt depositStoreExcessWindow 4 =
      some (.PUSH1, some (UInt256.ofNat SLOT_COUNT, 1)) := rfl

theorem deposit_store_excess_SSTORE_count :
    opcodeAt depositStoreExcessWindow 6 = some (.SSTORE, none) := rfl

theorem exit_store_excess_JUMPDEST :
    opcodeAt exitStoreExcessWindow 0 = some (.JUMPDEST, none) := rfl

theorem exit_store_excess_PUSH0_SLOT_EXCESS :
    opcodeAt exitStoreExcessWindow 1 = some (.PUSH0, none) := rfl

theorem exit_store_excess_SSTORE_excess :
    opcodeAt exitStoreExcessWindow 2 = some (.SSTORE, none) := rfl

theorem exit_store_excess_PUSH0_value :
    opcodeAt exitStoreExcessWindow 3 = some (.PUSH0, none) := rfl

theorem exit_store_excess_PUSH1_SLOT_COUNT :
    opcodeAt exitStoreExcessWindow 4 =
      some (.PUSH1, some (UInt256.ofNat SLOT_COUNT, 1)) := rfl

theorem exit_store_excess_SSTORE_count :
    opcodeAt exitStoreExcessWindow 6 = some (.SSTORE, none) := rfl

/-- `PUSH0; SSTORE` writes `SLOT_EXCESS` (= 0). -/
theorem store_excess_key_is_slot_excess :
    SLOT_EXCESS = 0 := rfl

/-! ## SSTORE keys of the system CFG

Five sites, both predeploys: partial HEAD, reset HEAD, reset TAIL, excess,
count. No other system-path `SSTORE` (see the `hasSstore` scans below).
-/

/-- Keys pushed immediately before each system-path `SSTORE`. Order:
`update_head`, `reset_queue` HEAD, `reset_queue` TAIL, `store_excess` excess,
`store_excess` count. Identical for both predeploys. -/
def systemSstoreKeys (_kind : Kind) : List Nat :=
  [QUEUE_HEAD, QUEUE_HEAD, QUEUE_TAIL, SLOT_EXCESS, SLOT_COUNT]

theorem systemSstoreKeys_eq (kind : Kind) :
    systemSstoreKeys kind = [2, 2, 3, 0, 1] := by
  cases kind <;> rfl

theorem systemSstoreKeys_subset_control (kind : Kind) :
    ∀ key ∈ systemSstoreKeys kind, key ∈ controlKeys := by
  intro key hk
  rw [systemSstoreKeys_eq] at hk
  simp [controlKeys, SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL]
  simp at hk
  rcases hk with h | h | h | h | h <;> omega

/-- Opcode-at-PC package: every system-path `SSTORE` is preceded by a PUSH of
a control slot. Both predeploys. -/
theorem system_sstore_opcodes (kind : Kind) :
    opcodeAt (match kind with
        | .deposit => depositUpdateHeadWindow
        | .exit => exitUpdateHeadWindow) 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
    opcodeAt (match kind with
        | .deposit => depositUpdateHeadWindow
        | .exit => exitUpdateHeadWindow) 13 =
      some (.SSTORE, none) ∧
    opcodeAt (match kind with
        | .deposit => depositResetQueueWindow
        | .exit => exitResetQueueWindow) 4 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
    opcodeAt (match kind with
        | .deposit => depositResetQueueWindow
        | .exit => exitResetQueueWindow) 6 =
      some (.SSTORE, none) ∧
    opcodeAt (match kind with
        | .deposit => depositResetQueueWindow
        | .exit => exitResetQueueWindow) 8 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_TAIL, 1)) ∧
    opcodeAt (match kind with
        | .deposit => depositResetQueueWindow
        | .exit => exitResetQueueWindow) 10 =
      some (.SSTORE, none) ∧
    opcodeAt (match kind with
        | .deposit => depositStoreExcessWindow
        | .exit => exitStoreExcessWindow) 1 =
      some (.PUSH0, none) ∧
    opcodeAt (match kind with
        | .deposit => depositStoreExcessWindow
        | .exit => exitStoreExcessWindow) 2 =
      some (.SSTORE, none) ∧
    opcodeAt (match kind with
        | .deposit => depositStoreExcessWindow
        | .exit => exitStoreExcessWindow) 4 =
      some (.PUSH1, some (UInt256.ofNat SLOT_COUNT, 1)) ∧
    opcodeAt (match kind with
        | .deposit => depositStoreExcessWindow
        | .exit => exitStoreExcessWindow) 6 =
      some (.SSTORE, none) := by
  cases kind
  · exact ⟨deposit_update_head_PUSH1_QUEUE_HEAD, deposit_update_head_SSTORE,
      deposit_reset_queue_PUSH1_QUEUE_HEAD, deposit_reset_queue_SSTORE_head,
      deposit_reset_queue_PUSH1_QUEUE_TAIL, deposit_reset_queue_SSTORE_tail,
      deposit_store_excess_PUSH0_SLOT_EXCESS, deposit_store_excess_SSTORE_excess,
      deposit_store_excess_PUSH1_SLOT_COUNT, deposit_store_excess_SSTORE_count⟩
  · exact ⟨exit_update_head_PUSH1_QUEUE_HEAD, exit_update_head_SSTORE,
      exit_reset_queue_PUSH1_QUEUE_HEAD, exit_reset_queue_SSTORE_head,
      exit_reset_queue_PUSH1_QUEUE_TAIL, exit_reset_queue_SSTORE_tail,
      exit_store_excess_PUSH0_SLOT_EXCESS, exit_store_excess_SSTORE_excess,
      exit_store_excess_PUSH1_SLOT_COUNT, exit_store_excess_SSTORE_count⟩

/-! ## Instruction-start scan (`0x55` = `SSTORE`)

Used to show `accum_loop` (and the `read_requests` / `update_excess` bodies)
contain no `SSTORE`. PUSH immediates are skipped so a `0x55` data byte is
not a false positive.
-/

/-- `1` plus the PUSH immediate width (`0` for non-PUSH). -/
def instrWidth (b : Nat) : Nat :=
  if 0x60 ≤ b && b ≤ 0x7f then b - 0x5f + 1 else 1

theorem instrWidth_pos (b : Nat) : 0 < instrWidth b := by
  unfold instrWidth
  split_ifs <;> omega

/-- Fuel-bounded instruction-start walk. Structural on `fuel` so ground
`rfl` closes `= false` (well-founded `List` recursion does not reduce).
`fuel ≥ bytes.length` is enough: each step consumes at least one byte. -/
def hasSstoreFuel : Nat → List Nat → Bool
  | 0, _ => false
  | _, [] => false
  | n + 1, b :: rest =>
      (b == 0x55) || hasSstoreFuel n (rest.drop (instrWidth b - 1))

def hasSstore (bytes : List Nat) : Bool :=
  hasSstoreFuel bytes.length bytes

/-- Ground fact: byte `0x55` decodes as `SSTORE`. -/
theorem sstore_opcode_byte :
    opcodeAt (fromHex "55") 0 = some (.SSTORE, none) := rfl

/-! ### `accum_loop` bodies (no `SSTORE`)

Pinned bytes from `accum_loop` through the byte before `update_head`.
SLOAD/MSTORE only.
-/

def depositAccumBytes : List Nat :=
  [ 0x5b, 0x81, 0x81, 0x14, 0x61, 0x01, 0xd7, 0x57, 0x82, 0x81, 0x01, 0x60
  , 0x06, 0x02, 0x60, 0x04, 0x01, 0x81, 0x60, 0xb8, 0x02, 0x81, 0x54, 0x81
  , 0x52, 0x60, 0x20, 0x01, 0x81, 0x60, 0x01, 0x01, 0x54, 0x81, 0x52, 0x60
  , 0x20, 0x01, 0x81, 0x60, 0x02, 0x01, 0x54, 0x80, 0x82, 0x52, 0x60, 0x40
  , 0x1c, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81
  , 0x60, 0x10, 0x01, 0x81, 0x60, 0x38, 0x1c, 0x81, 0x60, 0x07, 0x01, 0x53
  , 0x81, 0x60, 0x30, 0x1c, 0x81, 0x60, 0x06, 0x01, 0x53, 0x81, 0x60, 0x28
  , 0x1c, 0x81, 0x60, 0x05, 0x01, 0x53, 0x81, 0x60, 0x20, 0x1c, 0x81, 0x60
  , 0x04, 0x01, 0x53, 0x81, 0x60, 0x18, 0x1c, 0x81, 0x60, 0x03, 0x01, 0x53
  , 0x81, 0x60, 0x10, 0x1c, 0x81, 0x60, 0x02, 0x01, 0x53, 0x81, 0x60, 0x08
  , 0x1c, 0x81, 0x60, 0x01, 0x01, 0x53, 0x53, 0x60, 0x20, 0x01, 0x81, 0x60
  , 0x03, 0x01, 0x54, 0x81, 0x52, 0x60, 0x20, 0x01, 0x81, 0x60, 0x04, 0x01
  , 0x54, 0x81, 0x52, 0x60, 0x20, 0x01, 0x90, 0x60, 0x05, 0x01, 0x54, 0x90
  , 0x52, 0x60, 0x01, 0x01, 0x61, 0x01, 0x33, 0x56 ]

def exitAccumBytes : List Nat :=
  [ 0x5b, 0x81, 0x81, 0x14, 0x61, 0x01, 0x2d, 0x57, 0x82, 0x81, 0x01, 0x60
  , 0x03, 0x02, 0x60, 0x04, 0x01, 0x81, 0x60, 0x44, 0x02, 0x81, 0x54, 0x60
  , 0x60, 0x1b, 0x81, 0x52, 0x60, 0x14, 0x01, 0x81, 0x60, 0x01, 0x01, 0x54
  , 0x81, 0x52, 0x60, 0x20, 0x01, 0x90, 0x60, 0x02, 0x01, 0x54, 0x90, 0x52
  , 0x60, 0x01, 0x01, 0x60, 0xf7, 0x56 ]

def accumBytes : Kind → List Nat
  | .deposit => depositAccumBytes
  | .exit => exitAccumBytes

theorem deposit_accum_len : depositAccumBytes.length = 164 := rfl
theorem exit_accum_len : exitAccumBytes.length = 54 := rfl

set_option maxHeartbeats 4000000 in
theorem deposit_accum_loop_no_sstore :
    hasSstore depositAccumBytes = false := rfl

theorem exit_accum_loop_no_sstore :
    hasSstore exitAccumBytes = false := rfl

theorem accum_loop_no_sstore (kind : Kind) :
    hasSstore (accumBytes kind) = false := by
  cases kind
  · exact deposit_accum_loop_no_sstore
  · exact exit_accum_loop_no_sstore

/-! ### `read_requests` prefix (no `SSTORE`)

From `read_requests` through the `PUSH0` before `accum_loop`. SLOADs of
TAIL/HEAD only.
-/

def depositReadRequestsBytes : List Nat :=
  [ 0x5b, 0x60, 0x03, 0x54, 0x60, 0x02, 0x54, 0x80, 0x82, 0x03, 0x80, 0x60
  , 0x40, 0x11, 0x61, 0x01, 0x31, 0x57, 0x50, 0x60, 0x40, 0x5b, 0x5f ]

def exitReadRequestsBytes : List Nat :=
  [ 0x5b, 0x60, 0x03, 0x54, 0x60, 0x02, 0x54, 0x80, 0x82, 0x03, 0x80, 0x60
  , 0x10, 0x11, 0x60, 0xf5, 0x57, 0x50, 0x60, 0x10, 0x5b, 0x5f ]

theorem deposit_read_requests_no_sstore :
    hasSstore depositReadRequestsBytes = false := rfl

theorem exit_read_requests_no_sstore :
    hasSstore exitReadRequestsBytes = false := rfl

theorem read_requests_prefix_no_sstore (kind : Kind) :
    hasSstore (match kind with
        | .deposit => depositReadRequestsBytes
        | .exit => exitReadRequestsBytes) = false := by
  cases kind
  · exact deposit_read_requests_no_sstore
  · exact exit_read_requests_no_sstore

/-! ### `update_excess` body (no `SSTORE`)

From `update_excess` through the byte before `store_excess`. The two PUSH32
`INHIBITOR` immediates are skipped by `instrWidth`. SLOAD of slots 0 and 1
only.
-/

def depositUpdateExcessBytes : List Nat :=
  [ 0x5b, 0x36, 0x61, 0x02, 0x42, 0x57, 0x5f, 0x54, 0x60, 0x01, 0x54, 0x81
  , 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x14, 0x61, 0x02
  , 0x30, 0x57, 0x60, 0x08, 0x82, 0x82, 0x01, 0x11, 0x61, 0x02, 0x38, 0x57
  , 0x5b, 0x50, 0x50, 0x5f, 0x61, 0x02, 0x64, 0x56, 0x5b, 0x01, 0x60, 0x08
  , 0x90, 0x03, 0x61, 0x02, 0x64, 0x56, 0x5b, 0x7f, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff ]

def exitUpdateExcessBytes : List Nat :=
  [ 0x5b, 0x36, 0x61, 0x01, 0x98, 0x57, 0x5f, 0x54, 0x60, 0x01, 0x54, 0x81
  , 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x14, 0x61, 0x01
  , 0x86, 0x57, 0x60, 0x02, 0x82, 0x82, 0x01, 0x11, 0x61, 0x01, 0x8e, 0x57
  , 0x5b, 0x50, 0x50, 0x5f, 0x61, 0x01, 0xba, 0x56, 0x5b, 0x01, 0x60, 0x02
  , 0x90, 0x03, 0x61, 0x01, 0xba, 0x56, 0x5b, 0x7f, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff ]

set_option maxHeartbeats 4000000 in
theorem deposit_update_excess_no_sstore :
    hasSstore depositUpdateExcessBytes = false := rfl

theorem exit_update_excess_no_sstore :
    hasSstore exitUpdateExcessBytes = false := rfl

theorem update_excess_no_sstore (kind : Kind) :
    hasSstore (match kind with
        | .deposit => depositUpdateExcessBytes
        | .exit => exitUpdateExcessBytes) = false := by
  cases kind
  · exact deposit_update_excess_no_sstore
  · exact exit_update_excess_no_sstore

/-! ## Parent: every system CFG `SSTORE` key is a control slot -/

def updateHeadWindow : Kind → ByteArray
  | .deposit => depositUpdateHeadWindow
  | .exit => exitUpdateHeadWindow

/-- Every `SSTORE` key on the system CFG is in
`{SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL}`.

Hypotheses: `WellFormed` (via `CallHyp`), gas ≥ 30M, system caller
(`isUser = false`). The opening gate lands on `read_requests`; the SSTORE
sites are the F1 labels `update_head` / `reset_queue` / `store_excess`;
`accum_loop` has no `SSTORE`.

The `PUSH1 QUEUE_HEAD` conjunct is the Wave-6 kill-line (deposit offset 483,
exit offset 313): retargeting that immediate off slot 2 makes this false.
-/
theorem system_sstore_keys_subset
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (hsys : h.isUser = false) :
    (∀ {m : CfgState},
      runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
        .ok m →
      m.pc = readRequestsPc kind) ∧
    opcodeAt (updateHeadWindow kind) 11 =
      some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
    opcodeAt (updateHeadWindow kind) 13 = some (.SSTORE, none) ∧
    (∀ key ∈ systemSstoreKeys kind, key ∈ controlKeys) ∧
    hasSstore (accumBytes kind) = false :=
  ⟨fun hrun => system_path_pc kind σ h hsys hrun,
    (update_head_sstore_key kind).1,
    (update_head_sstore_key kind).2,
    systemSstoreKeys_subset_control kind,
    accum_loop_no_sstore kind⟩

/-! ## Stale slots (`n ≥ 4`) are not written

A system-CFG execution is a finite list of `SSTORE`s whose keys are among
`systemSstoreKeys`. Last-write-wins lookup on that list agrees with the
pre-state at every slot whose `toNat` is ≥ `QUEUE_OFFSET`.
-/

/-- Last write of key `n` in a CFG store list, if any. -/
def lastWrite (writes : List (Nat × UInt256)) (n : Nat) : Option UInt256 :=
  (writes.reverse.find? (fun kv => kv.1 = n)).map Prod.snd

/-- Post-state observation at `slot` after the given CFG stores. -/
def postGet (σ : Storage) (writes : List (Nat × UInt256))
    (slot : UInt256) : UInt256 :=
  match lastWrite writes slot.toNat with
  | some v => v
  | none => σ.getD slot (UInt256.ofNat 0)

def postLoad (σ : Storage) (writes : List (Nat × UInt256)) (n : Nat) : Nat :=
  match lastWrite writes n with
  | some v => v.toNat
  | none => loadNat σ n

theorem lastWrite_none_of_keys_lt
    {writes : List (Nat × UInt256)} {n : Nat}
    (hw : ∀ kv ∈ writes, kv.1 < n) :
    lastWrite writes n = none := by
  unfold lastWrite
  cases hfind : writes.reverse.find? (fun kv => kv.1 = n) with
  | none => rfl
  | some kv =>
      have hmem : kv ∈ writes.reverse := List.mem_of_find?_eq_some hfind
      have hmem' : kv ∈ writes := List.mem_reverse.mp hmem
      have htrue : kv.1 = n := by
        have := List.find?_some hfind
        simpa using this
      have hlt : kv.1 < n := hw kv hmem'
      exact (Nat.lt_irrefl n (htrue ▸ hlt)).elim

theorem lastWrite_none_of_control
    (kind : Kind) {writes : List (Nat × UInt256)} {n : Nat}
    (hw : ∀ kv ∈ writes, kv.1 ∈ systemSstoreKeys kind)
    (hn : n ≥ QUEUE_OFFSET) :
    lastWrite writes n = none := by
  apply lastWrite_none_of_keys_lt
  intro kv hkv
  have hk := systemSstoreKeys_subset_control kind kv.1 (hw kv hkv)
  have hlt := controlKey_lt_offset hk
  exact Nat.lt_of_lt_of_le hlt hn

/-- `∀ n ≥ 4`, the post-image of a system CFG store list equals the
pre-image. `n` is the logical slot (not reduced mod `2^256`); wrapping keys
are the `UInt256` form below.
-/
theorem stale_slots_preserved
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (hsys : h.isUser = false)
    (writes : List (Nat × UInt256))
    (hw : ∀ kv ∈ writes, kv.1 ∈ systemSstoreKeys kind)
    (n : Nat) (hn : n ≥ QUEUE_OFFSET) :
    postLoad σ writes n = loadNat σ n := by
  have := h.wellFormed
  have := hsys
  unfold postLoad
  rw [lastWrite_none_of_control kind hw hn]

/-- Same fact on `UInt256` keys: every slot with `toNat ≥ 4` is unchanged.
This is the wrap-safe form (`UInt256.toNat < 2^256`). -/
theorem stale_slots_preserved_u256
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (hsys : h.isUser = false)
    (writes : List (Nat × UInt256))
    (hw : ∀ kv ∈ writes, kv.1 ∈ systemSstoreKeys kind)
    (slot : UInt256) (hslot : slot.toNat ≥ QUEUE_OFFSET) :
    postGet σ writes slot = σ.getD slot (UInt256.ofNat 0) := by
  have := h.wellFormed
  have := hsys
  unfold postGet
  rw [lastWrite_none_of_control kind hw hslot]

end Eip8282.Audit.Guarantees.PDrain1.Footprint
