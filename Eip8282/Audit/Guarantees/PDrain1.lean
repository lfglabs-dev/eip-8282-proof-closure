import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Guarantees.PDrain1.Footprint
import Eip8282.Audit.Guarantees.PDrain1.Fifo
import Eip8282.Audit.Guarantees.PDrain1.Encode

namespace Eip8282.Audit.Guarantees.PDrain1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pDrain1, [.model, .evm]⟩

/-! ## Abstract model layer

Scaffolding over `Model.systemCall`. These are *not* the load-bearing parent:
`systemCall` is a hand-written abstraction with no proven relation to the
deployed bytecode. The load-bearing statement is `pdrain1_forall_parent`:
CFG-level `∀` under `WellFormed` / `CallHyp` (`isUser = false`, gas ≥ 30M)
for footprint, FIFO pointers, and BE→LE encode, plus the Wave-6
`pdrain1_bytecode_parent` traces as the kill-line witness. F4 left
`A-ABSTRACT-TX` open, so this is not `Ξ ↔ Model`.
-/

theorem system_always_succeeds (s : State) (calldataNonempty : Bool) :
    (systemCall s calldataNonempty).isRevert = false := by
  unfold systemCall
  simp

theorem fifo_bounded (s : State) (calldataNonempty : Bool) :
    (systemCall s calldataNonempty).state.queue = s.queue.drop (capOf s.kind) := by
  unfold systemCall
  simp

theorem fifo_return (s : State) (calldataNonempty : Bool) :
    systemCall s calldataNonempty =
      .success (systemCall s calldataNonempty).state
        (concatReturned (s.queue.take (capOf s.kind))) := by
  unfold systemCall
  simp

theorem empty_queue_after_full_drain
    (s : State) (calldataNonempty : Bool)
    (h : s.queue.length ≤ capOf s.kind) :
    (systemCall s calldataNonempty).state.queue = [] := by
  unfold systemCall
  simp [List.drop_eq_nil_of_le h]

theorem encoding
    (calldata : List Byte) (amount : Nat) (source : Address) (pubkey : List Byte) :
    encodeReturned (.deposit calldata amount) =
      calldata.take 80 ++ toLeBytes amount 8 ++ calldata.drop 88 ∧
    encodeReturned (.exit source pubkey) = toBeBytes source 20 ++ pubkey := by
  constructor <;> rfl

/-! ## Pinned-bytecode layer

Everything below runs `Eip8282.Audit.Bytecode.depositRuntime` and
`exitRuntime` — the bytes of `pinned/bytecode/builder_{deposits,exits}/main.hex`
— inside `EvmYul.EVM.Ξ` via `Eip8282.Audit.EvmRunner.runDepositSystem` /
`runExitSystem`. Those runners differ from the user runners only in
`msg.sender` (`SYSTEM_ADDR`) and zero value.

P-DRAIN-1 is about the *FIFO drain*: how many records a system call returns,
which record comes out first, how the amount field is recoded, and how
`QUEUE_HEAD` / `QUEUE_TAIL` move. Every claim below is therefore a system
call against a *non-empty* (or, for the zero case, empty) queue image —
never a user submission, and never the empty-queue control plane that
P-CONTROL-1 already owns.

Each fact is a `Bool` parameterized by the runtime `code`, so
`Eip8282.Tests.PDrain1Mutant` can feed a *byte-mutated* runtime to the same
`drainFacts` and get `false`.

The mutated bytes live only on the system drain path: exit `MAX_PER_BLOCK` at
offset 244, exit `RECORD_SIZE` at offset 450, the deposit `MAX_PER_BLOCK`
clamp at offset 304, the partial-drain `QUEUE_HEAD` SSTORE slot at
deposit offset 483, and the exit partial-drain `QUEUE_HEAD` SSTORE slot at
offset 313. P-SUBMIT-1 never calls from `SYSTEM_ADDR`. P-CONTROL-1
does, but the empty-queue `controlFacts` hold `QUEUE_HEAD = QUEUE_TAIL = 0`,
so the drain loop is a no-op, the over-cap clamp is never loaded, the
partial-drain head stores are never taken (the empty queue resets both
pointers), and `0 * RECORD_SIZE` is still 0. Sibling independence is
proved in `Eip8282.Tests.PDrain1Mutant`.
-/

open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

def FUEL : Nat := 80000

/-- Interpreter fuel for the 64-record deposit drain. Each item does six
`SLOAD`s plus the little-endian amount rewrite, so the 17-exit budget of
`FUEL` is not enough. Gas is still `30_000_000`. -/
def DEPOSIT_CAP_FUEL : Nat := 300000

/-- A non-system, non-privileged caller. Same id as the siblings. -/
def submitter : Nat := 0x1234

/-- `SLOT_EXCESS := 100`, `SLOT_COUNT := 5`, `QUEUE_HEAD := head`, `QUEUE_TAIL := tail`,
plus the queued record words. Excess/count match the sibling images so a
system call still folds excess to the known post-state (97 deposits / 103
exits) and the drain claim is isolated to the return buffer and the two
queue pointers. -/
def queueStorage (excess count head tail : Nat) (words : List (Nat × Nat)) :=
  storageFromList ([(0, excess), (1, count), (2, head), (3, tail)] ++ words)

/-- Distinctive 20-byte source address for queued exit `i`. -/
def exitSrc (i : Nat) : Nat := 0xA100 + i

/-- First pubkey word of exit `i`: bytes `[0xB0, i, 0, …]`. -/
def exitPk1 (i : Nat) : Nat := (0xB000 + i) * (2 ^ 240)

/-- Second pubkey word of exit `i`, left-aligned 16 bytes: `[0xC0, i, 0, …]`. -/
def exitPk2 (i : Nat) : Nat := (0xC000 + i) * (2 ^ 240)

def exitItemWords (i : Nat) : List (Nat × Nat) :=
  let base := 4 + 3 * i
  [(base, exitSrc i), (base + 1, exitPk1 i), (base + 2, exitPk2 i)]

/-- `n` queued exits at `head = 0`, `tail = n`. -/
def exitQueue (n : Nat) :=
  queueStorage 100 5 0 n ((List.range n).flatMap exitItemWords)

/-- Packed deposit slot 2: `wc[16:32] = 0xff..ff`, amount `amt`, `sig[0:8] = 0`. -/
def depositAmtWord (amt : Nat) : Nat :=
  (2 ^ 128 - 1) * (2 ^ 128) + amt * (2 ^ 64)

def depositItemWords (i amt : Nat) : List (Nat × Nat) :=
  let base := 4 + 6 * i
  [ (base,     (0x1100 + i) * (2 ^ 240))
  , (base + 1, (0x2200 + i) * (2 ^ 240))
  , (base + 2, depositAmtWord amt)
  , (base + 3, (0x3300 + i) * (2 ^ 240))
  , (base + 4, (0x4400 + i) * (2 ^ 240))
  , (base + 5, (0x5500 + i) * (2 ^ 240)) ]

/-- Distinctive big-endian amount for queued deposit `i`. -/
def depositAmtOf (i : Nat) : Nat := 0x0102030405060708 + i * 0x0101010101010101

/-- Empty deposit queue at `head = tail = 0`. -/
def depositQueue0 :=
  queueStorage 100 5 0 0 []

/-- One queued deposit whose amount field is the big-endian `0x0102030405060708`. -/
def depositQueue1 :=
  queueStorage 100 5 0 1 (depositItemWords 0 0x0102030405060708)

/-- Two queued deposits with distinct amounts, for a FIFO check. -/
def depositQueue2 :=
  queueStorage 100 5 0 2
    (depositItemWords 0 0x0102030405060708 ++ depositItemWords 1 0x1112131415161718)

/-- Sixty-five queued deposits at `head = 0`, `tail = 65`: one over the
per-block deposit cap of 64. Each item carries a distinctive amount so the
returned window can be checked at both ends. -/
def depositQueue65 :=
  queueStorage 100 5 0 65 ((List.range 65).flatMap (fun i => depositItemWords i (depositAmtOf i)))

/-- 20-byte BE address `src` occupies bytes `[off, off+20)` of the return. -/
def outAddrIs (res : RunResult) (off src : Nat) : Bool :=
  (List.range 20).all fun i =>
    successOutByteIs res (off + i) ((src / 256 ^ (19 - i)) % 256)

/-- Exit record `idx` was packed at `idx * 68` from queued item `i`. -/
def outExitRecordIs (res : RunResult) (idx i : Nat) : Bool :=
  let off := idx * 68
  outAddrIs res off (exitSrc i)
    && successOutByteIs res (off + 20) 0xB0
    && successOutByteIs res (off + 21) i
    && successOutByteIs res (off + 52) 0xC0
    && successOutByteIs res (off + 53) i

/-- Little-endian amount bytes at the EIP-6110 offset inside record `idx`. -/
def outAmountLeIs (res : RunResult) (idx : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | b0, b1, b2, b3, b4, b5, b6, b7 =>
    let off := idx * 184 + 80
    successOutByteIs res off b0
      && successOutByteIs res (off + 1) b1
      && successOutByteIs res (off + 2) b2
      && successOutByteIs res (off + 3) b3
      && successOutByteIs res (off + 4) b4
      && successOutByteIs res (off + 5) b5
      && successOutByteIs res (off + 6) b6
      && successOutByteIs res (off + 7) b7

/-- Amount field of returned record `idx` is the little-endian encoding of
the big-endian `amt` that was stored for that queued item. -/
def outAmountLeOf (res : RunResult) (idx amt : Nat) : Bool :=
  outAmountLeIs res idx
    (amt % 256)
    ((amt / 256) % 256)
    ((amt / 256 ^ 2) % 256)
    ((amt / 256 ^ 3) % 256)
    ((amt / 256 ^ 4) % 256)
    ((amt / 256 ^ 5) % 256)
    ((amt / 256 ^ 6) % 256)
    ((amt / 256 ^ 7) % 256)

/-- Storage word at `QUEUE_OFFSET + 6*i` (the first word of queued deposit
`i`) is still `pk1` after the drain. Used to pin stale-slot non-erasure:
advancing `QUEUE_HEAD` does not `SSTORE` the drained record slots to zero. -/
def staleDepositPk1Is (res : RunResult) (i expectedHi : Nat) : Bool :=
  storageSlotIs res depositAddr (u256 (4 + 6 * i)) (u256 (expectedHi * (2 ^ 240)))

/-- Remaining five words of queued deposit `i` still match the distinctive
pre-drain image. Complements `staleDepositPk1Is` so non-erasure is not
pinned on the first word alone. -/
def staleDepositRestIs (res : RunResult) (i : Nat) : Bool :=
  storageSlotIs res depositAddr (u256 (4 + 6 * i + 1))
      (u256 ((0x2200 + i) * (2 ^ 240)))
    && storageSlotIs res depositAddr (u256 (4 + 6 * i + 2))
      (u256 (depositAmtWord (depositAmtOf i)))
    && storageSlotIs res depositAddr (u256 (4 + 6 * i + 3))
      (u256 ((0x3300 + i) * (2 ^ 240)))
    && storageSlotIs res depositAddr (u256 (4 + 6 * i + 4))
      (u256 ((0x4400 + i) * (2 ^ 240)))
    && storageSlotIs res depositAddr (u256 (4 + 6 * i + 5))
      (u256 ((0x5500 + i) * (2 ^ 240)))

/-- First word of queued exit `i` (the 20-byte source) is still `exitSrc i`. -/
def staleExitSrcIs (res : RunResult) (i : Nat) : Bool :=
  storageSlotIs res exitAddr (u256 (4 + 3 * i)) (u256 (exitSrc i))

/-- Second word of queued exit `i` (pubkey `[0:32]`) is still `exitPk1 i`. -/
def staleExitPk1Is (res : RunResult) (i : Nat) : Bool :=
  storageSlotIs res exitAddr (u256 (4 + 3 * i + 1)) (u256 (exitPk1 i))

/-- Third word of queued exit `i` (pubkey `[32:48]`) is still `exitPk2 i`.
Wave 3 pinned src and pk1 of item 0 and src of item 15; this remaining
word was left out. -/
def staleExitPk2Is (res : RunResult) (i : Nat) : Bool :=
  storageSlotIs res exitAddr (u256 (4 + 3 * i + 2)) (u256 (exitPk2 i))

/-! ### builder_exits drain -/

/-- Empty queue: the system call still succeeds, returns no records, and
leaves both queue pointers at 0. Included so a mutant that breaks the
system return itself is visible; the load-bearing content is the nonempty
facts below. -/
def exitEmptyDrainFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := exitQueue 0)
  isSuccess r && successOutSize r == 0 && slots0to3Are r exitAddr 103 0 0 0

/-- Two queued exits, under the per-block cap of 16: both records come back
in FIFO order as 68-byte chunks, and a full drain resets `QUEUE_HEAD` and
`QUEUE_TAIL` to 0. Excess still folds `100 + 5 - 2 = 103`. -/
def exitUnderCapFifoFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := exitQueue 2)
  isSuccess r
    && successOutSize r == 136
    && slots0to3Are r exitAddr 103 0 0 0
    && outExitRecordIs r 0 0
    && outExitRecordIs r 1 1

/-- Seventeen queued exits, one over the cap: exactly 16 records return
(1088 bytes), `QUEUE_HEAD` advances by 16, `QUEUE_TAIL` stays 17, and the
returned window is the *oldest* sixteen — item 0 first, item 15 last.
Item 16 is not in the buffer. Wave 3 pinned the first two words of
drained item 0 and the first word of drained item 15. Wave 6 adds the
remaining pk2 word of item 0, both leftover words of item 15, and both
words plus pk2 of another drained index (item 7), so advancing the head
does not erase those exit slots either. This is the conjunct the
exit-cap mutant refutes (via the window / pointers); the Wave-3 head-slot
mutant refutes the deposit-side sibling of the stale-slot half and
Wave 6 pins items 7 and 15 fully. -/
def exitOverCapFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := exitQueue 17)
  isSuccess r
    && successOutSize r == 1088
    && storageSlotIs r exitAddr (u256 0) (u256 103)
    && storageSlotIs r exitAddr (u256 1) (u256 0)
    && storageSlotIs r exitAddr (u256 2) (u256 16)
    && storageSlotIs r exitAddr (u256 3) (u256 17)
    && outExitRecordIs r 0 0
    && outExitRecordIs r 15 15
    && staleExitSrcIs r 0
    && staleExitPk1Is r 0
    && staleExitPk2Is r 0
    && staleExitSrcIs r 15
    && staleExitPk1Is r 15
    && staleExitPk2Is r 15
    && staleExitSrcIs r 7
    && staleExitPk1Is r 7
    && staleExitPk2Is r 7

/-- A user fee-getter on a seeded queue does not consume it: 32-byte quote,
pointers stay `head = 0`, `tail = 2`. Only `SYSTEM_ADDR` drains. -/
def exitUserDoesNotDrainFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter 0 ByteArray.empty (code := code) (storage := exitQueue 2)
  isSuccess r && successOutSize r == 32 && slots0to3Are r exitAddr 100 5 0 2

/-! ### builder_deposits drain -/

/-- One queued deposit comes back as 184 bytes, the 8-byte amount field at
offset 80 is recoded little-endian (`0x0102030405060708` →
`08 07 06 05 04 03 02 01`), and a full drain resets both pointers.
Excess folds `100 + 5 - 8 = 97`. -/
def depositLeFact (code : ByteArray) : Bool :=
  let r := runDepositSystem FUEL ByteArray.empty (code := code) (storage := depositQueue1)
  isSuccess r
    && successOutSize r == 184
    && slots0to3Are r depositAddr 97 0 0 0
    && outAmountLeIs r 0 0x08 0x07 0x06 0x05 0x04 0x03 0x02 0x01
    && successOutByteIs r 0 0x11
    && successOutByteIs r 1 0x00

/-- Two queued deposits: 368 bytes, amounts in FIFO order, pointers reset. -/
def depositFifoFact (code : ByteArray) : Bool :=
  let r := runDepositSystem FUEL ByteArray.empty (code := code) (storage := depositQueue2)
  isSuccess r
    && successOutSize r == 368
    && slots0to3Are r depositAddr 97 0 0 0
    && outAmountLeIs r 0 0x08 0x07 0x06 0x05 0x04 0x03 0x02 0x01
    && outAmountLeIs r 1 0x18 0x17 0x16 0x15 0x14 0x13 0x12 0x11

/-- Empty deposit queue: the system call still succeeds, returns no records,
and leaves both queue pointers at 0. Symmetric with `exitEmptyDrainFact`;
the Wave-1 parent only had the exit empty-queue conjunct. Excess still
folds `100 + 5 - 8 = 97`. -/
def depositEmptyDrainFact (code : ByteArray) : Bool :=
  let r := runDepositSystem FUEL ByteArray.empty (code := code) (storage := depositQueue0)
  isSuccess r && successOutSize r == 0 && slots0to3Are r depositAddr 97 0 0 0

/-- Sixty-five queued deposits, one over the per-block cap of 64: exactly
64 records return (`64 * 184 = 11776` bytes), `QUEUE_HEAD` advances to 64,
`QUEUE_TAIL` stays 65, and the returned window is the *oldest* sixty-four
— item 0 first, item 63 last. Item 64 is not in the buffer. Stale-slot
non-erasure is pinned on more than the first word of item 0: the other
five words of item 0, all five remaining words of item 1, the first word
of drained item 32, the first word *and* remaining five words of drained
item 63, and the first word of still-queued item 64 all remain. Wave 6
adds item 1 rest-words, item 32 first word, and item 63 rest-words. This
is the conjunct the deposit-cap mutant and the Wave-3 and Wave-6
head-slot mutants refute. -/
def depositOverCapFact (code : ByteArray) : Bool :=
  let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
    (code := code) (storage := depositQueue65)
  isSuccess r
    && successOutSize r == 11776
    && storageSlotIs r depositAddr (u256 0) (u256 97)
    && storageSlotIs r depositAddr (u256 1) (u256 0)
    && storageSlotIs r depositAddr (u256 2) (u256 64)
    && storageSlotIs r depositAddr (u256 3) (u256 65)
    && outAmountLeOf r 0 (depositAmtOf 0)
    && outAmountLeOf r 63 (depositAmtOf 63)
    && successOutByteIs r 0 0x11
    && successOutByteIs r 1 0x00
    && staleDepositPk1Is r 0 0x1100
    && staleDepositRestIs r 0
    && staleDepositRestIs r 1
    && staleDepositPk1Is r 32 0x1120
    && staleDepositPk1Is r 63 0x113F
    && staleDepositRestIs r 63
    && staleDepositPk1Is r 64 0x1140

/-- The whole P-DRAIN-1 drain claim, as a function of the two runtimes.
Feeding a mutated `depCode` or `exitCode` must make this `false`. -/
def drainFacts (depCode exitCode : ByteArray) : Bool :=
  exitEmptyDrainFact exitCode
    && exitUnderCapFifoFact exitCode
    && exitOverCapFact exitCode
    && exitUserDoesNotDrainFact exitCode
    && depositEmptyDrainFact depCode
    && depositLeFact depCode
    && depositFifoFact depCode
    && depositOverCapFact depCode

/--
**P-DRAIN-1 parent, on pinned bytecode.**

`drainFacts depositRuntime exitRuntime` holds of the actual sys-asm@83f9801
runtime bytes executed by `EvmYul.EVM.Ξ`. The conjuncts spelled out after it
are the separations the guarantee is really about, stated directly on
`runExitSystem` / `runDepositSystem` so the parent cannot be read as a
definitional restatement of `drainFacts`:

* two queued exits come back as 136 bytes in FIFO order and a full drain
  zeroes both queue pointers;
* seventeen queued exits return exactly sixteen records (1088 bytes),
  `QUEUE_HEAD` advances to 16 and `QUEUE_TAIL` stays 17;
* one queued deposit returns 184 bytes with the amount field converted
  from big-endian `0x0102030405060708` to little-endian
  `08 07 06 05 04 03 02 01`;
* an empty deposit queue still succeeds, returns 0 bytes, and leaves
  both queue pointers at 0;
* sixty-five queued deposits return exactly sixty-four records
  (`64 * 184 = 11776` bytes), `QUEUE_HEAD` advances to 64 and
  `QUEUE_TAIL` stays 65;
* after that 64-record drain the remaining five words of item 0, the
  five remaining words of item 1, the first word of drained item 32,
  the first word *and* remaining five words of drained item 63, and
  the first word of still-queued item 64 are still the distinctive
  pre-drain image;
* after the 16-record exit drain the three words of item 0, all three
  words of item 15, and all three words of item 7 are still the
  distinctive pre-drain image (`QUEUE_HEAD = 16`, `QUEUE_TAIL = 17`).

Kept as the kill-line witness inside `pdrain1_forall_parent`. Feeding a
mutated runtime to `drainFacts` still makes this conjunction false
(exit cap@244, RECORD_SIZE@450, deposit cap@304, deposit HEAD@483,
exit HEAD@313). Finite traces, not the `∀`.

Discharged by `native_decide`: a concrete `Ξ` trace reaches the `opaque`
`@[extern]` constants `EvmYul.FFI.keccak256` / `sha256` / `BLAKE2Compress`,
which the kernel cannot reduce by construction. (`D_J` is no longer a
reason — it is structurally recursive as of EVMYulLean `0ff72b2`, and the
jumpdest tables are now `decide +kernel`.) The resulting compiler-generated
axiom is disclosed in `Eip8282.Audit.Trust` and as `A-NATIVE-DECIDE` in
`audit/assumptions.yaml`.
-/
theorem pdrain1_bytecode_parent :
    drainFacts depositRuntime exitRuntime = true
    ∧ successOutSize (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 2)) = 136
    ∧ slots0to3Are (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 2)) exitAddr 103 0 0 0 = true
    ∧ outExitRecordIs (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 2)) 0 0 = true
    ∧ outExitRecordIs (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 2)) 1 1 = true
    ∧ successOutSize (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 17)) = 1088
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 17))
        exitAddr (u256 2) (u256 16) = true
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 17))
        exitAddr (u256 3) (u256 17) = true
    ∧ successOutSize (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue1)) = 184
    ∧ outAmountLeIs (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue1))
        0 0x08 0x07 0x06 0x05 0x04 0x03 0x02 0x01 = true
    ∧ (let empty := runDepositSystem FUEL ByteArray.empty
          (code := depositRuntime) (storage := depositQueue0);
        successOutSize empty = 0
          ∧ slots0to3Are empty depositAddr 97 0 0 0 = true)
    ∧ (let over := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
          (code := depositRuntime) (storage := depositQueue65);
        successOutSize over = 11776
          ∧ storageSlotIs over depositAddr (u256 2) (u256 64) = true
          ∧ storageSlotIs over depositAddr (u256 3) (u256 65) = true
          ∧ staleDepositPk1Is over 0 0x1100 = true
          ∧ staleDepositRestIs over 0 = true
          ∧ staleDepositRestIs over 1 = true
          ∧ staleDepositPk1Is over 32 0x1120 = true
          ∧ staleDepositPk1Is over 63 0x113F = true
          ∧ staleDepositRestIs over 63 = true
          ∧ staleDepositPk1Is over 64 0x1140 = true)
    ∧ (let overEx := runExitSystem FUEL ByteArray.empty
          (code := exitRuntime) (storage := exitQueue 17);
        storageSlotIs overEx exitAddr (u256 2) (u256 16) = true
          ∧ storageSlotIs overEx exitAddr (u256 3) (u256 17) = true
          ∧ staleExitSrcIs overEx 0 = true
          ∧ staleExitPk1Is overEx 0 = true
          ∧ staleExitPk2Is overEx 0 = true
          ∧ staleExitSrcIs overEx 15 = true
          ∧ staleExitPk1Is overEx 15 = true
          ∧ staleExitPk2Is overEx 15 = true
          ∧ staleExitSrcIs overEx 7 = true
          ∧ staleExitPk1Is overEx 7 = true
          ∧ staleExitPk2Is overEx 7 = true) := by
  native_decide

/-! ## Public `∀` parent (CFG + kill-line traces)

D1–D3 are CFG / algebraic `∀` under `CallHyp` (well-formed storage, gas ≥ 30M,
fuel ≥ 80000, system caller `isUser = false`). They do not execute
`EvmYul.EVM.Ξ`. The Wave-6 `drainFacts` traces stay as the
mutation-discriminating conjunct: a one-byte cut of exit cap@244,
RECORD_SIZE@450, deposit cap@304, deposit HEAD@483, or exit HEAD@313 still
makes `drainFacts mutated = false`, so this parent is false of that mutant.
Opcode pins name those PCs on the fragments the `∀` lemmas step.
-/

open Eip8282.Audit.Jumpdests
open EvmYul (UInt256)
open EvmYul.Operation
open Eip8282.Audit.WellFormed (QUEUE_HEAD)

/-- Runtime PCs the kill-line mutates, on the CFG fragments D1–D3 step.
Exit cap PUSH1 16 is clamp relative 18 = runtime 244; deposit cap
PUSH1 64 is clamp relative 19 = runtime 304; deposit PUSH1 QUEUE_HEAD
is update_head relative 12 = runtime 483; exit PUSH1 QUEUE_HEAD is
update_head relative 12 = runtime 313; exit PUSH1 68 (RECORD_SIZE)
is store_excess relative 8 = runtime 450. -/
theorem pdrain1_kill_line_opcodes :
    opcodeAt Fifo.exitClamp 18 =
      some (.PUSH1, some (UInt256.ofNat Fifo.exitCap, 1)) ∧
      Fifo.exitCapOffset = 244 ∧
      Exit.read_requests + 19 = 244 ∧
      opcodeAt Fifo.depositClamp 19 =
        some (.PUSH1, some (UInt256.ofNat Fifo.depositCap, 1)) ∧
      Fifo.depositCapOffset = 304 ∧
      Deposit.read_requests + 20 = 304 ∧
      opcodeAt Footprint.depositUpdateHeadWindow 11 =
        some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
      Deposit.update_head + 12 = 483 ∧
      opcodeAt Footprint.exitUpdateHeadWindow 11 =
        some (.PUSH1, some (UInt256.ofNat QUEUE_HEAD, 1)) ∧
      Exit.update_head + 12 = 313 ∧
      opcodeAt Footprint.exitStoreExcessWindow 7 =
        some (.PUSH1, some (UInt256.ofNat 68, 1)) ∧
      Exit.store_excess + 8 = 450 ∧
      Fifo.recordSize Kind.exit = 68 :=
  And.intro Fifo.exit_clamp_opcode_PUSH1_cap <|
  And.intro (rfl : Fifo.exitCapOffset = 244) <|
  And.intro Fifo.exit_clamp_rel_cap <|
  And.intro Fifo.deposit_clamp_opcode_PUSH1_cap <|
  And.intro (rfl : Fifo.depositCapOffset = 304) <|
  And.intro Fifo.deposit_clamp_rel_cap <|
  And.intro Footprint.deposit_update_head_PUSH1_QUEUE_HEAD <|
  And.intro Footprint.deposit_kill_line_immediate_pc <|
  And.intro Footprint.exit_update_head_PUSH1_QUEUE_HEAD <|
  And.intro Footprint.exit_kill_line_immediate_pc <|
  And.intro (rfl : opcodeAt Footprint.exitStoreExcessWindow 7 =
      some (.PUSH1, some (UInt256.ofNat 68, 1))) <|
  And.intro (rfl : Exit.store_excess + 8 = 450)
    Fifo.recordSize_exit

/-- D1: system SSTORE keys in {SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL};
every n ≥ 4 is unchanged after a system CFG store list.
Kill-line: PUSH1 QUEUE_HEAD at deposit 483 / exit 313. -/
def pdrain1_d1_footprint_forall :=
  And.intro (@Footprint.system_sstore_keys_subset) (@Footprint.stale_slots_preserved)

/-- D2: n = min(tail-head, capOf) wrap-free under WellFormed; oldest window;
full drain pointers (0,0); partial HEAD+=n, TAIL unchanged; caps 64/16.
Kill-line: PUSH1 cap at 304/244. Not a Xi reduction. -/
def pdrain1_d2_fifo_forall :=
  And.intro (@Fifo.fifo_system_spec) (@Fifo.fifo_pointers_both_kinds)

/-- D3: deposit amount BE storage to LE return for every drained index;
exit records are source||pubkey with no recode; a user fee quote does not
move QUEUE_HEAD / QUEUE_TAIL. -/
def pdrain1_d3_encode_forall :=
  And.intro (@Encode.deposit_amount_be_to_le) <|
  And.intro (@Encode.exit_record_encoding)
    (@Encode.user_fee_does_not_move_pointers)

/--
**P-DRAIN-1 parent.** CFG-level forall under WellFormed / CallHyp
(gas ≥ 30M, fuel ≥ 80000, system caller isUser = false) for SSTORE
footprint, FIFO count/pointers, and deposit BE to LE encode, plus the Wave-6
pdrain1_bytecode_parent traces. Not unfold systemCall. Not Xi ↔ Model.
Does not claim Xi computes FIFO for every excess.

The kill-line still falsifies this parent: pdrain1_bytecode_parent
contains drainFacts depositRuntime exitRuntime = true, and
Eip8282.Tests.PDrain1Mutant.mutant_refutes_parent shows that same
drainFacts is false on exit cap@244, RECORD_SIZE@450, deposit cap@304,
deposit HEAD@483 (to 9 and to 196), and exit HEAD@313 mutants. The opcode
conjuncts name those mutated PCs on the CFG fragments.

The leading conjunct pins what the CFG layer stepped against: the jumpdest
tables in every lemma below are the tables `EvmYul.EVM.Ξ` itself derives from
the pinned images, kernel-checked by `decide +kernel` (EVMYulLean 0ff72b2),
not hand-written arrays that happen to look right.
-/
def pdrain1_forall_pack :=
  And.intro Eip8282.Audit.Step.validJumps_are_Xi_tables <|
  And.intro pdrain1_kill_line_opcodes <|
  And.intro pdrain1_d1_footprint_forall <|
  And.intro pdrain1_d2_fifo_forall <|
  And.intro pdrain1_d3_encode_forall
    pdrain1_bytecode_parent

theorem pdrain1_forall_parent : type_of% pdrain1_forall_pack :=
  pdrain1_forall_pack

end Eip8282.Audit.Guarantees.PDrain1
