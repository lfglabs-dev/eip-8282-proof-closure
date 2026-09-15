import Eip8282.Audit.Execution.Words

/-! Minimal fixtures and the five existing finite native receipts used by the
registered mutation refutations. Definitions, receipt statements and proof
bodies are retained from the original source; public names are preserved.
The old universal/model parents and unused mutation campaigns are removed.
A-NATIVE-DECIDE applies to these five receipts, not correctness or the funded
LOG0 witness. -/

section

namespace Eip8282.Audit.EvmRunner

open EvmYul

open EvmYul.EVM

open Eip8282.Audit.Bytecode

/-- `UInt256.ofNat`, re-exported so callers need not `open EvmYul` (which would
make `Storage` and `State` ambiguous against `Eip8282.Audit.Model`). -/
def u256 (n : Nat) : UInt256 := UInt256.ofNat n

def ZERO_U256 : UInt256 := UInt256.ofNat 0

def defaultGas : UInt256 := UInt256.ofNat 30000000

def oneEth : UInt256 := UInt256.ofNat (10 ^ 18)

def mkAccount (code : ByteArray) (balance : UInt256 := ZERO_U256)
    (storage : Storage := default) : Account .EVM :=
  { nonce := ZERO_U256
    balance := balance
    storage := storage
    tstorage := default
    code := code }

def storageFromList (pairs : List (Nat × Nat)) : Storage :=
  pairs.foldl (fun acc (k, v) => acc.insert (UInt256.ofNat k) (UInt256.ofNat v)) default

def worldWith
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (callerBalance : UInt256)
    (storage : Storage := default) : AccountMap .EVM :=
  let empty : AccountMap .EVM := default
  empty.insert target (mkAccount code ZERO_U256 storage)
    |>.insert caller (mkAccount ByteArray.empty callerBalance)

def callEnv
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (value : UInt256) (calldata : ByteArray)
    : ExecutionEnv .EVM :=
  { codeOwner := target
    sender := caller
    source := caller
    weiValue := value
    calldata := calldata
    code := code
    gasPrice := 0
    header := default
    depth := 0
    perm := true
    blobVersionedHashes := [] }

/-- Execute `code` at `target` as a message call from `caller`, via `EVM.Ξ`. -/
def run
    (fuel : Nat)
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (value : UInt256) (calldata : ByteArray)
    (gas : UInt256 := defaultGas)
    (storage : Storage := default)
    : RunResult :=
  let σ := worldWith target code caller (value + oneEth) storage
  Ξ fuel default default default σ σ gas default
    (callEnv target code caller value calldata)

/-- Non-system call on the builder-deposits runtime. `code` defaults to the pin. -/
def runDeposit (fuel : Nat) (caller : Nat) (value : Nat) (calldata : ByteArray)
    (code : ByteArray := depositRuntime) (storage : Storage := default) : RunResult :=
  run fuel depositAddr code (toAddress caller) (UInt256.ofNat value) calldata
    (storage := storage)

/-- System call on the builder-deposits runtime: same `run`, caller `sysAddr`,
zero value. Only the caller distinguishes it from `runDeposit`. -/
def runDepositSystem (fuel : Nat) (calldata : ByteArray)
    (code : ByteArray := depositRuntime) (storage : Storage := default) : RunResult :=
  run fuel depositAddr code sysAddr ZERO_U256 calldata (storage := storage)

/-- System call on the builder-exits runtime. -/
def runExitSystem (fuel : Nat) (calldata : ByteArray)
    (code : ByteArray := exitRuntime) (storage : Storage := default) : RunResult :=
  run fuel exitAddr code sysAddr ZERO_U256 calldata (storage := storage)

def isRevert (res : RunResult) : Bool :=
  match res with
  | .ok (.revert _ _) => true
  | _ => false

def isSuccess (res : RunResult) : Bool :=
  match res with
  | .ok (.success _ _) => true
  | _ => false

def successOutSize (res : RunResult) : Nat :=
  match res with
  | .ok (.success _ o) => o.size
  | _ => 0

/-- Byte `i` of a successful return buffer equals `b`. False on revert or OOB. -/
def successOutByteIs (res : RunResult) (i : Nat) (b : Nat) : Bool :=
  match res with
  | .ok (.success _ o) => i < o.size && (o.get! i).toNat == b
  | _ => false

/-- Big-endian value of a successful 32-byte return buffer. -/
def successOutWord (res : RunResult) : Option UInt256 :=
  match res with
  | .ok (.success _ o) =>
      if o.size = 32 then
        some (UInt256.ofNat (o.foldl (fun acc b => acc * 256 + b.toNat) 0))
      else none
  | _ => none

/-- Post-state storage slot of `target`; `none` unless the call succeeded. -/
def storageSlotAfter (res : RunResult) (target : AccountAddress) (slot : UInt256) :
    Option UInt256 :=
  match res with
  | .ok (.success (_, amap, _, _) _) =>
      amap.get? target |>.map (fun acc => acc.storage.getD slot ZERO_U256)
  | _ => none

def storageSlotIs (res : RunResult) (target : AccountAddress) (slot : UInt256)
    (expected : UInt256) : Bool :=
  match storageSlotAfter res target slot with
  | some v => v == expected
  | none => false

/-- Slots 0–3 of `target` after `res` equal the four given values. -/
def slots0to3Are (res : RunResult) (target : AccountAddress) (s0 s1 s2 s3 : Nat) : Bool :=
  storageSlotIs res target (UInt256.ofNat 0) (UInt256.ofNat s0) &&
  storageSlotIs res target (UInt256.ofNat 1) (UInt256.ofNat s1) &&
  storageSlotIs res target (UInt256.ofNat 2) (UInt256.ofNat s2) &&
  storageSlotIs res target (UInt256.ofNat 3) (UInt256.ofNat s3)

end Eip8282.Audit.EvmRunner

end

section

namespace Eip8282.Audit.Guarantees.PSubmit1

open Eip8282.Audit.Model

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Bytecode

/-- Well-formed 184-byte deposit input; bytes 80..87 are `MIN_AMOUNT` gwei. -/
def depositInput : ByteArray :=
  ByteArray.mk <|
    (Array.replicate 184 (7 : UInt8))
      |>.set! 80 0 |>.set! 81 0 |>.set! 82 0 |>.set! 83 0
      |>.set! 84 0x3b |>.set! 85 0x9a |>.set! 86 0xca |>.set! 87 0x00

open EvmYul (UInt256 Storage)

open EvmYul.EVM (D_J)

open EvmYul.Operation

open Eip8282.Audit.Jumpdests


set_option linter.unusedVariables false

end Eip8282.Audit.Guarantees.PSubmit1

end

section

namespace Eip8282.Audit.Guarantees.PDrain1

open Eip8282.Audit.Model

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Bytecode

def FUEL : Nat := 80000

/-- Interpreter fuel for the 64-record deposit drain. Each item does six
`SLOAD`s plus the little-endian amount rewrite, so the 17-exit budget of
`FUEL` is not enough. Gas is still `30_000_000`. -/
def DEPOSIT_CAP_FUEL : Nat := 300000

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

open Eip8282.Audit.Jumpdests

open EvmYul (UInt256)

open EvmYul.Operation

end Eip8282.Audit.Guarantees.PDrain1

end

section

namespace Eip8282.Audit.Guarantees.PControl1

open Eip8282.Audit.Model

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Bytecode

def FUEL : Nat := 80000

/-- A non-system, non-privileged caller. -/
def submitter : Nat := 0x1234

/-- `SLOT_EXCESS := excess`, `SLOT_COUNT := count`, empty queue. -/
def ctlStorage (excess count : Nat) :=
  storageFromList [(0, excess), (1, count), (2, 0), (3, 0)]

def INHIBITOR_NAT : Nat := 2 ^ 256 - 1

/-- The inhibited image: `SLOT_EXCESS = INHIBITOR`, empty queue. -/
def inhibitedStorage (count : Nat) := ctlStorage INHIBITOR_NAT count

/-- `TARGET_PER_BLOCK` of builder_deposits and builder_exits. Asserted against
the bytecode below, not assumed. -/
def depositTarget : Nat := 8

/-- The excess recurrence the assembly's `update_excess` block should implement:
`excess + count` over target, else zero. Note the assembly branches on strict
`GT`, so an exactly-on-target sum lands in `zero_excess`; both branches agree
there, and both boundary points are checked. -/
def expectedExcess (target excess count : Nat) : Nat :=
  if excess + count > target then excess + count - target else 0

/-- Well-formed 184-byte deposit input; bytes 80..87 are `MIN_AMOUNT` gwei. -/
def depositInput : ByteArray :=
  ByteArray.mk <|
    (Array.replicate 184 (7 : UInt8))
      |>.set! 80 0 |>.set! 81 0 |>.set! 82 0 |>.set! 83 0
      |>.set! 84 0x3b |>.set! 85 0x9a |>.set! 86 0xca |>.set! 87 0x00

/-- Strictly above the fee both runtimes quote at the images used below. -/
def payment : Nat := 10 ^ 18 + 100000

/-- One nonempty system calldata byte. Its *length*, not its value, is what the
`update_excess` block branches on. -/
def oneByte : ByteArray := ByteArray.mk #[0]

/-- **The caller gate.** The same bytes, the same storage image and the same
empty calldata take two different paths purely on `msg.sender`: an ordinary
caller is answered with a 32-byte fee quote and no storage write at all, while
`SYSTEM_ADDR` runs the system subroutine, which returns no records and rewrites
`SLOT_EXCESS`/`SLOT_COUNT`. This is the privilege boundary of P-CONTROL-1. -/
def depositGateFact (code : ByteArray) : Bool :=
  let u := runDeposit FUEL submitter 0 ByteArray.empty
    (code := code) (storage := ctlStorage 100 5)
  let s := runDepositSystem FUEL ByteArray.empty
    (code := code) (storage := ctlStorage 100 5)
  isSuccess u && successOutSize u == 32 && slots0to3Are u depositAddr 100 5 0 0
    && isSuccess s && successOutSize s == 0 && slots0to3Are s depositAddr 97 0 0 0

/-- Every system call clears the in-block counter, whatever it was. -/
def depositCountResetFact (code : ByteArray) : Bool :=
  [0, 1, 5, 8, 40].all fun c =>
    let r := runDepositSystem FUEL ByteArray.empty
      (code := code) (storage := ctlStorage 100 c)
    isSuccess r && storageSlotIs r depositAddr (u256 1) (u256 0)

/-- An empty system call rewrites `SLOT_EXCESS` to `max 0 (excess + count - 8)`.
The list straddles the target on both sides and lands on it exactly, so the
constant 8 is pinned by the trace set rather than merely mentioned. -/
def depositExcessFact (code : ByteArray) : Bool :=
  [(0, 0), (0, 7), (0, 8), (0, 9), (5, 3), (5, 4), (100, 5), (250, 0)].all
    fun (e, c) =>
      let r := runDepositSystem FUEL ByteArray.empty
        (code := code) (storage := ctlStorage e c)
      isSuccess r
        && storageSlotIs r depositAddr (u256 0) (u256 (expectedExcess depositTarget e c))

/-- **Inhibition gates users, never the system.** From the identical inhibited
image, both user entry points revert while both system entry points succeed, so
the drain and the re-enable path survive a kill switch that has stopped all
submission. -/
def depositInhibitedGatingFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage 5))
    && isRevert (runDeposit FUEL submitter payment depositInput
      (code := code) (storage := inhibitedStorage 5))
    && isSuccess (runDepositSystem FUEL ByteArray.empty
      (code := code) (storage := inhibitedStorage 5))
    && isSuccess (runDepositSystem FUEL oneByte
      (code := code) (storage := inhibitedStorage 5))

/-- **The quote uses the pre-submit counter, folded in at the target.** Quoting
at `(excess, count)` returns exactly the quote at `(excess + max 0 (count - 8), 0)`
— the `bump_excess` block — and the getter never writes. -/
def depositFeeCountFact (code : ByteArray) : Bool :=
  let quote (e c : Nat) :=
    successOutWord (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := ctlStorage e c))
  let readonly (e c : Nat) :=
    let r := runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := ctlStorage e c)
    isSuccess r && successOutSize r == 32 && slots0to3Are r depositAddr e c 0 0
  [(0, 0), (0, 8), (0, 9), (100, 5), (100, 20), (300, 17)].all fun (e, c) =>
    (quote e c).isSome
      && quote e c == quote (e + expectedExcess depositTarget 0 c) 0
      && readonly e c

/-- The folded quote is not the naive one: at `count = 20` the runtime charges
the `excess + 12` price, not the `excess + 20` price. Without this the previous
fact would also hold of a runtime that ignored the target. -/
def depositFeeDiscriminatesFact (code : ByteArray) : Bool :=
  let quote (e c : Nat) :=
    successOutWord (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := ctlStorage e c))
  (quote 100 20).isSome
    && quote 100 20 == quote 112 0
    && quote 100 20 != quote 120 0
    && quote 100 5 == quote 100 0

end Eip8282.Audit.Guarantees.PControl1

end

section

namespace Eip8282.Tests.PSubmit1Mutant

open Eip8282.Audit.Bytecode

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Guarantees.PSubmit1

/-- Offset of the `PUSH1 0xb8` immediate that sizes the user-path
`LOG0` (`60b85fa0`) on a paid deposit. Distinct from the calldatacopy
size at offset 269 and from every drain-only byte. -/
def depositLogSizeIdx : Nat := 274

/-- `PUSH1 184` → `PUSH1 0` on the user-path `LOG0` size only. -/
def logSizeMutatedDeposit : ByteArray := depositRuntime.set! depositLogSizeIdx 0x00

end Eip8282.Tests.PSubmit1Mutant

end

section

namespace Eip8282.Tests.PDrain1Mutant

open Eip8282.Audit.Bytecode

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Guarantees.PDrain1

/-- Offset of the second `PUSH1 0x10` (`MAX_PER_BLOCK`) in builder_exits'
system subroutine: the immediate that *clamps* the drain once the
`MAX > count` jump is not taken. -/
def exitCapIdx : Nat := 244

/-- Offset of the second `PUSH1 0x40` (`MAX_PER_BLOCK = 64`) in
builder_deposits' system subroutine: the immediate that *clamps* the
drain once the `MAX > count` jump is not taken. The comparison
immediate at offset 296 is the first `PUSH1 0x40` of that pair. -/
def depositCapIdx : Nat := 304

/-- Offset of the `PUSH1 QUEUE_HEAD` (`0x02`) that the *partial* deposit
drain uses to `SSTORE` the advanced head. The empty-queue / full-drain
reset is a different `PUSH0; PUSH1 2; SSTORE` whose operand sits at
offset 494 and is left alone. Slot `9` is `QUEUE_OFFSET + 5`, the last
remaining word of drained deposit item 0. -/
def depositHeadSlotIdx : Nat := 483

/-- Storage slot the Wave-3 mutant writes the new head into: last word
of drained item 0. -/
def depositItem0LastSlot : UInt8 := 9

/-- `PUSH1 16` → `PUSH1 8` on the over-cap clamp only. -/
def capMutatedExit : ByteArray := exitRuntime.set! exitCapIdx 0x08

/-- `PUSH1 64` → `PUSH1 32` on the deposit over-cap clamp only. -/
def capMutatedDeposit : ByteArray := depositRuntime.set! depositCapIdx 0x20

/-- `PUSH1 QUEUE_HEAD` → `PUSH1 9` on the partial-drain head store only.
The new head value `64` is written into slot 9 (last remaining word of
drained item 0) instead of slot 2. -/
def headSlotMutatedDeposit : ByteArray :=
  depositRuntime.set! depositHeadSlotIdx depositItem0LastSlot

/--
The cap mutant's mechanism, spelled out against the parent's own conjuncts.
Seventeen queued exits now return `8 * 68 = 544` bytes and advance the head
by 8, not 16. The under-cap two-record drain is untouched, because that
path never loads the clamp immediate.
-/
theorem cap_mutant_halves_the_over_cap_drain :
    successOutSize (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17)) = 544
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17))
        exitAddr (u256 2) (u256 8) = true
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17))
        exitAddr (u256 3) (u256 17) = true
    ∧ exitOverCapFact capMutatedExit = false
    ∧ exitUnderCapFifoFact capMutatedExit = true := by
  native_decide

/--
The deposit-cap mutant's mechanism. Sixty-five queued deposits now
return `32 * 184 = 5888` bytes and advance the head by 32, not 64.
`QUEUE_TAIL` stays 65. The empty-queue and under-cap (1- and 2-record)
deposit drains are untouched, because those paths never load the clamp
immediate.
-/
theorem deposit_cap_mutant_halves_the_over_cap_drain :
    (let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := capMutatedDeposit) (storage := depositQueue65);
      successOutSize r = 5888
        ∧ storageSlotIs r depositAddr (u256 2) (u256 32) = true
        ∧ storageSlotIs r depositAddr (u256 3) (u256 65) = true)
    ∧ depositOverCapFact capMutatedDeposit = false
    ∧ depositEmptyDrainFact capMutatedDeposit = true
    ∧ depositFifoFact capMutatedDeposit = true := by
  native_decide

/--
The Wave-3 head-slot mutant's mechanism. Sixty-five queued deposits
still return 64 records and still *intend* to advance the head by 64,
but the `SSTORE` writes that `64` into slot 9 — the last remaining word
of drained item 0 — instead of into `QUEUE_HEAD`. Slot 2 therefore
stays 0, slot 9 becomes 64 instead of the distinctive leftover word,
and `staleDepositRestIs 0` is false. The empty-queue and under-cap
full drains take the reset path (`PUSH0; PUSH1 2; SSTORE` at a
different offset) and stay true.
-/
theorem head_slot_mutant_overwrites_a_drained_word :
    (let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := headSlotMutatedDeposit) (storage := depositQueue65);
      successOutSize r = 11776
        ∧ storageSlotIs r depositAddr (u256 2) (u256 0) = true
        ∧ storageSlotIs r depositAddr (u256 3) (u256 65) = true
        ∧ storageSlotIs r depositAddr (u256 depositItem0LastSlot.toNat) (u256 64) = true
        ∧ staleDepositPk1Is r 0 0x1100 = true
        ∧ staleDepositRestIs r 0 = false
        ∧ staleDepositPk1Is r 63 0x113F = true
        ∧ staleDepositPk1Is r 64 0x1140 = true)
    ∧ depositOverCapFact headSlotMutatedDeposit = false
    ∧ depositEmptyDrainFact headSlotMutatedDeposit = true
    ∧ depositFifoFact headSlotMutatedDeposit = true := by
  native_decide

end Eip8282.Tests.PDrain1Mutant

end

section

namespace Eip8282.Tests.PControl1Mutant

open Eip8282.Audit.Bytecode

open Eip8282.Audit.EvmRunner

open Eip8282.Audit.Guarantees.PControl1

/-- Offset of the `EQ` in `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`,
the first four instructions of both runtimes. -/
def gateEqIdx : Nat := 22

/-- Offset of the `TARGET_PER_BLOCK` operand of `PUSH1 8` in builder_deposits'
`compute_excess` block (`ADD; PUSH1 8; SWAP1; SUB`), reachable only from the
system subroutine. -/
def sysTargetIdx : Nat := 571

/-- `EQ` → `LT`. `SYSTEM_ADDR < SYSTEM_ADDR` is false, so the system address no
longer opens the gate and every caller falls through to the user subroutine. -/
def gateMutatedDeposit : ByteArray := depositRuntime.set! gateEqIdx 0x10

/-- `PUSH1 8` → `PUSH1 9` in the system-side excess recurrence only. -/
def targetMutatedDeposit : ByteArray := depositRuntime.set! sysTargetIdx 0x09

/--
The gate mutant's mechanism, spelled out against the parent's own conjuncts.
With the gate cut, a call from `SYSTEM_ADDR` is answered as a *user* call: it
returns a 32-byte fee quote instead of draining, `SLOT_COUNT` keeps its old
value 5 instead of being reset, `SLOT_EXCESS` stays 100 instead of becoming 97 —
and, worst, from the inhibited image the system call now reverts, so the drain
and the re-enable path are lost exactly when the kill switch is down.
-/
theorem gate_mutant_loses_the_system_subroutine :
    successOutSize (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := ctlStorage 100 5)) = 32
    ∧ slots0to3Are (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := ctlStorage 100 5)) depositAddr 100 5 0 0 = true
    ∧ isRevert (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := inhibitedStorage 5)) = true
    ∧ depositGateFact gateMutatedDeposit = false
    ∧ depositCountResetFact gateMutatedDeposit = false
    ∧ depositInhibitedGatingFact gateMutatedDeposit = false := by
  native_decide

/--
The target mutant's mechanism. It is surgical: the user-facing quote is
untouched (the `bump_excess` copy of the target lives at a different offset), but
the system-side recurrence now subtracts 9, so `(100, 5)` folds to 96 instead of
97 and `(0, 9)` folds to 0 instead of 1.
-/
theorem target_mutant_shifts_only_the_system_recurrence :
    storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := targetMutatedDeposit) (storage := ctlStorage 100 5))
        depositAddr (u256 0) (u256 96) = true
    ∧ storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := targetMutatedDeposit) (storage := ctlStorage 0 9))
        depositAddr (u256 0) (u256 0) = true
    ∧ depositExcessFact targetMutatedDeposit = false
    ∧ depositFeeCountFact targetMutatedDeposit = true
    ∧ depositFeeDiscriminatesFact targetMutatedDeposit = true := by
  native_decide

end Eip8282.Tests.PControl1Mutant

end
