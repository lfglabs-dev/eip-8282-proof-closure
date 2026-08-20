import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Guarantees.PControl1.Gate
import Eip8282.Audit.Guarantees.PControl1.Excess
import Eip8282.Audit.Guarantees.PControl1.Count
import Eip8282.Audit.Guarantees.PControl1.Ctor

namespace Eip8282.Audit.Guarantees.PControl1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pControl1, [.model, .evm]⟩

/-! ## Abstract model layer

Scaffolding over `Model.userCall` / `Model.systemCall`. These are *not* the
load-bearing parent: both are hand-written abstractions with no proven relation
to the deployed bytecode. The load-bearing statement is
`pcontrol1_forall_parent`: CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, caller class), plus the Wave-1 `pcontrol1_bytecode_parent` and
Wave-5 `pcontrol1_nonempty_bytecode_parent` traces as kill-line witnesses.
F4 left `A-ABSTRACT-TX` open, so this is not `Ξ ↔ Model`.
-/

theorem targets :
    targetOf .deposit = 8 ∧ targetOf .exit = 2 := by
  constructor <;> rfl

theorem initial_gating :
    inhibited initialDeposit = false ∧ inhibited initialExit = true := by
  constructor <;> rfl

theorem fee_getter_readonly
    (s : State) (caller : Address)
    (hInh : inhibited s = false) :
    userCall s caller [] 0 = .success s (toBeBytes (currentFee s) 32) := by
  unfold userCall
  simp [hInh]

theorem count_increments
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.count = s.count + 1 := by
  unfold userCall
  simp [hInh, hne, hAdm, appendRecord]

theorem system_resets_count (s : State) (b : Bool) :
    (systemCall s b).state.count = 0 := by
  unfold systemCall
  simp

theorem nonempty_sets_inhibitor (s : State) :
    (systemCall s true).state.storedExcess = inhibitor := by
  unfold systemCall nextExcess
  simp

theorem empty_clears_inhibitor (s : State) (h : inhibited s = true) :
    (systemCall s false).state.storedExcess = 0 := by
  unfold systemCall nextExcess
  simp [h]

theorem empty_updates_excess (s : State) (h : inhibited s = false) :
    (systemCall s false).state.storedExcess =
      if s.storedExcess + s.count ≥ targetOf s.kind then
        s.storedExcess + s.count - targetOf s.kind
      else 0 := by
  unfold systemCall nextExcess
  simp [h]

theorem inhibit_users_not_system
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei) (b : Bool)
    (h : inhibited s = true) :
    (userCall s caller calldata value).isRevert = true ∧
      (systemCall s b).isRevert = false := by
  constructor
  · unfold userCall; simp [h]
  · unfold systemCall; simp

/-! ## Pinned-bytecode layer

Everything below runs `Eip8282.Audit.Bytecode.depositRuntime` and `exitRuntime`
— the bytes of `pinned/bytecode/builder_{deposits,exits}/main.hex` — inside
`EvmYul.EVM.Ξ` via `Eip8282.Audit.EvmRunner`.

P-CONTROL-1 is about the *control plane*: who may drive the state machine
(`SYSTEM_ADDR` vs anyone else), what the in-block counter and the long-term
excess become after each kind of call, and whether inhibition is reversible.
Every claim below is therefore a pair of runs that differ only in `msg.sender`,
in the system calldata length, or in the stored excess — never in the code.

Each fact is a `Bool` parameterized by the runtime `code`, so
`Eip8282.Tests.PControl1Mutant` can feed a *byte-mutated* runtime to the same
`controlFacts` and get `false`.

The queue is held empty (`QUEUE_HEAD = QUEUE_TAIL = 0`) throughout, which keeps
the drained-record count at zero. That is deliberate: it isolates the control
state machine from the FIFO drain, which is P-DRAIN-1's subject.
-/

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
def exitTarget : Nat := 2

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

/-- Well-formed 48-byte exit input (a BLS pubkey). -/
def exitInput : ByteArray := ByteArray.mk (Array.replicate 48 (9 : UInt8))

/-- Strictly above the fee both runtimes quote at the images used below. -/
def payment : Nat := 10 ^ 18 + 100000

/-- One nonempty system calldata byte. Its *length*, not its value, is what the
`update_excess` block branches on. -/
def oneByte : ByteArray := ByteArray.mk #[0]

/-! ### builder_deposits control plane -/

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

/-- Nonempty system calldata stores `INHIBITOR` instead, and still resets the
counter. -/
def depositInhibitFact (code : ByteArray) : Bool :=
  [0, 5, 40].all fun c =>
    let r := runDepositSystem FUEL oneByte (code := code) (storage := ctlStorage 100 c)
    isSuccess r
      && storageSlotIs r depositAddr (u256 0) INHIBITOR_U256
      && storageSlotIs r depositAddr (u256 1) (u256 0)

/-- **Inhibition is reversible.** An empty system call from the inhibited image
clears `SLOT_EXCESS` to exactly `0` — not to `INHIBITOR + count - 8`, which is
what the ordinary recurrence would give. The `zero_excess` branch is what makes
the kill switch a switch rather than a latch. -/
def depositUninhibitFact (code : ByteArray) : Bool :=
  [0, 3, 40].all fun c =>
    let r := runDepositSystem FUEL ByteArray.empty
      (code := code) (storage := inhibitedStorage c)
    isSuccess r
      && storageSlotIs r depositAddr (u256 0) (u256 0)
      && storageSlotIs r depositAddr (u256 1) (u256 0)

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

/-- An accepted paid submission moves the *counter* by exactly one and leaves
`SLOT_EXCESS` untouched: in-block demand is absorbed by `SLOT_COUNT`, and only a
system call folds it into the long-term excess. -/
def depositCountIncrementFact (code : ByteArray) : Bool :=
  [0, 5, 8, 30].all fun c =>
    let r := runDeposit FUEL submitter payment depositInput
      (code := code) (storage := ctlStorage 100 c)
    isSuccess r
      && storageSlotIs r depositAddr (u256 1) (u256 (c + 1))
      && storageSlotIs r depositAddr (u256 0) (u256 100)

/-! ### builder_exits control plane

The same claims at `TARGET_PER_BLOCK = 2`. Running both runtimes is what shows
the target is read out of each contract rather than shared.
-/

def exitGateFact (code : ByteArray) : Bool :=
  let u := runExit FUEL submitter 0 ByteArray.empty
    (code := code) (storage := ctlStorage 100 5)
  let s := runExitSystem FUEL ByteArray.empty
    (code := code) (storage := ctlStorage 100 5)
  isSuccess u && successOutSize u == 32 && slots0to3Are u exitAddr 100 5 0 0
    && isSuccess s && successOutSize s == 0 && slots0to3Are s exitAddr 103 0 0 0

def exitExcessFact (code : ByteArray) : Bool :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (5, 3), (100, 5)].all fun (e, c) =>
    let r := runExitSystem FUEL ByteArray.empty
      (code := code) (storage := ctlStorage e c)
    isSuccess r
      && storageSlotIs r exitAddr (u256 0) (u256 (expectedExcess exitTarget e c))

def exitInhibitFact (code : ByteArray) : Bool :=
  [0, 5, 40].all fun c =>
    let r := runExitSystem FUEL oneByte (code := code) (storage := ctlStorage 100 c)
    isSuccess r
      && storageSlotIs r exitAddr (u256 0) INHIBITOR_U256
      && storageSlotIs r exitAddr (u256 1) (u256 0)

def exitUninhibitFact (code : ByteArray) : Bool :=
  [0, 3, 40].all fun c =>
    let r := runExitSystem FUEL ByteArray.empty
      (code := code) (storage := inhibitedStorage c)
    isSuccess r
      && storageSlotIs r exitAddr (u256 0) (u256 0)
      && storageSlotIs r exitAddr (u256 1) (u256 0)

def exitInhibitedGatingFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage 5))
    && isRevert (runExit FUEL submitter payment exitInput
      (code := code) (storage := inhibitedStorage 5))
    && isSuccess (runExitSystem FUEL ByteArray.empty
      (code := code) (storage := inhibitedStorage 5))
    && isSuccess (runExitSystem FUEL oneByte
      (code := code) (storage := inhibitedStorage 5))

def exitFeeCountFact (code : ByteArray) : Bool :=
  let quote (e c : Nat) :=
    successOutWord (runExit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := ctlStorage e c))
  [(0, 0), (0, 2), (0, 3), (100, 5), (100, 20)].all fun (e, c) =>
    (quote e c).isSome
      && quote e c == quote (e + expectedExcess exitTarget 0 c) 0

def exitCountIncrementFact (code : ByteArray) : Bool :=
  [0, 2, 5, 30].all fun c =>
    let r := runExit FUEL submitter payment exitInput
      (code := code) (storage := ctlStorage 100 c)
    isSuccess r
      && storageSlotIs r exitAddr (u256 1) (u256 (c + 1))
      && storageSlotIs r exitAddr (u256 0) (u256 100)

/-- The whole P-CONTROL-1 control-plane claim, as a function of the two
runtimes. Feeding a mutated `depCode` or `exitCode` must make this `false`. -/
def controlFacts (depCode exitCode : ByteArray) : Bool :=
  depositGateFact depCode
    && depositCountResetFact depCode
    && depositExcessFact depCode
    && depositInhibitFact depCode
    && depositUninhibitFact depCode
    && depositInhibitedGatingFact depCode
    && depositFeeCountFact depCode
    && depositFeeDiscriminatesFact depCode
    && depositCountIncrementFact depCode
    && exitGateFact exitCode
    && exitExcessFact exitCode
    && exitInhibitFact exitCode
    && exitUninhibitFact exitCode
    && exitInhibitedGatingFact exitCode
    && exitFeeCountFact exitCode
    && exitCountIncrementFact exitCode

/-! ### Nonempty-queue excess fold (Wave 5)

The previous section isolates the control state machine with
`QUEUE_HEAD = QUEUE_TAIL = 0`. That leaves open the question whether the
`update_excess` recurrence (`excess + count - TARGET`) still holds when the
system subroutine has just drained records. Wave 5 closes that gap: the same
`SLOT_EXCESS`/`SLOT_COUNT` updates must occur even though `QUEUE_HEAD`/`TAIL`
move and a nonzero `RECORD_SIZE * n` buffer is returned.

Each fact below is therefore a system call against a *nonempty* queue image.
`queueStorage` is the same layout P-DRAIN-1 uses, but the *assertions* are the
control ones (excess, count, inhibitor) together with the minimal drain
observations (return size, head/tail) that make the statement false if the
queue had been empty. P-DRAIN-1 already proves FIFO order and amount recoding;
this section does not duplicate that.

The facts are again `Bool` over the runtime `code`, so a byte-mutated runtime
can be fed to the same `nonemptyControlFacts` and must yield `false`.
-/

def DEPOSIT_CAP_FUEL : Nat := 300000

def queueStorage (excess count head tail : Nat) (words : List (Nat × Nat)) :=
  storageFromList ([(0, excess), (1, count), (2, head), (3, tail)] ++ words)

def exitSrc (i : Nat) : Nat := 0xA100 + i
def exitPk1 (i : Nat) : Nat := (0xB000 + i) * (2 ^ 240)
def exitPk2 (i : Nat) : Nat := (0xC000 + i) * (2 ^ 240)
def exitItemWords (i : Nat) : List (Nat × Nat) :=
  let base := 4 + 3 * i
  [(base, exitSrc i), (base + 1, exitPk1 i), (base + 2, exitPk2 i)]
def exitQueue (n : Nat) :=
  queueStorage 100 5 0 n ((List.range n).flatMap exitItemWords)

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
def depositAmtOf (i : Nat) : Nat := 0x0102030405060708 + i * 0x0101010101010101
def depositQueue (n : Nat) :=
  queueStorage 100 5 0 n ((List.range n).flatMap (fun i => depositItemWords i (depositAmtOf i)))

/-- Fee quote with a nonempty queue must not drain and must fold the counter at the
target, exactly as the empty-queue quote does. The queue pointers stay `0,2`. -/
def depositNonemptyFeeFact (code : ByteArray) : Bool :=
  let q := depositQueue 2
  let r := runDeposit FUEL submitter 0 ByteArray.empty (code := code) (storage := q)
  isSuccess r && successOutSize r == 32 && slots0to3Are r depositAddr 100 5 0 2
    && successOutWord r == successOutWord (runDeposit FUEL submitter 0 ByteArray.empty (code := code) (storage := ctlStorage 100 5))

def exitNonemptyFeeFact (code : ByteArray) : Bool :=
  let q := exitQueue 2
  let r := runExit FUEL submitter 0 ByteArray.empty (code := code) (storage := q)
  isSuccess r && successOutSize r == 32 && slots0to3Are r exitAddr 100 5 0 2

/-- Two queued deposits: under-cap full drain, excess `100+5-8=97`, return `2*184=368`. -/
def depositNonemptyUnderCapFact (code : ByteArray) : Bool :=
  let r := runDepositSystem FUEL ByteArray.empty (code := code) (storage := depositQueue 2)
  isSuccess r
    && successOutSize r == 368
    && slots0to3Are r depositAddr 97 0 0 0
    && storageSlotIs r depositAddr (u256 0) (u256 97)

/-- Sixty-five queued deposits: over-cap partial drain, `64*184=11776`, `HEAD=64`,
`TAIL=65`, excess still `97`. This is the case the Wave-1 empty parent never
exercises. -/
def depositNonemptyOverCapFact (code : ByteArray) : Bool :=
  let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty (code := code) (storage := depositQueue 65)
  isSuccess r
    && successOutSize r == 11776
    && slots0to3Are r depositAddr 97 0 64 65

/-- Two queued exits: `2*68=136`, `HEAD=0 TAIL=0` after full drain, excess `103`. -/
def exitNonemptyUnderCapFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := exitQueue 2)
  isSuccess r
    && successOutSize r == 136
    && slots0to3Are r exitAddr 103 0 0 0

/-- Seventeen queued exits: `16*68=1088`, `HEAD=16 TAIL=17`, excess `103`. -/
def exitNonemptyOverCapFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := exitQueue 17)
  isSuccess r
    && successOutSize r == 1088
    && storageSlotIs r exitAddr (u256 2) (u256 16)
    && storageSlotIs r exitAddr (u256 3) (u256 17)
    && storageSlotIs r exitAddr (u256 0) (u256 103)

/-- System `INHIBITOR` and re-enable with a nonempty queue: the queue still
drains, and the excess update is still `INHIBITOR` / `0`. -/
def depositNonemptyInhibitFact (code : ByteArray) : Bool :=
  let r := runDepositSystem FUEL oneByte (code := code) (storage := depositQueue 2)
  isSuccess r
    && storageSlotIs r depositAddr (u256 0) INHIBITOR_U256
    && storageSlotIs r depositAddr (u256 1) (u256 0)
    && successOutSize r == 368
    && slots0to3Are r depositAddr (2 ^ 256 - 1) 0 0 0

def exitNonemptyInhibitFact (code : ByteArray) : Bool :=
  let r := runExitSystem FUEL oneByte (code := code) (storage := exitQueue 2)
  isSuccess r
    && storageSlotIs r exitAddr (u256 0) INHIBITOR_U256
    && storageSlotIs r exitAddr (u256 1) (u256 0)
    && successOutSize r == 136
    && slots0to3Are r exitAddr (2 ^ 256 - 1) 0 0 0

def depositNonemptyUninhibitFact (code : ByteArray) : Bool :=
  let inhabited := queueStorage INHIBITOR_NAT 5 0 2 ((List.range 2).flatMap (fun i => depositItemWords i (depositAmtOf i)))
  let r := runDepositSystem FUEL ByteArray.empty (code := code) (storage := inhabited)
  isSuccess r
    && storageSlotIs r depositAddr (u256 0) (u256 0)
    && storageSlotIs r depositAddr (u256 1) (u256 0)
    && successOutSize r == 368
    && slots0to3Are r depositAddr 0 0 0 0

def exitNonemptyUninhibitFact (code : ByteArray) : Bool :=
  let inhabited := queueStorage INHIBITOR_NAT 5 0 2 ((List.range 2).flatMap exitItemWords)
  let r := runExitSystem FUEL ByteArray.empty (code := code) (storage := inhabited)
  isSuccess r
    && storageSlotIs r exitAddr (u256 0) (u256 0)
    && storageSlotIs r exitAddr (u256 1) (u256 0)
    && successOutSize r == 136
    && slots0to3Are r exitAddr 0 0 0 0

def nonemptyControlFacts (depCode exitCode : ByteArray) : Bool :=
  depositNonemptyFeeFact depCode
    && exitNonemptyFeeFact exitCode
    && depositNonemptyUnderCapFact depCode
    && depositNonemptyOverCapFact depCode
    && exitNonemptyUnderCapFact exitCode
    && exitNonemptyOverCapFact exitCode
    && depositNonemptyInhibitFact depCode
    && exitNonemptyInhibitFact exitCode
    && depositNonemptyUninhibitFact depCode
    && exitNonemptyUninhibitFact exitCode

/--
**P-CONTROL-1 empty-queue traces, on pinned bytecode.**

Kept as a kill-line witness inside `pcontrol1_forall_parent`. Feeding a
mutated runtime to `controlFacts` still makes this conjunction false
(EQ@22, TARGET 8@571). Finite traces, not the `∀`.

`controlFacts depositRuntime exitRuntime` holds of the actual sys-asm@83f9801
runtime bytes executed by `EvmYul.EVM.Ξ`. The conjuncts spelled out after it are
the three separations the guarantee is really about, stated directly on
`runDeposit`/`runDepositSystem` so the parent cannot be read as a definitional
restatement of `controlFacts`:

* the same call differs on `msg.sender` alone — a user is quoted a fee and
  writes nothing, `SYSTEM_ADDR` rewrites `SLOT_EXCESS` from 100 to 97 and
  `SLOT_COUNT` to 0;
* a nonempty system call latches `INHIBITOR`, and an empty one from the
  inhibited image clears it back to 0, so the kill switch is reversible;
* from the inhibited image the user path reverts while the system path still
  succeeds.

This is a finite set of concrete traces at a fixed family of storage images, not
a universally quantified P-CONTROL-1. See `A-EVM-WORLD`.

Discharged by `native_decide`: `Ξ` calls the `partial def D_J_aux` jumpdest
scanner, which is kernel-opaque, so `decide`/`rfl` cannot reduce it. The
resulting compiler-generated axiom is disclosed in `Eip8282.Audit.Trust` and as
`A-NATIVE-DECIDE` in `audit/assumptions.yaml`.
-/
theorem pcontrol1_bytecode_parent :
    controlFacts depositRuntime exitRuntime = true
    ∧ successOutSize (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := ctlStorage 100 5)) = 32
    ∧ slots0to3Are (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := ctlStorage 100 5)) depositAddr 100 5 0 0 = true
    ∧ slots0to3Are (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := ctlStorage 100 5)) depositAddr 97 0 0 0 = true
    ∧ storageSlotIs (runDepositSystem FUEL oneByte
        (code := depositRuntime) (storage := ctlStorage 100 5))
        depositAddr (u256 0) INHIBITOR_U256 = true
    ∧ storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := inhibitedStorage 3))
        depositAddr (u256 0) (u256 0) = true
    ∧ isRevert (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := inhibitedStorage 5)) = true
    ∧ isSuccess (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := inhibitedStorage 5)) = true
    ∧ slots0to3Are (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := ctlStorage 100 5)) exitAddr 103 0 0 0 = true
    ∧ isRevert (runExit FUEL submitter 0 ByteArray.empty
        (code := exitRuntime) (storage := inhibitedStorage 5)) = true
    ∧ isSuccess (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := inhibitedStorage 5)) = true := by
  native_decide

/--
**P-CONTROL-1 Wave 5: nonempty-queue excess fold, on pinned bytecode.**

Kept as a kill-line witness inside `pcontrol1_forall_parent`. Feeding a
mutated runtime to `nonemptyControlFacts` still makes this conjunction false
(TARGET 8@571, TARGET 2@401, and the gate EQ@22). Finite traces, not the `∀`.

`nonemptyControlFacts depositRuntime exitRuntime` holds of the same pinned
runtimes and `EvmYul.EVM.Ξ`, but against images where `QUEUE_HEAD = 0` and
`QUEUE_TAIL ∈ {2,17,65}`. The queue therefore contains distinctive records
(three slots per exit, six per deposit) and the system call must *both* drain
the FIFO *and* fold `SLOT_EXCESS` via `max(0, excess+count-TARGET)` / `INHIBITOR`.

The conjunction spelled out after `nonemptyControlFacts` makes the claim
load-bearing and not a restatement of Wave 1: a queue-empty image would give
`successOutSize = 0` and leave `QUEUE_HEAD = QUEUE_TAIL = 0`, so

* `depositNonemptyUnderCapFact` (`2*184 = 368`, `97 0 0 0`);
* `depositNonemptyOverCapFact` (`64*184 = 11776`, `97 0 64 65`);
* `exitNonemptyOverCapFact` (`16*68 = 1088`, `HEAD 16 TAIL 17`);
* and the fee quote leaving `HEAD 0 TAIL 2` untouched

would all be `false`. The nonempty queue is therefore essential, and the
control update is proved to be *independent* of how many records were drained.

Finite-trace, `A-EVM-WORLD`, discharged by `native_decide` for the same
`D_J_aux` reason as the Wave-1 parent.
-/
theorem pcontrol1_nonempty_bytecode_parent :
    nonemptyControlFacts depositRuntime exitRuntime = true
    ∧ successOutSize (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 2)) = 368
    ∧ slots0to3Are (runDepositSystem FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 2)) depositAddr 97 0 0 0 = true
    ∧ successOutSize (runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 65)) = 11776
    ∧ storageSlotIs (runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 65)) depositAddr (u256 2) (u256 64) = true
    ∧ storageSlotIs (runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 65)) depositAddr (u256 3) (u256 65) = true
    ∧ successOutSize (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 17)) = 1088
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := exitRuntime) (storage := exitQueue 17)) exitAddr (u256 2) (u256 16) = true
    ∧ slots0to3Are (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := depositQueue 2)) depositAddr 100 5 0 2 = true
    ∧ isSuccess (runDepositSystem FUEL oneByte
        (code := depositRuntime) (storage := depositQueue 2)) = true
    ∧ storageSlotIs (runDepositSystem FUEL oneByte
        (code := depositRuntime) (storage := depositQueue 2)) depositAddr (u256 0) INHIBITOR_U256 = true := by
  native_decide

/-! ## Public `∀` parent (CFG + kill-line traces)

C1–C4 are CFG-direct `∀` under `WellFormed` / `CallHyp` (gas ≥ 30M,
caller class). They do not execute `EvmYul.EVM.Ξ`. The Wave-1
`controlFacts` traces and Wave-5 `nonemptyControlFacts` traces stay as
the mutation-discriminating conjuncts: a one-byte cut of EQ@22,
TARGET 8@571, or TARGET 2@401 still makes those facts `false`, so this
parent is false of that mutant. Opcode pins name those PCs on the
fragments the `∀` lemmas step.
-/

/-- Runtime PCs the kill-line mutates, on the CFG fragments C1–C2 step.
Opening `EQ` is offset 22 on both runtimes; deposit `compute_excess`
`PUSH1 8` is local 70 of `update_excess` = runtime 571; exit `PUSH1 2`
is local 70 = runtime 401. -/
def pcontrol1_kill_line_opcodes :=
  And.intro (pcontrol1_opening_eq_jumpi .deposit) <|
  And.intro (pcontrol1_opening_eq_jumpi .exit) <|
  And.intro Excess.pcontrol1_excess_deposit_kill_line
    Excess.pcontrol1_excess_exit_kill_line

/-- C1: `CALLER = SYSTEM_ADDR` iff the opening `EQ`/`JUMPI` lands on
`read_requests`, for every well-formed storage and campaign-gas caller. -/
def pcontrol1_c1_gate_forall :=
  @pcontrol1_gate_forall

/-- C2: `∀` excess, count, calldata length: nonempty → `INHIBITOR`;
inhibited+empty → 0; else `max(0, excess+count−TARGET)` for targets 8
and 2. Queue length is unused. Kill-line immediates are deposit 571 and
exit 401. -/
def pcontrol1_c2_excess_forall :=
  And.intro (@Excess.pcontrol1_excess_forall) <|
  And.intro (@Excess.pcontrol1_excess_nonempty_forall) <|
  And.intro (@Excess.expectedExcess_nonempty) <|
  And.intro (@Excess.expectedExcess_inhibited)
    (@Excess.expectedExcess_fold)

/-- C3: paid user wraps `SLOT_COUNT += 1` and leaves excess; system
`store_excess` writes `SLOT_COUNT := 0`. `∀` prior count (mod 2^256). -/
def pcontrol1_c3_count_forall :=
  And.intro (@Count.paid_user_count_inc)
    (@Count.system_count_reset)

/-- C4: exit init stores `INHIBITOR` at slot 0 then returns runtime;
deposit init does not `SSTORE`. Closes `initial_gating` on bytes. -/
def pcontrol1_c4_ctor_forall :=
  And.intro Ctor.initial_gating_bytes <|
  And.intro (@Ctor.exit_ctor_stores_inhibitor)
    (@Ctor.deposit_ctor_storage_zero)

/--
**P-CONTROL-1 parent.** CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, caller class) for the caller gate, excess recurrence,
count increment/reset, and init-bytecode gating, plus the Wave-1
`pcontrol1_bytecode_parent` and Wave-5 `pcontrol1_nonempty_bytecode_parent`
traces. Not `unfold userCall` / `systemCall`. Not `Ξ ↔ Model`.

The kill-line still falsifies this parent: the kept trace theorems
contain `controlFacts depositRuntime exitRuntime = true` and
`nonemptyControlFacts depositRuntime exitRuntime = true`, and
`Eip8282.Tests.PControl1Mutant.mutant_refutes_parent` /
`wave5_mutant_refutes_nonempty_parent` show those same facts are `false`
on EQ@22, TARGET 8@571, and TARGET 2@401 mutants. The opcode conjuncts
name those mutated PCs on the CFG fragments.
-/
def pcontrol1_forall_conj :=
  And.intro pcontrol1_kill_line_opcodes <|
  And.intro pcontrol1_c1_gate_forall <|
  And.intro pcontrol1_c2_excess_forall <|
  And.intro pcontrol1_c3_count_forall <|
  And.intro pcontrol1_c4_ctor_forall <|
  And.intro pcontrol1_bytecode_parent
    pcontrol1_nonempty_bytecode_parent

theorem pcontrol1_forall_parent :
    type_of% pcontrol1_forall_conj :=
  pcontrol1_forall_conj

end Eip8282.Audit.Guarantees.PControl1
