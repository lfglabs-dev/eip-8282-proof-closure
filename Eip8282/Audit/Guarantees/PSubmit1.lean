import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Guarantees.PSubmit1.Revert
import Eip8282.Audit.Guarantees.PSubmit1.Append
import Eip8282.Audit.Guarantees.PSubmit1.Fee
import Eip8282.Audit.Guarantees.PSubmit1.FakeExpo

namespace Eip8282.Audit.Guarantees.PSubmit1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pSubmit1, [.model, .evm]⟩

/-! ## Abstract model layer

Scaffolding over `Model.userCall`. These are *not* the load-bearing parent:
`userCall` is a hand-written abstraction with no proven relation to the
deployed bytecode. The load-bearing statement is `psubmit1_forall_parent`:
CFG-level `∀` under `WellFormed` / `CallHyp`, plus the Wave-6
`psubmit1_bytecode_parent` traces as the kill-line witness. F4 left
`A-ABSTRACT-TX` open, so this is not `Ξ ↔ Model`.
-/

theorem revert_is_atomic
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei) :
    (userCall s caller calldata value).isRevert = true →
      (userCall s caller calldata value).state = s := by
  unfold userCall
  by_cases hInh : inhibited s = true
  · simp [hInh]
  · simp [hInh]
    by_cases hEmpty : calldata = []
    · simp [hEmpty]
      by_cases hVal : value = 0
      · simp [hVal]
      · have : ¬ value = 0 := hVal
        simp [this]
    · simp [hEmpty]
      by_cases hAdm : admissible s calldata value = true
      · simp [hAdm]
      · simp [hAdm]

theorem success_count_and_balance
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    let t := (userCall s caller calldata value).state
    t.count = s.count + 1 ∧
      t.balance = s.balance + value ∧
      t.queue = (appendRecord s caller calldata value).queue := by
  unfold userCall
  simp [hInh, hne, hAdm, appendRecord]

theorem deposit_appends_calldata
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .deposit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.deposit calldata (depositAmount calldata)] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem exit_binds_caller
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .exit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.exit caller calldata] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem inhibited_blocks_users
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (h : inhibited s = true) :
    userCall s caller calldata value = .revert s := by
  unfold userCall
  simp [h]

/-! ## Pinned-bytecode layer

Everything below runs `Eip8282.Audit.Bytecode.depositRuntime` and
`exitRuntime` — the bytes of `pinned/bytecode/builder_{deposits,exits}/main.hex`
— inside `EvmYul.EVM.Ξ` via `Eip8282.Audit.EvmRunner`.

Each fact is a `Bool` parameterized by the runtime `code`. That is the whole
point: `Eip8282.Tests.PSubmit1Mutant` feeds a *byte-mutated* runtime to the
same `submitFacts` and gets `false`, so the parent is refuted by changing the
bytecode rather than by changing the model.
-/

open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

def FUEL : Nat := 80000

/-- A non-system, non-privileged caller. -/
def submitter : Nat := 0x1234

/-- `SLOT_EXCESS = 100`, `SLOT_COUNT = 5`, `SLOT_HEAD = 7`, `SLOT_TAIL = 9`.
Reachable-shaped: nonempty window `[head, tail)`, count below the deposit
target so the quote is `fake_exponential(1, 100, 17) = 357`. -/
def liveStorage := storageFromList [(0, 100), (1, 5), (2, 7), (3, 9)]

/-- The same queue state with `SLOT_EXCESS` holding `INHIBITOR = 2^256 - 1`. -/
def inhibitedStorage :=
  (storageFromList [(1, 5), (2, 7), (3, 9)]).insert ZERO_U256 INHIBITOR_U256

/-- Second reachable-shaped image: different excess/count/head/tail so the
parent is not a restatement of the Wave-4 traces. Count 3 is below the
deposit target (quote = `fake_exponential(1, 50, 17) = 18`) and above the
exit target (quote = `fake_exponential(1, 51, 17) = 19`). -/
def altStorage := storageFromList [(0, 50), (1, 3), (2, 2), (3, 6)]

/-- Inhibitor on the second image; head/tail/count stay reachable-shaped. -/
def altInhibitedStorage :=
  (storageFromList [(1, 3), (2, 2), (3, 6)]).insert ZERO_U256 INHIBITOR_U256

/-- `QUEUE_OFFSET + SLOT_TAIL * SLOTS_PER_ITEM` for builder_deposits. -/
def depositQueueBase : Nat := 4 + 9 * 6

/-- `QUEUE_OFFSET + SLOT_TAIL * SLOTS_PER_ITEM` for builder_exits. -/
def exitQueueBase : Nat := 4 + 9 * 3

/-- Append base on `altStorage` (`tail = 6`). -/
def altDepositQueueBase : Nat := 4 + 6 * 6

def altExitQueueBase : Nat := 4 + 6 * 3

/-- Quoted fees at `liveStorage` / `altStorage`, matching the getter traces. -/
def liveDepositFee : Nat := 357
def liveExitFee : Nat := 427
def altDepositFee : Nat := 18
def altExitFee : Nat := 19

/-- Well-formed 184-byte deposit input; bytes 80..87 are `MIN_AMOUNT` gwei. -/
def depositInput : ByteArray :=
  ByteArray.mk <|
    (Array.replicate 184 (7 : UInt8))
      |>.set! 80 0 |>.set! 81 0 |>.set! 82 0 |>.set! 83 0
      |>.set! 84 0x3b |>.set! 85 0x9a |>.set! 86 0xca |>.set! 87 0x00

/-- Well-formed 48-byte exit input (a BLS pubkey). -/
def exitInput : ByteArray := ByteArray.mk (Array.replicate 48 (9 : UInt8))

/-- Strictly above the fee both runtimes quote for `liveStorage`. -/
def payment : Nat := 10 ^ 18 + 100000

/-- Empty calldata with `value = 0` returns 32 bytes and leaves slots 0–3 alone. -/
def depositFeeGetterFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter 0 ByteArray.empty (code := code) (storage := liveStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some 357
    && slots0to3Are r depositAddr 100 5 7 9

/-- Empty calldata with `value ≠ 0` reverts, so no storage write survives. -/
def depositValueRejectedFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter 1 ByteArray.empty (code := code) (storage := liveStorage))

/-- A paid 184-byte write bumps only `SLOT_COUNT`/`SLOT_TAIL` and appends the
calldata verbatim as six `CALLDATALOAD`-sized words at the tail. -/
def depositPaidAppendFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := liveStorage)
  isSuccess r
    && slots0to3Are r depositAddr 100 6 7 10
    && (List.range 6).all (fun i =>
         storageSlotIs r depositAddr (u256 (depositQueueBase + i))
           (calldataWord depositInput (32 * i)))

/-- The same paid deposit emits one anonymous `LOG0` whose data is the
184-byte calldata `Ξ` copied (`push RECORD_SIZE; push 0; log0`). That
pins the first word, the amount at bytes 80..87, and the remaining
record bytes — the same fields `depositPaidAppendFact` stores. -/
def depositPaidLogFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := liveStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 184
    && successLog0Is r 0 depositInput

/-- With `SLOT_EXCESS = INHIBITOR`, both the getter and the write path revert. -/
def depositInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter payment depositInput
      (code := code) (storage := inhibitedStorage))
    && isRevert (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage))

def exitFeeGetterFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter 0 ByteArray.empty (code := code) (storage := liveStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some 427
    && slots0to3Are r exitAddr 100 5 7 9

def exitValueRejectedFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter 1 ByteArray.empty (code := code) (storage := liveStorage))

/-- A paid 48-byte write appends `msg.sender` followed by the pubkey words. The
first appended slot is the *caller*, not calldata: that is the authenticity bind. -/
def exitPaidAppendFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := liveStorage)
  isSuccess r
    && slots0to3Are r exitAddr 100 6 7 10
    && storageSlotIs r exitAddr (u256 exitQueueBase) (u256 submitter)
    && storageSlotIs r exitAddr (u256 (exitQueueBase + 1)) (calldataWord exitInput 0)
    && storageSlotIs r exitAddr (u256 (exitQueueBase + 2)) (calldataWord exitInput 32)

/-- 20-byte big-endian encoding of `submitter = 0x1234`, the source the
exit write path `mstore`s before the pubkey and then `LOG0`s. -/
def exitLogSource : ByteArray :=
  ByteArray.mk <| (Array.replicate 20 (0 : UInt8)).set! 18 0x12 |>.set! 19 0x34

/-- `RECORD_SIZE = 68` payload the exit runtime actually logs:
`msg.sender` (20) then the 48-byte pubkey. -/
def exitLogPayload : ByteArray := exitLogSource ++ exitInput

/-- The same paid exit emits one anonymous `LOG0` of 68 data bytes:
source address then pubkey — the same fields `exitPaidAppendFact` stores. -/
def exitPaidLogFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := liveStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 68
    && successLog0Is r 0 exitLogPayload

def exitInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter payment exitInput
      (code := code) (storage := inhibitedStorage))
    && isRevert (runExit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage))

/-- Ξ `.revert` carries no account map (`storageSlotAfter` is `none`), so a
reverting call cannot be shown to have written slots 0–3 or any of the
`n` queue words at `queueBase`. That is the Yellow Paper discard: the
underpay does not leave an observable mutated world. -/
def revertFreezesSlots (res : RunResult) (target : EvmYul.AccountAddress)
    (queueBase n : Nat) : Bool :=
  isRevert res
    && (storageSlotAfter res target (u256 0)).isNone
    && (storageSlotAfter res target (u256 1)).isNone
    && (storageSlotAfter res target (u256 2)).isNone
    && (storageSlotAfter res target (u256 3)).isNone
    && (List.range n).all (fun i =>
         (storageSlotAfter res target (u256 (queueBase + i))).isNone)

/-- Well-formed 184-byte deposit whose `msg.value` is strictly below the
fee quoted at `liveStorage` (`357 - 1`). Must revert; slots 0–3 and the
six words at the live tail are not observable as writes. -/
def depositUnderpayFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter (liveDepositFee - 1) depositInput
    (code := code) (storage := liveStorage)
  revertFreezesSlots r depositAddr depositQueueBase 6

/-- Well-formed 48-byte exit whose `msg.value` is strictly below the fee
quoted at `liveStorage` (`427 - 1`). Same freeze. -/
def exitUnderpayFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter (liveExitFee - 1) exitInput
    (code := code) (storage := liveStorage)
  revertFreezesSlots r exitAddr exitQueueBase 3

/-! ### Second storage image (`excess=50`, `count=3`, `head=2`, `tail=6`)

Fee getter, paid append, LOG0, inhibited revert, and underpay must all
still hold, so the parent is not a single-image restatement of Wave 4.
-/

def altDepositFeeGetterFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter 0 ByteArray.empty (code := code) (storage := altStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some altDepositFee
    && slots0to3Are r depositAddr 50 3 2 6

def altDepositPaidAppendFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := altStorage)
  isSuccess r
    && slots0to3Are r depositAddr 50 4 2 7
    && (List.range 6).all (fun i =>
         storageSlotIs r depositAddr (u256 (altDepositQueueBase + i))
           (calldataWord depositInput (32 * i)))

def altDepositPaidLogFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := altStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 184
    && successLog0Is r 0 depositInput

def altDepositInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter payment depositInput
      (code := code) (storage := altInhibitedStorage))
    && isRevert (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := altInhibitedStorage))

def altDepositUnderpayFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter (altDepositFee - 1) depositInput
    (code := code) (storage := altStorage)
  revertFreezesSlots r depositAddr altDepositQueueBase 6

def altExitFeeGetterFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter 0 ByteArray.empty (code := code) (storage := altStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some altExitFee
    && slots0to3Are r exitAddr 50 3 2 6

def altExitPaidAppendFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := altStorage)
  isSuccess r
    && slots0to3Are r exitAddr 50 4 2 7
    && storageSlotIs r exitAddr (u256 altExitQueueBase) (u256 submitter)
    && storageSlotIs r exitAddr (u256 (altExitQueueBase + 1)) (calldataWord exitInput 0)
    && storageSlotIs r exitAddr (u256 (altExitQueueBase + 2)) (calldataWord exitInput 32)

def altExitPaidLogFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := altStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 68
    && successLog0Is r 0 exitLogPayload

def altExitInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter payment exitInput
      (code := code) (storage := altInhibitedStorage))
    && isRevert (runExit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := altInhibitedStorage))

def altExitUnderpayFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter (altExitFee - 1) exitInput
    (code := code) (storage := altStorage)
  revertFreezesSlots r exitAddr altExitQueueBase 3

/-- The whole P-SUBMIT-1 write-path claim, as a function of the two runtimes.
Feeding a mutated `depCode` or `exitCode` must make this `false`. -/
def submitFacts (depCode exitCode : ByteArray) : Bool :=
  depositFeeGetterFact depCode
    && depositValueRejectedFact depCode
    && depositPaidAppendFact depCode
    && depositPaidLogFact depCode
    && depositInhibitedFact depCode
    && depositUnderpayFact depCode
    && exitFeeGetterFact exitCode
    && exitValueRejectedFact exitCode
    && exitPaidAppendFact exitCode
    && exitPaidLogFact exitCode
    && exitInhibitedFact exitCode
    && exitUnderpayFact exitCode
    && altDepositFeeGetterFact depCode
    && altDepositPaidAppendFact depCode
    && altDepositPaidLogFact depCode
    && altDepositInhibitedFact depCode
    && altDepositUnderpayFact depCode
    && altExitFeeGetterFact exitCode
    && altExitPaidAppendFact exitCode
    && altExitPaidLogFact exitCode
    && altExitInhibitedFact exitCode
    && altExitUnderpayFact exitCode

/--
**P-SUBMIT-1 parent, on pinned bytecode.**

`submitFacts depositRuntime exitRuntime` holds of the actual
sys-asm@83f9801 runtime bytes executed by `EvmYul.EVM.Ξ`. The extra
conjuncts pin the getter/rejection dispatch, the underpay freeze, and the
second-image getter outside `submitFacts` so the statement mentions
`runDeposit`/`runExit` and both runtimes directly.

Kept as the kill-line witness inside `psubmit1_forall_parent`. Feeding a
mutated runtime to `submitFacts` still makes this conjunction false
(RETURN@158, LOG size@274, CALLVALUE@161). Finite traces, not the `∀`.

Discharged by `native_decide`: `Ξ` calls the `partial def D_J_aux` jumpdest
scanner, which is kernel-opaque, so `decide`/`rfl` cannot reduce it. The
resulting compiler-generated axiom is disclosed in `Eip8282.Audit.Trust` and
as `A-NATIVE-DECIDE` in `audit/assumptions.yaml`.
-/
theorem psubmit1_bytecode_parent :
    submitFacts depositRuntime exitRuntime = true
    ∧ isSuccess (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runDeposit FUEL submitter 1 ByteArray.empty
        (code := depositRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runDeposit FUEL submitter (liveDepositFee - 1) depositInput
        (code := depositRuntime) (storage := liveStorage)) = true
    ∧ isSuccess (runExit FUEL submitter 0 ByteArray.empty
        (code := exitRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runExit FUEL submitter 1 ByteArray.empty
        (code := exitRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runExit FUEL submitter (liveExitFee - 1) exitInput
        (code := exitRuntime) (storage := liveStorage)) = true
    ∧ isSuccess (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := altStorage)) = true
    ∧ (successOutWord (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := altStorage))).map (·.toNat)
        = some altDepositFee
    ∧ isRevert (runDeposit FUEL submitter (altDepositFee - 1) depositInput
        (code := depositRuntime) (storage := altStorage)) = true
    ∧ isSuccess (runExit FUEL submitter 0 ByteArray.empty
        (code := exitRuntime) (storage := altStorage)) = true
    ∧ (successOutWord (runExit FUEL submitter 0 ByteArray.empty
        (code := exitRuntime) (storage := altStorage))).map (·.toNat)
        = some altExitFee
    ∧ isRevert (runExit FUEL submitter (altExitFee - 1) exitInput
        (code := exitRuntime) (storage := altStorage)) = true := by
  native_decide

/-! ## Public `∀` parent (CFG + kill-line traces)

S1–S4 are CFG / algebraic `∀` under `CallHyp` (well-formed storage, gas ≥ 30M,
fuel ≥ 80000, user caller). They do not execute `EvmYul.EVM.Ξ`. The Wave-6
`submitFacts` traces stay as the mutation-discriminating conjunct: a one-byte
cut of RETURN@158, LOG size@274, or CALLVALUE@161 still makes
`submitFacts mutated exitRuntime = false`, so this parent is false of that
mutant. Opcode pins name those PCs on the fragments the `∀` lemmas step.
-/

open EvmYul (UInt256 Storage)
open EvmYul.Operation
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (CallHyp)
open Eip8282.Audit.WellFormed (slotExcess slotCount queueHead queueTail)

set_option linter.unusedVariables false

/-- Runtime PCs the kill-line mutates, on the CFG fragments S1–S3 step.
Getter `RETURN` is suffix local 30 = runtime 158; handle_input `CALLVALUE`
is relative 2 = runtime 161; handle_input `PUSH1 184` is relative 114 =
runtime 273 (immediate at 274). -/
theorem psubmit1_kill_line_opcodes :
    opcodeAt Fee.depositSuffixChunk 30 = some (.RETURN, none) ∧
      opcodeAt Revert.depositUserPrefix 161 = some (.CALLVALUE, none) ∧
      opcodeAt Append.depositHandleInput 2 = some (.CALLVALUE, none) ∧
      opcodeAt Append.depositHandleInput 114 =
        some (.PUSH1, some (UInt256.ofNat 184, 1)) ∧
      Deposit.handle_input + 2 = 161 ∧
      Deposit.handle_input + 114 = 273 ∧
      Deposit.handle_input + 115 = 274 ∧
      Fee.suffixChunkBase + 30 = 158 :=
  ⟨Fee.deposit_suffix_opcode_RETURN, Revert.deposit_opcode_callvalue_161,
    Append.dOp_2, Append.dOp_114, rfl, rfl, rfl, rfl⟩

/--
**P-SUBMIT-1 parent.** CFG-level `∀` under `WellFormed` / `CallHyp`
(gas ≥ 30M, fuel ≥ 80000, user caller) for revert-before-writes, append+LOG0,
getter readonly, and algebraic `fakeExponential`, plus the Wave-6
`submitFacts` traces. Not `unfold userCall`. Not `Ξ ↔ Model`.

The kill-line still falsifies this parent: it contains
`submitFacts depositRuntime exitRuntime = true`, and
`Eip8282.Tests.PSubmit1Mutant.mutant_refutes_parent` shows that same
`submitFacts` is `false` on RETURN@158, LOG size@274, and CALLVALUE@161
mutants. The opcode conjuncts name those mutated PCs on the CFG fragments.
-/
theorem psubmit1_forall_parent :
    opcodeAt Fee.depositSuffixChunk 30 = some (.RETURN, none) ∧
      opcodeAt Revert.depositUserPrefix 161 = some (.CALLVALUE, none) ∧
      opcodeAt Append.depositHandleInput 2 = some (.CALLVALUE, none) ∧
      opcodeAt Append.depositHandleInput 114 =
        some (.PUSH1, some (UInt256.ofNat 184, 1)) ∧
      Deposit.handle_input + 2 = 161 ∧
      Deposit.handle_input + 115 = 274 ∧
      Fee.suffixChunkBase + 30 = 158 ∧
      (∀ pc, pc ∈ Revert.depositUserRevertJumpiPcs →
        opcodeAt Revert.depositUserPrefix pc = some (.JUMPI, none) ∧
          pc < Revert.depositFirstSstorePc ∧ pc < Revert.depositFirstLog0Pc) ∧
      (∀ pc, pc ∈ Revert.exitUserRevertJumpiPcs →
        opcodeAt Revert.exitUserPrefix pc = some (.JUMPI, none) ∧
          pc < Revert.exitFirstSstorePc ∧ pc < Revert.exitFirstLog0Pc) ∧
      (∀ {σ : Storage} (_h : CallHyp .deposit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hbad : env.calldatasize ≠ UInt256.ofNat 0 ∧
            env.calldatasize ≠ UInt256.ofNat 184),
        ∃ m, Revert.runSteps 8 Revert.depositUserPrefix env depositJumpdests
            { pc := 136, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Deposit.revert ∧
          Revert.depositBadCdsJumpiPc < Revert.depositFirstSstorePc) ∧
      (∀ {σ : Storage} (_h : CallHyp .exit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hbad : env.calldatasize ≠ UInt256.ofNat 0 ∧
            env.calldatasize ≠ UInt256.ofNat 48),
        ∃ m, Revert.runSteps 8 Revert.exitUserPrefix env exitJumpdests
            { pc := 135, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Exit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .deposit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (h0 : env.calldatasize = UInt256.ofNat 0)
          (hv : env.callvalue ≠ UInt256.ofNat 0),
        ∃ m, Revert.runSteps 11 Revert.depositUserPrefix env depositJumpdests
            { pc := 136, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Deposit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .exit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (h0 : env.calldatasize = UInt256.ofNat 0)
          (hv : env.callvalue ≠ UInt256.ofNat 0),
        ∃ m, Revert.runSteps 11 Revert.exitUserPrefix env exitJumpdests
            { pc := 135, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Exit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .deposit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hlt : env.callvalue < quotedFee),
        ∃ m, Revert.runSteps 6 Revert.depositUserPrefix env depositJumpdests
            { pc := 159, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Deposit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .exit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hlt : env.callvalue < quotedFee),
        ∃ m, Revert.runSteps 5 Revert.exitUserPrefix env exitJumpdests
            { pc := 158, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Exit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .deposit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hmin : UInt256.ofNat Revert.MIN_AMOUNT > Revert.amountOf env),
        ∃ m, Revert.runSteps 9 Revert.depositUserPrefix env depositJumpdests
            { pc := 167, stack := [quotedFee], gas := g } = .ok m ∧
          m.pc = Deposit.revert) ∧
      (∀ {σ : Storage} (_h : CallHyp .deposit σ) (quotedFee : UInt256)
          (env : Revert.TxEnv) (g : Nat) (hg : g ≥ Revert.fragmentGas)
          (hst : UInt256.sub env.callvalue quotedFee <
            UInt256.mul (UInt256.ofNat Revert.GWEI) (Revert.amountOf env)),
        ∃ m, Revert.runSteps 8 Revert.depositUserPrefix env depositJumpdests
            { pc := 191, stack := [Revert.amountOf env, quotedFee], gas := g } =
              .ok m ∧
          m.pc = Deposit.revert) ∧
      (∀ (env : Append.CallEnv) (σ : Storage) (fee : UInt256)
          (h : CallHyp .deposit σ) (huser : h.isUser = true)
          (hinh : slotExcess σ ≠ inhibitor)
          (hsize : env.calldata.size = 184)
          (hpay : Append.PaidDeposit env fee),
        ∃ m, Append.runFuel Append.depositHandleInput env 82
            (Append.depositStart σ fee) = .ok m ∧
          m.halted = true ∧
          m.logs = [(List.range 184).map (fun i => env.calldata.get! i)]) ∧
      (∀ (env : Append.CallEnv) (σ : Storage) (fee : UInt256)
          (h : CallHyp .exit σ) (huser : h.isUser = true)
          (hinh : slotExcess σ ≠ inhibitor)
          (hsize : env.calldata.size = 48)
          (hpay : Append.PaidExit env fee),
        ∃ m, Append.runFuel Append.exitHandleInput env 50
            (Append.exitStart σ fee) = .ok m ∧
          m.halted = true ∧ m.logs.length = 1) ∧
      (∀ (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
          (huser : h.isUser = true) (cds val : UInt256)
          (hcds : cds = UInt256.ofNat 0) (hval : val = UInt256.ofNat 0)
          (hinh : slotExcess σ ≠ inhibitor) (quote : UInt256),
        let obs := Fee.feeGetterObservation kind σ cds val quote h.gas
        obs.reverted = false ∧ obs.returnSize = 32 ∧
          obs.slotExcess = slotExcess σ ∧ obs.slotCount = slotCount σ ∧
          obs.queueHead = queueHead σ ∧ obs.queueTail = queueTail σ) ∧
      (∀ (kind : Kind) (excess count : Nat) (_notInh : excess ≠ inhibitor),
        currentFee
            { kind := kind, storedExcess := excess, count := count,
              queue := [], balance := 0 } =
          fakeExponential.go (FakeExpo.foldedExcess excess count (targetOf kind))
            17 256 1 0 17 ∧
          fakeExponential 1 (FakeExpo.foldedExcess excess count (targetOf kind)) 17 =
            FakeExpo.asmLoop (FakeExpo.foldedExcess excess count (targetOf kind))
              17 256 1 0 17 ∧
          FakeExpo.foldedExcess excess count (targetOf kind) =
            excess + (count - targetOf kind)) ∧
      submitFacts depositRuntime exitRuntime = true := by
  refine ⟨Fee.deposit_suffix_opcode_RETURN,
    Revert.deposit_opcode_callvalue_161, Append.dOp_2, Append.dOp_114,
    rfl, rfl, rfl, ?jumpisD, ?jumpisE, ?badD, ?badE, ?valD, ?valE,
    ?underD, ?underE, ?minD, ?stakeD, ?appD, ?appE, ?fee, ?s4,
    psubmit1_bytecode_parent.1⟩
  · exact Revert.deposit_every_user_revert_jumpi_before_writes.1
  · exact fun pc h => (Revert.exit_every_user_revert_jumpi_before_writes.1 pc h)
  · intro σ _h quotedFee env g hg hbad
    have h := Revert.deposit_bad_calldatasize_reverts_before_writes
      quotedFee _h env g hg hbad
    exact ⟨_, h.1, rfl, h.2.1⟩
  · intro σ _h quotedFee env g hg hbad
    have h := Revert.exit_bad_calldatasize_reverts_before_writes
      quotedFee _h env g hg hbad
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg h0 hv
    have h := Revert.deposit_value_on_getter_reverts_before_writes
      quotedFee _h env g hg h0 hv
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg h0 hv
    have h := Revert.exit_value_on_getter_reverts_before_writes
      quotedFee _h env g hg h0 hv
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg hlt
    have h := Revert.deposit_underpay_reverts_before_writes
      quotedFee _h env g hg hlt
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg hlt
    have h := Revert.exit_underpay_reverts_before_writes
      quotedFee _h env g hg hlt
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg hmin
    have h := Revert.deposit_min_amount_reverts_before_writes
      quotedFee _h env g hg hmin
    exact ⟨_, h.1, rfl⟩
  · intro σ _h quotedFee env g hg hst
    have h := Revert.deposit_stake_reverts_before_writes
      quotedFee _h env g hg hst
    exact ⟨_, h.1, rfl⟩
  · intro env σ fee h huser hinh hsize hpay
    have pack := Append.deposit_handle_input_append env σ fee h huser hinh hsize hpay
    refine ⟨_, pack.1, rfl, ?_⟩
    simpa [Append.done] using congrArg (fun l => [l]) pack.2.1
  · intro env σ fee h huser hinh hsize hpay
    have pack := Append.exit_handle_input_append env σ fee h huser hinh hsize hpay
    refine ⟨_, pack.1, rfl, ?_⟩
    simp [Append.done]
  · intro kind σ h huser cds val hcds hval hinh quote
    exact Fee.fee_getter_readonly kind σ h huser cds val hcds hval hinh quote
  · intro kind excess count hnot
    exact FakeExpo.s4_algebraic_forall kind excess count hnot

end Eip8282.Audit.Guarantees.PSubmit1
