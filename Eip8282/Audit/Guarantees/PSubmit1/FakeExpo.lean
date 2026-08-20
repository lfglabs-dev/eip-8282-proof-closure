import Eip8282.Audit.Model
import Eip8282.Audit.Step
import Eip8282.Audit.WellFormed

/-!
# S4 — pinned `fake_expo` equals `Model.fakeExponential`

Claim worker module. Does **not** edit the P-SUBMIT-1 parent, Fee/Revert/Append,
foundation files, or YAML.

## What is `∀`

* `asmFakeExpoGo` is a structural `Nat` rec of the shared include loop
  (PUSH/MUL/DIV/ADD, same recurrence as `Model.fakeExponential.go`).
* `asmFakeExpo factor numerator denominator = Model.fakeExponential …` for
  **all** `Nat` arguments (induction on loop fuel). Specialised to
  `minRequestFee = 1`, `feeUpdateFraction = 17`, and to every
  `excess < 2^256`.
* `foldExcess` is the `bump_excess` fold: `stored + max(0, count - target)`.
  Equals `Model.effectiveExcess` for all states. Getter quotes use this
  folded excess (no `Ξ`).
* `quotedFee` therefore equals `Model.currentFee` for all states. The Wave-6
  traces (357 / 427 at `(100, 5)`, 18 / 19 at `(50, 3)`) are the same
  function at those points — not new images.

## What is still a CFG fragment

* Opcode-at-PC on **short** hex snippets (`fromHex` of the loop body / entry /
  bump, not the full runtime). Jump immediates are the absolute F1 PCs.
* String-prefix facts: those snippets occur in the pinned runtime hex.
* A CFG stepper `feeCfgStep`. Closed: `compute_user_fee` initialises
  `(output, accum, i) = (0, factor*den, 1)`; the loop header `JUMPI`s to
  `fake_expo_done` when `accum = 0`; `bump_excess` is `stored + (count - TARGET)`
  on `UInt256`. Continue-iteration MUL/DIV is opcode-identified, not a full
  `Ξ` trace. Wrapping vs `Nat` on a continue step is not closed.
-/

namespace Eip8282.Audit.Guarantees.PSubmit1.FakeExpo

open EvmYul (UInt256)
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.Model
open GasConstants

set_option maxRecDepth 20000
set_option maxHeartbeats 400000

/-! ## Transcribed loop (`asmFakeExpo`) -/

/-- One loop of the shared `fake_expo` include, as a structurally recursive
`Nat` function. Argument order matches `Model.fakeExponential.go`
(`numerator`, `denominator` closed; then `fuel`, `i`, `output`, accum).

The bytecode does `accum * num / (i * den)`; `Nat.mul` commutes so this is
`Model.go`'s `den * i` in the divisor. Fuel 256 is the EIP-1559 bound used
by the model; the assembly itself loops until `accum = 0`. -/
def asmFakeExpoGo (numerator denominator fuel i output numeratorAccum : Nat) : Nat :=
  match fuel with
  | 0 => output / denominator
  | fuel' + 1 =>
      if numeratorAccum = 0 then
        output / denominator
      else
        let output' := output + numeratorAccum
        let next := numeratorAccum * numerator / (denominator * i)
        asmFakeExpoGo numerator denominator fuel' (i + 1) output' next

/-- EIP-1559 initialisation: `i = 1`, `output = 0`, `accum = factor * den`. -/
def asmFakeExpo (factor numerator denominator : Nat) : Nat :=
  asmFakeExpoGo numerator denominator 256 1 0 (factor * denominator)

theorem asmFakeExpoGo_zero
    (numerator denominator i output accum : Nat) :
    asmFakeExpoGo numerator denominator 0 i output accum = output / denominator :=
  rfl

theorem asmFakeExpoGo_zero_accum
    (numerator denominator fuel i output : Nat) :
    asmFakeExpoGo numerator denominator fuel i output 0 = output / denominator := by
  cases fuel with
  | zero => rfl
  | succ _ => rfl

theorem asmFakeExpoGo_succ
    (numerator denominator fuel i output accum : Nat) (h : accum ≠ 0) :
    asmFakeExpoGo numerator denominator (fuel + 1) i output accum =
      asmFakeExpoGo numerator denominator fuel (i + 1) (output + accum)
        (accum * numerator / (denominator * i)) := by
  simp [asmFakeExpoGo, h]

/-- Bytecode divisor `i * den` equals the model's `den * i`. -/
theorem divisor_comm (accum num i den : Nat) :
    accum * num / (den * i) = accum * num / (i * den) := by
  rw [Nat.mul_comm den i]

/-- Induction on loop fuel: transcribed `go` equals `Model.fakeExponential.go`. -/
theorem asmFakeExpoGo_eq_model_go
    (numerator denominator fuel i output accum : Nat) :
    asmFakeExpoGo numerator denominator fuel i output accum =
      Model.fakeExponential.go numerator denominator fuel i output accum := by
  induction fuel generalizing i output accum with
  | zero =>
      rfl
  | succ fuel ih =>
      have hAsm :
          asmFakeExpoGo numerator denominator (fuel + 1) i output accum =
            if accum = 0 then output / denominator
            else
              asmFakeExpoGo numerator denominator fuel (i + 1) (output + accum)
                (accum * numerator / (denominator * i)) :=
        rfl
      have hMod :
          Model.fakeExponential.go numerator denominator (fuel + 1) i output accum =
            if accum = 0 then output / denominator
            else
              Model.fakeExponential.go numerator denominator fuel (i + 1) (output + accum)
                (accum * numerator / (denominator * i)) :=
        rfl
      rw [hAsm, hMod]
      split_ifs
      · rfl
      · exact ih (i + 1) (output + accum)
          (accum * numerator / (denominator * i))

/-- `∀` factor, numerator, denominator: transcribed loop equals the model. -/
theorem asmFakeExpo_eq_fakeExponential
    (factor numerator denominator : Nat) :
    asmFakeExpo factor numerator denominator =
      Model.fakeExponential factor numerator denominator := by
  unfold asmFakeExpo Model.fakeExponential
  exact asmFakeExpoGo_eq_model_go numerator denominator 256 1 0
    (factor * denominator)

/-- Pinned constants: `MIN_FEE = 1`, `FEE_UPDATE_FRACTION = 17`. -/
theorem pinned_fee_constants :
    minRequestFee = 1 ∧ feeUpdateFraction = 17 :=
  ⟨rfl, rfl⟩

/-- The load-bearing `∀` on the quote: every excess, including every
`excess < 2^256` that can sit in `SLOT_EXCESS`. -/
theorem asmFakeExpo_eq_fakeExponential_pinned (excess : Nat) :
    asmFakeExpo 1 excess 17 = Model.fakeExponential 1 excess 17 :=
  asmFakeExpo_eq_fakeExponential 1 excess 17

theorem asmFakeExpo_eq_fakeExponential_word (excess : Nat)
    (_h : excess < UInt256.size) :
    asmFakeExpo minRequestFee excess feeUpdateFraction =
      Model.fakeExponential minRequestFee excess feeUpdateFraction :=
  asmFakeExpo_eq_fakeExponential _ _ _

/-! ## `bump_excess` fold (getter; no `Ξ`) -/

/-- Effective excess after the user-path `count > TARGET` bump.
Matches `bump_excess:` (`ADD` of `count - TARGET` into stored excess)
and the fall-through `POP` when `count ≤ TARGET`. Lean `Nat` subtraction
already yields `0` when `count ≤ target`, so this is
`storedExcess + (count - target)`. -/
def foldExcess (storedExcess count target : Nat) : Nat :=
  if target < count then storedExcess + (count - target) else storedExcess

theorem foldExcess_eq_add_sub (storedExcess count target : Nat) :
    foldExcess storedExcess count target = storedExcess + (count - target) := by
  unfold foldExcess
  split_ifs with h
  · rfl
  · have hle : count ≤ target := Nat.le_of_not_lt h
    simp [Nat.sub_eq_zero_of_le hle]

theorem effectiveExcess_eq_fold (s : Model.State) :
    effectiveExcess s = foldExcess s.storedExcess s.count (targetOf s.kind) :=
  (foldExcess_eq_add_sub s.storedExcess s.count (targetOf s.kind)).symm

theorem foldExcess_le_of_le (storedExcess count target : Nat)
    (h : count ≤ target) :
    foldExcess storedExcess count target = storedExcess := by
  unfold foldExcess
  simp [Nat.not_lt.mpr h]

theorem foldExcess_of_gt (storedExcess count target : Nat)
    (h : target < count) :
    foldExcess storedExcess count target = storedExcess + (count - target) := by
  unfold foldExcess
  simp [h]

/-- Deposit target 8, exit target 2 — the two `bump_excess` immediates. -/
theorem bump_targets :
    targetOf .deposit = 8 ∧ targetOf .exit = 2 :=
  ⟨rfl, rfl⟩

/-- Wave-6 storage images: folded excess (count 5 is below deposit target 8
and above exit target 2; count 3 likewise). -/
theorem fold_live_deposit : foldExcess 100 5 8 = 100 := rfl
theorem fold_live_exit : foldExcess 100 5 2 = 103 := rfl
theorem fold_alt_deposit : foldExcess 50 3 8 = 50 := rfl
theorem fold_alt_exit : foldExcess 50 3 2 = 51 := rfl

/-- Getter quote: `fake_expo(1, folded excess, 17)`. Shared with control. -/
def quotedFee (kind : Kind) (storedExcess count : Nat) : Nat :=
  asmFakeExpo minRequestFee (foldExcess storedExcess count (targetOf kind))
    feeUpdateFraction

/-- `∀` states: the transcribed quote is `Model.currentFee`. -/
theorem quotedFee_eq_currentFee (s : Model.State) :
    quotedFee s.kind s.storedExcess s.count = currentFee s := by
  unfold quotedFee currentFee
  rw [asmFakeExpo_eq_fakeExponential, ← effectiveExcess_eq_fold]

/-- Word-sized inputs: the same `∀`, with the campaign hypothesis that the
control words fit in `UInt256`. -/
theorem quotedFee_eq_currentFee_word (s : Model.State)
    (_he : s.storedExcess < UInt256.size) (_hc : s.count < UInt256.size) :
    quotedFee s.kind s.storedExcess s.count = currentFee s :=
  quotedFee_eq_currentFee s

/-! Wave-6 numeric quotes are the same `quotedFee` at the two campaign images
(`fold` 100/103 and 50/51). They are implied by `quotedFee_eq_currentFee`
plus `fold_live_*` / `fold_alt_*`; this module does not `native_decide` or
kernel-reduce the 256-fuel rec at those points. -/

/-! ## Pinned hex fragments (not full-runtime `fromHex`) -/

/-- First five `++` chunks of `depositRuntimeHex` (string only). -/
def depositFeePrefixHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff"
  ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14"
  ++ "6102705760015460088111605257506058565b60089003015b60119060018202"
  ++ "6001905f5b5f821115607f57810190830284830290049160010191906064565b"
  ++ "90939004925050503660b814609f57366102705734610270575f5260205ff35b"

def exitFeePrefixHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff"
  ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1461"
  ++ "01c65760015460028111605157506057565b60029003015b6011906001820260"
  ++ "01905f5b5f821115607e57810190830284830290049160010191906063565b90"
  ++ "9390049250505036603014609e57366101c657346101c6575f5260205ff35b34"

/-- `bump_excess:` at deposit PC 82. -/
def depositBumpHex : String := "5b6008900301"
def depositBump : ByteArray := fromHex depositBumpHex

/-- `compute_user_fee:` through the PUSH0 that seeds `output` (deposit PC 88). -/
def depositEntryHex : String := "5b601190600182026001905f"
def depositEntry : ByteArray := fromHex depositEntryHex

/-- Loop body + epilogue at deposit PC 100 (36 bytes). Immediates are absolute
(`0x7f` = 127, `0x64` = 100). -/
def depositLoopBodyHex : String :=
  "5b5f821115607f57810190830284830290049160010191906064565b9093900492505050"
def depositLoopBody : ByteArray := fromHex depositLoopBodyHex

/-- Exit `bump_excess:` at PC 81 (`TARGET = 2`). -/
def exitBumpHex : String := "5b6002900301"
def exitBump : ByteArray := fromHex exitBumpHex

/-- Exit `compute_user_fee:` at PC 87. Same ops as deposit. -/
def exitEntryHex : String := "5b601190600182026001905f"
def exitEntry : ByteArray := fromHex exitEntryHex

def exitLoopBodyHex : String :=
  "5b5f821115607e57810190830284830290049160010191906063565b9093900492505050"
def exitLoopBody : ByteArray := fromHex exitLoopBodyHex

theorem depositFeePrefixHex_eq :
    depositFeePrefixHex =
      "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff"
      ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14"
      ++ "6102705760015460088111605257506058565b60089003015b60119060018202"
      ++ "6001905f5b5f821115607f57810190830284830290049160010191906064565b"
      ++ "90939004925050503660b814609f57366102705734610270575f5260205ff35b" :=
  rfl

theorem exitFeePrefixHex_eq :
    exitFeePrefixHex =
      "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff"
      ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1461"
      ++ "01c65760015460028111605157506057565b60029003015b6011906001820260"
      ++ "01905f5b5f821115607e57810190830284830290049160010191906063565b90"
      ++ "9390049250505036603014609e57366101c657346101c6575f5260205ff35b34" :=
  rfl

/-- The five chunks are the opening of `depositRuntimeHex` / `exitRuntimeHex`
as written in `Bytecode.lean`. `String.startsWith` does not reduce on those
`++` spines, so the connection is this literal match plus the snippet infixes
below (same hex as the assembly at the F1 PCs). -/
theorem depositBumpHex_eq : depositBumpHex = "5b6008900301" := rfl
theorem depositEntryHex_eq : depositEntryHex = "5b601190600182026001905f" := rfl
theorem exitBumpHex_eq : exitBumpHex = "5b6002900301" := rfl
theorem exitEntry_eq_depositEntry : exitEntryHex = depositEntryHex := rfl

theorem deposit_loop_pcs :
    Deposit.bump_excess = 82 ∧
      Deposit.compute_user_fee = 88 ∧
      Deposit.fake_expo_loop = 100 ∧
      Deposit.fake_expo_done = 127 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem exit_loop_pcs :
    Exit.bump_excess = 81 ∧
      Exit.compute_user_fee = 87 ∧
      Exit.fake_expo_loop = 99 ∧
      Exit.fake_expo_done = 126 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Opcode-at-PC — bump / entry / loop snippets -/

theorem depositBump_op_JUMPDEST :
    opcodeAt depositBump 0 = some (.JUMPDEST, none) := rfl
theorem depositBump_op_PUSH1 :
    opcodeAt depositBump 1 = some (.PUSH1, some (UInt256.ofNat 8, 1)) := rfl
theorem depositBump_op_SWAP1 :
    opcodeAt depositBump 3 = some (.SWAP1, none) := rfl
theorem depositBump_op_SUB :
    opcodeAt depositBump 4 = some (.SUB, none) := rfl
theorem depositBump_op_ADD :
    opcodeAt depositBump 5 = some (.ADD, none) := rfl

theorem exitBump_op_JUMPDEST :
    opcodeAt exitBump 0 = some (.JUMPDEST, none) := rfl
theorem exitBump_op_PUSH1 :
    opcodeAt exitBump 1 = some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl
theorem exitBump_op_SUB :
    opcodeAt exitBump 4 = some (.SUB, none) := rfl
theorem exitBump_op_ADD :
    opcodeAt exitBump 5 = some (.ADD, none) := rfl

theorem depositEntry_op_JUMPDEST :
    opcodeAt depositEntry 0 = some (.JUMPDEST, none) := rfl
theorem depositEntry_op_PUSH1_frac :
    opcodeAt depositEntry 1 = some (.PUSH1, some (UInt256.ofNat 17, 1)) := rfl
theorem depositEntry_op_SWAP1 :
    opcodeAt depositEntry 3 = some (.SWAP1, none) := rfl
theorem depositEntry_op_PUSH1_min :
    opcodeAt depositEntry 4 = some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl
theorem depositEntry_op_DUP3 :
    opcodeAt depositEntry 6 = some (.DUP3, none) := rfl
theorem depositEntry_op_MUL :
    opcodeAt depositEntry 7 = some (.MUL, none) := rfl
theorem depositEntry_op_PUSH1_i :
    opcodeAt depositEntry 8 = some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl
theorem depositEntry_op_SWAP1_i :
    opcodeAt depositEntry 10 = some (.SWAP1, none) := rfl
theorem depositEntry_op_PUSH0 :
    opcodeAt depositEntry 11 = some (.PUSH0, none) := rfl

theorem depositLoop_op_JUMPDEST :
    opcodeAt depositLoopBody 0 = some (.JUMPDEST, none) := rfl
theorem depositLoop_op_PUSH0 :
    opcodeAt depositLoopBody 1 = some (.PUSH0, none) := rfl
theorem depositLoop_op_DUP3 :
    opcodeAt depositLoopBody 2 = some (.DUP3, none) := rfl
theorem depositLoop_op_GT :
    opcodeAt depositLoopBody 3 = some (.GT, none) := rfl
theorem depositLoop_op_ISZERO :
    opcodeAt depositLoopBody 4 = some (.ISZERO, none) := rfl
theorem depositLoop_op_PUSH1_done :
    opcodeAt depositLoopBody 5 =
      some (.PUSH1, some (UInt256.ofNat Deposit.fake_expo_done, 1)) := rfl
theorem depositLoop_op_JUMPI :
    opcodeAt depositLoopBody 7 = some (.JUMPI, none) := rfl
theorem depositLoop_op_DUP2 :
    opcodeAt depositLoopBody 8 = some (.DUP2, none) := rfl
theorem depositLoop_op_ADD :
    opcodeAt depositLoopBody 9 = some (.ADD, none) := rfl
theorem depositLoop_op_SWAP1 :
    opcodeAt depositLoopBody 10 = some (.SWAP1, none) := rfl
theorem depositLoop_op_DUP4 :
    opcodeAt depositLoopBody 11 = some (.DUP4, none) := rfl
theorem depositLoop_op_MUL :
    opcodeAt depositLoopBody 12 = some (.MUL, none) := rfl
theorem depositLoop_op_DUP5 :
    opcodeAt depositLoopBody 13 = some (.DUP5, none) := rfl
theorem depositLoop_op_DUP4_i :
    opcodeAt depositLoopBody 14 = some (.DUP4, none) := rfl
theorem depositLoop_op_MUL_den :
    opcodeAt depositLoopBody 15 = some (.MUL, none) := rfl
theorem depositLoop_op_SWAP1_div :
    opcodeAt depositLoopBody 16 = some (.SWAP1, none) := rfl
theorem depositLoop_op_DIV :
    opcodeAt depositLoopBody 17 = some (.DIV, none) := rfl
theorem depositLoop_op_SWAP2 :
    opcodeAt depositLoopBody 18 = some (.SWAP2, none) := rfl
theorem depositLoop_op_PUSH1_one :
    opcodeAt depositLoopBody 19 = some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl
theorem depositLoop_op_ADD_i :
    opcodeAt depositLoopBody 21 = some (.ADD, none) := rfl
theorem depositLoop_op_SWAP2_acc :
    opcodeAt depositLoopBody 22 = some (.SWAP2, none) := rfl
theorem depositLoop_op_SWAP1_out :
    opcodeAt depositLoopBody 23 = some (.SWAP1, none) := rfl
theorem depositLoop_op_PUSH1_back :
    opcodeAt depositLoopBody 24 =
      some (.PUSH1, some (UInt256.ofNat Deposit.fake_expo_loop, 1)) := rfl
theorem depositLoop_op_JUMP :
    opcodeAt depositLoopBody 26 = some (.JUMP, none) := rfl
theorem depositLoop_op_done_JUMPDEST :
    opcodeAt depositLoopBody 27 = some (.JUMPDEST, none) := rfl
theorem depositLoop_op_done_DIV :
    opcodeAt depositLoopBody 31 = some (.DIV, none) := rfl
theorem depositLoop_op_done_POP3 :
    opcodeAt depositLoopBody 35 = some (.POP, none) := rfl

theorem exitLoop_op_JUMPDEST :
    opcodeAt exitLoopBody 0 = some (.JUMPDEST, none) := rfl
theorem exitLoop_op_PUSH1_done :
    opcodeAt exitLoopBody 5 =
      some (.PUSH1, some (UInt256.ofNat Exit.fake_expo_done, 1)) := rfl
theorem exitLoop_op_JUMPI :
    opcodeAt exitLoopBody 7 = some (.JUMPI, none) := rfl
theorem exitLoop_op_DIV :
    opcodeAt exitLoopBody 17 = some (.DIV, none) := rfl
theorem exitLoop_op_PUSH1_back :
    opcodeAt exitLoopBody 24 =
      some (.PUSH1, some (UInt256.ofNat Exit.fake_expo_loop, 1)) := rfl
theorem exitLoop_op_JUMP :
    opcodeAt exitLoopBody 26 = some (.JUMP, none) := rfl

/-! ## CFG stepper for the fee fragment -/

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

def feeGasBound : Nat := 200

theorem feeGasBound_ge_Gverylow : feeGasBound ≥ Gverylow := by decide
theorem feeGasBound_ge_Glow : feeGasBound ≥ Glow := by decide
theorem feeGasBound_ge_Ghigh : feeGasBound ≥ Ghigh := by decide
theorem feeGasBound_ge_Gmid : feeGasBound ≥ Gmid := by decide
theorem feeGasBound_ge_Gjumpdest : feeGasBound ≥ Gjumpdest := by decide
theorem feeGasBound_ge_Gbase : feeGasBound ≥ Gbase := by decide

set_option linter.unusedSimpArgs false

/-- One CFG tick for the fee / `fake_expo` ops. Not `X`. -/
def feeCfgStep (code : ByteArray) (validJumps : Array UInt256) (m : CfgState) :
    Except CfgError CfgState :=
  match opcodeAt code m.pc with
  | some (.JUMPDEST, none) =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok { pc := m.pc + 1, stack := m.stack, gas := m.gas - Gjumpdest }
  | some (.PUSH0, none) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := UInt256.ofNat 0 :: m.stack,
              gas := m.gas - Gverylow }
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1 + width, stack := imm :: m.stack,
              gas := m.gas - Gverylow }
  | some (.DUP2, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := b :: a :: b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.DUP3, none) =>
      match m.stack with
      | a :: b :: c :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := c :: a :: b :: c :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.DUP4, none) =>
      match m.stack with
      | a :: b :: c :: d :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := d :: a :: b :: c :: d :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.DUP5, none) =>
      match m.stack with
      | a :: b :: c :: d :: e :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := e :: a :: b :: c :: d :: e :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.SWAP1, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := b :: a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.SWAP2, none) =>
      match m.stack with
      | a :: b :: c :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := c :: b :: a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.SWAP3, none) =>
      match m.stack with
      | a :: b :: c :: d :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := d :: b :: c :: a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.SWAP4, none) =>
      match m.stack with
      | a :: b :: c :: d :: e :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := e :: b :: c :: d :: a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.ADD, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := (a + b) :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.SUB, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := (a - b) :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.MUL, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Glow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := (a * b) :: rest, gas := m.gas - Glow }
      | _ => .error .stackUnderflow
  | some (.DIV, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Glow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := (a / b) :: rest, gas := m.gas - Glow }
      | _ => .error .stackUnderflow
  | some (.GT, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.gt a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.ISZERO, none) =>
      match m.stack with
      | a :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.isZero a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.POP, none) =>
      match m.stack with
      | _ :: rest =>
          if m.gas < Gbase then .error .outOfGas
          else .ok { pc := m.pc + 1, stack := rest, gas := m.gas - Gbase }
      | [] => .error .stackUnderflow
  | some (.JUMP, none) =>
      match m.stack with
      | dest :: rest =>
          if m.gas < Gmid then .error .outOfGas
          else if validJumps.contains dest then
            .ok { pc := dest.toNat, stack := rest, gas := m.gas - Gmid }
          else
            .error .badJump
      | [] => .error .stackUnderflow
  | some (.JUMPI, none) =>
      match m.stack with
      | dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond != UInt256.ofNat 0 then
            if validJumps.contains dest then
              .ok { pc := dest.toNat, stack := rest, gas := m.gas - Ghigh }
            else
              .error .badJump
          else
            .ok { pc := m.pc + 1, stack := rest, gas := m.gas - Ghigh }
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

theorem deposit_fake_expo_loop_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.fake_expo_loop) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  exact ⟨UInt256.ofNat Deposit.fake_expo_loop,
    mem_depositJumpdests_of_mem_nats (by decide), rfl⟩

theorem deposit_fake_expo_done_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.fake_expo_done) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  exact ⟨UInt256.ofNat Deposit.fake_expo_done,
    mem_depositJumpdests_of_mem_nats (by decide), rfl⟩

theorem toNat_deposit_loop :
    (UInt256.ofNat Deposit.fake_expo_loop).toNat = Deposit.fake_expo_loop :=
  rfl

theorem toNat_deposit_done :
    (UInt256.ofNat Deposit.fake_expo_done).toNat = Deposit.fake_expo_done :=
  rfl

private theorem bne_one_zero :
    (UInt256.ofNat 1 != UInt256.ofNat 0) = true := by
  decide

private theorem bne_zero_zero :
    (UInt256.ofNat 0 != UInt256.ofNat 0) = false := by
  decide

private theorem isZero_zero :
    UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  decide

private theorem gt_zero_zero :
    UInt256.gt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  decide

/-! ## CFG: `bump_excess` is `stored + (count − TARGET)` (UInt256) -/

theorem deposit_cfg_bump_JUMPDEST (count excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositBump depositJumpdests
        { pc := 0, stack := [count, excess], gas } =
      .ok { pc := 1, stack := [count, excess], gas := gas - Gjumpdest } := by
  unfold feeCfgStep
  simp only [depositBump_op_JUMPDEST]
  have : ¬ gas < Gjumpdest :=
    not_lt_of_ge (Nat.le_trans feeGasBound_ge_Gjumpdest hgas)
  simp [this]

theorem deposit_cfg_bump_PUSH1 (count excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositBump depositJumpdests
        { pc := 1, stack := [count, excess], gas := gas - Gjumpdest } =
      .ok { pc := 3, stack := [UInt256.ofNat 8, count, excess],
            gas := gas - Gjumpdest - Gverylow } := by
  unfold feeCfgStep
  simp only [depositBump_op_PUSH1]
  have hrem : gas - Gjumpdest ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_bump_SWAP1 (count excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositBump depositJumpdests
        { pc := 3, stack := [UInt256.ofNat 8, count, excess],
          gas := gas - Gjumpdest - Gverylow } =
      .ok { pc := 4, stack := [count, UInt256.ofNat 8, excess],
            gas := gas - Gjumpdest - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositBump_op_SWAP1]
  have hrem : gas - Gjumpdest - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_bump_SUB (count excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositBump depositJumpdests
        { pc := 4, stack := [count, UInt256.ofNat 8, excess],
          gas := gas - Gjumpdest - Gverylow - Gverylow } =
      .ok { pc := 5, stack := [count - UInt256.ofNat 8, excess],
            gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositBump_op_SUB]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_bump_ADD (count excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositBump depositJumpdests
        { pc := 5, stack := [count - UInt256.ofNat 8, excess],
          gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 6, stack := [(count - UInt256.ofNat 8) + excess],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositBump_op_ADD]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

/-! ## CFG: `compute_user_fee` seeds `(0, factor*den, 1)` -/

theorem deposit_cfg_entry_JUMPDEST (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 0, stack := [excess], gas } =
      .ok { pc := 1, stack := [excess], gas := gas - Gjumpdest } := by
  unfold feeCfgStep
  simp only [depositEntry_op_JUMPDEST]
  have : ¬ gas < Gjumpdest :=
    not_lt_of_ge (Nat.le_trans feeGasBound_ge_Gjumpdest hgas)
  simp [this]

theorem deposit_cfg_entry_PUSH1_frac (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 1, stack := [excess], gas := gas - Gjumpdest } =
      .ok { pc := 3, stack := [UInt256.ofNat 17, excess],
            gas := gas - Gjumpdest - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_PUSH1_frac]
  have hrem : gas - Gjumpdest ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_entry_SWAP1 (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 3, stack := [UInt256.ofNat 17, excess],
          gas := gas - Gjumpdest - Gverylow } =
      .ok { pc := 4, stack := [excess, UInt256.ofNat 17],
            gas := gas - Gjumpdest - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_SWAP1]
  have hrem : gas - Gjumpdest - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_entry_PUSH1_min (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 4, stack := [excess, UInt256.ofNat 17],
          gas := gas - Gjumpdest - Gverylow - Gverylow } =
      .ok { pc := 6, stack := [UInt256.ofNat 1, excess, UInt256.ofNat 17],
            gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_PUSH1_min]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_entry_DUP3 (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 6, stack := [UInt256.ofNat 1, excess, UInt256.ofNat 17],
          gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 7,
            stack :=
              [UInt256.ofNat 17, UInt256.ofNat 1, excess, UInt256.ofNat 17],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_DUP3]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_entry_MUL (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 7,
          stack :=
            [UInt256.ofNat 17, UInt256.ofNat 1, excess, UInt256.ofNat 17],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 8,
            stack :=
              [UInt256.ofNat 17 * UInt256.ofNat 1, excess, UInt256.ofNat 17],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Glow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_MUL]
  have hrem :
      gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow ≥ Glow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow < Glow :=
    not_lt_of_ge hrem
  simp [this]

theorem mul_one_17 : UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 := by
  decide

theorem deposit_cfg_entry_PUSH1_i (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 8,
          stack :=
            [UInt256.ofNat 17 * UInt256.ofNat 1, excess, UInt256.ofNat 17],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
              - Glow } =
      .ok { pc := 10,
            stack :=
              [UInt256.ofNat 1, UInt256.ofNat 17 * UInt256.ofNat 1, excess,
                UInt256.ofNat 17],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Glow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_PUSH1_i]
  have hrem :
      gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow ≥
        Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow <
          Gverylow :=
    not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_entry_SWAP1_i (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 10,
          stack :=
            [UInt256.ofNat 1, UInt256.ofNat 17 * UInt256.ofNat 1, excess,
              UInt256.ofNat 17],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
              - Glow - Gverylow } =
      .ok { pc := 11,
            stack :=
              [UInt256.ofNat 17 * UInt256.ofNat 1, UInt256.ofNat 1, excess,
                UInt256.ofNat 17],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Glow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_SWAP1_i]
  have hrem :
      gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow
        - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow
          - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

/-- After the entry snippet the stack is `[output, accum, i, excess, den]`
with `output = 0`, `accum = 1*17`, `i = 1`, `den = 17` — the same
initialisation as `asmFakeExpoGo _ _ 256 1 0 (1*17)`. -/
theorem deposit_cfg_entry_PUSH0 (excess : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositEntry depositJumpdests
        { pc := 11,
          stack :=
            [UInt256.ofNat 17 * UInt256.ofNat 1, UInt256.ofNat 1, excess,
              UInt256.ofNat 17],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
              - Glow - Gverylow - Gverylow } =
      .ok { pc := 12,
            stack :=
              [UInt256.ofNat 0, UInt256.ofNat 17 * UInt256.ofNat 1,
                UInt256.ofNat 1, excess, UInt256.ofNat 17],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Glow - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositEntry_op_PUSH0]
  have hrem :
      gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow
        - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Glow
          - Gverylow - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

theorem deposit_entry_init_stack (excess : UInt256) :
    [UInt256.ofNat 0, UInt256.ofNat 17 * UInt256.ofNat 1,
      UInt256.ofNat 1, excess, UInt256.ofNat 17] =
      [UInt256.ofNat 0, UInt256.ofNat 17, UInt256.ofNat 1, excess,
        UInt256.ofNat 17] := by
  simp [mul_one_17]

/-! ## CFG: loop header — `JUMPI @done` when `accum = 0` -/

theorem deposit_cfg_loop_JUMPDEST (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 0, stack := [output, accum, i, num, den], gas } =
      .ok { pc := 1, stack := [output, accum, i, num, den],
            gas := gas - Gjumpdest } := by
  unfold feeCfgStep
  simp only [depositLoop_op_JUMPDEST]
  have : ¬ gas < Gjumpdest :=
    not_lt_of_ge (Nat.le_trans feeGasBound_ge_Gjumpdest hgas)
  simp [this]

theorem deposit_cfg_loop_PUSH0 (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 1, stack := [output, accum, i, num, den],
          gas := gas - Gjumpdest } =
      .ok { pc := 2,
            stack := [UInt256.ofNat 0, output, accum, i, num, den],
            gas := gas - Gjumpdest - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_PUSH0]
  have hrem : gas - Gjumpdest ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_loop_DUP3 (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 2,
          stack := [UInt256.ofNat 0, output, accum, i, num, den],
          gas := gas - Gjumpdest - Gverylow } =
      .ok { pc := 3,
            stack := [accum, UInt256.ofNat 0, output, accum, i, num, den],
            gas := gas - Gjumpdest - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_DUP3]
  have hrem : gas - Gjumpdest - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_loop_GT (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 3,
          stack := [accum, UInt256.ofNat 0, output, accum, i, num, den],
          gas := gas - Gjumpdest - Gverylow - Gverylow } =
      .ok { pc := 4,
            stack :=
              [UInt256.gt accum (UInt256.ofNat 0), output, accum, i, num, den],
            gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_GT]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_loop_ISZERO (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 4,
          stack :=
            [UInt256.gt accum (UInt256.ofNat 0), output, accum, i, num, den],
          gas := gas - Gjumpdest - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 5,
            stack :=
              [UInt256.isZero (UInt256.gt accum (UInt256.ofNat 0)),
                output, accum, i, num, den],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_ISZERO]
  have hrem : gas - Gjumpdest - Gverylow - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_loop_PUSH1_done (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 5,
          stack :=
            [UInt256.isZero (UInt256.gt accum (UInt256.ofNat 0)),
              output, accum, i, num, den],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 7,
            stack :=
              [UInt256.ofNat Deposit.fake_expo_done,
                UInt256.isZero (UInt256.gt accum (UInt256.ofNat 0)),
                output, accum, i, num, den],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_PUSH1_done]
  have hrem :
      gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow < Gverylow :=
    not_lt_of_ge hrem
  simp [this]

private theorem header_gas_ge_Ghigh {gas : Nat} (hgas : gas ≥ feeGasBound) :
    gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow ≥
      Ghigh := by
  simp [feeGasBound] at hgas
  simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
  omega

/-- When `accum = 0` the header `JUMPI`s to deposit PC `fake_expo_done` (127).
Snippet PCs: loop body starts at 0. -/
theorem deposit_cfg_loop_JUMPI_zero (output i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 7,
          stack :=
            [UInt256.ofNat Deposit.fake_expo_done,
              UInt256.isZero (UInt256.gt (UInt256.ofNat 0) (UInt256.ofNat 0)),
              output, UInt256.ofNat 0, i, num, den],
          gas :=
            gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
              - Gverylow } =
      .ok { pc := Deposit.fake_expo_done,
            stack := [output, UInt256.ofNat 0, i, num, den],
            gas :=
              gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
                - Gverylow - Ghigh } := by
  unfold feeCfgStep
  simp only [depositLoop_op_JUMPI]
  have hrem :
      ¬ gas - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow <
          Ghigh :=
    not_lt_of_ge (header_gas_ge_Ghigh hgas)
  simp [hrem, gt_zero_zero, isZero_zero, bne_one_zero,
        deposit_fake_expo_done_contains, toNat_deposit_done]

/-- Continue body starts with `DUP2; ADD`, i.e. `output + accum`. -/
theorem deposit_cfg_loop_DUP2 (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 8, stack := [output, accum, i, num, den], gas } =
      .ok { pc := 9, stack := [accum, output, accum, i, num, den],
            gas := gas - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_DUP2]
  have : ¬ gas < Gverylow :=
    not_lt_of_ge (Nat.le_trans feeGasBound_ge_Gverylow hgas)
  simp [this]

theorem deposit_cfg_loop_ADD (output accum i num den : UInt256) (gas : Nat)
    (hgas : gas ≥ feeGasBound) :
    feeCfgStep depositLoopBody depositJumpdests
        { pc := 9, stack := [accum, output, accum, i, num, den],
          gas := gas - Gverylow } =
      .ok { pc := 10, stack := [accum + output, accum, i, num, den],
            gas := gas - Gverylow - Gverylow } := by
  unfold feeCfgStep
  simp only [depositLoop_op_ADD]
  have hrem : gas - Gverylow ≥ Gverylow := by
    simp [feeGasBound] at hgas
    simp [Gjumpdest, Gverylow, Glow, Ghigh, Gmid, Gbase]
    omega
  have : ¬ gas - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

end Eip8282.Audit.Guarantees.PSubmit1.FakeExpo
