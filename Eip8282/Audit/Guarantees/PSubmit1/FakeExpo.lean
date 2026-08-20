import EvmYul.EVM.Semantics
import Eip8282.Audit.Model
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Bytecode

/-!
# S4 FakeExpo (attempt B) — induction on `Model.fakeExponential.go`

Pinned `fake_expo` equals `Model.fakeExponential` for all excess, as a
**Nat** fact. Shared with control quotes (`factor = 1`, `denominator = 17`).

**Honest split**

* Algebraic `∀`: lemmas about nested `go`, the matching `asmLoop`
  recurrence, `foldedExcess` / `bump_excess`, and the user-path quote
  `fakeExponential 1 (foldedExcess excess count TARGET) 17`.
* CFG fragment: `opcodeAt` of the **loop-body** and **bump_excess** hex
  chunks (not `fromHex` of the full runtime, not a `Ξ` stepper). The
  MUL/DIV/ADD/JUMPI stream is the same recurrence as `asmLoop`. Equality
  of `EvmYul.EVM.Ξ` to `go` for every excess is **not** claimed here.

No `sorry`, no project `axiom`, no `native_decide`, no extra 357/427
`Ξ` traces.
-/

namespace Eip8282.Audit.Guarantees.PSubmit1.FakeExpo

open EvmYul (UInt256)
open EvmYul.Operation
open Eip8282.Audit.Model (Kind State Record Wei inhibitor minRequestFee
  feeUpdateFraction targetOf fakeExponential currentFee effectiveExcess)
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests

set_option maxRecDepth 20000

/-! ## 1. Nested `go` -/

/-- `fakeExponential` is the 256-fuel entry of `go`. -/
theorem fakeExponential_eq_go (factor numerator denominator : Nat) :
    fakeExponential factor numerator denominator =
      fakeExponential.go numerator denominator 256 1 0 (factor * denominator) :=
  rfl

/-- Fuel exhaustion returns `output / denominator`, even if `accum ≠ 0`. -/
theorem go_fuel_zero (num den i output accum : Nat) :
    fakeExponential.go num den 0 i output accum = output / den := by
  simp [fakeExponential.go]

/-- The loop is done as soon as `numeratorAccum = 0`. -/
theorem go_accum_zero (num den i output : Nat) :
    ∀ fuel, fakeExponential.go num den fuel i output 0 = output / den := by
  intro fuel
  cases fuel with
  | zero =>
    simp [fakeExponential.go]
  | succ fuel =>
    simp [fakeExponential.go]

/-- One iteration of the EIP-1559 / EIP-7002 recurrence. -/
theorem go_step (num den fuel i output accum : Nat) (h : accum ≠ 0) :
    fakeExponential.go num den (fuel + 1) i output accum =
      fakeExponential.go num den fuel (i + 1) (output + accum)
        (accum * num / (den * i)) := by
  simp [fakeExponential.go, h]

/-! ## 2. `asmLoop` — same recurrence as `go`, not a CFG stepper -/

/-- Assembly-shaped recursor: `output += accum; accum := accum * num / (den * i); i += 1`,
fuel 256 at the `fakeExponential` entry. Copied from `go`, not from `Ξ`. -/
def asmLoop (numerator denominator fuel i output accum : Nat) : Nat :=
  match fuel with
  | 0 => output / denominator
  | fuel' + 1 =>
    if accum = 0 then
      output / denominator
    else
      asmLoop numerator denominator fuel' (i + 1) (output + accum)
        (accum * numerator / (denominator * i))

theorem asmLoop_fuel_zero (num den i output accum : Nat) :
    asmLoop num den 0 i output accum = output / den := by
  simp [asmLoop]

theorem asmLoop_accum_zero (num den i output : Nat) :
    ∀ fuel, asmLoop num den fuel i output 0 = output / den := by
  intro fuel
  cases fuel with
  | zero =>
    simp [asmLoop]
  | succ fuel =>
    simp [asmLoop]

theorem asmLoop_step (num den fuel i output accum : Nat) (h : accum ≠ 0) :
    asmLoop num den (fuel + 1) i output accum =
      asmLoop num den fuel (i + 1) (output + accum)
        (accum * num / (den * i)) := by
  simp [asmLoop, h]

/-- `asmLoop` and `go` coincide on every fuel. Induction on `go`'s fuel,
not a large CFG stepper. -/
theorem asmLoop_eq_go (num den : Nat) :
    ∀ fuel i output accum,
      asmLoop num den fuel i output accum =
        fakeExponential.go num den fuel i output accum := by
  intro fuel
  induction fuel with
  | zero =>
    intro i output accum
    rw [asmLoop_fuel_zero, go_fuel_zero]
  | succ fuel ih =>
    intro i output accum
    by_cases h : accum = 0
    · subst h
      rw [asmLoop_accum_zero, go_accum_zero]
    · rw [asmLoop_step num den fuel i output accum h,
          go_step num den fuel i output accum h]
      exact ih (i + 1) (output + accum) (accum * num / (den * i))

theorem fakeExponential_eq_asmLoop (factor num den : Nat) :
    fakeExponential factor num den =
      asmLoop num den 256 1 0 (factor * den) := by
  rw [fakeExponential_eq_go, asmLoop_eq_go]

/-! ## 3. Pinned `factor = 1`, `denominator = 17` -/

theorem minRequestFee_eq : minRequestFee = 1 := rfl
theorem feeUpdateFraction_eq : feeUpdateFraction = 17 := rfl

theorem fakeExponential_min_fee (numerator : Nat) :
    fakeExponential minRequestFee numerator feeUpdateFraction =
      fakeExponential.go numerator 17 256 1 0 17 := by
  rw [minRequestFee_eq, feeUpdateFraction_eq, fakeExponential_eq_go]

theorem fakeExponential_min_fee_asmLoop (numerator : Nat) :
    fakeExponential minRequestFee numerator feeUpdateFraction =
      asmLoop numerator 17 256 1 0 17 := by
  rw [fakeExponential_min_fee, ← asmLoop_eq_go]

/-- `i` starts at 1 and only increases, so `17 * i ≠ 0`. -/
theorem feeUpdateFraction_mul_ne_zero {i : Nat} (hi : 0 < i) :
    feeUpdateFraction * i ≠ 0 := by
  rw [feeUpdateFraction_eq]
  exact Nat.mul_ne_zero (by decide : 17 ≠ 0) (Nat.ne_of_gt hi)

/-! ## 4. `bump_excess`: folded numerator -/

/-- Bytecode `GT` / `bump_excess` fold: if `count > TARGET` then
`excess + (count - TARGET)`, else `excess`. Nat subtraction makes this
equal to `excess + (count - TARGET)` for every pair. -/
def foldedExcess (excess count target : Nat) : Nat :=
  if target < count then excess + (count - target) else excess

theorem foldedExcess_eq_add_sub (excess count target : Nat) :
    foldedExcess excess count target = excess + (count - target) := by
  unfold foldedExcess
  split_ifs with h
  · rfl
  · have : count ≤ target := Nat.not_lt.mp h
    rw [Nat.sub_eq_zero_of_le this, Nat.add_zero]

theorem effectiveExcess_eq_folded (s : State) :
    effectiveExcess s =
      foldedExcess s.storedExcess s.count (targetOf s.kind) := by
  rw [foldedExcess_eq_add_sub]
  rfl

theorem target_deposit : targetOf .deposit = 8 := rfl
theorem target_exit : targetOf .exit = 2 := rfl

theorem foldedExcess_deposit (excess count : Nat) :
    foldedExcess excess count (targetOf .deposit) =
      if 8 < count then excess + (count - 8) else excess := by
  rw [target_deposit]
  rfl

theorem foldedExcess_exit (excess count : Nat) :
    foldedExcess excess count (targetOf .exit) =
      if 2 < count then excess + (count - 2) else excess := by
  rw [target_exit]
  rfl

/-! ## 5. `∀ excess count` user-path quote -/

/-- Unrestricted Nat identity. The bytecode user path additionally
requires `excess ≠ INHIBITOR` (the inhibitor `JUMPI` sits *before*
`bump_excess` / `fake_expo`). -/
theorem currentFee_eq_fakeExponential (s : State) :
    currentFee s =
      fakeExponential 1 (foldedExcess s.storedExcess s.count (targetOf s.kind)) 17 := by
  unfold currentFee
  rw [minRequestFee_eq, feeUpdateFraction_eq, effectiveExcess_eq_folded]

theorem currentFee_eq_go (s : State) :
    currentFee s =
      fakeExponential.go
        (foldedExcess s.storedExcess s.count (targetOf s.kind)) 17 256 1 0 17 := by
  rw [currentFee_eq_fakeExponential, fakeExponential_eq_go]

theorem currentFee_eq_asmLoop (s : State) :
    currentFee s =
      asmLoop (foldedExcess s.storedExcess s.count (targetOf s.kind))
        17 256 1 0 17 := by
  rw [currentFee_eq_go, ← asmLoop_eq_go]

/-- `∀ excess count` (and kind). `excess ≠ INHIBITOR` is the user-quote
guard; the equality does not use it. -/
theorem user_quote
    (kind : Kind) (excess count : Nat)
    (_notInhibitor : excess ≠ inhibitor) :
    fakeExponential minRequestFee (foldedExcess excess count (targetOf kind))
        feeUpdateFraction =
      fakeExponential 1 (foldedExcess excess count (targetOf kind)) 17 := by
  rw [minRequestFee_eq, feeUpdateFraction_eq]

theorem user_quote_go
    (kind : Kind) (excess count : Nat)
    (_notInhibitor : excess ≠ inhibitor) :
    fakeExponential 1 (foldedExcess excess count (targetOf kind)) 17 =
      fakeExponential.go (foldedExcess excess count (targetOf kind))
        17 256 1 0 17 :=
  fakeExponential_eq_go 1 _ 17

theorem user_quote_fields
    (kind : Kind) (excess count : Nat) (queue : List Record) (balance : Wei)
    (_notInhibitor : excess ≠ inhibitor) :
    currentFee
        { kind := kind, storedExcess := excess, count := count,
          queue := queue, balance := balance } =
      fakeExponential 1 (foldedExcess excess count (targetOf kind)) 17 :=
  currentFee_eq_fakeExponential _

/-! ## 6. CFG fragment — loop-body hex (not full runtime)

Deposit loop JUMPDEST is F1 PC 100; done is 127. Exit loop is 99 / 126.
The chunk is the shared `fake_expo.eas` body, so ByteArray offset 0 is
`fake_expo_loop`. PUSH immediates are the F1 PCs.
-/

/-- Deposit PCs 100–131: loop JUMPDEST through post-loop `DIV` (`output / den`). -/
def depositLoopHex : String :=
  "5b5f821115607f57810190830284830290049160010191906064565b90939004"

/-- Exit PCs 99–130: same body; JUMPI dest 126, JUMP dest 99. -/
def exitLoopHex : String :=
  "5b5f821115607e57810190830284830290049160010191906063565b90939004"

def depositLoopChunk : ByteArray := fromHex depositLoopHex
def exitLoopChunk : ByteArray := fromHex exitLoopHex

theorem deposit_fake_expo_pcs :
    Deposit.fake_expo_loop = 100 ∧ Deposit.fake_expo_done = 127 :=
  ⟨rfl, rfl⟩

theorem exit_fake_expo_pcs :
    Exit.fake_expo_loop = 99 ∧ Exit.fake_expo_done = 126 :=
  ⟨rfl, rfl⟩

/-! ### Deposit loop opcodes (relative to F1 `fake_expo_loop`) -/

theorem deposit_loop_JUMPDEST :
    opcodeAt depositLoopChunk 0 = some (.JUMPDEST, none) := rfl

theorem deposit_loop_PUSH0 :
    opcodeAt depositLoopChunk 1 = some (.PUSH0, none) := rfl

theorem deposit_loop_DUP3 :
    opcodeAt depositLoopChunk 2 = some (.DUP3, none) := rfl

theorem deposit_loop_GT :
    opcodeAt depositLoopChunk 3 = some (.GT, none) := rfl

theorem deposit_loop_ISZERO :
    opcodeAt depositLoopChunk 4 = some (.ISZERO, none) := rfl

/-- JUMPI destination is F1 `fake_expo_done` = 127. -/
theorem deposit_loop_PUSH_done :
    opcodeAt depositLoopChunk 5 =
      some (.PUSH1, some (UInt256.ofNat Deposit.fake_expo_done, 1)) := rfl

theorem deposit_loop_JUMPI :
    opcodeAt depositLoopChunk 7 = some (.JUMPI, none) := rfl

theorem deposit_loop_DUP2 :
    opcodeAt depositLoopChunk 8 = some (.DUP2, none) := rfl

/-- `output += accum`. -/
theorem deposit_loop_ADD :
    opcodeAt depositLoopChunk 9 = some (.ADD, none) := rfl

theorem deposit_loop_SWAP1 :
    opcodeAt depositLoopChunk 10 = some (.SWAP1, none) := rfl

theorem deposit_loop_DUP4 :
    opcodeAt depositLoopChunk 11 = some (.DUP4, none) := rfl

/-- `accum * numerator`. -/
theorem deposit_loop_MUL_num :
    opcodeAt depositLoopChunk 12 = some (.MUL, none) := rfl

theorem deposit_loop_DUP5 :
    opcodeAt depositLoopChunk 13 = some (.DUP5, none) := rfl

theorem deposit_loop_DUP4_i :
    opcodeAt depositLoopChunk 14 = some (.DUP4, none) := rfl

/-- `denominator * i`. -/
theorem deposit_loop_MUL_den_i :
    opcodeAt depositLoopChunk 15 = some (.MUL, none) := rfl

theorem deposit_loop_SWAP1_div :
    opcodeAt depositLoopChunk 16 = some (.SWAP1, none) := rfl

/-- `accum := (accum * num) / (den * i)`. -/
theorem deposit_loop_DIV :
    opcodeAt depositLoopChunk 17 = some (.DIV, none) := rfl

theorem deposit_loop_SWAP2 :
    opcodeAt depositLoopChunk 18 = some (.SWAP2, none) := rfl

theorem deposit_loop_PUSH1_one :
    opcodeAt depositLoopChunk 19 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl

/-- `i += 1`. -/
theorem deposit_loop_ADD_i :
    opcodeAt depositLoopChunk 21 = some (.ADD, none) := rfl

theorem deposit_loop_SWAP2_back :
    opcodeAt depositLoopChunk 22 = some (.SWAP2, none) := rfl

theorem deposit_loop_SWAP1_back :
    opcodeAt depositLoopChunk 23 = some (.SWAP1, none) := rfl

/-- JUMP destination is F1 `fake_expo_loop` = 100. -/
theorem deposit_loop_PUSH_loop :
    opcodeAt depositLoopChunk 24 =
      some (.PUSH1, some (UInt256.ofNat Deposit.fake_expo_loop, 1)) := rfl

theorem deposit_loop_JUMP :
    opcodeAt depositLoopChunk 26 = some (.JUMP, none) := rfl

theorem deposit_loop_done_JUMPDEST :
    opcodeAt depositLoopChunk 27 = some (.JUMPDEST, none) := rfl

/-- Post-loop `output / denominator`. -/
theorem deposit_loop_done_DIV :
    opcodeAt depositLoopChunk 31 = some (.DIV, none) := rfl

/-! ### Exit loop opcodes (relative to F1 `fake_expo_loop` = 99) -/

theorem exit_loop_JUMPDEST :
    opcodeAt exitLoopChunk 0 = some (.JUMPDEST, none) := rfl

theorem exit_loop_PUSH0 :
    opcodeAt exitLoopChunk 1 = some (.PUSH0, none) := rfl

theorem exit_loop_DUP3 :
    opcodeAt exitLoopChunk 2 = some (.DUP3, none) := rfl

theorem exit_loop_GT :
    opcodeAt exitLoopChunk 3 = some (.GT, none) := rfl

theorem exit_loop_ISZERO :
    opcodeAt exitLoopChunk 4 = some (.ISZERO, none) := rfl

theorem exit_loop_PUSH_done :
    opcodeAt exitLoopChunk 5 =
      some (.PUSH1, some (UInt256.ofNat Exit.fake_expo_done, 1)) := rfl

theorem exit_loop_JUMPI :
    opcodeAt exitLoopChunk 7 = some (.JUMPI, none) := rfl

theorem exit_loop_DUP2 :
    opcodeAt exitLoopChunk 8 = some (.DUP2, none) := rfl

theorem exit_loop_ADD :
    opcodeAt exitLoopChunk 9 = some (.ADD, none) := rfl

theorem exit_loop_SWAP1 :
    opcodeAt exitLoopChunk 10 = some (.SWAP1, none) := rfl

theorem exit_loop_DUP4 :
    opcodeAt exitLoopChunk 11 = some (.DUP4, none) := rfl

theorem exit_loop_MUL_num :
    opcodeAt exitLoopChunk 12 = some (.MUL, none) := rfl

theorem exit_loop_DUP5 :
    opcodeAt exitLoopChunk 13 = some (.DUP5, none) := rfl

theorem exit_loop_DUP4_i :
    opcodeAt exitLoopChunk 14 = some (.DUP4, none) := rfl

theorem exit_loop_MUL_den_i :
    opcodeAt exitLoopChunk 15 = some (.MUL, none) := rfl

theorem exit_loop_SWAP1_div :
    opcodeAt exitLoopChunk 16 = some (.SWAP1, none) := rfl

theorem exit_loop_DIV :
    opcodeAt exitLoopChunk 17 = some (.DIV, none) := rfl

theorem exit_loop_SWAP2 :
    opcodeAt exitLoopChunk 18 = some (.SWAP2, none) := rfl

theorem exit_loop_PUSH1_one :
    opcodeAt exitLoopChunk 19 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl

theorem exit_loop_ADD_i :
    opcodeAt exitLoopChunk 21 = some (.ADD, none) := rfl

theorem exit_loop_SWAP2_back :
    opcodeAt exitLoopChunk 22 = some (.SWAP2, none) := rfl

theorem exit_loop_SWAP1_back :
    opcodeAt exitLoopChunk 23 = some (.SWAP1, none) := rfl

theorem exit_loop_PUSH_loop :
    opcodeAt exitLoopChunk 24 =
      some (.PUSH1, some (UInt256.ofNat Exit.fake_expo_loop, 1)) := rfl

theorem exit_loop_JUMP :
    opcodeAt exitLoopChunk 26 = some (.JUMP, none) := rfl

theorem exit_loop_done_JUMPDEST :
    opcodeAt exitLoopChunk 27 = some (.JUMPDEST, none) := rfl

theorem exit_loop_done_DIV :
    opcodeAt exitLoopChunk 31 = some (.DIV, none) := rfl

/-- The two runtimes share the loop body; only the JUMP/JUMPI
immediates differ (F1 PCs). -/
theorem loop_body_same_ops :
    opcodeAt depositLoopChunk 9 = some (.ADD, none) ∧
      opcodeAt depositLoopChunk 12 = some (.MUL, none) ∧
      opcodeAt depositLoopChunk 15 = some (.MUL, none) ∧
      opcodeAt depositLoopChunk 17 = some (.DIV, none) ∧
      opcodeAt depositLoopChunk 7 = some (.JUMPI, none) ∧
      opcodeAt exitLoopChunk 9 = some (.ADD, none) ∧
      opcodeAt exitLoopChunk 12 = some (.MUL, none) ∧
      opcodeAt exitLoopChunk 15 = some (.MUL, none) ∧
      opcodeAt exitLoopChunk 17 = some (.DIV, none) ∧
      opcodeAt exitLoopChunk 7 = some (.JUMPI, none) :=
  ⟨deposit_loop_ADD, deposit_loop_MUL_num, deposit_loop_MUL_den_i,
    deposit_loop_DIV, deposit_loop_JUMPI,
    exit_loop_ADD, exit_loop_MUL_num, exit_loop_MUL_den_i,
    exit_loop_DIV, exit_loop_JUMPI⟩

/-! ## 7. CFG fragment — `bump_excess` (F1 PCs 82 / 81)

Deposit: `JUMPDEST; PUSH1 8; SWAP1; SUB; ADD`.
Exit: `JUMPDEST; PUSH1 2; SWAP1; SUB; ADD`.
The preceding `GT` / `JUMPI @bump_excess` is in the dispatch chunk.
-/

/-- Deposit PCs 71–87: `PUSH1 8; DUP2; GT; JUMPI @82; … bump body`. -/
def depositBumpHex : String :=
  "60088111605257506058565b6008900301"

/-- Exit PCs 70–86: `PUSH1 2; DUP2; GT; JUMPI @81; … bump body`. -/
def exitBumpHex : String :=
  "60028111605157506057565b6002900301"

def depositBumpChunk : ByteArray := fromHex depositBumpHex
def exitBumpChunk : ByteArray := fromHex exitBumpHex

theorem deposit_bump_pc : Deposit.bump_excess = 82 := rfl
theorem exit_bump_pc : Exit.bump_excess = 81 := rfl

theorem deposit_bump_base_rel :
    Deposit.bump_excess - 71 = 11 := rfl

theorem exit_bump_base_rel :
    Exit.bump_excess - 70 = 11 := rfl

theorem deposit_dispatch_PUSH_target :
    opcodeAt depositBumpChunk 0 =
      some (.PUSH1, some (UInt256.ofNat 8, 1)) := rfl

theorem deposit_dispatch_DUP2 :
    opcodeAt depositBumpChunk 2 = some (.DUP2, none) := rfl

theorem deposit_dispatch_GT :
    opcodeAt depositBumpChunk 3 = some (.GT, none) := rfl

theorem deposit_dispatch_PUSH_bump :
    opcodeAt depositBumpChunk 4 =
      some (.PUSH1, some (UInt256.ofNat Deposit.bump_excess, 1)) := rfl

theorem deposit_dispatch_JUMPI :
    opcodeAt depositBumpChunk 6 = some (.JUMPI, none) := rfl

theorem deposit_bump_JUMPDEST :
    opcodeAt depositBumpChunk 11 = some (.JUMPDEST, none) := rfl

theorem deposit_bump_PUSH_target :
    opcodeAt depositBumpChunk 12 =
      some (.PUSH1, some (UInt256.ofNat 8, 1)) := rfl

theorem deposit_bump_SWAP1 :
    opcodeAt depositBumpChunk 14 = some (.SWAP1, none) := rfl

theorem deposit_bump_SUB :
    opcodeAt depositBumpChunk 15 = some (.SUB, none) := rfl

theorem deposit_bump_ADD :
    opcodeAt depositBumpChunk 16 = some (.ADD, none) := rfl

theorem exit_dispatch_PUSH_target :
    opcodeAt exitBumpChunk 0 =
      some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl

theorem exit_dispatch_DUP2 :
    opcodeAt exitBumpChunk 2 = some (.DUP2, none) := rfl

theorem exit_dispatch_GT :
    opcodeAt exitBumpChunk 3 = some (.GT, none) := rfl

theorem exit_dispatch_PUSH_bump :
    opcodeAt exitBumpChunk 4 =
      some (.PUSH1, some (UInt256.ofNat Exit.bump_excess, 1)) := rfl

theorem exit_dispatch_JUMPI :
    opcodeAt exitBumpChunk 6 = some (.JUMPI, none) := rfl

theorem exit_bump_JUMPDEST :
    opcodeAt exitBumpChunk 11 = some (.JUMPDEST, none) := rfl

theorem exit_bump_PUSH_target :
    opcodeAt exitBumpChunk 12 =
      some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl

theorem exit_bump_SWAP1 :
    opcodeAt exitBumpChunk 14 = some (.SWAP1, none) := rfl

theorem exit_bump_SUB :
    opcodeAt exitBumpChunk 15 = some (.SUB, none) := rfl

theorem exit_bump_ADD :
    opcodeAt exitBumpChunk 16 = some (.ADD, none) := rfl

/-- `bump_excess` body is `x := x + (count - TARGET)` when the `GT`
branch is taken. Combined with `foldedExcess_eq_add_sub`, that is the
numerator of `fakeExponential 1 · 17`. -/
theorem bump_excess_ops :
    opcodeAt depositBumpChunk 15 = some (.SUB, none) ∧
      opcodeAt depositBumpChunk 16 = some (.ADD, none) ∧
      opcodeAt exitBumpChunk 15 = some (.SUB, none) ∧
      opcodeAt exitBumpChunk 16 = some (.ADD, none) :=
  ⟨deposit_bump_SUB, deposit_bump_ADD, exit_bump_SUB, exit_bump_ADD⟩

/-! ## Summary (algebraic `∀` vs CFG fragment) -/

/-- Load-bearing algebraic package. CFG equality of `Ξ` to `go` is not
included; see the opcode listings above. -/
theorem s4_algebraic_forall
    (kind : Kind) (excess count : Nat)
    (_h : excess ≠ inhibitor) :
    currentFee
        { kind := kind, storedExcess := excess, count := count,
          queue := [], balance := 0 } =
      fakeExponential.go (foldedExcess excess count (targetOf kind))
        17 256 1 0 17 ∧
      fakeExponential 1 (foldedExcess excess count (targetOf kind)) 17 =
        asmLoop (foldedExcess excess count (targetOf kind)) 17 256 1 0 17 ∧
      foldedExcess excess count (targetOf kind) =
        excess + (count - targetOf kind) :=
  ⟨currentFee_eq_go _, fakeExponential_eq_asmLoop 1 _ 17,
    foldedExcess_eq_add_sub _ _ _⟩

end Eip8282.Audit.Guarantees.PSubmit1.FakeExpo
