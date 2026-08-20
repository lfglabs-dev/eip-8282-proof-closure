import Eip8282.Audit.Correspondence

/-!
C2: `∀` excess recurrence on the system `update_excess` block.

`EvmYul.EVM.X` / `Ξ` loop until halt, so this module does not reduce a
symbolic system call. It CFG-steps the pinned `update_excess` …
`SLOT_EXCESS` `SSTORE` under symbolic excess, count, and `calldatasize`.
Queue length never appears: the leftover stack word at entry is the
drain count (P-DRAIN-1) and is not read by this block.

Kill-line immediates (Wave 5): deposit runtime byte 571 `PUSH1 8`, exit
runtime byte 401 `PUSH1 2`, both inside `compute_excess`
(`ADD; PUSH1 TARGET; SWAP1; SUB`).
-/

namespace Eip8282.Audit.Guarantees.PControl1.Excess

open EvmYul
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model
open GasConstants

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! ## Labels and TARGET immediates

Relative layout of the block is identical on both runtimes. Absolute
PCs are F1's `update_excess` / `zero_excess` / `compute_excess` /
`set_inhibitor` / `store_excess`.
-/

@[simp] def blockBase : Kind → Nat
  | .deposit => Deposit.update_excess
  | .exit => Exit.update_excess

@[simp] def setInhibitorPc : Kind → Nat
  | .deposit => Deposit.set_inhibitor
  | .exit => Exit.set_inhibitor

@[simp] def zeroExcessPc : Kind → Nat
  | .deposit => Deposit.zero_excess
  | .exit => Exit.zero_excess

@[simp] def computeExcessPc : Kind → Nat
  | .deposit => Deposit.compute_excess
  | .exit => Exit.compute_excess

@[simp] def storeExcessPc : Kind → Nat
  | .deposit => Deposit.store_excess
  | .exit => Exit.store_excess

@[simp] def validJumps : Kind → Array UInt256
  | .deposit => depositJumpdests
  | .exit => exitJumpdests

/-- TARGET immediates of the system `GT` / `compute_excess` `PUSH1`s.
A one-byte mutant `8→9` (deposit 571) or `2→3` (exit 401) falsifies
every theorem that uses these constants. -/
def targetImm : Kind → Nat
  | .deposit => 8
  | .exit => 2

theorem targetImm_eq_targetOf (kind : Kind) :
    targetImm kind = targetOf kind := by
  cases kind <;> rfl

theorem targetImm_deposit : targetImm .deposit = 8 := rfl
theorem targetImm_exit : targetImm .exit = 2 := rfl

theorem blockBase_deposit : blockBase .deposit = 500 := rfl
theorem blockBase_exit : blockBase .exit = 330 := rfl

theorem setInhibitorPc_offset (kind : Kind) :
    setInhibitorPc kind = blockBase kind + 78 := by
  cases kind <;> rfl

theorem zeroExcessPc_offset (kind : Kind) :
    zeroExcessPc kind = blockBase kind + 60 := by
  cases kind <;> rfl

theorem computeExcessPc_offset (kind : Kind) :
    computeExcessPc kind = blockBase kind + 68 := by
  cases kind <;> rfl

theorem storeExcessPc_offset (kind : Kind) :
    storeExcessPc kind = blockBase kind + 112 := by
  cases kind <;> rfl

/-- Kill-line byte: `PUSH1` immediate of `compute_excess`. -/
theorem deposit_kill_line_pc : blockBase .deposit + 71 = 571 := rfl
theorem exit_kill_line_pc : blockBase .exit + 71 = 401 := rfl

theorem deposit_kill_line_is_compute_imm :
    Deposit.compute_excess + 3 = 571 :=
  rfl

theorem exit_kill_line_is_compute_imm :
    Exit.compute_excess + 3 = 401 :=
  rfl

/-! ## Spec -/

/-- Post-value of `SLOT_EXCESS` after `update_excess`.
Nonempty system calldata latches `INHIBITOR`; inhibited+empty clears to
0; otherwise `max(0, excess+count−TARGET)`. Assembly branches on strict
`GT`, so an exactly-on-target sum is 0 on both sides. -/
def expectedExcess (kind : Kind) (excess count : Nat)
    (calldataNonempty : Bool) : Nat :=
  if calldataNonempty then inhibitor
  else if excess = inhibitor then 0
  else if excess + count ≥ targetImm kind then
    excess + count - targetImm kind
  else 0

theorem expectedExcess_nonempty (kind : Kind) (excess count : Nat) :
    expectedExcess kind excess count true = inhibitor :=
  rfl

theorem expectedExcess_inhibited (kind : Kind) (count : Nat) :
    expectedExcess kind inhibitor count false = 0 := by
  simp [expectedExcess]

theorem expectedExcess_fold (kind : Kind) (excess count : Nat)
    (hne : excess ≠ inhibitor) :
    expectedExcess kind excess count false =
      if excess + count ≥ targetImm kind then
        excess + count - targetImm kind
      else 0 := by
  simp [expectedExcess, hne]

theorem expectedExcess_on_target (kind : Kind) (excess count : Nat)
    (hne : excess ≠ inhibitor) (heq : excess + count = targetImm kind) :
    expectedExcess kind excess count false = 0 := by
  simp [expectedExcess, hne, heq]

theorem expectedExcess_eq_nextExcess (kind : Kind) (σ : Storage)
    (balance : Wei) (calldataNonempty : Bool) :
    expectedExcess kind (slotExcess σ) (slotCount σ) calldataNonempty =
      nextExcess (toModel kind σ balance) calldataNonempty := by
  cases calldataNonempty with
  | true => rfl
  | false => simp [expectedExcess, nextExcess, inhibited, targetImm_eq_targetOf]

/-! ## Pinned hex of the block (source of the kill-line bytes)

Four 32-byte `++` chunks, same layout as `Bytecode.lean`. Local byte 0
is `update_excess`. The `compute_excess` `PUSH1 TARGET` is local 70–71
= hex offset 140 of the concatenation = chunk 2 offset 12.
-/

def depositExcessHex0 : String :=
  "5b36610242575f54600154817fffffffffffffffffffffffffffffffffffffff"
def depositExcessHex1 : String :=
  "ffffffffffffffffffffffffff1461023057600882820111610238575b50505f"
def depositExcessHex2 : String :=
  "610264565b0160089003610264565b7fffffffffffffffffffffffffffffffff"
def depositExcessHex3 : String :=
  "ffffffffffffffffffffffffffffffff5b5f55"

def exitExcessHex0 : String :=
  "5b36610198575f54600154817fffffffffffffffffffffffffffffffffffffff"
def exitExcessHex1 : String :=
  "ffffffffffffffffffffffffff146101865760028282011161018e575b50505f"
def exitExcessHex2 : String :=
  "6101ba565b01600290036101ba565b7fffffffffffffffffffffffffffffffff"
def exitExcessHex3 : String :=
  "ffffffffffffffffffffffffffffffff5b5f55"

/-- Chunk 2 hex chars 12–15 are the `compute_excess` `PUSH1 8` (runtime 570–571). -/
theorem depositHex2_compute_target :
    depositExcessHex2.get? ⟨12⟩ = some '6' ∧
      depositExcessHex2.get? ⟨13⟩ = some '0' ∧
      depositExcessHex2.get? ⟨14⟩ = some '0' ∧
      depositExcessHex2.get? ⟨15⟩ = some '8' := by
  decide

/-- Chunk 2 hex chars 12–15 are the `compute_excess` `PUSH1 2` (runtime 400–401). -/
theorem exitHex2_compute_target :
    exitExcessHex2.get? ⟨12⟩ = some '6' ∧
      exitExcessHex2.get? ⟨13⟩ = some '0' ∧
      exitExcessHex2.get? ⟨14⟩ = some '0' ∧
      exitExcessHex2.get? ⟨15⟩ = some '2' := by
  decide

/-! ## Opcode-at-PC encodings (short hex; kernel-reducible)

Each fact is `decode` of the instruction's own bytes, not of the 115-byte
block (that `fromHex` does not unfold in the kernel). The kill-line
`PUSH1` encodings are the load-bearing ones.
-/

theorem enc_JUMPDEST :
    opcodeAt (fromHex "5b") 0 = some (.JUMPDEST, none) :=
  rfl

theorem enc_CALLDATASIZE :
    opcodeAt (fromHex "36") 0 = some (.CALLDATASIZE, none) :=
  rfl

theorem enc_JUMPI :
    opcodeAt (fromHex "57") 0 = some (.JUMPI, none) :=
  rfl

theorem enc_JUMP :
    opcodeAt (fromHex "56") 0 = some (.JUMP, none) :=
  rfl

theorem enc_PUSH0 :
    opcodeAt (fromHex "5f") 0 = some (.PUSH0, none) :=
  rfl

theorem enc_SLOAD :
    opcodeAt (fromHex "54") 0 = some (.SLOAD, none) :=
  rfl

theorem enc_SSTORE :
    opcodeAt (fromHex "55") 0 = some (.SSTORE, none) :=
  rfl

theorem enc_DUP2 :
    opcodeAt (fromHex "81") 0 = some (.DUP2, none) :=
  rfl

theorem enc_DUP3 :
    opcodeAt (fromHex "82") 0 = some (.DUP3, none) :=
  rfl

theorem enc_SWAP1 :
    opcodeAt (fromHex "90") 0 = some (.SWAP1, none) :=
  rfl

theorem enc_EQ :
    opcodeAt (fromHex "14") 0 = some (.EQ, none) :=
  rfl

theorem enc_GT :
    opcodeAt (fromHex "11") 0 = some (.GT, none) :=
  rfl

theorem enc_ADD :
    opcodeAt (fromHex "01") 0 = some (.ADD, none) :=
  rfl

theorem enc_SUB :
    opcodeAt (fromHex "03") 0 = some (.SUB, none) :=
  rfl

theorem enc_POP :
    opcodeAt (fromHex "50") 0 = some (.POP, none) :=
  rfl

theorem enc_PUSH1_1 :
    opcodeAt (fromHex "6001") 0 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem enc_PUSH1_8 :
    opcodeAt (fromHex "6008") 0 =
      some (.PUSH1, some (UInt256.ofNat 8, 1)) :=
  rfl

theorem enc_PUSH1_2 :
    opcodeAt (fromHex "6002") 0 =
      some (.PUSH1, some (UInt256.ofNat 2, 1)) :=
  rfl

theorem enc_PUSH2_deposit_set_inhibitor :
    opcodeAt (fromHex "610242") 0 =
      some (.PUSH2, some (UInt256.ofNat Deposit.set_inhibitor, 2)) :=
  rfl

theorem enc_PUSH2_exit_set_inhibitor :
    opcodeAt (fromHex "610198") 0 =
      some (.PUSH2, some (UInt256.ofNat Exit.set_inhibitor, 2)) :=
  rfl

theorem enc_PUSH2_deposit_zero :
    opcodeAt (fromHex "610230") 0 =
      some (.PUSH2, some (UInt256.ofNat Deposit.zero_excess, 2)) :=
  rfl

theorem enc_PUSH2_exit_zero :
    opcodeAt (fromHex "610186") 0 =
      some (.PUSH2, some (UInt256.ofNat Exit.zero_excess, 2)) :=
  rfl

theorem enc_PUSH2_deposit_compute :
    opcodeAt (fromHex "610238") 0 =
      some (.PUSH2, some (UInt256.ofNat Deposit.compute_excess, 2)) :=
  rfl

theorem enc_PUSH2_exit_compute :
    opcodeAt (fromHex "61018e") 0 =
      some (.PUSH2, some (UInt256.ofNat Exit.compute_excess, 2)) :=
  rfl

theorem enc_PUSH2_deposit_store :
    opcodeAt (fromHex "610264") 0 =
      some (.PUSH2, some (UInt256.ofNat Deposit.store_excess, 2)) :=
  rfl

theorem enc_PUSH2_exit_store :
    opcodeAt (fromHex "6101ba") 0 =
      some (.PUSH2, some (UInt256.ofNat Exit.store_excess, 2)) :=
  rfl

/-! ## CFG opcode table of the block

`blockOp kind loc` is the instruction at local offset `loc`. JUMP/JUMPI
immediates are the F1 runtime PCs. The kill-line `PUSH1` at local 70 is
`targetImm` (8 or 2).
-/

def blockOp (kind : Kind) : Nat → Option (Operation .EVM × Option (UInt256 × Nat))
  | 0 => some (.JUMPDEST, none)
  | 1 => some (.CALLDATASIZE, none)
  | 2 => some (.PUSH2, some (UInt256.ofNat (setInhibitorPc kind), 2))
  | 5 => some (.JUMPI, none)
  | 6 => some (.PUSH0, none)
  | 7 => some (.SLOAD, none)
  | 8 => some (.PUSH1, some (UInt256.ofNat 1, 1))
  | 10 => some (.SLOAD, none)
  | 11 => some (.DUP2, none)
  | 12 => some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  | 45 => some (.EQ, none)
  | 46 => some (.PUSH2, some (UInt256.ofNat (zeroExcessPc kind), 2))
  | 49 => some (.JUMPI, none)
  | 50 => some (.PUSH1, some (UInt256.ofNat (targetImm kind), 1))
  | 52 => some (.DUP3, none)
  | 53 => some (.DUP3, none)
  | 54 => some (.ADD, none)
  | 55 => some (.GT, none)
  | 56 => some (.PUSH2, some (UInt256.ofNat (computeExcessPc kind), 2))
  | 59 => some (.JUMPI, none)
  | 60 => some (.JUMPDEST, none)
  | 61 => some (.POP, none)
  | 62 => some (.POP, none)
  | 63 => some (.PUSH0, none)
  | 64 => some (.PUSH2, some (UInt256.ofNat (storeExcessPc kind), 2))
  | 67 => some (.JUMP, none)
  | 68 => some (.JUMPDEST, none)
  | 69 => some (.ADD, none)
  | 70 => some (.PUSH1, some (UInt256.ofNat (targetImm kind), 1))
  | 72 => some (.SWAP1, none)
  | 73 => some (.SUB, none)
  | 74 => some (.PUSH2, some (UInt256.ofNat (storeExcessPc kind), 2))
  | 77 => some (.JUMP, none)
  | 78 => some (.JUMPDEST, none)
  | 79 => some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  | 112 => some (.JUMPDEST, none)
  | 113 => some (.PUSH0, none)
  | 114 => some (.SSTORE, none)
  | _ => none

theorem blockOp_deposit_compute_target :
    blockOp .deposit 70 = some (.PUSH1, some (UInt256.ofNat 8, 1)) :=
  rfl

theorem blockOp_exit_compute_target :
    blockOp .exit 70 = some (.PUSH1, some (UInt256.ofNat 2, 1)) :=
  rfl

theorem blockOp_deposit_gt_target :
    blockOp .deposit 50 = some (.PUSH1, some (UInt256.ofNat 8, 1)) :=
  rfl

theorem blockOp_exit_gt_target :
    blockOp .exit 50 = some (.PUSH1, some (UInt256.ofNat 2, 1)) :=
  rfl

theorem blockOp_deposit_compute_target_enc :
    opcodeAt (fromHex "6008") 0 = blockOp .deposit 70 :=
  rfl

theorem blockOp_exit_compute_target_enc :
    opcodeAt (fromHex "6002") 0 = blockOp .exit 70 :=
  rfl

theorem blockOp_JUMPDEST_update (kind : Kind) :
    blockOp kind 0 = some (.JUMPDEST, none) ∧
      opcodeAt (fromHex "5b") 0 = blockOp kind 0 := by
  constructor <;> cases kind <;> rfl

/-! ## CFG state and loc-indexed stepper

`excessStep` is indexed by local PC so proofs do not match on
`Operation` constructors. `blockOp` remains the opcode-at-PC table;
each loc implements that instruction's stack effect.
-/

structure ExcessState where
  pc : Nat
  stack : List UInt256
  gas : Nat
  σ : Storage
  deriving Inhabited, Repr

def excessGasBound : Nat := 30000

theorem excessGasBound_le_campaign : excessGasBound ≤ campaignGasBound := by
  decide

theorem campaign_ge_excess {g : Nat} (h : g ≥ campaignGasBound) :
    g ≥ excessGasBound :=
  Nat.le_trans excessGasBound_le_campaign h

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

theorem loc_at (kind : Kind) (k : Nat) :
    blockBase kind + k - blockBase kind = k :=
  Nat.add_sub_cancel_left _ _

/-- Conservative `SSTORE` cost (`Gsset`) so remaining gas is a lower bound. -/
def excessStep (kind : Kind) (cds : UInt256) (m : ExcessState) :
    Except CfgError ExcessState :=
  match m.pc - blockBase kind with
  | 0 =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok ⟨m.pc + 1, m.stack, m.gas - Gjumpdest, m.σ⟩
  | 1 =>
      if m.gas < Gbase then .error .outOfGas
      else .ok ⟨m.pc + 1, cds :: m.stack, m.gas - Gbase, m.σ⟩
  | 2 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 3, UInt256.ofNat (setInhibitorPc kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 5 =>
      match m.stack with
      | _dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond = UInt256.ofNat 0 then
            .ok ⟨m.pc + 1, rest, m.gas - Ghigh, m.σ⟩
          else
            .ok ⟨setInhibitorPc kind, rest, m.gas - Ghigh, m.σ⟩
      | _ => .error .stackUnderflow
  | 6 =>
      if m.gas < Gbase then .error .outOfGas
      else .ok ⟨m.pc + 1, UInt256.ofNat 0 :: m.stack, m.gas - Gbase, m.σ⟩
  | 7 =>
      match m.stack with
      | key :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok ⟨m.pc + 1, m.σ.getD key (UInt256.ofNat 0) :: rest,
                m.gas - Gcoldsload, m.σ⟩
      | _ => .error .stackUnderflow
  | 8 =>
      if m.gas < Gverylow then .error .outOfGas
      else .ok ⟨m.pc + 2, UInt256.ofNat 1 :: m.stack, m.gas - Gverylow, m.σ⟩
  | 10 =>
      match m.stack with
      | key :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok ⟨m.pc + 1, m.σ.getD key (UInt256.ofNat 0) :: rest,
                m.gas - Gcoldsload, m.σ⟩
      | _ => .error .stackUnderflow
  | 11 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, b :: a :: b :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 12 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 33, UInt256.ofNat inhibitor :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 45 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, UInt256.eq a b :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 46 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 3, UInt256.ofNat (zeroExcessPc kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 49 =>
      match m.stack with
      | _dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond = UInt256.ofNat 0 then
            .ok ⟨m.pc + 1, rest, m.gas - Ghigh, m.σ⟩
          else
            .ok ⟨zeroExcessPc kind, rest, m.gas - Ghigh, m.σ⟩
      | _ => .error .stackUnderflow
  | 50 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 2, UInt256.ofNat (targetImm kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 52 =>
      match m.stack with
      | a :: b :: c :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, c :: a :: b :: c :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 53 =>
      match m.stack with
      | a :: b :: c :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, c :: a :: b :: c :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 54 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, (a + b) :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 55 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, UInt256.gt a b :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 56 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 3, UInt256.ofNat (computeExcessPc kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 59 =>
      match m.stack with
      | _dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond = UInt256.ofNat 0 then
            .ok ⟨m.pc + 1, rest, m.gas - Ghigh, m.σ⟩
          else
            .ok ⟨computeExcessPc kind, rest, m.gas - Ghigh, m.σ⟩
      | _ => .error .stackUnderflow
  | 60 =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok ⟨m.pc + 1, m.stack, m.gas - Gjumpdest, m.σ⟩
  | 61 =>
      match m.stack with
      | _ :: rest =>
          if m.gas < Gbase then .error .outOfGas
          else .ok ⟨m.pc + 1, rest, m.gas - Gbase, m.σ⟩
      | _ => .error .stackUnderflow
  | 62 =>
      match m.stack with
      | _ :: rest =>
          if m.gas < Gbase then .error .outOfGas
          else .ok ⟨m.pc + 1, rest, m.gas - Gbase, m.σ⟩
      | _ => .error .stackUnderflow
  | 63 =>
      if m.gas < Gbase then .error .outOfGas
      else .ok ⟨m.pc + 1, UInt256.ofNat 0 :: m.stack, m.gas - Gbase, m.σ⟩
  | 64 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 3, UInt256.ofNat (storeExcessPc kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 67 =>
      match m.stack with
      | dest :: rest =>
          if m.gas < Gmid then .error .outOfGas
          else .ok ⟨dest.toNat, rest, m.gas - Gmid, m.σ⟩
      | _ => .error .stackUnderflow
  | 68 =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok ⟨m.pc + 1, m.stack, m.gas - Gjumpdest, m.σ⟩
  | 69 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, (a + b) :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 70 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 2, UInt256.ofNat (targetImm kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 72 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, b :: a :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 73 =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok ⟨m.pc + 1, (a - b) :: rest, m.gas - Gverylow, m.σ⟩
      | _ => .error .stackUnderflow
  | 74 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 3, UInt256.ofNat (storeExcessPc kind) :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 77 =>
      match m.stack with
      | dest :: rest =>
          if m.gas < Gmid then .error .outOfGas
          else .ok ⟨dest.toNat, rest, m.gas - Gmid, m.σ⟩
      | _ => .error .stackUnderflow
  | 78 =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok ⟨m.pc + 1, m.stack, m.gas - Gjumpdest, m.σ⟩
  | 79 =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok ⟨m.pc + 33, UInt256.ofNat inhibitor :: m.stack,
            m.gas - Gverylow, m.σ⟩
  | 112 =>
      if m.gas < Gjumpdest then .error .outOfGas
      else .ok ⟨m.pc + 1, m.stack, m.gas - Gjumpdest, m.σ⟩
  | 113 =>
      if m.gas < Gbase then .error .outOfGas
      else .ok ⟨m.pc + 1, UInt256.ofNat 0 :: m.stack, m.gas - Gbase, m.σ⟩
  | 114 =>
      match m.stack with
      | key :: val :: rest =>
          if m.gas < Gsset then .error .outOfGas
          else
            .ok ⟨m.pc + 1, rest, m.gas - Gsset, m.σ.insert key val⟩
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

def runN (n : Nat) (kind : Kind) (cds : UInt256) (m : ExcessState) :
    Except CfgError ExcessState :=
  match n with
  | 0 => .ok m
  | n + 1 =>
      match excessStep kind cds m with
      | .error e => .error e
      | .ok m' => runN n kind cds m'

/-- Drive the block until local PC 115 (`SSTORE` fall-through). Fuel 32
covers the longest path (`compute_excess`, 30 opcodes). -/
def excessFuel : Nat := 32

def runToStore : Nat → Kind → UInt256 → ExcessState → Except CfgError ExcessState
  | 0, kind, _, m =>
      if m.pc = blockBase kind + 115 then .ok m else .error .outOfGas
  | n + 1, kind, cds, m =>
      if m.pc = blockBase kind + 115 then .ok m
      else
        match excessStep kind cds m with
        | .error e => .error e
        | .ok m' => runToStore n kind cds m'

def startState (kind : Kind) (drainN : UInt256) (g : Nat) (σ : Storage) :
    ExcessState :=
  ⟨blockBase kind, [drainN], g, σ⟩

theorem loc_ne_store (kind : Kind) {k : Nat} (hk : k ≠ 115) :
    blockBase kind + k ≠ blockBase kind + 115 :=
  mt (Nat.add_left_cancel (n := blockBase kind)) hk

theorem runToStore_done (n : Nat) (kind : Kind) (cds : UInt256)
    (m : ExcessState) (h : m.pc = blockBase kind + 115) :
    runToStore n kind cds m = .ok m := by
  cases n with
  | zero => simp [runToStore, h]
  | succ _ => simp [runToStore, h]

theorem runToStore_succ {n : Nat} {kind : Kind} {cds : UInt256}
    {m m' : ExcessState}
    (hpc : m.pc ≠ blockBase kind + 115)
    (hs : excessStep kind cds m = .ok m') :
    runToStore (n + 1) kind cds m = runToStore n kind cds m' := by
  conv => lhs; unfold runToStore
  split_ifs with hEq
  · exact (hpc hEq).elim
  · rw [hs]

/-! ## Helpers -/

private theorem eq_one_of_eq {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

theorem inhibitor_lt_size : inhibitor < UInt256.size := by
  unfold inhibitor UInt256.size
  decide

theorem toNat_ofNat_inhibitor :
    (UInt256.ofNat inhibitor).toNat = inhibitor := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt inhibitor_lt_size]

theorem toNat_storeExcess (kind : Kind) :
    (UInt256.ofNat (storeExcessPc kind)).toNat = storeExcessPc kind := by
  cases kind <;> rfl

theorem toNat_ofNat_target (kind : Kind) :
    (UInt256.ofNat (targetImm kind)).toNat = targetImm kind := by
  cases kind <;> rfl

theorem toNat_zero : (UInt256.ofNat 0).toNat = 0 := rfl

theorem loadU256_eq_inhibitor {σ : Storage} (h : slotExcess σ = inhibitor) :
    loadU256 σ 0 = UInt256.ofNat inhibitor :=
  loadU256_of_excess_eq_inhibitor h

theorem loadU256_ne_inhibitor {σ : Storage} (h : slotExcess σ ≠ inhibitor) :
    loadU256 σ 0 ≠ UInt256.ofNat inhibitor := by
  intro heq
  apply h
  unfold slotExcess loadNat
  simp [SLOT_EXCESS]
  rw [heq, toNat_ofNat_inhibitor]

theorem sload_slot0 (σ : Storage) :
    σ.getD (UInt256.ofNat 0) (UInt256.ofNat 0) = loadU256 σ 0 := by
  simp [loadU256, SLOT_EXCESS]

theorem sload_slot1 (σ : Storage) :
    σ.getD (UInt256.ofNat 1) (UInt256.ofNat 0) = loadU256 σ 1 := by
  simp [loadU256, SLOT_COUNT]

theorem toNat_add_of_lt (a b : UInt256)
    (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  change (a.val + b.val).val = a.val.val + b.val.val
  rw [Fin.val_add]
  exact Nat.mod_eq_of_lt h

theorem toNat_sub_of_le (a b : UInt256) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  Fin.sub_val_of_le h

private theorem gt_one_of_gt {a b : UInt256} (h : b < a) :
    UInt256.gt a b = UInt256.ofNat 1 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

private theorem gt_zero_of_not_gt {a b : UInt256} (h : ¬ b < a) :
    UInt256.gt a b = UInt256.ofNat 0 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

theorem ofNat_one_ne_zero : UInt256.ofNat 1 ≠ UInt256.ofNat 0 := by
  decide

/-! ## Step lemmas -/

theorem step_update_JUMPDEST (kind : Kind) (cds drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ Gjumpdest) :
    excessStep kind cds ⟨blockBase kind, [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 1, [drainN], g - Gjumpdest, σ⟩ := by
  unfold excessStep
  simp [Nat.sub_self, not_lt_of_ge hg]

theorem step_CALLDATASIZE (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 1, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 2, cds :: stk, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_PUSH2_set (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 2, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 5, UInt256.ofNat (setInhibitorPc kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_JUMPI_set_taken (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Ghigh)
    (hcds : cds ≠ UInt256.ofNat 0) :
    excessStep kind cds
        ⟨blockBase kind + 5,
          UInt256.ofNat (setInhibitorPc kind) :: cds :: stk, g, σ⟩ =
      .ok ⟨blockBase kind + 78, stk, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg, hcds]
  exact setInhibitorPc_offset kind

theorem step_JUMPI_set_fall (kind : Kind) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Ghigh) :
    excessStep kind (UInt256.ofNat 0)
        ⟨blockBase kind + 5,
          UInt256.ofNat (setInhibitorPc kind) :: UInt256.ofNat 0 :: stk, g, σ⟩ =
      .ok ⟨blockBase kind + 6, stk, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_set_JUMPDEST (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gjumpdest) :
    excessStep kind cds ⟨blockBase kind + 78, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 79, stk, g - Gjumpdest, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_set_PUSH32 (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 79, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 112, UInt256.ofNat inhibitor :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_store_JUMPDEST (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gjumpdest) :
    excessStep kind cds ⟨blockBase kind + 112, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 113, stk, g - Gjumpdest, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_store_PUSH0 (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 113, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 114, UInt256.ofNat 0 :: stk, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [loc_at, not_lt_of_ge hg]

theorem step_store_SSTORE (kind : Kind) (cds val drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gsset) :
    excessStep kind cds
        ⟨blockBase kind + 114, UInt256.ofNat 0 :: val :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 115, [drainN], g - Gsset,
          σ.insert (UInt256.ofNat 0) val⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH0_slot0 (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 6, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 7, UInt256.ofNat 0 :: stk, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_SLOAD_excess (kind : Kind) (cds drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gcoldsload) :
    excessStep kind cds
        ⟨blockBase kind + 7, UInt256.ofNat 0 :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 8, loadU256 σ 0 :: [drainN], g - Gcoldsload, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg, sload_slot0]

theorem step_PUSH1_count (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 8, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 10, UInt256.ofNat 1 :: stk, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_SLOAD_count (kind : Kind) (cds excess drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gcoldsload) :
    excessStep kind cds
        ⟨blockBase kind + 10, UInt256.ofNat 1 :: excess :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 11, loadU256 σ 1 :: excess :: [drainN],
          g - Gcoldsload, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg, sload_slot1]

theorem step_DUP2_excess (kind : Kind) (cds count excess drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds
        ⟨blockBase kind + 11, count :: excess :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 12, excess :: count :: excess :: [drainN],
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH32_cmp (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 12, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 45, UInt256.ofNat inhibitor :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_EQ_inhibitor (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 45, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 46, UInt256.eq a b :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH2_zero (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 46, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 49, UInt256.ofNat (zeroExcessPc kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_JUMPI_zero_taken (kind : Kind) (cds cond : UInt256)
    (rest : List UInt256) (σ : Storage) (g : Nat) (hg : g ≥ Ghigh)
    (htaken : cond ≠ UInt256.ofNat 0) :
    excessStep kind cds
        ⟨blockBase kind + 49,
          UInt256.ofNat (zeroExcessPc kind) :: cond :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 60, rest, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg, htaken]
  exact zeroExcessPc_offset kind

theorem step_JUMPI_zero_fall (kind : Kind) (cds : UInt256)
    (rest : List UInt256) (σ : Storage) (g : Nat) (hg : g ≥ Ghigh) :
    excessStep kind cds
        ⟨blockBase kind + 49,
          UInt256.ofNat (zeroExcessPc kind) :: UInt256.ofNat 0 :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 50, rest, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH1_gt_target (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 50, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 52, UInt256.ofNat (targetImm kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_DUP3_52 (kind : Kind) (cds a b c : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 52, a :: b :: c :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 53, c :: a :: b :: c :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_DUP3_53 (kind : Kind) (cds a b c : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 53, a :: b :: c :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 54, c :: a :: b :: c :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_ADD_54 (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 54, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 55, (a + b) :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_GT_55 (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 55, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 56, UInt256.gt a b :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH2_compute (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 56, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 59, UInt256.ofNat (computeExcessPc kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_JUMPI_compute_taken (kind : Kind) (cds cond : UInt256)
    (rest : List UInt256) (σ : Storage) (g : Nat) (hg : g ≥ Ghigh)
    (htaken : cond ≠ UInt256.ofNat 0) :
    excessStep kind cds
        ⟨blockBase kind + 59,
          UInt256.ofNat (computeExcessPc kind) :: cond :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 68, rest, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg, htaken]
  exact computeExcessPc_offset kind

theorem step_JUMPI_compute_fall (kind : Kind) (cds : UInt256)
    (rest : List UInt256) (σ : Storage) (g : Nat) (hg : g ≥ Ghigh) :
    excessStep kind cds
        ⟨blockBase kind + 59,
          UInt256.ofNat (computeExcessPc kind) :: UInt256.ofNat 0 :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 60, rest, g - Ghigh, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_zero_JUMPDEST (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gjumpdest) :
    excessStep kind cds ⟨blockBase kind + 60, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 61, stk, g - Gjumpdest, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_POP_61 (kind : Kind) (cds x : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 61, x :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 62, rest, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_POP_62 (kind : Kind) (cds x : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 62, x :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 63, rest, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH0_zero (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gbase) :
    excessStep kind cds ⟨blockBase kind + 63, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 64, UInt256.ofNat 0 :: stk, g - Gbase, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH2_store_64 (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 64, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 67, UInt256.ofNat (storeExcessPc kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_JUMP_store_67 (kind : Kind) (cds val drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gmid) :
    excessStep kind cds
        ⟨blockBase kind + 67,
          UInt256.ofNat (storeExcessPc kind) :: val :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 112, val :: [drainN], g - Gmid, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]
  cases kind <;> rfl

theorem step_compute_JUMPDEST (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gjumpdest) :
    excessStep kind cds ⟨blockBase kind + 68, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 69, stk, g - Gjumpdest, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_ADD_69 (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 69, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 70, (a + b) :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

/-- Kill-line `PUSH1 TARGET` (deposit byte 571 / exit byte 401). -/
theorem step_PUSH1_compute_target (kind : Kind) (cds : UInt256)
    (stk : List UInt256) (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 70, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 72, UInt256.ofNat (targetImm kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_SWAP1_72 (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 72, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 73, b :: a :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_SUB_73 (kind : Kind) (cds a b : UInt256) (rest : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 73, a :: b :: rest, g, σ⟩ =
      .ok ⟨blockBase kind + 74, (a - b) :: rest, g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_PUSH2_store_74 (kind : Kind) (cds : UInt256) (stk : List UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gverylow) :
    excessStep kind cds ⟨blockBase kind + 74, stk, g, σ⟩ =
      .ok ⟨blockBase kind + 77, UInt256.ofNat (storeExcessPc kind) :: stk,
          g - Gverylow, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]

theorem step_JUMP_store_77 (kind : Kind) (cds val drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ Gmid) :
    excessStep kind cds
        ⟨blockBase kind + 77,
          UInt256.ofNat (storeExcessPc kind) :: val :: [drainN], g, σ⟩ =
      .ok ⟨blockBase kind + 112, val :: [drainN], g - Gmid, σ⟩ := by
  unfold excessStep
  simp [not_lt_of_ge hg]
  cases kind <;> rfl

/-! ## Path composition

`runToStore_succ` rewrites one opcode. `gok` discharges remaining-gas
lower bounds from `g ≥ excessGasBound`.
-/

/-- Remaining-gas bound after the two cold `SLOAD`s of the empty path. -/
def tailGasBound : Nat := 20500

theorem tailGasBound_le_excess : tailGasBound ≤ excessGasBound := by decide

syntax "go" : tactic
macro_rules
  | `(tactic| go) =>
    `(tactic| (simp [excessGasBound, tailGasBound, Gjumpdest, Gbase, Gverylow,
        Ghigh, Gmid, Gcoldsload, Gsset] at * <;> omega))

/-! ## Path: nonempty calldata → `INHIBITOR` -/

theorem run_nonempty (kind : Kind) (cds drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ excessGasBound) (hcds : cds ≠ UInt256.ofNat 0) :
    runToStore excessFuel kind cds (startState kind drainN g σ) =
      .ok ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow
            - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0) (UInt256.ofNat inhibitor)⟩ := by
  unfold startState excessFuel
  have s0 := step_update_JUMPDEST kind cds drainN σ g (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 0 ≠ 115)) s0]
  have s1 := step_CALLDATASIZE kind cds [drainN] σ (g - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 1 ≠ 115)) s1]
  have s2 := step_PUSH2_set kind cds (cds :: [drainN]) σ (g - Gjumpdest - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 2 ≠ 115)) s2]
  have s3 := step_JUMPI_set_taken kind cds [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow) (by go) hcds
  rw [runToStore_succ (loc_ne_store kind (by decide : 5 ≠ 115)) s3]
  have s4 := step_set_JUMPDEST kind cds [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 78 ≠ 115)) s4]
  have s5 := step_set_PUSH32 kind cds [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 79 ≠ 115)) s5]
  have s6 := step_store_JUMPDEST kind cds [UInt256.ofNat inhibitor, drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 112 ≠ 115)) s6]
  have s7 := step_store_PUSH0 kind cds [UInt256.ofNat inhibitor, drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow
        - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 113 ≠ 115)) s7]
  have s8 := step_store_SSTORE kind cds (UInt256.ofNat inhibitor) drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow
        - Gjumpdest - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 114 ≠ 115)) s8]
  exact runToStore_done _ kind cds _ rfl

theorem nonempty_stores_inhibitor (kind : Kind) (cds drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ excessGasBound)
    (hcds : cds ≠ UInt256.ofNat 0) {m : ExcessState}
    (h : runToStore excessFuel kind cds (startState kind drainN g σ) = .ok m) :
    m.σ = σ.insert (UInt256.ofNat 0) (UInt256.ofNat inhibitor) := by
  rw [run_nonempty kind cds drainN σ g hg hcds] at h
  cases h
  rfl

/-! ## Shared empty-calldata prefix through `EQ` -/

/-- Empty `calldatasize` falls through the first `JUMPI` onto `PUSH0; SLOAD`. -/
theorem run_empty_to_eq (kind : Kind) (drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ excessGasBound) (n : Nat) :
    runToStore (n + 12) kind (UInt256.ofNat 0) (startState kind drainN g σ) =
      runToStore n kind (UInt256.ofNat 0)
        ⟨blockBase kind + 49,
          UInt256.ofNat (zeroExcessPc kind) ::
            UInt256.eq (UInt256.ofNat inhibitor) (loadU256 σ 0) ::
              loadU256 σ 1 :: loadU256 σ 0 :: [drainN],
          g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
            - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow,
          σ⟩ := by
  unfold startState
  have s0 := step_update_JUMPDEST kind (UInt256.ofNat 0) drainN σ g (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 0 ≠ 115)) s0]
  have s1 := step_CALLDATASIZE kind (UInt256.ofNat 0) [drainN] σ
      (g - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 1 ≠ 115)) s1]
  have s2 := step_PUSH2_set kind (UInt256.ofNat 0) (UInt256.ofNat 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 2 ≠ 115)) s2]
  have s3 := step_JUMPI_set_fall kind [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 5 ≠ 115)) s3]
  have s4 := step_PUSH0_slot0 kind (UInt256.ofNat 0) [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 6 ≠ 115)) s4]
  have s5 := step_SLOAD_excess kind (UInt256.ofNat 0) drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 7 ≠ 115)) s5]
  have s6 := step_PUSH1_count kind (UInt256.ofNat 0)
      (loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 8 ≠ 115)) s6]
  have s7 := step_SLOAD_count kind (UInt256.ofNat 0) (loadU256 σ 0) drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 10 ≠ 115)) s7]
  have s8 := step_DUP2_excess kind (UInt256.ofNat 0) (loadU256 σ 1)
      (loadU256 σ 0) drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 11 ≠ 115)) s8]
  have s9 := step_PUSH32_cmp kind (UInt256.ofNat 0)
      (loadU256 σ 0 :: loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 12 ≠ 115)) s9]
  have s10 := step_EQ_inhibitor kind (UInt256.ofNat 0)
      (UInt256.ofNat inhibitor) (loadU256 σ 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 45 ≠ 115)) s10]
  have s11 := step_PUSH2_zero kind (UInt256.ofNat 0)
      (UInt256.eq (UInt256.ofNat inhibitor) (loadU256 σ 0) ::
        loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 46 ≠ 115)) s11]

/-- `zero_excess` then `store_excess`: pop count/excess, `SSTORE` slot 0. -/
theorem run_zero_store (kind : Kind) (cds count excess drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ tailGasBound) (n : Nat) :
    runToStore (n + 9) kind cds
        ⟨blockBase kind + 60, count :: excess :: [drainN], g, σ⟩ =
      runToStore n kind cds
        ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gbase - Gbase - Gbase - Gverylow - Gmid
            - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0) (UInt256.ofNat 0)⟩ := by
  have s0 := step_zero_JUMPDEST kind cds (count :: excess :: [drainN]) σ g (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 60 ≠ 115)) s0]
  have s1 := step_POP_61 kind cds count (excess :: [drainN]) σ
      (g - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 61 ≠ 115)) s1]
  have s2 := step_POP_62 kind cds excess [drainN] σ
      (g - Gjumpdest - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 62 ≠ 115)) s2]
  have s3 := step_PUSH0_zero kind cds [drainN] σ
      (g - Gjumpdest - Gbase - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 63 ≠ 115)) s3]
  have s4 := step_PUSH2_store_64 kind cds (UInt256.ofNat 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gbase - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 64 ≠ 115)) s4]
  have s5 := step_JUMP_store_67 kind cds (UInt256.ofNat 0) drainN σ
      (g - Gjumpdest - Gbase - Gbase - Gbase - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 67 ≠ 115)) s5]
  have s6 := step_store_JUMPDEST kind cds (UInt256.ofNat 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gbase - Gbase - Gverylow - Gmid) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 112 ≠ 115)) s6]
  have s7 := step_store_PUSH0 kind cds (UInt256.ofNat 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gbase - Gbase - Gverylow - Gmid - Gjumpdest)
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 113 ≠ 115)) s7]
  have s8 := step_store_SSTORE kind cds (UInt256.ofNat 0) drainN σ
      (g - Gjumpdest - Gbase - Gbase - Gbase - Gverylow - Gmid - Gjumpdest
        - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 114 ≠ 115)) s8]

/-- Kill-line `compute_excess`: `ADD; PUSH1 TARGET; SWAP1; SUB` then store. -/
theorem run_compute_store (kind : Kind) (cds count excess drainN : UInt256)
    (σ : Storage) (g : Nat) (hg : g ≥ tailGasBound) (n : Nat) :
    runToStore (n + 10) kind cds
        ⟨blockBase kind + 68, count :: excess :: [drainN], g, σ⟩ =
      runToStore n kind cds
        ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow
            - Gverylow - Gmid - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0)
            ((count + excess) - UInt256.ofNat (targetImm kind))⟩ := by
  have s0 := step_compute_JUMPDEST kind cds (count :: excess :: [drainN]) σ g
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 68 ≠ 115)) s0]
  have s1 := step_ADD_69 kind cds count excess [drainN] σ (g - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 69 ≠ 115)) s1]
  have s2 := step_PUSH1_compute_target kind cds ((count + excess) :: [drainN]) σ
      (g - Gjumpdest - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 70 ≠ 115)) s2]
  have s3 := step_SWAP1_72 kind cds (UInt256.ofNat (targetImm kind))
      (count + excess) [drainN] σ
      (g - Gjumpdest - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 72 ≠ 115)) s3]
  have s4 := step_SUB_73 kind cds (count + excess)
      (UInt256.ofNat (targetImm kind)) [drainN] σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 73 ≠ 115)) s4]
  have s5 := step_PUSH2_store_74 kind cds
      (((count + excess) - UInt256.ofNat (targetImm kind)) :: [drainN]) σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 74 ≠ 115)) s5]
  have s6 := step_JUMP_store_77 kind cds
      ((count + excess) - UInt256.ofNat (targetImm kind)) drainN σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow)
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 77 ≠ 115)) s6]
  have s7 := step_store_JUMPDEST kind cds
      (((count + excess) - UInt256.ofNat (targetImm kind)) :: [drainN]) σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
        - Gmid) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 112 ≠ 115)) s7]
  have s8 := step_store_PUSH0 kind cds
      (((count + excess) - UInt256.ofNat (targetImm kind)) :: [drainN]) σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
        - Gmid - Gjumpdest) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 113 ≠ 115)) s8]
  have s9 := step_store_SSTORE kind cds
      ((count + excess) - UInt256.ofNat (targetImm kind)) drainN σ
      (g - Gjumpdest - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
        - Gmid - Gjumpdest - Gbase) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 114 ≠ 115)) s9]

/-! ## Empty + inhibited → store 0 -/

theorem run_empty_inhibited (kind : Kind) (drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ excessGasBound)
    (hinh : slotExcess σ = inhibitor) :
    runToStore excessFuel kind (UInt256.ofNat 0) (startState kind drainN g σ) =
      .ok ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
            - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow
            - Ghigh - Gjumpdest - Gbase - Gbase - Gbase - Gverylow - Gmid
            - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0) (UInt256.ofNat 0)⟩ := by
  have heq : UInt256.eq (UInt256.ofNat inhibitor) (loadU256 σ 0) =
      UInt256.ofNat 1 :=
    eq_one_of_eq (loadU256_eq_inhibitor hinh).symm
  have htaken : UInt256.ofNat 1 ≠ UInt256.ofNat 0 := ofNat_one_ne_zero
  -- 12 prefix + 1 JUMPI + 9 zero_store + 10 leftover = 32
  rw [show excessFuel = 12 + 20 from rfl, run_empty_to_eq kind drainN σ g hg 20]
  rw [heq]
  have sJ := step_JUMPI_zero_taken kind (UInt256.ofNat 0) (UInt256.ofNat 1)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
      htaken
  rw [runToStore_succ (loc_ne_store kind (by decide : 49 ≠ 115)) sJ]
  rw [run_zero_store kind (UInt256.ofNat 0) (loadU256 σ 1) (loadU256 σ 0)
      drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
      (by go) 10]
  exact runToStore_done _ kind _ _ rfl

private theorem add_toNat_slots (σ : Storage)
    (hsum : slotExcess σ + slotCount σ < UInt256.size) :
    (loadU256 σ 1 + loadU256 σ 0).toNat = slotCount σ + slotExcess σ := by
  rw [toNat_add_of_lt]
  · rfl
  · rw [Nat.add_comm]
    exact hsum

private theorem gt_one_of_toNat {a b : UInt256} (h : b.toNat < a.toNat) :
    UInt256.gt a b = UInt256.ofNat 1 := by
  have hlt : b < a := lt_of_le_not_ge (Nat.le_of_lt h) (Nat.not_le_of_lt h)
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, hlt]

private theorem gt_zero_of_toNat {a b : UInt256} (h : a.toNat ≤ b.toNat) :
    UInt256.gt a b = UInt256.ofNat 0 := by
  have n : ¬ b < a := fun hlt => not_le_of_gt hlt h
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, n]

private theorem target_gt_one {kind : Kind} {σ : Storage}
    (hsum : slotExcess σ + slotCount σ < UInt256.size)
    (hgt : slotExcess σ + slotCount σ > targetImm kind) :
    UInt256.gt (loadU256 σ 1 + loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) = UInt256.ofNat 1 := by
  apply gt_one_of_toNat
  rw [toNat_ofNat_target, add_toNat_slots σ hsum, Nat.add_comm]
  exact hgt

private theorem target_gt_zero {kind : Kind} {σ : Storage}
    (hsum : slotExcess σ + slotCount σ < UInt256.size)
    (hle : slotExcess σ + slotCount σ ≤ targetImm kind) :
    UInt256.gt (loadU256 σ 1 + loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) = UInt256.ofNat 0 := by
  apply gt_zero_of_toNat
  rw [add_toNat_slots σ hsum, toNat_ofNat_target, Nat.add_comm]
  exact hle

/-- Kill-line subtract equals the Nat spec when the sum does not wrap. -/
theorem fold_u256_eq_expected (kind : Kind) (σ : Storage)
    (hsum : slotExcess σ + slotCount σ < UInt256.size)
    (hgt : slotExcess σ + slotCount σ > targetImm kind) :
    (loadU256 σ 1 + loadU256 σ 0) - UInt256.ofNat (targetImm kind) =
      UInt256.ofNat (slotExcess σ + slotCount σ - targetImm kind) := by
  apply Correspondence.eq_of_toNat_eq
  have hle : (UInt256.ofNat (targetImm kind)).toNat ≤
      (loadU256 σ 1 + loadU256 σ 0).toNat := by
    rw [toNat_ofNat_target, add_toNat_slots σ hsum, Nat.add_comm]
    exact Nat.le_of_lt hgt
  rw [toNat_sub_of_le _ _ hle, add_toNat_slots σ hsum, toNat_ofNat_target,
      Nat.add_comm (slotCount σ)]
  have hs : slotExcess σ + slotCount σ - targetImm kind < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hsum
  rw [Correspondence.toNat_ofNat, Nat.mod_eq_of_lt hs]

/-! ## Empty, not inhibited, `e+c > TARGET` → subtract kill-line TARGET -/

theorem run_empty_fold_over (kind : Kind) (drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ excessGasBound)
    (hne : slotExcess σ ≠ inhibitor)
    (hsum : slotExcess σ + slotCount σ < UInt256.size)
    (hgt : slotExcess σ + slotCount σ > targetImm kind) :
    runToStore excessFuel kind (UInt256.ofNat 0) (startState kind drainN g σ) =
      .ok ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
            - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow
            - Ghigh - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
            - Gverylow - Ghigh - Gjumpdest - Gverylow - Gverylow - Gverylow
            - Gverylow - Gverylow - Gmid - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0)
            ((loadU256 σ 1 + loadU256 σ 0) -
              UInt256.ofNat (targetImm kind))⟩ := by
  have heq : UInt256.eq (UInt256.ofNat inhibitor) (loadU256 σ 0) =
      UInt256.ofNat 0 :=
    eq_zero_of_ne (Ne.symm (loadU256_ne_inhibitor hne))
  have hgt1 : UInt256.gt (loadU256 σ 1 + loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) = UInt256.ofNat 1 :=
    target_gt_one hsum hgt
  -- 12 prefix + 1 JUMPI-zero-fall + 7 GT-path + 10 compute_store + 2 leftover
  rw [show excessFuel = 12 + 20 from rfl, run_empty_to_eq kind drainN σ g hg 20]
  rw [heq]
  have sJ := step_JUMPI_zero_fall kind (UInt256.ofNat 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 49 ≠ 115)) sJ]
  have s50 := step_PUSH1_gt_target kind (UInt256.ofNat 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 50 ≠ 115)) s50]
  have s52 := step_DUP3_52 kind (UInt256.ofNat 0)
      (UInt256.ofNat (targetImm kind)) (loadU256 σ 1) (loadU256 σ 0) [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 52 ≠ 115)) s52]
  have s53 := step_DUP3_53 kind (UInt256.ofNat 0) (loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) (loadU256 σ 1) (loadU256 σ 0 :: [drainN])
      σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 53 ≠ 115)) s53]
  have s54 := step_ADD_54 kind (UInt256.ofNat 0) (loadU256 σ 1) (loadU256 σ 0)
      (UInt256.ofNat (targetImm kind) :: loadU256 σ 1 :: loadU256 σ 0 ::
        [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 54 ≠ 115)) s54]
  have s55 := step_GT_55 kind (UInt256.ofNat 0)
      (loadU256 σ 1 + loadU256 σ 0) (UInt256.ofNat (targetImm kind))
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 55 ≠ 115)) s55]
  rw [hgt1]
  have s56 := step_PUSH2_compute kind (UInt256.ofNat 0)
      (UInt256.ofNat 1 :: loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 56 ≠ 115)) s56]
  have s59 := step_JUMPI_compute_taken kind (UInt256.ofNat 0)
      (UInt256.ofNat 1) (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow)
      (by go) ofNat_one_ne_zero
  rw [runToStore_succ (loc_ne_store kind (by decide : 59 ≠ 115)) s59]
  rw [run_compute_store kind (UInt256.ofNat 0) (loadU256 σ 1) (loadU256 σ 0)
      drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
        - Ghigh) (by go) 2]
  exact runToStore_done _ kind _ _ rfl

/-! ## Empty, not inhibited, `e+c ≤ TARGET` → store 0 -/

theorem run_empty_fold_under (kind : Kind) (drainN : UInt256) (σ : Storage)
    (g : Nat) (hg : g ≥ excessGasBound)
    (hne : slotExcess σ ≠ inhibitor)
    (hsum : slotExcess σ + slotCount σ < UInt256.size)
    (hle : slotExcess σ + slotCount σ ≤ targetImm kind) :
    runToStore excessFuel kind (UInt256.ofNat 0) (startState kind drainN g σ) =
      .ok ⟨blockBase kind + 115, [drainN],
          g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
            - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow
            - Ghigh - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
            - Gverylow - Ghigh - Gjumpdest - Gbase - Gbase - Gbase
            - Gverylow - Gmid - Gjumpdest - Gbase - Gsset,
          σ.insert (UInt256.ofNat 0) (UInt256.ofNat 0)⟩ := by
  have heq : UInt256.eq (UInt256.ofNat inhibitor) (loadU256 σ 0) =
      UInt256.ofNat 0 :=
    eq_zero_of_ne (Ne.symm (loadU256_ne_inhibitor hne))
  have hgt0 : UInt256.gt (loadU256 σ 1 + loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) = UInt256.ofNat 0 :=
    target_gt_zero hsum hle
  rw [show excessFuel = 12 + 20 from rfl, run_empty_to_eq kind drainN σ g hg 20]
  rw [heq]
  have sJ := step_JUMPI_zero_fall kind (UInt256.ofNat 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 49 ≠ 115)) sJ]
  have s50 := step_PUSH1_gt_target kind (UInt256.ofNat 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 50 ≠ 115)) s50]
  have s52 := step_DUP3_52 kind (UInt256.ofNat 0)
      (UInt256.ofNat (targetImm kind)) (loadU256 σ 1) (loadU256 σ 0) [drainN] σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 52 ≠ 115)) s52]
  have s53 := step_DUP3_53 kind (UInt256.ofNat 0) (loadU256 σ 0)
      (UInt256.ofNat (targetImm kind)) (loadU256 σ 1) (loadU256 σ 0 :: [drainN])
      σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 53 ≠ 115)) s53]
  have s54 := step_ADD_54 kind (UInt256.ofNat 0) (loadU256 σ 1) (loadU256 σ 0)
      (UInt256.ofNat (targetImm kind) :: loadU256 σ 1 :: loadU256 σ 0 ::
        [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 54 ≠ 115)) s54]
  have s55 := step_GT_55 kind (UInt256.ofNat 0)
      (loadU256 σ 1 + loadU256 σ 0) (UInt256.ofNat (targetImm kind))
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 55 ≠ 115)) s55]
  rw [hgt0]
  have s56 := step_PUSH2_compute kind (UInt256.ofNat 0)
      (UInt256.ofNat 0 :: loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow) (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 56 ≠ 115)) s56]
  have s59 := step_JUMPI_compute_fall kind (UInt256.ofNat 0)
      (loadU256 σ 1 :: loadU256 σ 0 :: [drainN]) σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow)
      (by go)
  rw [runToStore_succ (loc_ne_store kind (by decide : 59 ≠ 115)) s59]
  rw [run_zero_store kind (UInt256.ofNat 0) (loadU256 σ 1) (loadU256 σ 0)
      drainN σ
      (g - Gjumpdest - Gbase - Gverylow - Ghigh - Gbase - Gcoldsload
        - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh
        - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow
        - Ghigh) (by go) 3]
  exact runToStore_done _ kind _ _ rfl

/-! ## Parent `∀` -/

theorem pcontrol1_excess_nonempty_forall
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (_hsys : h.isUser = false)
    (cds drainN : UInt256)
    (hcds : cds ≠ UInt256.ofNat 0)
    {m : ExcessState}
    (hrun : runToStore excessFuel kind cds (startState kind drainN h.gas σ) =
      .ok m) :
    m.σ = σ.insert (UInt256.ofNat 0) (UInt256.ofNat inhibitor) ∧
      expectedExcess kind (slotExcess σ) (slotCount σ) true = inhibitor := by
  have hg : h.gas ≥ excessGasBound := campaign_ge_excess h.gas_ge
  constructor
  · exact nonempty_stores_inhibitor kind cds drainN σ h.gas hg hcds hrun
  · rfl

theorem pcontrol1_excess_deposit_target_is_8 : targetImm .deposit = 8 :=
  targetImm_deposit

theorem pcontrol1_excess_deposit_kill_line :
    blockOp .deposit 70 = some (.PUSH1, some (UInt256.ofNat 8, 1)) ∧
      blockBase .deposit + 71 = 571 :=
  ⟨blockOp_deposit_compute_target, deposit_kill_line_pc⟩

theorem pcontrol1_excess_exit_target_is_2 : targetImm .exit = 2 :=
  targetImm_exit

theorem pcontrol1_excess_exit_kill_line :
    blockOp .exit 70 = some (.PUSH1, some (UInt256.ofNat 2, 1)) ∧
      blockBase .exit + 71 = 401 :=
  ⟨blockOp_exit_compute_target, exit_kill_line_pc⟩

/-- `∀` excess recurrence for both predeploys (TARGET 8 and 2).

Post-`update_excess` slot 0 is `INHIBITOR` on nonempty system calldata,
`0` when already inhibited, and otherwise `max(0, excess+count−TARGET)`
where `TARGET` is the kill-line immediate (`PUSH1 8` at deposit 571,
`PUSH1 2` at exit 401). Queue length is unused. `SLOT_COUNT := 0` is C3.
The sum-no-wrap hypothesis is only needed on the empty non-inhibited
fold (UInt256 `ADD` would otherwise disagree with Nat `nextExcess`). -/
theorem pcontrol1_excess_forall
    (kind : Kind) (σ : Storage) (h : CallHyp kind σ)
    (_hsys : h.isUser = false)
    (cds drainN : UInt256)
    (hsum : slotExcess σ + slotCount σ < UInt256.size ∨
      cds ≠ UInt256.ofNat 0 ∨ slotExcess σ = inhibitor)
    {m : ExcessState}
    (hrun : runToStore excessFuel kind cds (startState kind drainN h.gas σ) =
      .ok m) :
    m.σ = σ.insert (UInt256.ofNat 0)
        (UInt256.ofNat (expectedExcess kind (slotExcess σ) (slotCount σ)
          (decide (cds ≠ UInt256.ofNat 0)))) := by
  have hg : h.gas ≥ excessGasBound := campaign_ge_excess h.gas_ge
  by_cases hcds : cds = UInt256.ofNat 0
  · subst hcds
    simp only [ne_eq, not_true_eq_false, decide_false]
    by_cases hinh : slotExcess σ = inhibitor
    · have := run_empty_inhibited kind drainN σ h.gas hg hinh
      rw [this] at hrun
      cases hrun
      simp [expectedExcess, hinh]
    · have hs : slotExcess σ + slotCount σ < UInt256.size := by
        cases hsum with
        | inl h => exact h
        | inr h =>
            cases h with
            | inl hne => exact (hne rfl).elim
            | inr hi => exact (hinh hi).elim
      by_cases hgt : slotExcess σ + slotCount σ > targetImm kind
      · have := run_empty_fold_over kind drainN σ h.gas hg hinh hs hgt
        rw [this] at hrun
        cases hrun
        rw [fold_u256_eq_expected kind σ hs hgt]
        simp [expectedExcess, hinh, Nat.le_of_lt hgt]
      · have hle : slotExcess σ + slotCount σ ≤ targetImm kind :=
          Nat.not_lt.mp hgt
        have := run_empty_fold_under kind drainN σ h.gas hg hinh hs hle
        rw [this] at hrun
        cases hrun
        simp [expectedExcess, hinh, hle]
  · have := run_nonempty kind cds drainN σ h.gas hg hcds
    rw [this] at hrun
    cases hrun
    simp [expectedExcess, hcds]

end Eip8282.Audit.Guarantees.PControl1.Excess


