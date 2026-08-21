import Eip8282.Audit.Correspondence
import Eip8282.Audit.WellFormed
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Step
import Eip8282.Audit.Bytecode
import Eip8282.Audit.Model

/-!
S3: empty-calldata / zero-value fee getter is read-only.

CFG-direct on the suffix after `fake_expo`: `CALLDATASIZE` / `CALLVALUE`
fall through, then `PUSH0; MSTORE; PUSH1 32; PUSH0; RETURN`. The 32-byte
return is whatever word `mstore` wrote — not `Model.fakeExponential`
(that is S4). `bump_excess` folds `count` at `TARGET` on the stack only.
The stepper records every `SSTORE` in a `stores` overlay and reads
post-storage through it; the getter's read-only claim is the proved fact
that a completing run's overlay is empty, so post-storage slots 0–3 equal
the well-formed pre-state for every excess and count.
-/

namespace Eip8282.Audit.Guarantees.PSubmit1.Fee

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model (Kind inhibitor)
open GasConstants

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-! ## 32-byte chunks (kernel-reducible `fromHex`, F3-style)

Deposit / exit suffix bytes are runtime offsets 128..159 (fifth `++` chunk).
Local PC `i` is runtime PC `128 + i`. Getter `JUMPI`s are not taken
(`calldatasize = 0`, `value = 0`), so destinations stay absolute labels
in F1's tables and need not be local.

Bump bytes are the third chunk (runtime 64..95). `jumpBase = 64` converts
`JUMP`/`JUMPI` destinations back into that window.
-/

def depositSuffixHex : String :=
  "90939004925050503660b814609f57366102705734610270575f5260205ff35b"

def exitSuffixHex : String :=
  "9390049250505036603014609e57366101c657346101c6575f5260205ff35b34"

def depositBumpHex : String :=
  "6102705760015460088111605257506058565b60089003015b60119060018202"

def exitBumpHex : String :=
  "01c65760015460028111605157506057565b60029003015b6011906001820260"

def depositSuffixChunk : ByteArray := fromHex depositSuffixHex
def exitSuffixChunk : ByteArray := fromHex exitSuffixHex
def depositBumpChunk : ByteArray := fromHex depositBumpHex
def exitBumpChunk : ByteArray := fromHex exitBumpHex

@[simp] def suffixChunkBase : Nat := 128
@[simp] def bumpChunkBase : Nat := 64

/-- Local PC of deposit `CALLDATASIZE` after `fake_expo` cleanup (`136 - 128`). -/
@[simp] def depositSuffixLocal : Nat := 8
@[simp] def exitSuffixLocal : Nat := 7

@[simp] def depositAfterInhLocal : Nat := 4
@[simp] def exitAfterInhLocal : Nat := 3

def suffixChunk : Kind → ByteArray
  | .deposit => depositSuffixChunk
  | .exit => exitSuffixChunk

def bumpChunk : Kind → ByteArray
  | .deposit => depositBumpChunk
  | .exit => exitBumpChunk

def suffixLocalPc : Kind → Nat
  | .deposit => depositSuffixLocal
  | .exit => exitSuffixLocal

def computeUserFeePc : Kind → Nat
  | .deposit => Deposit.compute_user_fee
  | .exit => Exit.compute_user_fee

def bumpExcessPc : Kind → Nat
  | .deposit => Deposit.bump_excess
  | .exit => Exit.bump_excess

def targetImm : Kind → Nat
  | .deposit => 8
  | .exit => 2

def openingJumps : Kind → Array UInt256
  | .deposit => depositJumpdests
  | .exit => exitJumpdests

/-! ## Getter CFG state -/

structure GetterState where
  pc : Nat
  stack : List UInt256
  gas : Nat
  mem0 : UInt256 := UInt256.ofNat 0
  returned : Option Nat := none
  /-- Chronological `SSTORE` overlay: every write the run performed, in
  order. Post-storage is read through this list (`loadAfterStores`), so a
  run that wrote cannot masquerade as read-only. -/
  stores : List (UInt256 × UInt256) := []
  deriving Inhabited, Repr

/-- Copy `m`, replacing PC / stack / gas; the write overlay is carried. -/
def stepOk (m : GetterState) (pc : Nat) (stack : List UInt256) (gas : Nat) :
    GetterState :=
  { pc := pc, stack := stack, gas := gas, mem0 := m.mem0, returned := m.returned,
    stores := m.stores }

/-- Storage overlay lookup: the latest recorded write to `key`, else the
pre-state. Same `findRev?` discipline as `Append.loadAfter`. -/
def loadAfterStores (σ : Storage) (ws : List (UInt256 × UInt256)) (key : UInt256) :
    UInt256 :=
  match ws.findRev? (fun p => decide (p.1 = key)) with
  | some (_, v) => v
  | none => σ.getD key (UInt256.ofNat 0)

@[simp] theorem loadAfterStores_nil (σ : Storage) (key : UInt256) :
    loadAfterStores σ [] key = σ.getD key (UInt256.ofNat 0) :=
  rfl

/-- Post-run value of slot `slot`: the pre-state overlaid with the run's
own recorded `SSTORE`s. "Slots unchanged" is measured against this, not
against a copy of `σ`. -/
def postSlotNat (σ : Storage) (ws : List (UInt256 × UInt256)) (slot : Nat) : Nat :=
  (loadAfterStores σ ws (UInt256.ofNat slot)).toNat

@[simp] theorem postSlotNat_nil (σ : Storage) (slot : Nat) :
    postSlotNat σ [] slot = loadNat σ slot :=
  rfl

/-- One tick. `SSTORE` is a real case: it appends to the `stores` overlay
(charging `Gsset`, the conservative set cost), so the getter's read-only
claim is the *proved* fact that a completing run's overlay is empty — not
an opcode that errors out. `jumpBase` is subtracted from absolute
`JUMP`/`JUMPI` destinations so a 32-byte window can host `bump_excess`.
Unused on the getter suffix (those `JUMPI`s fall through). -/
def getterStep (code : ByteArray) (validJumps : Array UInt256)
    (σ : Storage) (cds val : UInt256) (jumpBase : Nat) (m : GetterState) :
    Except CfgError GetterState :=
  match opcodeAt code m.pc with
  | some (.Push .PUSH0, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok (stepOk m (m.pc + 1) (UInt256.ofNat 0 :: m.stack) (m.gas - Gbase))
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok (stepOk m (m.pc + 1 + width) (imm :: m.stack) (m.gas - Gverylow))
  | some (.StackMemFlow .SLOAD, none) =>
      match m.stack with
      | key :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1)
              (loadAfterStores σ m.stores key :: rest) (m.gas - Gcoldsload))
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .SSTORE, none) =>
      match m.stack with
      | key :: v :: rest =>
          if m.gas < Gsset then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := rest, gas := m.gas - Gsset,
                  mem0 := m.mem0, returned := m.returned,
                  stores := m.stores ++ [(key, v)] }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .POP, none) =>
      match m.stack with
      | _ :: rest =>
          if m.gas < Gbase then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) rest (m.gas - Gbase))
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPDEST, none) =>
      if m.gas < Gjumpdest then .error .outOfGas
      else
        .ok (stepOk m (m.pc + 1) m.stack (m.gas - Gjumpdest))
  | some (.StackMemFlow .JUMP, none) =>
      match m.stack with
      | dest :: rest =>
          if m.gas < Gmid then .error .outOfGas
          else if validJumps.contains dest then
            .ok (stepOk m (dest.toNat - jumpBase) rest (m.gas - Gmid))
          else
            .error .badJump
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPI, none) =>
      match m.stack with
      | dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond != UInt256.ofNat 0 then
            if validJumps.contains dest then
              .ok (stepOk m (dest.toNat - jumpBase) rest (m.gas - Ghigh))
            else
              .error .badJump
          else
            .ok (stepOk m (m.pc + 1) rest (m.gas - Ghigh))
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .MSTORE, none) =>
      match m.stack with
      | offset :: v :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := rest, gas := m.gas - Gverylow,
                  mem0 := if offset = UInt256.ofNat 0 then v else m.mem0,
                  returned := m.returned, stores := m.stores }
      | _ => .error .stackUnderflow
  | some (.Dup .DUP2, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (b :: a :: b :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.Exchange .SWAP1, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (b :: a :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.CompBit .EQ, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (UInt256.eq a b :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.CompBit .GT, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (UInt256.gt a b :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.StopArith .ADD, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (UInt256.add a b :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.StopArith .SUB, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok (stepOk m (m.pc + 1) (UInt256.sub a b :: rest) (m.gas - Gverylow))
      | _ => .error .stackUnderflow
  | some (.Env .CALLDATASIZE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok (stepOk m (m.pc + 1) (cds :: m.stack) (m.gas - Gbase))
  | some (.Env .CALLVALUE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok (stepOk m (m.pc + 1) (val :: m.stack) (m.gas - Gbase))
  | some (.System .RETURN, none) =>
      match m.stack with
      | _offset :: size :: rest =>
          if m.gas < Gzero then .error .outOfGas
          else
            .ok { pc := m.pc, stack := rest, gas := m.gas, mem0 := m.mem0,
                  returned := some size.toNat, stores := m.stores }
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

/-! ## Helpers -/

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem bne_zero_zero :
    (UInt256.ofNat 0 != UInt256.ofNat 0) = false := by
  decide

private theorem bne_one_zero :
    (UInt256.ofNat 1 != UInt256.ofNat 0) = true := by
  decide

theorem toNat_32 : (UInt256.ofNat 32).toNat = 32 := rfl

theorem inhibitor_lt_size : inhibitor < UInt256.size := by
  decide

theorem loadU256_ne_inhibitor {σ : Storage}
    (h : slotExcess σ ≠ inhibitor) :
    loadU256 σ 0 ≠ UInt256.ofNat inhibitor := by
  intro heq
  apply h
  have := congrArg UInt256.toNat heq
  rw [Correspondence.toNat_ofNat, Nat.mod_eq_of_lt inhibitor_lt_size] at this
  exact this

theorem sload_slot1 (σ : Storage) :
    σ.getD (UInt256.ofNat 1) (UInt256.ofNat 0) = loadU256 σ 1 :=
  rfl

theorem deposit_compute_user_fee_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.compute_user_fee) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Deposit.compute_user_fee,
      mem_depositJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem deposit_bump_excess_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.bump_excess) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Deposit.bump_excess,
      mem_depositJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem exit_compute_user_fee_contains :
    exitJumpdests.contains (UInt256.ofNat Exit.compute_user_fee) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Exit.compute_user_fee,
      mem_exitJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem exit_bump_excess_contains :
    exitJumpdests.contains (UInt256.ofNat Exit.bump_excess) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Exit.bump_excess,
      mem_exitJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem toNat_deposit_compute_user_fee :
    (UInt256.ofNat Deposit.compute_user_fee).toNat = Deposit.compute_user_fee :=
  rfl

theorem toNat_deposit_bump_excess :
    (UInt256.ofNat Deposit.bump_excess).toNat = Deposit.bump_excess :=
  rfl

theorem toNat_exit_compute_user_fee :
    (UInt256.ofNat Exit.compute_user_fee).toNat = Exit.compute_user_fee :=
  rfl

theorem toNat_exit_bump_excess :
    (UInt256.ofNat Exit.bump_excess).toNat = Exit.bump_excess :=
  rfl

/-! ## Suffix opcodes (32-byte chunks) -/

theorem deposit_suffix_opcode_CALLDATASIZE :
    opcodeAt depositSuffixChunk 8 = some (.CALLDATASIZE, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH1_184 :
    opcodeAt depositSuffixChunk 9 =
      some (.PUSH1, some (UInt256.ofNat 184, 1)) :=
  rfl

theorem deposit_suffix_opcode_EQ :
    opcodeAt depositSuffixChunk 11 = some (.EQ, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH1_handle :
    opcodeAt depositSuffixChunk 12 =
      some (.PUSH1, some (UInt256.ofNat Deposit.handle_input, 1)) :=
  rfl

theorem deposit_suffix_opcode_JUMPI_handle :
    opcodeAt depositSuffixChunk 14 = some (.JUMPI, none) :=
  rfl

theorem deposit_suffix_opcode_CALLDATASIZE₂ :
    opcodeAt depositSuffixChunk 15 = some (.CALLDATASIZE, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH2_revert :
    opcodeAt depositSuffixChunk 16 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) :=
  rfl

theorem deposit_suffix_opcode_JUMPI_revert :
    opcodeAt depositSuffixChunk 19 = some (.JUMPI, none) :=
  rfl

theorem deposit_suffix_opcode_CALLVALUE :
    opcodeAt depositSuffixChunk 20 = some (.CALLVALUE, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH2_revert₂ :
    opcodeAt depositSuffixChunk 21 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) :=
  rfl

theorem deposit_suffix_opcode_JUMPI_value :
    opcodeAt depositSuffixChunk 24 = some (.JUMPI, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH0 :
    opcodeAt depositSuffixChunk 25 = some (.PUSH0, none) :=
  rfl

theorem deposit_suffix_opcode_MSTORE :
    opcodeAt depositSuffixChunk 26 = some (.MSTORE, none) :=
  rfl

theorem deposit_suffix_opcode_PUSH1_32 :
    opcodeAt depositSuffixChunk 27 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) :=
  rfl

theorem deposit_suffix_opcode_PUSH0₂ :
    opcodeAt depositSuffixChunk 29 = some (.PUSH0, none) :=
  rfl

theorem deposit_suffix_opcode_RETURN :
    opcodeAt depositSuffixChunk 30 = some (.RETURN, none) :=
  rfl

theorem exit_suffix_opcode_CALLDATASIZE :
    opcodeAt exitSuffixChunk 7 = some (.CALLDATASIZE, none) :=
  rfl

theorem exit_suffix_opcode_PUSH1_48 :
    opcodeAt exitSuffixChunk 8 =
      some (.PUSH1, some (UInt256.ofNat 48, 1)) :=
  rfl

theorem exit_suffix_opcode_EQ :
    opcodeAt exitSuffixChunk 10 = some (.EQ, none) :=
  rfl

theorem exit_suffix_opcode_PUSH1_handle :
    opcodeAt exitSuffixChunk 11 =
      some (.PUSH1, some (UInt256.ofNat Exit.handle_input, 1)) :=
  rfl

theorem exit_suffix_opcode_JUMPI_handle :
    opcodeAt exitSuffixChunk 13 = some (.JUMPI, none) :=
  rfl

theorem exit_suffix_opcode_CALLDATASIZE₂ :
    opcodeAt exitSuffixChunk 14 = some (.CALLDATASIZE, none) :=
  rfl

theorem exit_suffix_opcode_PUSH2_revert :
    opcodeAt exitSuffixChunk 15 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) :=
  rfl

theorem exit_suffix_opcode_JUMPI_revert :
    opcodeAt exitSuffixChunk 18 = some (.JUMPI, none) :=
  rfl

theorem exit_suffix_opcode_CALLVALUE :
    opcodeAt exitSuffixChunk 19 = some (.CALLVALUE, none) :=
  rfl

theorem exit_suffix_opcode_PUSH2_revert₂ :
    opcodeAt exitSuffixChunk 20 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) :=
  rfl

theorem exit_suffix_opcode_JUMPI_value :
    opcodeAt exitSuffixChunk 23 = some (.JUMPI, none) :=
  rfl

theorem exit_suffix_opcode_PUSH0 :
    opcodeAt exitSuffixChunk 24 = some (.PUSH0, none) :=
  rfl

theorem exit_suffix_opcode_MSTORE :
    opcodeAt exitSuffixChunk 25 = some (.MSTORE, none) :=
  rfl

theorem exit_suffix_opcode_PUSH1_32 :
    opcodeAt exitSuffixChunk 26 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) :=
  rfl

theorem exit_suffix_opcode_PUSH0₂ :
    opcodeAt exitSuffixChunk 28 = some (.PUSH0, none) :=
  rfl

theorem exit_suffix_opcode_RETURN :
    opcodeAt exitSuffixChunk 29 = some (.RETURN, none) :=
  rfl

/-! ## Suffix gas and runner -/

def suffixGasBound : Nat := 5 * Gbase + 7 * Gverylow + 3 * Ghigh

theorem suffixGasBound_eq : suffixGasBound = 61 := rfl

theorem suffixGasBound_le_campaign : suffixGasBound ≤ campaignGasBound := by
  decide

private theorem suffix_gas_parts {g : Nat} (hg : g ≥ suffixGasBound) :
    ¬ g < Gbase ∧
      ¬ g - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow < Ghigh ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh < Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow <
          Ghigh ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh < Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow < Ghigh ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow - Ghigh < Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow - Ghigh - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow - Ghigh - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow - Ghigh - Gbase - Gverylow - Gverylow <
          Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow - Ghigh - Gbase - Gverylow - Gverylow
            - Gbase < Gzero := by
  simp [suffixGasBound, Gbase, Gverylow, Ghigh, Gzero] at hg ⊢
  omega

def GS (g pc : Nat) (st : List UInt256) (mem : UInt256 := UInt256.ofNat 0)
    (ret : Option Nat := none) : GetterState :=
  { pc := pc, stack := st, gas := g, mem0 := mem, returned := ret }

def runDepositSuffix (σ : Storage) (cds val quote : UInt256) (g : Nat) :
    Except CfgError GetterState :=
  match getterStep depositSuffixChunk depositJumpdests σ cds val 0 (GS g 8 [quote]) with
  | .error e => .error e
  | .ok m1 =>
    match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m1 with
    | .error e => .error e
    | .ok m2 =>
      match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m2 with
      | .error e => .error e
      | .ok m3 =>
        match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m3 with
        | .error e => .error e
        | .ok m4 =>
          match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m4 with
          | .error e => .error e
          | .ok m5 =>
            match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m5 with
            | .error e => .error e
            | .ok m6 =>
              match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m6 with
              | .error e => .error e
              | .ok m7 =>
                match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m7 with
                | .error e => .error e
                | .ok m8 =>
                  match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m8 with
                  | .error e => .error e
                  | .ok m9 =>
                    match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m9 with
                    | .error e => .error e
                    | .ok m10 =>
                      match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m10 with
                      | .error e => .error e
                      | .ok m11 =>
                        match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m11 with
                        | .error e => .error e
                        | .ok m12 =>
                          match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m12 with
                          | .error e => .error e
                          | .ok m13 =>
                            match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m13 with
                            | .error e => .error e
                            | .ok m14 =>
                              match getterStep depositSuffixChunk depositJumpdests σ cds val 0 m14 with
                              | .error e => .error e
                              | .ok m15 =>
                                getterStep depositSuffixChunk depositJumpdests σ cds val 0 m15

def runExitSuffix (σ : Storage) (cds val quote : UInt256) (g : Nat) :
    Except CfgError GetterState :=
  match getterStep exitSuffixChunk exitJumpdests σ cds val 0 (GS g 7 [quote]) with
  | .error e => .error e
  | .ok m1 =>
    match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m1 with
    | .error e => .error e
    | .ok m2 =>
      match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m2 with
      | .error e => .error e
      | .ok m3 =>
        match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m3 with
        | .error e => .error e
        | .ok m4 =>
          match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m4 with
          | .error e => .error e
          | .ok m5 =>
            match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m5 with
            | .error e => .error e
            | .ok m6 =>
              match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m6 with
              | .error e => .error e
              | .ok m7 =>
                match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m7 with
                | .error e => .error e
                | .ok m8 =>
                  match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m8 with
                  | .error e => .error e
                  | .ok m9 =>
                    match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m9 with
                    | .error e => .error e
                    | .ok m10 =>
                      match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m10 with
                      | .error e => .error e
                      | .ok m11 =>
                        match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m11 with
                        | .error e => .error e
                        | .ok m12 =>
                          match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m12 with
                          | .error e => .error e
                          | .ok m13 =>
                            match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m13 with
                            | .error e => .error e
                            | .ok m14 =>
                              match getterStep exitSuffixChunk exitJumpdests σ cds val 0 m14 with
                              | .error e => .error e
                              | .ok m15 =>
                                getterStep exitSuffixChunk exitJumpdests σ cds val 0 m15

def runGetterSuffix (kind : Kind) (σ : Storage) (cds val quote : UInt256)
    (g : Nat) : Except CfgError GetterState :=
  match kind with
  | .deposit => runDepositSuffix σ cds val quote g
  | .exit => runExitSuffix σ cds val quote g

/-! ## Deposit suffix steps (`calldatasize = 0`, `value = 0`) -/

theorem deposit_suf_CALLDATASIZE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0 (GS g 8 [quote]) =
      .ok (GS (g - Gbase) 9 [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_CALLDATASIZE]
  simp [stepOk, GS, (suffix_gas_parts hg).1]

theorem deposit_suf_PUSH1_184 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase) 9 [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow) 11
        [UInt256.ofNat 184, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH1_184]
  simp [stepOk, GS, (suffix_gas_parts hg).2.1]

theorem deposit_suf_EQ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow) 11
          [UInt256.ofNat 184, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow) 12
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_EQ]
  have heq : UInt256.eq (UInt256.ofNat 184) (UInt256.ofNat 0) =
      UInt256.ofNat 0 := eq_zero_of_ne (by decide)
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.1, heq]

theorem deposit_suf_PUSH1_handle (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow) 12 [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow) 14
        [UInt256.ofNat Deposit.handle_input, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH1_handle]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.1]

theorem deposit_suf_JUMPI_handle (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow) 14
          [UInt256.ofNat Deposit.handle_input, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh) 15
        [quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_JUMPI_handle]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.1, bne_zero_zero]

theorem deposit_suf_CALLDATASIZE₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh) 15 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase) 16
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_CALLDATASIZE₂]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.1]

theorem deposit_suf_PUSH2_revert (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase) 16
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow) 19
        [UInt256.ofNat Deposit.revert, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH2_revert]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.1]

theorem deposit_suf_JUMPI_revert (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow) 19
          [UInt256.ofNat Deposit.revert, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh) 20 [quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_JUMPI_revert]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.1, bne_zero_zero]

theorem deposit_suf_CALLVALUE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh) 20 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase) 21
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_CALLVALUE]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.1]

theorem deposit_suf_PUSH2_revert₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase) 21
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow) 24
        [UInt256.ofNat Deposit.revert, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH2_revert₂]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.1]

theorem deposit_suf_JUMPI_value (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow) 24
          [UInt256.ofNat Deposit.revert, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh) 25 [quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_JUMPI_value]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.1, bne_zero_zero]

theorem deposit_suf_PUSH0 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh) 25 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase) 26
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH0]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.1]

theorem deposit_suf_MSTORE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase) 26
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow) 27 [] quote) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_MSTORE]
  simp [GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem deposit_suf_PUSH1_32 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow) 27 [] quote) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow - Gverylow) 29 [UInt256.ofNat 32] quote) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH1_32]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem deposit_suf_PUSH0₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow - Gverylow) 29 [UInt256.ofNat 32] quote) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow - Gverylow - Gbase) 30
        [UInt256.ofNat 0, UInt256.ofNat 32] quote) := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_PUSH0₂]
  simp [stepOk, GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem deposit_suf_RETURN (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep depositSuffixChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow - Gverylow - Gbase) 30
          [UInt256.ofNat 0, UInt256.ofNat 32] quote) =
      .ok { pc := 30, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                     - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                     - Gverylow - Gverylow - Gbase,
            mem0 := quote, returned := some 32 } := by
  unfold getterStep GS
  rw [deposit_suffix_opcode_RETURN]
  simp [GS, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, toNat_32]

theorem runDepositSuffix_ok (σ : Storage) (cds val quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound)
    (hcds : cds = UInt256.ofNat 0) (hval : val = UInt256.ofNat 0) :
    runDepositSuffix σ cds val quote g =
      .ok { pc := 30, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                     - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                     - Gverylow - Gverylow - Gbase,
            mem0 := quote, returned := some 32 } := by
  rw [hcds, hval]
  simp [runDepositSuffix,
        deposit_suf_CALLDATASIZE σ quote g hg,
        deposit_suf_PUSH1_184 σ quote g hg,
        deposit_suf_EQ σ quote g hg,
        deposit_suf_PUSH1_handle σ quote g hg,
        deposit_suf_JUMPI_handle σ quote g hg,
        deposit_suf_CALLDATASIZE₂ σ quote g hg,
        deposit_suf_PUSH2_revert σ quote g hg,
        deposit_suf_JUMPI_revert σ quote g hg,
        deposit_suf_CALLVALUE σ quote g hg,
        deposit_suf_PUSH2_revert₂ σ quote g hg,
        deposit_suf_JUMPI_value σ quote g hg,
        deposit_suf_PUSH0 σ quote g hg,
        deposit_suf_MSTORE σ quote g hg,
        deposit_suf_PUSH1_32 σ quote g hg,
        deposit_suf_PUSH0₂ σ quote g hg,
        deposit_suf_RETURN σ quote g hg]

/-! ## Exit suffix steps (`calldatasize = 0`, `value = 0`) -/

theorem exit_suf_CALLDATASIZE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0 (GS g 7 [quote]) =
      .ok (GS (g - Gbase) 8 [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_CALLDATASIZE]
  simp [stepOk, (suffix_gas_parts hg).1]

theorem exit_suf_PUSH1_48 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase) 8 [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow) 10
        [UInt256.ofNat 48, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH1_48]
  simp [stepOk, (suffix_gas_parts hg).2.1]

theorem exit_suf_EQ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow) 10
          [UInt256.ofNat 48, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow) 11
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_EQ]
  have heq : UInt256.eq (UInt256.ofNat 48) (UInt256.ofNat 0) =
      UInt256.ofNat 0 := eq_zero_of_ne (by decide)
  simp [stepOk, (suffix_gas_parts hg).2.2.1, heq]

theorem exit_suf_PUSH1_handle (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow) 11 [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow) 13
        [UInt256.ofNat Exit.handle_input, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH1_handle]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.1]

theorem exit_suf_JUMPI_handle (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow) 13
          [UInt256.ofNat Exit.handle_input, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh) 14
        [quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_JUMPI_handle]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.1, bne_zero_zero]

theorem exit_suf_CALLDATASIZE₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh) 14 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase) 15
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_CALLDATASIZE₂]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.1]

theorem exit_suf_PUSH2_revert (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase) 15
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow) 18
        [UInt256.ofNat Exit.revert, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH2_revert]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.1]

theorem exit_suf_JUMPI_revert (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow) 18
          [UInt256.ofNat Exit.revert, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh) 19 [quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_JUMPI_revert]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.1, bne_zero_zero]

theorem exit_suf_CALLVALUE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh) 19 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase) 20
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_CALLVALUE]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.1]

theorem exit_suf_PUSH2_revert₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase) 20
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow) 23
        [UInt256.ofNat Exit.revert, UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH2_revert₂]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.1]

theorem exit_suf_JUMPI_value (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow) 23
          [UInt256.ofNat Exit.revert, UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh) 24 [quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_JUMPI_value]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.1, bne_zero_zero]

theorem exit_suf_PUSH0 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh) 24 [quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase) 25
        [UInt256.ofNat 0, quote]) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH0]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.1]

theorem exit_suf_MSTORE (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase) 25
          [UInt256.ofNat 0, quote]) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow) 26 [] quote) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_MSTORE]
  simp [(suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem exit_suf_PUSH1_32 (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow) 26 [] quote) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow - Gverylow) 28 [UInt256.ofNat 32] quote) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH1_32]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem exit_suf_PUSH0₂ (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow - Gverylow) 28 [UInt256.ofNat 32] quote) =
      .ok (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                - Gverylow - Gverylow - Gbase) 29
        [UInt256.ofNat 0, UInt256.ofNat 32] quote) := by
  unfold getterStep GS
  rw [exit_suffix_opcode_PUSH0₂]
  simp [stepOk, (suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem exit_suf_RETURN (σ : Storage) (quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound) :
    getterStep exitSuffixChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) 0
        (GS (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
              - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
              - Gverylow - Gverylow - Gbase) 29
          [UInt256.ofNat 0, UInt256.ofNat 32] quote) =
      .ok { pc := 29, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                     - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                     - Gverylow - Gverylow - Gbase,
            mem0 := quote, returned := some 32 } := by
  unfold getterStep GS
  rw [exit_suffix_opcode_RETURN]
  simp [(suffix_gas_parts hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, toNat_32]

theorem runExitSuffix_ok (σ : Storage) (cds val quote : UInt256) (g : Nat)
    (hg : g ≥ suffixGasBound)
    (hcds : cds = UInt256.ofNat 0) (hval : val = UInt256.ofNat 0) :
    runExitSuffix σ cds val quote g =
      .ok { pc := 29, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                     - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                     - Gverylow - Gverylow - Gbase,
            mem0 := quote, returned := some 32 } := by
  rw [hcds, hval]
  simp [runExitSuffix,
        exit_suf_CALLDATASIZE σ quote g hg,
        exit_suf_PUSH1_48 σ quote g hg,
        exit_suf_EQ σ quote g hg,
        exit_suf_PUSH1_handle σ quote g hg,
        exit_suf_JUMPI_handle σ quote g hg,
        exit_suf_CALLDATASIZE₂ σ quote g hg,
        exit_suf_PUSH2_revert σ quote g hg,
        exit_suf_JUMPI_revert σ quote g hg,
        exit_suf_CALLVALUE σ quote g hg,
        exit_suf_PUSH2_revert₂ σ quote g hg,
        exit_suf_JUMPI_value σ quote g hg,
        exit_suf_PUSH0 σ quote g hg,
        exit_suf_MSTORE σ quote g hg,
        exit_suf_PUSH1_32 σ quote g hg,
        exit_suf_PUSH0₂ σ quote g hg,
        exit_suf_RETURN σ quote g hg]

theorem runGetterSuffix_ok (kind : Kind) (σ : Storage) (cds val quote : UInt256)
    (g : Nat) (hg : g ≥ suffixGasBound)
    (hcds : cds = UInt256.ofNat 0) (hval : val = UInt256.ofNat 0) :
    ∃ pc, runGetterSuffix kind σ cds val quote g =
      .ok { pc := pc, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase
                     - Gverylow - Ghigh - Gbase - Gverylow - Ghigh - Gbase
                     - Gverylow - Gverylow - Gbase,
            mem0 := quote, returned := some 32 } := by
  cases kind with
  | deposit => exact ⟨30, runDepositSuffix_ok σ cds val quote g hg hcds hval⟩
  | exit => exact ⟨29, runExitSuffix_ok σ cds val quote g hg hcds hval⟩

/-! ## Observation: 32-byte return, post-slots read through the run's writes -/

/-- CFG observation of the getter suffix. Post-slots are read from the
machine's own `SSTORE` overlay (`postSlotNat`), so a run that wrote slots
0–3 would report the written values; on a machine error there is no
post-state and the pre-state accessors are a placeholder under
`reverted = true` (same convention as `observationOfRunner`). -/
def feeGetterObservation (kind : Kind) (σ : Storage) (cds val quote : UInt256)
    (g : Nat) : Observation :=
  match runGetterSuffix kind σ cds val quote g with
  | .ok m =>
      { reverted := decide m.returned.isNone
        returnSize := m.returned.getD 0
        slotExcess := postSlotNat σ m.stores SLOT_EXCESS
        slotCount := postSlotNat σ m.stores SLOT_COUNT
        queueHead := postSlotNat σ m.stores QUEUE_HEAD
        queueTail := postSlotNat σ m.stores QUEUE_TAIL }
  | .error _ =>
      { reverted := true
        returnSize := 0
        slotExcess := slotExcess σ
        slotCount := slotCount σ
        queueHead := queueHead σ
        queueTail := queueTail σ }

/-- Empty calldata, value 0, not inhibited, user path: the getter suffix
returns 32 bytes (the `mstore`d quote word), the completing run's `SSTORE`
overlay is empty, and post-storage slots 0–3 — read through that overlay —
equal the well-formed pre-state for every excess and count. Not
`fake_expo` equality (S4). The empty overlay is a theorem about the run,
refutable by any fragment that reaches `SSTORE`. -/
theorem fee_getter_readonly
    (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ)
    (huser : h.isUser = true)
    (cds val : UInt256)
    (hcds : cds = UInt256.ofNat 0)
    (hval : val = UInt256.ofNat 0)
    (hinh : slotExcess σ ≠ inhibitor)
    (quote : UInt256) :
    ∃ m, runGetterSuffix kind σ cds val quote h.gas = .ok m ∧
      m.returned = some 32 ∧ m.mem0 = quote ∧ m.stores = [] ∧
      postSlotNat σ m.stores SLOT_EXCESS = slotExcess σ ∧
      postSlotNat σ m.stores SLOT_COUNT = slotCount σ ∧
      postSlotNat σ m.stores QUEUE_HEAD = queueHead σ ∧
      postSlotNat σ m.stores QUEUE_TAIL = queueTail σ := by
  have hg : h.gas ≥ suffixGasBound :=
    Nat.le_trans suffixGasBound_le_campaign h.gas_ge
  have _ := h.wellFormed
  have _ := huser
  have _ := hinh
  obtain ⟨pc, hrun⟩ := runGetterSuffix_ok kind σ cds val quote h.gas hg hcds hval
  exact ⟨_, hrun, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `Observation` view of the same run, for F4's `Corresponds` shape:
the observation's post-slots are read through the completing run's (empty)
write overlay, so they equal the well-formed pre-state. -/
theorem feeGetterObservation_readonly
    (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ)
    (huser : h.isUser = true)
    (cds val : UInt256)
    (hcds : cds = UInt256.ofNat 0)
    (hval : val = UInt256.ofNat 0)
    (hinh : slotExcess σ ≠ inhibitor)
    (quote : UInt256) :
    let obs := feeGetterObservation kind σ cds val quote h.gas
    obs.reverted = false ∧
      obs.returnSize = 32 ∧
      obs.slotExcess = slotExcess σ ∧
      obs.slotCount = slotCount σ ∧
      obs.queueHead = queueHead σ ∧
      obs.queueTail = queueTail σ := by
  have hg : h.gas ≥ suffixGasBound :=
    Nat.le_trans suffixGasBound_le_campaign h.gas_ge
  have _ := huser
  have _ := hinh
  obtain ⟨pc, hrun⟩ := runGetterSuffix_ok kind σ cds val quote h.gas hg hcds hval
  unfold feeGetterObservation
  rw [hrun]
  simp [postSlotNat, slotExcess, slotCount, queueHead, queueTail, loadNat, loadU256]

/-! ## `bump_excess` is stack-only (∀ count)

After the inhibitor fall-through the user path `SLOAD`s `SLOT_COUNT` and
either `JUMP`s to `compute_user_fee` or adds `count - TARGET` into the
excess word on the stack. Neither branch `SSTORE`s.
-/

theorem deposit_bump_opcode_PUSH1_count :
    opcodeAt depositBumpChunk 4 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl

theorem deposit_bump_opcode_SLOAD :
    opcodeAt depositBumpChunk 6 = some (.SLOAD, none) := rfl

theorem deposit_bump_opcode_PUSH1_target :
    opcodeAt depositBumpChunk 7 =
      some (.PUSH1, some (UInt256.ofNat 8, 1)) := rfl

theorem deposit_bump_opcode_DUP2 :
    opcodeAt depositBumpChunk 9 = some (.DUP2, none) := rfl

theorem deposit_bump_opcode_GT :
    opcodeAt depositBumpChunk 10 = some (.GT, none) := rfl

theorem deposit_bump_opcode_PUSH1_bump :
    opcodeAt depositBumpChunk 11 =
      some (.PUSH1, some (UInt256.ofNat Deposit.bump_excess, 1)) := rfl

theorem deposit_bump_opcode_JUMPI :
    opcodeAt depositBumpChunk 13 = some (.JUMPI, none) := rfl

theorem deposit_bump_opcode_POP :
    opcodeAt depositBumpChunk 14 = some (.POP, none) := rfl

theorem deposit_bump_opcode_PUSH1_compute :
    opcodeAt depositBumpChunk 15 =
      some (.PUSH1, some (UInt256.ofNat Deposit.compute_user_fee, 1)) := rfl

theorem deposit_bump_opcode_JUMP :
    opcodeAt depositBumpChunk 17 = some (.JUMP, none) := rfl

theorem deposit_bump_opcode_JUMPDEST_bump :
    opcodeAt depositBumpChunk 18 = some (.JUMPDEST, none) := rfl

theorem deposit_bump_opcode_PUSH1_target₂ :
    opcodeAt depositBumpChunk 19 =
      some (.PUSH1, some (UInt256.ofNat 8, 1)) := rfl

theorem deposit_bump_opcode_SWAP1 :
    opcodeAt depositBumpChunk 21 = some (.SWAP1, none) := rfl

theorem deposit_bump_opcode_SUB :
    opcodeAt depositBumpChunk 22 = some (.SUB, none) := rfl

theorem deposit_bump_opcode_ADD :
    opcodeAt depositBumpChunk 23 = some (.ADD, none) := rfl

theorem deposit_bump_opcode_JUMPDEST_compute :
    opcodeAt depositBumpChunk 24 = some (.JUMPDEST, none) := rfl

theorem exit_bump_opcode_PUSH1_count :
    opcodeAt exitBumpChunk 3 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl

theorem exit_bump_opcode_SLOAD :
    opcodeAt exitBumpChunk 5 = some (.SLOAD, none) := rfl

theorem exit_bump_opcode_PUSH1_target :
    opcodeAt exitBumpChunk 6 =
      some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl

theorem exit_bump_opcode_DUP2 :
    opcodeAt exitBumpChunk 8 = some (.DUP2, none) := rfl

theorem exit_bump_opcode_GT :
    opcodeAt exitBumpChunk 9 = some (.GT, none) := rfl

theorem exit_bump_opcode_PUSH1_bump :
    opcodeAt exitBumpChunk 10 =
      some (.PUSH1, some (UInt256.ofNat Exit.bump_excess, 1)) := rfl

theorem exit_bump_opcode_JUMPI :
    opcodeAt exitBumpChunk 12 = some (.JUMPI, none) := rfl

theorem exit_bump_opcode_POP :
    opcodeAt exitBumpChunk 13 = some (.POP, none) := rfl

theorem exit_bump_opcode_PUSH1_compute :
    opcodeAt exitBumpChunk 14 =
      some (.PUSH1, some (UInt256.ofNat Exit.compute_user_fee, 1)) := rfl

theorem exit_bump_opcode_JUMP :
    opcodeAt exitBumpChunk 16 = some (.JUMP, none) := rfl

theorem exit_bump_opcode_JUMPDEST_bump :
    opcodeAt exitBumpChunk 17 = some (.JUMPDEST, none) := rfl

theorem exit_bump_opcode_PUSH1_target₂ :
    opcodeAt exitBumpChunk 18 =
      some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl

theorem exit_bump_opcode_SWAP1 :
    opcodeAt exitBumpChunk 20 = some (.SWAP1, none) := rfl

theorem exit_bump_opcode_SUB :
    opcodeAt exitBumpChunk 21 = some (.SUB, none) := rfl

theorem exit_bump_opcode_ADD :
    opcodeAt exitBumpChunk 22 = some (.ADD, none) := rfl

theorem exit_bump_opcode_JUMPDEST_compute :
    opcodeAt exitBumpChunk 23 = some (.JUMPDEST, none) := rfl

/-- Conservative gas for either bump branch (`SLOAD` is the dominant term). -/
def bumpGasBound : Nat := Gcoldsload + 20 * Gverylow + Ghigh + Gmid + 2 * Gjumpdest + Gbase

theorem bumpGasBound_le_campaign : bumpGasBound ≤ campaignGasBound := by
  decide

private theorem gt_one_of_gt {a b : UInt256} (h : a > b) :
    UInt256.gt a b = UInt256.ofNat 1 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

private theorem gt_zero_of_not_gt {a b : UInt256} (h : ¬ a > b) :
    UInt256.gt a b = UInt256.ofNat 0 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

theorem deposit_compute_local :
    (UInt256.ofNat Deposit.compute_user_fee).toNat - bumpChunkBase = 24 := by
  rw [toNat_deposit_compute_user_fee]; rfl

theorem deposit_bump_local :
    (UInt256.ofNat Deposit.bump_excess).toNat - bumpChunkBase = 18 := by
  rw [toNat_deposit_bump_excess]; rfl

theorem exit_compute_local :
    (UInt256.ofNat Exit.compute_user_fee).toNat - bumpChunkBase = 23 := by
  rw [toNat_exit_compute_user_fee]; rfl

theorem exit_bump_local :
    (UInt256.ofNat Exit.bump_excess).toNat - bumpChunkBase = 17 := by
  rw [toNat_exit_bump_excess]; rfl

private theorem bump_gas_sload {g : Nat} (hg : g ≥ bumpGasBound) :
    ¬ g < Gverylow ∧ ¬ g - Gverylow < Gcoldsload := by
  simp [bumpGasBound, Gverylow, Gcoldsload] at hg ⊢
  omega

/-- `PUSH1 SLOT_COUNT; SLOAD` reads `slotCount σ` onto the stack. ∀ count. -/
theorem deposit_bump_sload_count (σ : Storage) (g : Nat)
    (hg : g ≥ bumpGasBound) (excess : UInt256) :
    getterStep depositBumpChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) bumpChunkBase
        (GS (g - Gverylow) 6 [UInt256.ofNat 1, excess]) =
      .ok (GS (g - Gverylow - Gcoldsload) 7 [loadU256 σ 1, excess]) := by
  unfold getterStep GS
  rw [deposit_bump_opcode_SLOAD]
  simp [stepOk, sload_slot1, (bump_gas_sload hg).2]

theorem deposit_bump_push_count (σ : Storage) (g : Nat)
    (hg : g ≥ bumpGasBound) (excess : UInt256) :
    getterStep depositBumpChunk depositJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) bumpChunkBase
        (GS g 4 [excess]) =
      .ok (GS (g - Gverylow) 6 [UInt256.ofNat 1, excess]) := by
  unfold getterStep GS
  rw [deposit_bump_opcode_PUSH1_count]
  simp [stepOk, (bump_gas_sload hg).1]

theorem exit_bump_push_count (σ : Storage) (g : Nat)
    (hg : g ≥ bumpGasBound) (excess : UInt256) :
    getterStep exitBumpChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) bumpChunkBase
        (GS g 3 [excess]) =
      .ok (GS (g - Gverylow) 5 [UInt256.ofNat 1, excess]) := by
  unfold getterStep GS
  rw [exit_bump_opcode_PUSH1_count]
  simp [stepOk, (bump_gas_sload hg).1]

theorem exit_bump_sload_count (σ : Storage) (g : Nat)
    (hg : g ≥ bumpGasBound) (excess : UInt256) :
    getterStep exitBumpChunk exitJumpdests σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) bumpChunkBase
        (GS (g - Gverylow) 5 [UInt256.ofNat 1, excess]) =
      .ok (GS (g - Gverylow - Gcoldsload) 6 [loadU256 σ 1, excess]) := by
  unfold getterStep GS
  rw [exit_bump_opcode_SLOAD]
  simp [stepOk, sload_slot1, (bump_gas_sload hg).2]

/-- ∀ kind, ∀ well-formed `σ`: the bump path `SLOAD`s `SLOT_COUNT` (never
`SSTORE`s it). The fold at `TARGET` is the same stack `ADD` as control. -/
theorem bump_readonly (kind : Kind) (σ : Storage) (g : Nat)
    (hg : g ≥ bumpGasBound) (excess : UInt256) :
    ∃ m, getterStep (bumpChunk kind) (openingJumps kind) σ
        (UInt256.ofNat 0) (UInt256.ofNat 0) bumpChunkBase
        (GS (g - Gverylow)
          (match kind with | .deposit => 6 | .exit => 5)
          [UInt256.ofNat 1, excess]) = .ok m ∧
      m.stack.head? = some (loadU256 σ 1) := by
  cases kind with
  | deposit =>
      refine ⟨_, deposit_bump_sload_count σ g hg excess, ?_⟩
      simp [GS]
  | exit =>
      refine ⟨_, exit_bump_sload_count σ g hg excess, ?_⟩
      simp [GS]

theorem deposit_after_inh_runtime_pc :
    bumpChunkBase + depositAfterInhLocal = 68 := rfl

theorem exit_after_inh_runtime_pc :
    bumpChunkBase + exitAfterInhLocal = 67 := rfl

/-- Both runtimes: first opcode after the inhibitor `JUMPI` is
`PUSH1 SLOT_COUNT`, not `SSTORE`. -/
theorem after_inhibitor_not_sstore (kind : Kind) :
    opcodeAt (bumpChunk kind)
        (match kind with | .deposit => depositAfterInhLocal | .exit => exitAfterInhLocal) ≠
      some (.SSTORE, none) := by
  cases kind with
  | deposit =>
      simp [bumpChunk]
      rw [deposit_bump_opcode_PUSH1_count]
      intro h; cases h
  | exit =>
      simp [bumpChunk]
      rw [exit_bump_opcode_PUSH1_count]
      intro h; cases h

end Eip8282.Audit.Guarantees.PSubmit1.Fee
