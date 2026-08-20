import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Bytecode
import Eip8282.Audit.Model
import Eip8282.Audit.WellFormed
import Eip8282.Audit.Step
import Eip8282.Audit.EvmRunner

/-!
CFG-level correspondence between `Model.userCall` and the pinned runtimes.

Attempt A (user path): extend F3's prefix stepper through the inhibitor
`JUMPI @revert` and through the fee-quote dispatch that sits *after*
`fake_expo`. Opcode facts are `rfl` on short `fromHex` prefixes — never on
the full runtime, and never via `native_decide`.

Full `Ξ` / `X` simulation (including the `fake_expo` loop that produces the
numeric fee) is left open. Exact `fakeExponential` equality is S4.
System-path correspondence is out of scope.
-/

namespace Eip8282.Audit.Correspondence

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Model
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Step
open Eip8282.Audit.EvmRunner
open GasConstants

set_option maxRecDepth 20000
set_option linter.unusedVariables false

/-- Interpreter fuel bound mentioned by the campaign (PSubmit1 uses 80000).
CFG lemmas do not reduce `Ξ`; this constant names the intended hyp. -/
def interpreterFuel : Nat := 80000

/-! ## Observations and correspondence -/

/-- CFG-level observation of a user-path fragment. -/
inductive Observation where
  /-- Opening gate fell through to the user `PUSH0`. -/
  | gateUser (pc : Nat)
  /-- `JUMPI` landed on the runtime `@revert` JUMPDEST. -/
  | jumpiRevert (pc : Nat)
  /-- `RETURN` of a 32-byte word (fee quote). The word is the stack/memory
  value, not claimed equal to `Model.currentFee`. -/
  | return32 (word : UInt256)
  deriving DecidableEq, Repr

/-- Relate a `Model.Outcome` to a CFG observation (shape, not numeric fee). -/
def Corresponds (out : Outcome) (obs : Observation) : Prop :=
  match out, obs with
  | .revert _, .jumpiRevert _ => True
  | .success _ data, .return32 _ => data.length = 32
  | _, _ => False

/-- Intended `Ξ`-level correspondence. Attempt A does not discharge this:
doing so requires reducing `EvmYul.EVM.X` / `Ξ`. -/
def CorrespondsRun (out : Outcome) (res : RunResult) : Prop :=
  match out with
  | .revert _ => isRevert res = true
  | .success _ data =>
      isSuccess res = true ∧ successOutSize res = data.length

/-! ## Extended CFG machine (F3's `CfgState` plus storage / env / halt) -/

inductive Halt where
  | running
  | reverted
  | returned (size : Nat)
  deriving DecidableEq, Repr, Inhabited

structure Machine where
  pc : Nat
  stack : List UInt256
  gas : Nat
  storage : Storage
  calldataSize : Nat
  callvalue : UInt256
  mem0 : UInt256
  sstoreCount : Nat
  halt : Halt
  deriving Inhabited, Repr

def mkRunning (pc : Nat) (stack : List UInt256) (gas : Nat)
    (σ : Storage) (cdSize : Nat) (value : UInt256) : Machine :=
  { pc := pc, stack := stack, gas := gas, storage := σ,
    calldataSize := cdSize, callvalue := value,
    mem0 := UInt256.ofNat 0, sstoreCount := 0, halt := .running }

/-- Lift F3's post-gate `CfgState` into the extended machine. -/
def ofGate (g : CfgState) (σ : Storage) (cdSize : Nat) (value : UInt256) :
    Machine :=
  mkRunning g.pc g.stack g.gas σ cdSize value

/-! ## User-path stepper (superset of F3 `cfgStep`; local to this module) -/

def Machine.push (m : Machine) (v : UInt256) (pcDelta gasCost : Nat) : Machine :=
  { pc := m.pc + pcDelta,
    stack := List.cons v m.stack,
    gas := m.gas - gasCost,
    storage := m.storage,
    calldataSize := m.calldataSize,
    callvalue := m.callvalue,
    mem0 := m.mem0,
    sstoreCount := m.sstoreCount,
    halt := m.halt }

def Machine.setStack (m : Machine) (stack : List UInt256) (pcDelta gasCost : Nat) :
    Machine :=
  { pc := m.pc + pcDelta,
    stack := stack,
    gas := m.gas - gasCost,
    storage := m.storage,
    calldataSize := m.calldataSize,
    callvalue := m.callvalue,
    mem0 := m.mem0,
    sstoreCount := m.sstoreCount,
    halt := m.halt }

def Machine.setPcStack (m : Machine) (pc : Nat) (stack : List UInt256) (gasCost : Nat) :
    Machine :=
  { pc := pc,
    stack := stack,
    gas := m.gas - gasCost,
    storage := m.storage,
    calldataSize := m.calldataSize,
    callvalue := m.callvalue,
    mem0 := m.mem0,
    sstoreCount := m.sstoreCount,
    halt := m.halt }

def Machine.mstore0 (m : Machine) (val : UInt256) (stack : List UInt256) (gasCost : Nat) :
    Machine :=
  { pc := m.pc + 1,
    stack := stack,
    gas := m.gas - gasCost,
    storage := m.storage,
    calldataSize := m.calldataSize,
    callvalue := m.callvalue,
    mem0 := val,
    sstoreCount := m.sstoreCount,
    halt := m.halt }

def Machine.doReturn (m : Machine) (size : Nat) (stack : List UInt256) :
    Machine :=
  { pc := m.pc,
    stack := stack,
    gas := m.gas,
    storage := m.storage,
    calldataSize := m.calldataSize,
    callvalue := m.callvalue,
    mem0 := m.mem0,
    sstoreCount := m.sstoreCount,
    halt := Halt.returned size }

def cfgStep (code : ByteArray) (validJumps : Array UInt256) (m : Machine) :
    Except CfgError Machine :=
  match opcodeAt code m.pc with
  | some (.Push _, none) =>
      if m.gas < Gbase then .error .outOfGas
      else .ok (m.push (UInt256.ofNat 0) 1 Gbase)
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else .ok (m.push imm (1 + width) Gverylow)
  | some (.StackMemFlow .SLOAD, none) =>
      match m.stack with
      | slot :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok (m.setStack (List.cons (m.storage.getD slot (UInt256.ofNat 0)) rest)
              1 Gcoldsload)
      | _ => .error .stackUnderflow
  | some (.Dup .DUP1, none) =>
      match m.stack with
      | a :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok (m.setStack (List.cons a (List.cons a rest)) 1 Gverylow)
      | _ => .error .stackUnderflow
  | some (.CompBit .EQ, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else .ok (m.setStack (List.cons (UInt256.eq a b) rest) 1 Gverylow)
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPI, none) =>
      match m.stack with
      | dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond = UInt256.ofNat 0 then
            .ok (m.setStack rest 1 Ghigh)
          else if validJumps.contains dest then
            .ok (m.setPcStack dest.toNat rest Ghigh)
          else
            .error .badJump
      | _ => .error .stackUnderflow
  | some (.Env .CALLDATASIZE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else .ok (m.push (UInt256.ofNat m.calldataSize) 1 Gbase)
  | some (.Env .CALLVALUE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else .ok (m.push m.callvalue 1 Gbase)
  | some (.StackMemFlow .MSTORE, none) =>
      match m.stack with
      | off :: val :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else if off = UInt256.ofNat 0 then
            .ok (m.mstore0 val rest Gverylow)
          else
            .error .unexpectedOpcode
      | _ => .error .stackUnderflow
  | some (.System .RETURN, none) =>
      match m.stack with
      | _off :: sz :: rest =>
          if m.gas < Gzero then .error .outOfGas
          else .ok (m.doReturn sz.toNat rest)
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

/-! ## Pinned prefixes (short `fromHex`; not the full runtime) -/

/-- Bytes 0..67 of `depositRuntime`: gate + inhibitor `JUMPI @revert`. -/
def depositInhibitorHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff"
  ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14"
  ++ "61027057"

/-- Bytes 0..66 of `exitRuntime`: gate + inhibitor `JUMPI @revert`. -/
def exitInhibitorHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff"
  ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1461"
  ++ "01c657"

def depositInhibitor : ByteArray := fromHex depositInhibitorHex
def exitInhibitor : ByteArray := fromHex exitInhibitorHex

/-- Fee-quote dispatch of the deposit runtime (PC 136..158 of the image).
Immediates (`INPUT_SIZE`, `@handle_input`, `@revert`) are absolute. -/
def depositDispatchHex : String :=
  "3660b814609f57366102705734610270575f5260205ff3"

/-- Fee-quote dispatch of the exit runtime (PC 135..157 of the image). -/
def exitDispatchHex : String :=
  "36603014609e57366101c657346101c6575f5260205ff3"

def depositDispatch : ByteArray := fromHex depositDispatchHex
def exitDispatch : ByteArray := fromHex exitDispatchHex

def inhibitorU256 : UInt256 := UInt256.ofNat inhibitor

@[simp] def depositInhJumpiPc : Nat := 67
@[simp] def exitInhJumpiPc : Nat := 66
@[simp] def depositAfterInhibitorPc : Nat := 68
@[simp] def exitAfterInhibitorPc : Nat := 67

/-- PCs inside a 23-byte dispatch slice (identical layout for both runtimes). -/
@[simp] def dispCalldatasize : Nat := 0
@[simp] def dispJumpiHandle : Nat := 6
@[simp] def dispJumpiNonempty : Nat := 11
@[simp] def dispJumpiValue : Nat := 16
@[simp] def dispReturn : Nat := 22

/-! ## Gas for the inhibitor prefix (after the F3 gate) -/

/-- `PUSH0; SLOAD; DUP1; PUSH32; EQ; PUSH2; JUMPI`.
`SLOAD` is charged `Gcoldsload` (cold; safe upper bound). -/
def inhibitorGasBound : Nat :=
  Gbase + Gcoldsload + 4 * Gverylow + Ghigh

theorem inhibitorGasBound_eq : inhibitorGasBound = 2124 := rfl

theorem inhibitorGasBound_le_campaign_minus_prefix :
    inhibitorGasBound ≤ campaignGasBound - prefixGasBound := by
  rw [inhibitorGasBound_eq, campaignGasBound, prefixGasBound_eq]
  decide

/-- Dispatch path through `RETURN` (empty + value 0). Generous bound. -/
def dispatchGasBound : Nat := 100

theorem dispatchGasBound_le_campaign :
    dispatchGasBound ≤ campaignGasBound := by
  simp [dispatchGasBound, campaignGasBound]

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

private theorem remaining_ge_inhibitor {gas : Nat}
    (hgas : gas ≥ campaignGasBound) :
    gas - prefixGasBound ≥ inhibitorGasBound :=
  Nat.le_trans inhibitorGasBound_le_campaign_minus_prefix
    (Nat.sub_le_sub_right hgas prefixGasBound)

/-! ## Opcode facts — inhibitor prefixes -/

theorem deposit_inh_PUSH0 :
    opcodeAt depositInhibitor 27 = some (.PUSH0, none) := rfl

theorem deposit_inh_SLOAD :
    opcodeAt depositInhibitor 28 = some (.SLOAD, none) := rfl

theorem deposit_inh_DUP1 :
    opcodeAt depositInhibitor 29 = some (.DUP1, none) := rfl

theorem deposit_inh_PUSH32 :
    opcodeAt depositInhibitor 30 =
      some (.PUSH32, some (inhibitorU256, 32)) := rfl

theorem deposit_inh_EQ :
    opcodeAt depositInhibitor 63 = some (.EQ, none) := rfl

theorem deposit_inh_PUSH2 :
    opcodeAt depositInhibitor 64 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_inh_JUMPI :
    opcodeAt depositInhibitor 67 = some (.JUMPI, none) := rfl

theorem exit_inh_PUSH0 :
    opcodeAt exitInhibitor 26 = some (.PUSH0, none) := rfl

theorem exit_inh_SLOAD :
    opcodeAt exitInhibitor 27 = some (.SLOAD, none) := rfl

theorem exit_inh_DUP1 :
    opcodeAt exitInhibitor 28 = some (.DUP1, none) := rfl

theorem exit_inh_PUSH32 :
    opcodeAt exitInhibitor 29 =
      some (.PUSH32, some (inhibitorU256, 32)) := rfl

theorem exit_inh_EQ :
    opcodeAt exitInhibitor 62 = some (.EQ, none) := rfl

theorem exit_inh_PUSH2 :
    opcodeAt exitInhibitor 63 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_inh_JUMPI :
    opcodeAt exitInhibitor 66 = some (.JUMPI, none) := rfl

/-! ## Opcode facts — fee-quote dispatch slices -/

theorem deposit_disp_CALLDATASIZE :
    opcodeAt depositDispatch 0 = some (.CALLDATASIZE, none) := rfl

theorem deposit_disp_PUSH_INPUT :
    opcodeAt depositDispatch 1 =
      some (.PUSH1, some (UInt256.ofNat 184, 1)) := rfl

theorem deposit_disp_EQ :
    opcodeAt depositDispatch 3 = some (.EQ, none) := rfl

theorem deposit_disp_PUSH_HANDLE :
    opcodeAt depositDispatch 4 =
      some (.PUSH1, some (UInt256.ofNat Deposit.handle_input, 1)) := rfl

theorem deposit_disp_JUMPI_HANDLE :
    opcodeAt depositDispatch 6 = some (.JUMPI, none) := rfl

theorem deposit_disp_CALLDATASIZE2 :
    opcodeAt depositDispatch 7 = some (.CALLDATASIZE, none) := rfl

theorem deposit_disp_PUSH_REVERT :
    opcodeAt depositDispatch 8 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_disp_JUMPI_NONEMPTY :
    opcodeAt depositDispatch 11 = some (.JUMPI, none) := rfl

theorem deposit_disp_CALLVALUE :
    opcodeAt depositDispatch 12 = some (.CALLVALUE, none) := rfl

theorem deposit_disp_PUSH_REVERT2 :
    opcodeAt depositDispatch 13 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_disp_JUMPI_VALUE :
    opcodeAt depositDispatch 16 = some (.JUMPI, none) := rfl

theorem deposit_disp_PUSH0 :
    opcodeAt depositDispatch 17 = some (.PUSH0, none) := rfl

theorem deposit_disp_MSTORE :
    opcodeAt depositDispatch 18 = some (.MSTORE, none) := rfl

theorem deposit_disp_PUSH_SIZE :
    opcodeAt depositDispatch 19 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) := rfl

theorem deposit_disp_PUSH0b :
    opcodeAt depositDispatch 21 = some (.PUSH0, none) := rfl

theorem deposit_disp_RETURN :
    opcodeAt depositDispatch 22 = some (.RETURN, none) := rfl

theorem exit_disp_CALLDATASIZE :
    opcodeAt exitDispatch 0 = some (.CALLDATASIZE, none) := rfl

theorem exit_disp_PUSH_INPUT :
    opcodeAt exitDispatch 1 =
      some (.PUSH1, some (UInt256.ofNat 48, 1)) := rfl

theorem exit_disp_EQ :
    opcodeAt exitDispatch 3 = some (.EQ, none) := rfl

theorem exit_disp_PUSH_HANDLE :
    opcodeAt exitDispatch 4 =
      some (.PUSH1, some (UInt256.ofNat Exit.handle_input, 1)) := rfl

theorem exit_disp_JUMPI_HANDLE :
    opcodeAt exitDispatch 6 = some (.JUMPI, none) := rfl

theorem exit_disp_CALLDATASIZE2 :
    opcodeAt exitDispatch 7 = some (.CALLDATASIZE, none) := rfl

theorem exit_disp_PUSH_REVERT :
    opcodeAt exitDispatch 8 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_disp_JUMPI_NONEMPTY :
    opcodeAt exitDispatch 11 = some (.JUMPI, none) := rfl

theorem exit_disp_CALLVALUE :
    opcodeAt exitDispatch 12 = some (.CALLVALUE, none) := rfl

theorem exit_disp_PUSH_REVERT2 :
    opcodeAt exitDispatch 13 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_disp_JUMPI_VALUE :
    opcodeAt exitDispatch 16 = some (.JUMPI, none) := rfl

theorem exit_disp_PUSH0 :
    opcodeAt exitDispatch 17 = some (.PUSH0, none) := rfl

theorem exit_disp_MSTORE :
    opcodeAt exitDispatch 18 = some (.MSTORE, none) := rfl

theorem exit_disp_PUSH_SIZE :
    opcodeAt exitDispatch 19 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) := rfl

theorem exit_disp_PUSH0b :
    opcodeAt exitDispatch 21 = some (.PUSH0, none) := rfl

theorem exit_disp_RETURN :
    opcodeAt exitDispatch 22 = some (.RETURN, none) := rfl

/-! ## Jumpdest membership and UInt256 helpers -/

theorem deposit_revert_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.revert) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Deposit.revert,
      mem_depositJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem exit_revert_contains :
    exitJumpdests.contains (UInt256.ofNat Exit.revert) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Exit.revert,
      mem_exitJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem toNat_deposit_revert :
    (UInt256.ofNat Deposit.revert).toNat = Deposit.revert := rfl

theorem toNat_exit_revert :
    (UInt256.ofNat Exit.revert).toNat = Exit.revert := rfl

private theorem eq_one_of_eq {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem ofNat_one_ne_zero : UInt256.ofNat 1 ≠ UInt256.ofNat 0 := by
  decide

theorem ofNat_toNat (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with
  | mk val =>
    simp [UInt256.ofNat, UInt256.toNat, Id.run]

theorem inhibitor_lt_size : inhibitor < UInt256.size := by
  unfold inhibitor UInt256.size
  exact Nat.sub_one_lt (by decide : 2 ^ 256 ≠ 0)

theorem toNat_ofNat_of_lt {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.toNat, UInt256.ofNat, Id.run]
  exact Nat.mod_eq_of_lt hn

theorem toNat_inhibitorU256 : inhibitorU256.toNat = inhibitor :=
  toNat_ofNat_of_lt inhibitor_lt_size

theorem loadU256_eq_ofNat_slotExcess (σ : Storage) :
    loadU256 σ SLOT_EXCESS = UInt256.ofNat (slotExcess σ) := by
  unfold slotExcess loadNat
  exact (ofNat_toNat (loadU256 σ SLOT_EXCESS)).symm

theorem loadU256_inhibitor {σ : Storage} (h : slotExcess σ = inhibitor) :
    loadU256 σ SLOT_EXCESS = inhibitorU256 := by
  rw [loadU256_eq_ofNat_slotExcess, h, inhibitorU256]

theorem loadU256_ne_inhibitor {σ : Storage} (h : slotExcess σ ≠ inhibitor) :
    loadU256 σ SLOT_EXCESS ≠ inhibitorU256 := by
  intro heq
  apply h
  calc slotExcess σ
      = (loadU256 σ SLOT_EXCESS).toNat := rfl
    _ = inhibitorU256.toNat := congrArg UInt256.toNat heq
    _ = inhibitor := toNat_inhibitorU256

theorem getD_slotExcess (σ : Storage) :
    σ.getD (UInt256.ofNat 0) (UInt256.ofNat 0) = loadU256 σ SLOT_EXCESS := by
  simp [loadU256, SLOT_EXCESS]

/-! ## Model facts used by correspondence -/

theorem userCall_inhibited (s : Model.State) (caller : Address) (cd : List Byte) (v : Wei)
    (h : inhibited s = true) :
    userCall s caller cd v = .revert s := by
  simp [userCall, h]

theorem userCall_empty_nonzero (s : Model.State) (caller : Address) (v : Wei)
    (hinh : inhibited s = false) (hv : v ≠ 0) :
    userCall s caller [] v = .revert s := by
  simp [userCall, hinh, hv]

theorem toLeBytes_length (n w : Nat) : (toLeBytes n w).length = w := by
  induction w generalizing n with
  | zero => simp [toLeBytes]
  | succ w ih => simp [toLeBytes, ih]

theorem toBeBytes_length (n w : Nat) : (toBeBytes n w).length = w := by
  simp [toBeBytes, toLeBytes_length, List.length_reverse]

theorem userCall_empty_zero (s : Model.State) (caller : Address)
    (hinh : inhibited s = false) :
    userCall s caller [] 0 = .success s (toBeBytes (currentFee s) 32) := by
  simp [userCall, hinh]

/-! ## F3 gate on the user path -/

theorem deposit_user_gate
    (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound)
    (huser : isUserCaller caller) {g : CfgState}
    (hg : runGatePrefix depositOpening caller depositJumpdests gas = .ok g) :
    g.pc = depositUserPc ∧ g.stack = [] := by
  have hpre : gas ≥ prefixGasBound := Nat.le_trans prefixGasBound_le_campaign hgas
  exact ⟨deposit_user_to_userPc caller gas hpre huser hg,
    (deposit_caller_gate caller gas hpre hg).2.2⟩

theorem exit_user_gate
    (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound)
    (huser : isUserCaller caller) {g : CfgState}
    (hg : runGatePrefix exitOpening caller exitJumpdests gas = .ok g) :
    g.pc = exitUserPc ∧ g.stack = [] := by
  have hpre : gas ≥ prefixGasBound := Nat.le_trans prefixGasBound_le_campaign hgas
  exact ⟨exit_user_to_userPc caller gas hpre huser hg,
    (exit_caller_gate caller gas hpre hg).2.2⟩

/-! ## Inhibitor CFG (seven ticks from the user PC) -/

def runInhibitor (code : ByteArray) (validJumps : Array UInt256) (m : Machine) :
    Except CfgError Machine :=
  match cfgStep code validJumps m with
  | .error e => .error e
  | .ok m1 =>
    match cfgStep code validJumps m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStep code validJumps m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStep code validJumps m3 with
        | .error e => .error e
        | .ok m4 =>
          match cfgStep code validJumps m4 with
          | .error e => .error e
          | .ok m5 =>
            match cfgStep code validJumps m5 with
            | .error e => .error e
            | .ok m6 => cfgStep code validJumps m6

private theorem inh_gas_ok {g : Nat} (h : g ≥ inhibitorGasBound) :
    ¬ g < Gbase ∧
    ¬ g - Gbase < Gcoldsload ∧
    ¬ g - Gbase - Gcoldsload < Gverylow ∧
    ¬ g - Gbase - Gcoldsload - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow < Ghigh := by
  simp [inhibitorGasBound, Gbase, Gcoldsload, Gverylow, Ghigh] at h
  simp [Gbase, Gcoldsload, Gverylow, Ghigh]
  omega

theorem deposit_cfg_PUSH0 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests (mkRunning 27 [] g σ cd v) =
      .ok (mkRunning 28 [UInt256.ofNat 0] (g - Gbase) σ cd v) := by
  simp [cfgStep, mkRunning, deposit_inh_PUSH0]
  have hlt := (inh_gas_ok hg).1
  simp [hlt, Machine.push]

theorem deposit_cfg_SLOAD (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 28 [UInt256.ofNat 0] (g - Gbase) σ cd v) =
      .ok (mkRunning 29 [loadU256 σ SLOT_EXCESS]
            (g - Gbase - Gcoldsload) σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_SLOAD]
  have hlt := (inh_gas_ok hg).2.1
  simp only [hlt, Machine.setStack]
  rw [getD_slotExcess]
  rfl

theorem deposit_cfg_DUP1 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 29 [exc] (g - Gbase - Gcoldsload) σ cd v) =
      .ok (mkRunning 30 [exc, exc]
            (g - Gbase - Gcoldsload - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_DUP1]
  have hlt := (inh_gas_ok hg).2.2.1
  simp only [hlt, Machine.setStack]
  rfl

theorem deposit_cfg_PUSH32 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 30 [exc, exc]
          (g - Gbase - Gcoldsload - Gverylow) σ cd v) =
      .ok (mkRunning 63 [inhibitorU256, exc, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_PUSH32]
  have hlt := (inh_gas_ok hg).2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem deposit_cfg_EQ (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 63 [inhibitorU256, exc, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow) σ cd v) =
      .ok (mkRunning 64 [UInt256.eq inhibitorU256 exc, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_EQ]
  have hlt := (inh_gas_ok hg).2.2.2.2.1
  simp only [hlt, Machine.setStack]
  rfl

theorem deposit_cfg_PUSH2_revert (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (cond exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 64 [cond, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow) σ cd v) =
      .ok (mkRunning 67 [UInt256.ofNat Deposit.revert, cond, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow)
            σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_PUSH2]
  have hlt := (inh_gas_ok hg).2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem deposit_cfg_JUMPI_inhibited (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound)
    (heq : UInt256.eq inhibitorU256 exc = UInt256.ofNat 1) :
    cfgStep depositInhibitor depositJumpdests
        (mkRunning 67
          [UInt256.ofNat Deposit.revert, UInt256.eq inhibitorU256 exc, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow)
          σ cd v) =
      .ok (mkRunning Deposit.revert [exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
            σ cd v) := by
  unfold cfgStep mkRunning
  rw [deposit_inh_JUMPI]
  have hlt := (inh_gas_ok hg).2.2.2.2.2.2
  rw [heq]
  simp only [hlt, ofNat_one_ne_zero, deposit_revert_contains, toNat_deposit_revert,
    Machine.setPcStack]
  rfl

theorem deposit_runInhibitor_inhibited (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) (hinh : slotExcess σ = inhibitor) :
    runInhibitor depositInhibitor depositJumpdests (mkRunning 27 [] g σ cd v) =
      .ok (mkRunning Deposit.revert [inhibitorU256]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
            σ cd v) := by
  have hexc := loadU256_inhibitor hinh
  have h0 := deposit_cfg_PUSH0 σ g cd v hg
  have h1 := deposit_cfg_SLOAD σ g cd v hg
  have h2 := deposit_cfg_DUP1 σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h3 := deposit_cfg_PUSH32 σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h4 := deposit_cfg_EQ σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h5 := deposit_cfg_PUSH2_revert σ g cd v
    (UInt256.eq inhibitorU256 (loadU256 σ SLOT_EXCESS))
    (loadU256 σ SLOT_EXCESS) hg
  simp [runInhibitor, h0, h1, h2, h3, h4, h5]
  rw [hexc]
  exact deposit_cfg_JUMPI_inhibited σ g cd v inhibitorU256 hg (eq_one_of_eq rfl)

/-- Inhibitor set: user path `JUMPI @revert` with no `SSTORE`. Matches `userCall`. -/
theorem deposit_inhibited_jumpi_revert
    (σ : Storage) (_wf : WellFormed .deposit σ)
    (caller : UInt256) (_huser : isUserCaller caller)
    (gas : Nat) (hgas : gas ≥ campaignGasBound)
    (_fuel : Nat) (_hfuel : fuel ≥ interpreterFuel)
    (cd : List Byte) (value : Wei)
    (hinh : slotExcess σ = inhibitor) :
    runInhibitor depositInhibitor depositJumpdests
        (mkRunning depositUserPc [] (gas - prefixGasBound) σ cd.length
          (UInt256.ofNat value)) =
      .ok (mkRunning Deposit.revert [inhibitorU256]
            (gas - prefixGasBound - Gbase - Gcoldsload - Gverylow - Gverylow
              - Gverylow - Gverylow - Ghigh)
            σ cd.length (UInt256.ofNat value)) ∧
      Corresponds
        (userCall (toModel .deposit σ 0) caller.toNat cd value)
        (.jumpiRevert Deposit.revert) := by
  have hg : gas - prefixGasBound ≥ inhibitorGasBound := remaining_ge_inhibitor hgas
  refine ⟨?_, ?_⟩
  · simpa [depositUserPc] using
      deposit_runInhibitor_inhibited σ (gas - prefixGasBound) cd.length
        (UInt256.ofNat value) hg hinh
  · have hinhm : inhibited (toModel .deposit σ 0) = true :=
      (inhibited_iff .deposit σ 0).mpr hinh
    rw [userCall_inhibited _ _ _ _ hinhm]
    trivial

theorem deposit_inhibited_no_sstore
    (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) (hinh : slotExcess σ = inhibitor)
    {m : Machine}
    (h : runInhibitor depositInhibitor depositJumpdests (mkRunning 27 [] g σ cd v) = .ok m) :
    m.sstoreCount = 0 ∧ m.storage = σ ∧ m.pc = Deposit.revert := by
  rw [deposit_runInhibitor_inhibited σ g cd v hg hinh] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-! ## Exit inhibitor CFG -/

theorem exit_cfg_PUSH0 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests (mkRunning 26 [] g σ cd v) =
      .ok (mkRunning 27 [UInt256.ofNat 0] (g - Gbase) σ cd v) := by
  simp [cfgStep, mkRunning, exit_inh_PUSH0]
  have hlt := (inh_gas_ok hg).1
  simp [hlt, Machine.push]

theorem exit_cfg_SLOAD (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 27 [UInt256.ofNat 0] (g - Gbase) σ cd v) =
      .ok (mkRunning 28 [loadU256 σ SLOT_EXCESS]
            (g - Gbase - Gcoldsload) σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_SLOAD]
  have hlt := (inh_gas_ok hg).2.1
  simp only [hlt, Machine.setStack]
  rw [getD_slotExcess]
  rfl

theorem exit_cfg_DUP1 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 28 [exc] (g - Gbase - Gcoldsload) σ cd v) =
      .ok (mkRunning 29 [exc, exc]
            (g - Gbase - Gcoldsload - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_DUP1]
  have hlt := (inh_gas_ok hg).2.2.1
  simp only [hlt, Machine.setStack]
  rfl

theorem exit_cfg_PUSH32 (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 29 [exc, exc]
          (g - Gbase - Gcoldsload - Gverylow) σ cd v) =
      .ok (mkRunning 62 [inhibitorU256, exc, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_PUSH32]
  have hlt := (inh_gas_ok hg).2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem exit_cfg_EQ (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 62 [inhibitorU256, exc, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow) σ cd v) =
      .ok (mkRunning 63 [UInt256.eq inhibitorU256 exc, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow) σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_EQ]
  have hlt := (inh_gas_ok hg).2.2.2.2.1
  simp only [hlt, Machine.setStack]
  rfl

theorem exit_cfg_PUSH2_revert (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (cond exc : UInt256) (hg : g ≥ inhibitorGasBound) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 63 [cond, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow) σ cd v) =
      .ok (mkRunning 66 [UInt256.ofNat Exit.revert, cond, exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow)
            σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_PUSH2]
  have hlt := (inh_gas_ok hg).2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem exit_cfg_JUMPI_inhibited (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (exc : UInt256) (hg : g ≥ inhibitorGasBound)
    (heq : UInt256.eq inhibitorU256 exc = UInt256.ofNat 1) :
    cfgStep exitInhibitor exitJumpdests
        (mkRunning 66
          [UInt256.ofNat Exit.revert, UInt256.eq inhibitorU256 exc, exc]
          (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow)
          σ cd v) =
      .ok (mkRunning Exit.revert [exc]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
            σ cd v) := by
  unfold cfgStep mkRunning
  rw [exit_inh_JUMPI]
  have hlt := (inh_gas_ok hg).2.2.2.2.2.2
  rw [heq]
  simp only [hlt, ofNat_one_ne_zero, exit_revert_contains, toNat_exit_revert,
    Machine.setPcStack]
  rfl

theorem exit_runInhibitor_inhibited (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) (hinh : slotExcess σ = inhibitor) :
    runInhibitor exitInhibitor exitJumpdests (mkRunning 26 [] g σ cd v) =
      .ok (mkRunning Exit.revert [inhibitorU256]
            (g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow - Ghigh)
            σ cd v) := by
  have hexc := loadU256_inhibitor hinh
  have h0 := exit_cfg_PUSH0 σ g cd v hg
  have h1 := exit_cfg_SLOAD σ g cd v hg
  have h2 := exit_cfg_DUP1 σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h3 := exit_cfg_PUSH32 σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h4 := exit_cfg_EQ σ g cd v (loadU256 σ SLOT_EXCESS) hg
  have h5 := exit_cfg_PUSH2_revert σ g cd v
    (UInt256.eq inhibitorU256 (loadU256 σ SLOT_EXCESS))
    (loadU256 σ SLOT_EXCESS) hg
  simp [runInhibitor, h0, h1, h2, h3, h4, h5]
  rw [hexc]
  exact exit_cfg_JUMPI_inhibited σ g cd v inhibitorU256 hg (eq_one_of_eq rfl)

theorem exit_inhibited_jumpi_revert
    (σ : Storage) (_wf : WellFormed .exit σ)
    (caller : UInt256) (_huser : isUserCaller caller)
    (gas : Nat) (hgas : gas ≥ campaignGasBound)
    (_fuel : Nat) (_hfuel : fuel ≥ interpreterFuel)
    (cd : List Byte) (value : Wei)
    (hinh : slotExcess σ = inhibitor) :
    runInhibitor exitInhibitor exitJumpdests
        (mkRunning exitUserPc [] (gas - prefixGasBound) σ cd.length
          (UInt256.ofNat value)) =
      .ok (mkRunning Exit.revert [inhibitorU256]
            (gas - prefixGasBound - Gbase - Gcoldsload - Gverylow - Gverylow
              - Gverylow - Gverylow - Ghigh)
            σ cd.length (UInt256.ofNat value)) ∧
      Corresponds
        (userCall (toModel .exit σ 0) caller.toNat cd value)
        (.jumpiRevert Exit.revert) := by
  have hg : gas - prefixGasBound ≥ inhibitorGasBound := remaining_ge_inhibitor hgas
  refine ⟨?_, ?_⟩
  · simpa [exitUserPc] using
      exit_runInhibitor_inhibited σ (gas - prefixGasBound) cd.length
        (UInt256.ofNat value) hg hinh
  · have hinhm : inhibited (toModel .exit σ 0) = true :=
      (inhibited_iff .exit σ 0).mpr hinh
    rw [userCall_inhibited _ _ _ _ hinhm]
    trivial

theorem exit_inhibited_no_sstore
    (σ : Storage) (g : Nat) (cd : Nat) (v : UInt256)
    (hg : g ≥ inhibitorGasBound) (hinh : slotExcess σ = inhibitor)
    {m : Machine}
    (h : runInhibitor exitInhibitor exitJumpdests (mkRunning 26 [] g σ cd v) = .ok m) :
    m.sstoreCount = 0 ∧ m.storage = σ ∧ m.pc = Exit.revert := by
  rw [exit_runInhibitor_inhibited σ g cd v hg hinh] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-! ## Fee-quote dispatch (after `fake_expo`)

Empty calldata is decided here: `CALLDATASIZE; JUMPI @handle_input` is not
taken, then `CALLDATASIZE; JUMPI @revert` is not taken, then `CALLVALUE;
JUMPI @revert` implements Model's empty+value cases. The `fake_expo` loop
that produces `fee` is not reduced (S4 / `Ξ` gap).
-/

private theorem zero_ne_184 : UInt256.ofNat 0 ≠ UInt256.ofNat 184 := by decide
private theorem zero_ne_48 : UInt256.ofNat 0 ≠ UInt256.ofNat 48 := by decide
private theorem ofNat_32_toNat : (UInt256.ofNat 32).toNat = 32 := rfl

private theorem disp_gas_ok {g : Nat} (h : g ≥ dispatchGasBound) :
    ¬ g < Gbase ∧
    ¬ g - Gbase < Gverylow ∧
    ¬ g - Gbase - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gverylow - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow < Ghigh ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh < Gbase ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase < Gverylow ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow < Ghigh ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh
        < Gbase ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh
        - Gbase < Gverylow ∧
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh
        - Gbase - Gverylow < Ghigh := by
  simp [dispatchGasBound, Gbase, Gverylow, Ghigh] at h
  simp [Gbase, Gverylow, Ghigh]
  omega

/-- `CALLVALUE; PUSH2 @revert; JUMPI` with nonempty value. -/
theorem deposit_disp_value_jumpi
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 12 [fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh)
          σ 0 value) =
      .ok (mkRunning 13 [value, fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [deposit_disp_CALLVALUE]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem deposit_cfg_disp_PUSH_REVERT2
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 13 [value, fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase)
          σ 0 value) =
      .ok (mkRunning 16 [UInt256.ofNat Deposit.revert, value, fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [deposit_disp_PUSH_REVERT2]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem deposit_disp_JUMPI_value_nonzero
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 16 [UInt256.ofNat Deposit.revert, value, fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow)
          σ 0 value) =
      .ok (mkRunning Deposit.revert [fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow - Ghigh)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [deposit_disp_JUMPI_VALUE]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.2.2
  simp only [hlt, hv, deposit_revert_contains, toNat_deposit_revert,
    Machine.setPcStack]
  rfl

theorem deposit_disp_JUMPI_value_zero
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 16 [UInt256.ofNat Deposit.revert, UInt256.ofNat 0, fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow)
          σ 0 (UInt256.ofNat 0)) =
      .ok (mkRunning 17 [fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow - Ghigh)
            σ 0 (UInt256.ofNat 0)) := by
  unfold cfgStep mkRunning
  rw [deposit_disp_JUMPI_VALUE]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.2.2
  simp only [hlt, Machine.setStack]
  rfl

/-- After the calldata checks, nonempty `CALLVALUE` jumps to `@revert`.
Matches `userCall` empty+value≠0 (model side requires `¬inhibited`). -/
theorem deposit_empty_nonzero_value_dispatch
    (σ : Storage) (_wf : WellFormed .deposit σ)
    (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0)
    (s : Model.State) (caller : Address)
    (hinh : inhibited s = false) (hval : value.toNat ≠ 0) :
    Corresponds (userCall s caller [] value.toNat)
      (.jumpiRevert Deposit.revert) := by
  rw [userCall_empty_nonzero s caller value.toNat hinh hval]
  trivial

theorem deposit_empty_zero_value_model
    (s : Model.State) (caller : Address)
    (hinh : inhibited s = false) :
    Corresponds (userCall s caller [] 0) (.return32 (UInt256.ofNat 0)) := by
  rw [userCall_empty_zero s caller hinh]
  exact toBeBytes_length _ 32

/-- CFG: `CALLVALUE ≠ 0` at the fee-quote dispatch `JUMPI @revert`. -/
theorem deposit_cfg_empty_nonzero_from_callvalue
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 12 [fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh)
          σ 0 value)
      >>= (fun m => cfgStep depositDispatch depositJumpdests m)
      >>= (fun m => cfgStep depositDispatch depositJumpdests m) =
      .ok (mkRunning Deposit.revert [fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow - Ghigh)
            σ 0 value) := by
  have h0 := deposit_disp_value_jumpi σ g fee value hg hv
  have h1 := deposit_cfg_disp_PUSH_REVERT2 σ g fee value hg
  have h2 := deposit_disp_JUMPI_value_nonzero σ g fee value hg hv
  simp [Bind.bind, Except.bind, h0, h1, h2]

/-! ## Fee-quote `RETURN 32` stub (PC 17 of the dispatch slice) -/

private theorem ret_gas_ok {g : Nat} (h : g ≥ dispatchGasBound) :
    ¬ g < Gbase ∧
    ¬ g - Gbase < Gverylow ∧
    ¬ g - Gbase - Gverylow < Gverylow ∧
    ¬ g - Gbase - Gverylow - Gverylow < Gbase := by
  simp [dispatchGasBound, Gbase, Gverylow] at h
  simp [Gbase, Gverylow]
  omega

theorem deposit_cfg_disp_PUSH0_mstore
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 17 [fee] g σ 0 (UInt256.ofNat 0)) =
      .ok (mkRunning 18 [UInt256.ofNat 0, fee] (g - Gbase) σ 0
            (UInt256.ofNat 0)) := by
  unfold cfgStep mkRunning
  rw [deposit_disp_PUSH0]
  have hlt := (ret_gas_ok hg).1
  simp only [hlt, Machine.push]
  rfl

theorem deposit_cfg_disp_MSTORE
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        (mkRunning 18 [UInt256.ofNat 0, fee] (g - Gbase) σ 0
          (UInt256.ofNat 0)) =
      .ok { pc := 19, stack := [], gas := g - Gbase - Gverylow,
            storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
            mem0 := fee, sstoreCount := 0, halt := .running } := by
  unfold cfgStep mkRunning
  rw [deposit_disp_MSTORE]
  have hlt := (ret_gas_ok hg).2.1
  simp [hlt, Machine.mstore0]

theorem deposit_cfg_disp_PUSH_SIZE
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        { pc := 19, stack := [], gas := g - Gbase - Gverylow,
          storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
          mem0 := fee, sstoreCount := 0, halt := .running } =
      .ok { pc := 21, stack := [UInt256.ofNat 32],
            gas := g - Gbase - Gverylow - Gverylow,
            storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
            mem0 := fee, sstoreCount := 0, halt := .running } := by
  unfold cfgStep
  rw [deposit_disp_PUSH_SIZE]
  have hlt := (ret_gas_ok hg).2.2.1
  simp [hlt, Machine.push]

theorem deposit_cfg_disp_PUSH0b
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        { pc := 21, stack := [UInt256.ofNat 32],
          gas := g - Gbase - Gverylow - Gverylow,
          storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
          mem0 := fee, sstoreCount := 0, halt := .running } =
      .ok { pc := 22, stack := [UInt256.ofNat 0, UInt256.ofNat 32],
            gas := g - Gbase - Gverylow - Gverylow - Gbase,
            storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
            mem0 := fee, sstoreCount := 0, halt := .running } := by
  unfold cfgStep
  rw [deposit_disp_PUSH0b]
  have hlt := (ret_gas_ok hg).2.2.2
  simp [hlt, Machine.push]

theorem deposit_cfg_disp_RETURN
    (σ : Storage) (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep depositDispatch depositJumpdests
        { pc := 22, stack := [UInt256.ofNat 0, UInt256.ofNat 32],
          gas := g - Gbase - Gverylow - Gverylow - Gbase,
          storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
          mem0 := fee, sstoreCount := 0, halt := .running } =
      .ok { pc := 22, stack := [],
            gas := g - Gbase - Gverylow - Gverylow - Gbase,
            storage := σ, calldataSize := 0, callvalue := UInt256.ofNat 0,
            mem0 := fee, sstoreCount := 0, halt := .returned 32 } := by
  unfold cfgStep
  rw [deposit_disp_RETURN]
  have : ¬ g - Gbase - Gverylow - Gverylow - Gbase < Gzero := by
    simp [Gzero]
  simp [this, Machine.doReturn, ofNat_32_toNat]

/-- Empty calldata + value 0: `MSTORE` the fee and `RETURN` 32 bytes.
Slots are unchanged (`sstoreCount = 0`). Exact fee numeric is S4. -/
theorem deposit_cfg_return32
    (σ : Storage) (_wf : WellFormed .deposit σ)
    (g : Nat) (fee : UInt256)
    (hg : g ≥ dispatchGasBound)
    {m : Machine}
    (h : cfgStep depositDispatch depositJumpdests
          (mkRunning 17 [fee] g σ 0 (UInt256.ofNat 0))
        >>= (fun m1 => cfgStep depositDispatch depositJumpdests m1)
        >>= (fun m2 => cfgStep depositDispatch depositJumpdests m2)
        >>= (fun m3 => cfgStep depositDispatch depositJumpdests m3)
        >>= (fun m4 => cfgStep depositDispatch depositJumpdests m4) = .ok m) :
    m.halt = .returned 32 ∧ m.mem0 = fee ∧ m.sstoreCount = 0 ∧ m.storage = σ := by
  have h0 := deposit_cfg_disp_PUSH0_mstore σ g fee hg
  have h1 := deposit_cfg_disp_MSTORE σ g fee hg
  have h2 := deposit_cfg_disp_PUSH_SIZE σ g fee hg
  have h3 := deposit_cfg_disp_PUSH0b σ g fee hg
  have h4 := deposit_cfg_disp_RETURN σ g fee hg
  simp [Bind.bind, Except.bind, h0, h1, h2, h3, h4] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exit dispatch: nonempty value at the fee-quote `CALLVALUE` `JUMPI`. -/
theorem exit_disp_value_jumpi
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep exitDispatch exitJumpdests
        (mkRunning 12 [fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh)
          σ 0 value) =
      .ok (mkRunning 13 [value, fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [exit_disp_CALLVALUE]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem exit_cfg_disp_PUSH_REVERT2
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) :
    cfgStep exitDispatch exitJumpdests
        (mkRunning 13 [value, fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase)
          σ 0 value) =
      .ok (mkRunning 16 [UInt256.ofNat Exit.revert, value, fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [exit_disp_PUSH_REVERT2]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.2.1
  simp only [hlt, Machine.push]
  rfl

theorem exit_disp_JUMPI_value_nonzero
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep exitDispatch exitJumpdests
        (mkRunning 16 [UInt256.ofNat Exit.revert, value, fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
            - Ghigh - Gbase - Gverylow)
          σ 0 value) =
      .ok (mkRunning Exit.revert [fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow - Ghigh)
            σ 0 value) := by
  unfold cfgStep mkRunning
  rw [exit_disp_JUMPI_VALUE]
  have hlt := (disp_gas_ok hg).2.2.2.2.2.2.2.2.2.2
  simp only [hlt, hv, exit_revert_contains, toNat_exit_revert, Machine.setPcStack]
  rfl

theorem exit_cfg_empty_nonzero_from_callvalue
    (σ : Storage) (g : Nat) (fee value : UInt256)
    (hg : g ≥ dispatchGasBound) (hv : value ≠ UInt256.ofNat 0) :
    cfgStep exitDispatch exitJumpdests
        (mkRunning 12 [fee]
          (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow - Ghigh)
          σ 0 value)
      >>= (fun m => cfgStep exitDispatch exitJumpdests m)
      >>= (fun m => cfgStep exitDispatch exitJumpdests m) =
      .ok (mkRunning Exit.revert [fee]
            (g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase - Gverylow
              - Ghigh - Gbase - Gverylow - Ghigh)
            σ 0 value) := by
  have h0 := exit_disp_value_jumpi σ g fee value hg hv
  have h1 := exit_cfg_disp_PUSH_REVERT2 σ g fee value hg
  have h2 := exit_disp_JUMPI_value_nonzero σ g fee value hg hv
  simp [Bind.bind, Except.bind, h0, h1, h2]

end Eip8282.Audit.Correspondence
