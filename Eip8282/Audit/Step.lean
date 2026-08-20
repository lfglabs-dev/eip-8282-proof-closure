import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import Eip8282.Audit.Jumpdests
import Eip8282.Audit.Bytecode

/-!
Opcode-at-PC, caller gate, and explicit gas for the opening
`CALLER; PUSH20 SYSTEM_ADDR; EQ; PUSH dest; JUMPI` of both runtimes.

The load-bearing gate is a CFG prefix stepper driven by `opcodeAt` of the
pinned opening bytes. It is **not** a reduction of `EvmYul.EVM.X`: `X` loops
until halt, so five instructions do not yield a PC-after-JUMPI fact without
running the rest of the program (or `native_decide` of a concrete `Ξ` image,
which this campaign forbids).

`fromHex` of the full runtime times out in the kernel (`fromHexGo` is private
and does not unfold on open terms). Opcode facts are therefore `rfl` on
`fromHex` of the first `++` chunk of each pinned hex — the same 32 bytes the
runtime image starts with. Valid-jump checks use F1's `depositJumpdests` /
`exitJumpdests` (`deposit_D_J` / `exit_D_J`), never `D_J_aux`.
-/

namespace Eip8282.Audit.Step

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open GasConstants

set_option maxRecDepth 20000

/-! ## Pinned opening bytes -/

/-- First `++` chunk of `depositRuntimeHex` (64 hex chars = 32 bytes). -/
def depositOpeningHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff"

/-- First `++` chunk of `exitRuntimeHex` (64 hex chars = 32 bytes). -/
def exitOpeningHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff"

def depositOpening : ByteArray := fromHex depositOpeningHex
def exitOpening : ByteArray := fromHex exitOpeningHex

theorem depositOpeningHex_first_chunk :
    depositOpeningHex =
      "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff" :=
  rfl

theorem exitOpeningHex_first_chunk :
    exitOpeningHex =
      "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff" :=
  rfl

/-! ## Named PCs of the opening sequence -/

/-- `EQ` of the caller gate. Same offset in both runtimes (`Jumpdests.gate_eq`). -/
@[simp] def gateEqPc : Nat := 22

@[simp] def depositPushPc : Nat := 23
@[simp] def depositJumpiPc : Nat := 26
/-- Fall-through after the deposit `JUMPI`: `PUSH0; SLOAD` of `SLOT_EXCESS`. -/
@[simp] def depositUserPc : Nat := 27

@[simp] def exitPushPc : Nat := 23
@[simp] def exitJumpiPc : Nat := 25
/-- Fall-through after the exit `JUMPI`: `PUSH0; SLOAD` of `SLOT_EXCESS`. -/
@[simp] def exitUserPc : Nat := 26

theorem depositUserPc_ne_read_requests :
    depositUserPc ≠ Deposit.read_requests := by
  decide

theorem exitUserPc_ne_read_requests :
    exitUserPc ≠ Exit.read_requests := by
  decide

theorem gateEqPc_eq : gateEqPc = gate_eq := rfl

/-! ## Opcode-at-PC (ground `decode` of the pinned opening) -/

theorem deposit_opcode_CALLER :
    opcodeAt depositOpening 0 = some (.CALLER, none) := rfl

theorem deposit_opcode_PUSH20 :
    opcodeAt depositOpening 1 =
      some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) := rfl

theorem deposit_opcode_EQ :
    opcodeAt depositOpening 22 = some (.EQ, none) := rfl

theorem deposit_opcode_PUSH2 :
    opcodeAt depositOpening 23 =
      some (.PUSH2, some (UInt256.ofNat Deposit.read_requests, 2)) := rfl

theorem deposit_opcode_JUMPI :
    opcodeAt depositOpening 26 = some (.JUMPI, none) := rfl

theorem deposit_opcode_user_PUSH0 :
    opcodeAt depositOpening 27 = some (.PUSH0, none) := rfl

theorem deposit_opcode_user_SLOAD :
    opcodeAt depositOpening 28 = some (.SLOAD, none) := rfl

theorem exit_opcode_CALLER :
    opcodeAt exitOpening 0 = some (.CALLER, none) := rfl

theorem exit_opcode_PUSH20 :
    opcodeAt exitOpening 1 =
      some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) := rfl

theorem exit_opcode_EQ :
    opcodeAt exitOpening 22 = some (.EQ, none) := rfl

theorem exit_opcode_PUSH1 :
    opcodeAt exitOpening 23 =
      some (.PUSH1, some (UInt256.ofNat Exit.read_requests, 1)) := rfl

theorem exit_opcode_JUMPI :
    opcodeAt exitOpening 25 = some (.JUMPI, none) := rfl

theorem exit_opcode_user_PUSH0 :
    opcodeAt exitOpening 26 = some (.PUSH0, none) := rfl

theorem exit_opcode_user_SLOAD :
    opcodeAt exitOpening 27 = some (.SLOAD, none) := rfl

/-! ## Caller class -/

def sysAddrU256 : UInt256 := UInt256.ofNat systemAddress

/-- `CALLER` pushes this word (`ExecutionEnv.source` as `UInt256`). -/
def callerWord (src : AccountAddress) : UInt256 := UInt256.ofNat src.val

def isSystemCaller (caller : UInt256) : Prop := caller = sysAddrU256
def isUserCaller (caller : UInt256) : Prop := caller ≠ sysAddrU256

instance (caller : UInt256) : Decidable (isSystemCaller caller) :=
  inferInstanceAs (Decidable (_ = _))

instance (caller : UInt256) : Decidable (isUserCaller caller) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem isUserCaller_iff (caller : UInt256) :
    isUserCaller caller ↔ ¬ isSystemCaller caller :=
  Iff.rfl

def isSystemAddr (src : AccountAddress) : Prop :=
  src = AccountAddress.ofNat systemAddress

def isUserAddr (src : AccountAddress) : Prop := ¬ isSystemAddr src

/-! ## Enough gas -/

/-- Yellow-paper cost of `CALLER; PUSH20; EQ; PUSH dest; JUMPI`.
`CALLER` is `Gbase`; the two pushes and `EQ` are `Gverylow`; `JUMPI` is `Ghigh`.
Memory expansion is 0 (no memory ops). PUSH1 and PUSH2 share `Gverylow`. -/
def prefixGasBound : Nat := Gbase + 3 * Gverylow + Ghigh

theorem prefixGasBound_eq : prefixGasBound = 21 := rfl

/-- Campaign-level gas hypothesis (`EvmRunner.defaultGas`). Strictly above
`prefixGasBound`. -/
def campaignGasBound : Nat := 30000000

theorem prefixGasBound_le_campaign : prefixGasBound ≤ campaignGasBound := by
  decide

theorem prefixGasBound_ge_Gbase : prefixGasBound ≥ Gbase := by decide
theorem prefixGasBound_ge_Gverylow : prefixGasBound ≥ Gverylow := by decide
theorem prefixGasBound_ge_Ghigh : prefixGasBound ≥ Ghigh := by decide

/-! ## CFG prefix stepper -/

inductive CfgError where
  | outOfGas
  | stackUnderflow
  | badJump
  | unexpectedOpcode
  deriving DecidableEq, Repr

/-- PC, stack (top at the head, same as `EVM.State.stack`), remaining gas. -/
structure CfgState where
  pc : Nat
  stack : List UInt256
  gas : Nat
  deriving Inhabited, Repr

/-- One CFG tick driven by `opcodeAt`. Gas is the schedule for this prefix. -/
def cfgStep (code : ByteArray) (caller : UInt256)
    (validJumps : Array UInt256) (m : CfgState) : Except CfgError CfgState :=
  match opcodeAt code m.pc with
  | some (.Env .CALLER, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := caller :: m.stack, gas := m.gas - Gbase }
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1 + width, stack := imm :: m.stack,
              gas := m.gas - Gverylow }
  | some (.CompBit .EQ, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.eq a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPI, none) =>
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

/-- Five ticks: `CALLER; PUSH20; EQ; PUSH dest; JUMPI`. -/
def runGatePrefix (code : ByteArray) (caller : UInt256)
    (validJumps : Array UInt256) (gas : Nat) : Except CfgError CfgState :=
  match cfgStep code caller validJumps { pc := 0, stack := [], gas } with
  | .error e => .error e
  | .ok m1 =>
    match cfgStep code caller validJumps m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStep code caller validJumps m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStep code caller validJumps m3 with
        | .error e => .error e
        | .ok m4 => cfgStep code caller validJumps m4

/-! ## Intermediate CFG steps (each carries `gas ≥ prefixGasBound`) -/

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

theorem deposit_cfg_CALLER (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep depositOpening caller validJumps { pc := 0, stack := [], gas } =
      .ok { pc := 1, stack := [caller], gas := gas - Gbase } := by
  unfold cfgStep
  rw [deposit_opcode_CALLER]
  have : ¬ gas < Gbase := not_lt_of_ge (Nat.le_trans prefixGasBound_ge_Gbase hgas)
  simp [this]

theorem deposit_cfg_PUSH20 (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep depositOpening caller validJumps
        { pc := 1, stack := [caller], gas := gas - Gbase } =
      .ok { pc := 22, stack := [sysAddrU256, caller],
            gas := gas - Gbase - Gverylow } := by
  unfold cfgStep
  rw [deposit_opcode_PUSH20]
  have hrem : gas - Gbase ≥ Gverylow := by
    have := Nat.sub_le_sub_right hgas Gbase
    -- prefixGasBound - Gbase = 3*Gverylow + Ghigh ≥ Gverylow
    simp [prefixGasBound] at this
    omega
  have : ¬ gas - Gbase < Gverylow := not_lt_of_ge hrem
  simp [this, sysAddrU256]

theorem deposit_cfg_EQ (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep depositOpening caller validJumps
        { pc := 22, stack := [sysAddrU256, caller],
          gas := gas - Gbase - Gverylow } =
      .ok { pc := 23,
            stack := [UInt256.eq sysAddrU256 caller],
            gas := gas - Gbase - Gverylow - Gverylow } := by
  unfold cfgStep
  simp only [deposit_opcode_EQ]
  have hrem : gas - Gbase - Gverylow ≥ Gverylow := by
    simp [prefixGasBound] at hgas
    omega
  have : ¬ gas - Gbase - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem deposit_cfg_PUSH2 (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep depositOpening caller validJumps
        { pc := 23, stack := [UInt256.eq sysAddrU256 caller],
          gas := gas - Gbase - Gverylow - Gverylow } =
      .ok { pc := 26,
            stack := [UInt256.ofNat Deposit.read_requests,
                      UInt256.eq sysAddrU256 caller],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStep
  simp only [deposit_opcode_PUSH2]
  have hrem : gas - Gbase - Gverylow - Gverylow ≥ Gverylow := by
    simp [prefixGasBound] at hgas
    omega
  have : ¬ gas - Gbase - Gverylow - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

private theorem remaining_ge_Ghigh {gas : Nat} (hgas : gas ≥ prefixGasBound) :
    gas - Gbase - Gverylow - Gverylow - Gverylow ≥ Ghigh := by
  simp [prefixGasBound] at hgas
  omega

theorem deposit_read_requests_contains :
    depositJumpdests.contains (UInt256.ofNat Deposit.read_requests) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Deposit.read_requests,
      mem_depositJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem exit_read_requests_contains :
    exitJumpdests.contains (UInt256.ofNat Exit.read_requests) = true := by
  refine (Array.contains_iff_exists_mem_beq).mpr ?_
  refine ⟨UInt256.ofNat Exit.read_requests,
      mem_exitJumpdests_of_mem_nats (by decide), ?_⟩
  rfl

theorem toNat_deposit_read_requests :
    (UInt256.ofNat Deposit.read_requests).toNat = Deposit.read_requests :=
  rfl

theorem toNat_exit_read_requests :
    (UInt256.ofNat Exit.read_requests).toNat = Exit.read_requests :=
  rfl

private theorem eq_one_of_eq {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem bne_one_zero :
    (UInt256.ofNat 1 != UInt256.ofNat 0) = true := by
  decide

private theorem bne_zero_zero :
    (UInt256.ofNat 0 != UInt256.ofNat 0) = false := by
  decide

theorem deposit_cfg_JUMPI (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) :
    cfgStep depositOpening caller depositJumpdests
        { pc := 26,
          stack := [UInt256.ofNat Deposit.read_requests,
                    UInt256.eq sysAddrU256 caller],
          gas := gas - Gbase - Gverylow - Gverylow - Gverylow } =
      .ok { pc := if isSystemCaller caller then Deposit.read_requests
                  else depositUserPc,
            stack := [],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStep
  simp only [deposit_opcode_JUMPI]
  have hrem : ¬ gas - Gbase - Gverylow - Gverylow - Gverylow < Ghigh :=
    not_lt_of_ge (remaining_ge_Ghigh hgas)
  by_cases hsys : isSystemCaller caller
  · rw [if_pos hsys]
    have heq : UInt256.eq sysAddrU256 caller = UInt256.ofNat 1 :=
      eq_one_of_eq (Eq.symm hsys)
    simp [hrem, heq, bne_one_zero, deposit_read_requests_contains,
          toNat_deposit_read_requests]
  · rw [if_neg hsys]
    have heq : UInt256.eq sysAddrU256 caller = UInt256.ofNat 0 :=
      eq_zero_of_ne (fun h => hsys (Eq.symm h))
    simp [hrem, heq, bne_zero_zero]

/-! ## Deposit gate -/

theorem deposit_runGatePrefix (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) :
    runGatePrefix depositOpening caller depositJumpdests gas =
      .ok { pc := if isSystemCaller caller then Deposit.read_requests
                  else depositUserPc,
            stack := [],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  simp [runGatePrefix,
        deposit_cfg_CALLER caller gas depositJumpdests hgas,
        deposit_cfg_PUSH20 caller gas depositJumpdests hgas,
        deposit_cfg_EQ caller gas depositJumpdests hgas,
        deposit_cfg_PUSH2 caller gas depositJumpdests hgas,
        deposit_cfg_JUMPI caller gas hgas]

/-- After the opening `JUMPI`, PC is `read_requests` iff the caller word is
`SYSTEM_ADDR`. Otherwise PC is the user-path `PUSH0` at `depositUserPc`.
CFG-level; not a reduction of `X`. -/
theorem deposit_caller_gate (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    (m.pc = Deposit.read_requests ↔ isSystemCaller caller) ∧
      (m.pc = depositUserPc ↔ isUserCaller caller) ∧
      m.stack = [] := by
  rw [deposit_runGatePrefix caller gas hgas] at h
  cases h
  unfold isSystemCaller isUserCaller
  by_cases hsys : caller = sysAddrU256 <;> (simp [hsys]; try decide)

theorem deposit_system_to_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (hsys : isSystemCaller caller) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    m.pc = Deposit.read_requests :=
  (deposit_caller_gate caller gas hgas h).1.mpr hsys

theorem deposit_user_to_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (huser : isUserCaller caller) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    m.pc = depositUserPc :=
  (deposit_caller_gate caller gas hgas h).2.1.mpr huser

/-- User path never begins at `read_requests`. -/
theorem deposit_user_path_not_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (huser : isUserCaller caller) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    m.pc ≠ Deposit.read_requests := by
  rw [deposit_user_to_userPc caller gas hgas huser h]
  exact depositUserPc_ne_read_requests

/-! ## Exit CFG steps -/

theorem exit_cfg_CALLER (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep exitOpening caller validJumps { pc := 0, stack := [], gas } =
      .ok { pc := 1, stack := [caller], gas := gas - Gbase } := by
  unfold cfgStep
  rw [exit_opcode_CALLER]
  have : ¬ gas < Gbase := not_lt_of_ge (Nat.le_trans prefixGasBound_ge_Gbase hgas)
  simp [this]

theorem exit_cfg_PUSH20 (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep exitOpening caller validJumps
        { pc := 1, stack := [caller], gas := gas - Gbase } =
      .ok { pc := 22, stack := [sysAddrU256, caller],
            gas := gas - Gbase - Gverylow } := by
  unfold cfgStep
  rw [exit_opcode_PUSH20]
  have hrem : gas - Gbase ≥ Gverylow := by
    simp [prefixGasBound] at hgas
    omega
  have : ¬ gas - Gbase < Gverylow := not_lt_of_ge hrem
  simp [this, sysAddrU256]

theorem exit_cfg_EQ (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep exitOpening caller validJumps
        { pc := 22, stack := [sysAddrU256, caller],
          gas := gas - Gbase - Gverylow } =
      .ok { pc := 23,
            stack := [UInt256.eq sysAddrU256 caller],
            gas := gas - Gbase - Gverylow - Gverylow } := by
  unfold cfgStep
  simp only [exit_opcode_EQ]
  have hrem : gas - Gbase - Gverylow ≥ Gverylow := by
    simp [prefixGasBound] at hgas
    omega
  have : ¬ gas - Gbase - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem exit_cfg_PUSH1 (caller : UInt256) (gas : Nat)
    (validJumps : Array UInt256) (hgas : gas ≥ prefixGasBound) :
    cfgStep exitOpening caller validJumps
        { pc := 23, stack := [UInt256.eq sysAddrU256 caller],
          gas := gas - Gbase - Gverylow - Gverylow } =
      .ok { pc := 25,
            stack := [UInt256.ofNat Exit.read_requests,
                      UInt256.eq sysAddrU256 caller],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStep
  simp only [exit_opcode_PUSH1]
  have hrem : gas - Gbase - Gverylow - Gverylow ≥ Gverylow := by
    simp [prefixGasBound] at hgas
    omega
  have : ¬ gas - Gbase - Gverylow - Gverylow < Gverylow := not_lt_of_ge hrem
  simp [this]

theorem exit_cfg_JUMPI (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) :
    cfgStep exitOpening caller exitJumpdests
        { pc := 25,
          stack := [UInt256.ofNat Exit.read_requests,
                    UInt256.eq sysAddrU256 caller],
          gas := gas - Gbase - Gverylow - Gverylow - Gverylow } =
      .ok { pc := if isSystemCaller caller then Exit.read_requests
                  else exitUserPc,
            stack := [],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStep
  simp only [exit_opcode_JUMPI]
  have hrem : ¬ gas - Gbase - Gverylow - Gverylow - Gverylow < Ghigh :=
    not_lt_of_ge (remaining_ge_Ghigh hgas)
  by_cases hsys : isSystemCaller caller
  · rw [if_pos hsys]
    have heq : UInt256.eq sysAddrU256 caller = UInt256.ofNat 1 :=
      eq_one_of_eq (Eq.symm hsys)
    simp [hrem, heq, bne_one_zero, exit_read_requests_contains,
          toNat_exit_read_requests]
  · rw [if_neg hsys]
    have heq : UInt256.eq sysAddrU256 caller = UInt256.ofNat 0 :=
      eq_zero_of_ne (fun h => hsys (Eq.symm h))
    simp [hrem, heq, bne_zero_zero]

/-! ## Exit gate -/

theorem exit_runGatePrefix (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) :
    runGatePrefix exitOpening caller exitJumpdests gas =
      .ok { pc := if isSystemCaller caller then Exit.read_requests
                  else exitUserPc,
            stack := [],
            gas := gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  simp [runGatePrefix,
        exit_cfg_CALLER caller gas exitJumpdests hgas,
        exit_cfg_PUSH20 caller gas exitJumpdests hgas,
        exit_cfg_EQ caller gas exitJumpdests hgas,
        exit_cfg_PUSH1 caller gas exitJumpdests hgas,
        exit_cfg_JUMPI caller gas hgas]

/-- After the opening `JUMPI`, PC is `read_requests` iff the caller word is
`SYSTEM_ADDR`. Otherwise PC is the user-path `PUSH0` at `exitUserPc`.
CFG-level; not a reduction of `X`. -/
theorem exit_caller_gate (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    (m.pc = Exit.read_requests ↔ isSystemCaller caller) ∧
      (m.pc = exitUserPc ↔ isUserCaller caller) ∧
      m.stack = [] := by
  rw [exit_runGatePrefix caller gas hgas] at h
  cases h
  unfold isSystemCaller isUserCaller
  by_cases hsys : caller = sysAddrU256 <;> (simp [hsys]; try decide)

theorem exit_system_to_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (hsys : isSystemCaller caller) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    m.pc = Exit.read_requests :=
  (exit_caller_gate caller gas hgas h).1.mpr hsys

theorem exit_user_to_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (huser : isUserCaller caller) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    m.pc = exitUserPc :=
  (exit_caller_gate caller gas hgas h).2.1.mpr huser

theorem exit_user_path_not_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (huser : isUserCaller caller) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    m.pc ≠ Exit.read_requests := by
  rw [exit_user_to_userPc caller gas hgas huser h]
  exact exitUserPc_ne_read_requests

/-! ## `D_J` rewrite (F1 tables; do not re-enter `D_J_aux`) -/

theorem deposit_validJumps_eq_D_J :
    depositJumpdests = D_J depositRuntime ⟨0⟩ :=
  deposit_D_J.symm

theorem exit_validJumps_eq_D_J :
    exitJumpdests = D_J exitRuntime ⟨0⟩ :=
  exit_D_J.symm

/-!
`X` gap. `EvmYul.EVM.X fuel validJumps s` decodes, runs `Z` (gas / stack /
jumpdest), then `EvmYul.step`, then recurses until `H` (STOP/RETURN/REVERT/
SELFDESTRUCT). The opening gate is five instructions; the remainder is a full
user or system path. Unfolding `X` therefore does not stop at `read_requests`
or `depositUserPc`. This module does not `native_decide` a concrete `Ξ` image.
F4 may identify `cfgStep` with one `X` iteration on this prefix, using
`deposit_validJumps_eq_D_J` so `validJumps = D_J depositRuntime ⟨0⟩`.
-/

end Eip8282.Audit.Step
