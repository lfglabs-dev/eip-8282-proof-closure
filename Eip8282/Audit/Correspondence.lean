import Eip8282.Audit.Step
import Eip8282.Audit.WellFormed
import Eip8282.Audit.EvmRunner

/-!
Model ↔ CFG correspondence for the two pinned runtimes.

F4: A-ABSTRACT-TX remains; CFG dispatch closed.

`Corresponds` relates `toModel` + `userCall` / `systemCall` to observations
that claim workers can fill from the CFG stepper or from `EvmRunner`
(success/revert, slots 0–3, return size). It does **not** assert
`EvmYul.EVM.Ξ` agreement: the interpreter still loops until halt, and this
module does not `native_decide` a concrete `Ξ` image.

What is closed: the F3 caller gate (`isSystemCaller ↔` PC `read_requests`),
F2 `inhibited_iff` / empty-queue transport, and — when the CFG prefix
reduces — the user-path inhibitor JUMPI landing on `*.revert`.
-/

namespace Eip8282.Audit.Correspondence

open EvmYul (UInt256 Storage AccountAddress)
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Model (Kind Outcome Byte Address Wei inhibitor userCall systemCall inhibited)
open GasConstants

set_option maxRecDepth 20000

/-! ## Kind-indexed runtimes and PCs -/

/-- Pinned runtime image. Not unfolded in theorems (`fromHex` of the full
hex is kernel-opaque); claim workers pass this to `EvmRunner`. -/
def runtimeCode : Kind → ByteArray
  | .deposit => depositRuntime
  | .exit => exitRuntime

/-- F3's 32-byte opening (first `++` chunk). Gate lemmas use this, not the
full runtime. -/
def openingCode : Kind → ByteArray
  | .deposit => depositOpening
  | .exit => exitOpening

def openingJumps : Kind → Array UInt256
  | .deposit => depositJumpdests
  | .exit => exitJumpdests

def readRequestsPc : Kind → Nat
  | .deposit => Deposit.read_requests
  | .exit => Exit.read_requests

def userPathPc : Kind → Nat
  | .deposit => depositUserPc
  | .exit => exitUserPc

def revertPc : Kind → Nat
  | .deposit => Deposit.revert
  | .exit => Exit.revert

def targetAddr : Kind → AccountAddress
  | .deposit => EvmRunner.depositAddr
  | .exit => EvmRunner.exitAddr

/-- Interpreter fuel used by the existing `Ξ` kill-lines. A hypothesis on
`CallHyp`, not a proved bound on `X`. -/
def campaignFuelBound : Nat := 80000

/-! ## `CallHyp` — campaign hypotheses on every `∀` -/

/-- Allowed hypotheses: packed-queue `WellFormed`, gas ≥ 30M, interpreter
fuel, and caller class (`SYSTEM_ADDR` vs not). -/
structure CallHyp (kind : Kind) (σ : Storage) where
  wellFormed : WellFormed kind σ
  gas : Nat
  gas_ge : gas ≥ campaignGasBound
  fuel : Nat
  fuel_ge : fuel ≥ campaignFuelBound
  caller : UInt256
  /-- `true` = user path (caller ≠ `SYSTEM_ADDR`). -/
  isUser : Bool
  caller_class : isUser = true ↔ isUserCaller caller

namespace CallHyp

variable {kind : Kind} {σ : Storage}

theorem gas_ge_prefix (h : CallHyp kind σ) : h.gas ≥ prefixGasBound :=
  Nat.le_trans prefixGasBound_le_campaign h.gas_ge

theorem isSystem_iff (h : CallHyp kind σ) :
    isSystemCaller h.caller ↔ h.isUser = false := by
  by_cases hu : isUserCaller h.caller
  · have his : h.isUser = true := h.caller_class.mpr hu
    constructor
    · intro hs
      exact ((isUserCaller_iff h.caller).mp hu hs).elim
    · intro hf
      simp [his] at hf
  · have his : h.isUser = false := by
      cases ht : h.isUser with
      | false => rfl
      | true => exact (hu (h.caller_class.mp ht)).elim
    constructor
    · intro; exact his
    · intro
      by_cases hs : isSystemCaller h.caller
      · exact hs
      · exact (hu ((isUserCaller_iff h.caller).mpr hs)).elim

theorem isUser_iff (h : CallHyp kind σ) :
    isUserCaller h.caller ↔ h.isUser = true :=
  h.caller_class.symm

def runnerGas (h : CallHyp kind σ) : UInt256 := UInt256.ofNat h.gas
def runnerFuel (h : CallHyp kind σ) : Nat := h.fuel

end CallHyp

/-! ## Observations and `Corresponds` -/

/-- CFG / runner observation: success/revert, slots 0–3, return size.
`gatePc` / `inhibitorDest` are CFG extras; they are not a `Ξ` PC. -/
structure Observation where
  reverted : Bool
  returnSize : Nat
  slotExcess : Nat
  slotCount : Nat
  queueHead : Nat
  queueTail : Nat
  gatePc : Nat := 0
  inhibitorDest : Option Nat := none
  deriving Repr

def returnSizeOf : Outcome → Nat
  | .success _ d => d.length
  | .revert _ => 0

/-- Dispatch into the abstract model. `user = true` is the non-system path. -/
def modelCall (kind : Kind) (user : Bool) (σ : Storage) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei) : Outcome :=
  let s := toModel kind σ balance
  if user then userCall s caller calldata value
  else systemCall s (!calldata.isEmpty)

theorem modelCall_user (kind : Kind) (σ : Storage) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei) :
    modelCall kind true σ balance caller calldata value =
      userCall (toModel kind σ balance) caller calldata value :=
  rfl

theorem modelCall_system (kind : Kind) (σ : Storage) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei) :
    modelCall kind false σ balance caller calldata value =
      systemCall (toModel kind σ balance) (!calldata.isEmpty) :=
  rfl

/--
Intended Model ↔ observation relation on the campaign hypotheses.

Closes success/revert, slots 0–3 (excess and count on success), and return
size against `userCall` / `systemCall` of `toModel`. Does **not** claim
`EvmRunner.run` (i.e. `Ξ`) equals `modelCall`. That gap is `A-ABSTRACT-TX`.
Claim workers CFG-direct revert/append/gate/excess/footprint.
-/
def Corresponds (kind : Kind) (user : Bool) (σ : Storage) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei)
    (model : Outcome) (obs : Observation) : Prop :=
  model = modelCall kind user σ balance caller calldata value ∧
    (obs.reverted = true ↔ model.isRevert = true) ∧
    obs.returnSize = returnSizeOf model ∧
    (model.isRevert = false →
      obs.slotExcess = model.state.storedExcess ∧
        obs.slotCount = model.state.count)

/-- Pre-state slots 0–3 of a well-formed image. -/
def preSlots (σ : Storage) : Nat × Nat × Nat × Nat :=
  (slotExcess σ, slotCount σ, queueHead σ, queueTail σ)

/-- Project an `EvmRunner` result. Honest about revert: post-slots are `none`
in the runner API, so this fills pre-state slots and sets `reverted`. -/
def observationOfRunner (res : EvmRunner.RunResult) (target : AccountAddress)
    (σ : Storage) (gatePc : Nat := 0) : Observation :=
  match EvmRunner.storageSlotAfter res target (UInt256.ofNat 0),
        EvmRunner.storageSlotAfter res target (UInt256.ofNat 1),
        EvmRunner.storageSlotAfter res target (UInt256.ofNat 2),
        EvmRunner.storageSlotAfter res target (UInt256.ofNat 3) with
  | some e, some c, some h, some t =>
      { reverted := EvmRunner.isRevert res
        returnSize := EvmRunner.successOutSize res
        slotExcess := e.toNat
        slotCount := c.toNat
        queueHead := h.toNat
        queueTail := t.toNat
        gatePc }
  | _, _, _, _ =>
      { reverted := EvmRunner.isRevert res
        returnSize := EvmRunner.successOutSize res
        slotExcess := slotExcess σ
        slotCount := slotCount σ
        queueHead := queueHead σ
        queueTail := queueTail σ
        gatePc }

def observationOfGate (m : CfgState) (σ : Storage)
    (inhibitorDest : Option Nat := none) : Observation :=
  { reverted := inhibitorDest.isSome
    returnSize := 0
    slotExcess := slotExcess σ
    slotCount := slotCount σ
    queueHead := queueHead σ
    queueTail := queueTail σ
    gatePc := m.pc
    inhibitorDest }

/-! ## F2 transport (re-exported so claim workers import one module) -/

theorem inhibited_iff (kind : Kind) (σ : Storage) (balance : Wei := 0) :
    inhibited (toModel kind σ balance) = true ↔ slotExcess σ = inhibitor :=
  WellFormed.inhibited_iff kind σ balance

theorem queueOf_empty_of_eq (kind : Kind) (σ : Storage)
    (h : queueHead σ = queueTail σ) :
    queueOf kind σ = [] :=
  WellFormed.queueOf_empty_of_eq kind σ h

theorem queueOf_empty (kind : Kind) {σ : Storage}
    (_wf : WellFormed kind σ) (h : queueHead σ = queueTail σ) :
    queueOf kind σ = [] :=
  queueOf_empty_of_eq kind σ h

theorem toModel_queue_empty (kind : Kind) {σ : Storage} (balance : Wei := 0)
    (h : queueHead σ = queueTail σ) :
    (toModel kind σ balance).queue = [] := by
  rw [toModel_queue, queueOf_empty_of_eq kind σ h]

theorem callHyp_queue_empty {kind : Kind} {σ : Storage}
    (_h : CallHyp kind σ) (heq : queueHead σ = queueTail σ) :
    queueOf kind σ = [] :=
  queueOf_empty_of_eq kind σ heq

theorem callHyp_inhibited_iff {kind : Kind} {σ : Storage} (balance : Wei)
    (_h : CallHyp kind σ) :
    inhibited (toModel kind σ balance) = true ↔ slotExcess σ = inhibitor :=
  inhibited_iff kind σ balance

/-- Model-side: inhibited user calls revert. Transport, not a bytecode parent. -/
theorem modelCall_user_of_inhibited (kind : Kind) (σ : Storage) (balance : Wei)
    (caller : Address) (calldata : List Byte) (value : Wei)
    (h : inhibited (toModel kind σ balance) = true) :
    modelCall kind true σ balance caller calldata value =
      Outcome.revert (toModel kind σ balance) := by
  simp [modelCall, userCall, h]

/-! ## F3 dispatch: `isSystemCaller ↔` PC `read_requests` -/

theorem caller_gate (kind : Kind) (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix (openingCode kind) caller (openingJumps kind) gas = .ok m) :
    (m.pc = readRequestsPc kind ↔ isSystemCaller caller) ∧
      (m.pc = userPathPc kind ↔ isUserCaller caller) ∧
      m.stack = [] := by
  have hpre : gas ≥ prefixGasBound := Nat.le_trans prefixGasBound_le_campaign hgas
  cases kind with
  | deposit => exact deposit_caller_gate caller gas hpre h
  | exit => exact exit_caller_gate caller gas hpre h

theorem system_iff_read_requests (kind : Kind) (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix (openingCode kind) caller (openingJumps kind) gas = .ok m) :
    isSystemCaller caller ↔ m.pc = readRequestsPc kind :=
  (caller_gate kind caller gas hgas h).1.symm

theorem user_iff_userPathPc (kind : Kind) (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix (openingCode kind) caller (openingJumps kind) gas = .ok m) :
    isUserCaller caller ↔ m.pc = userPathPc kind :=
  (caller_gate kind caller gas hgas h).2.1.symm

theorem deposit_system_iff_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    isSystemCaller caller ↔ m.pc = Deposit.read_requests :=
  system_iff_read_requests .deposit caller gas hgas h

theorem deposit_user_iff_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    isUserCaller caller ↔ m.pc = depositUserPc :=
  user_iff_userPathPc .deposit caller gas hgas h

theorem exit_system_iff_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    isSystemCaller caller ↔ m.pc = Exit.read_requests :=
  system_iff_read_requests .exit caller gas hgas h

theorem exit_user_iff_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ campaignGasBound) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    isUserCaller caller ↔ m.pc = exitUserPc :=
  user_iff_userPathPc .exit caller gas hgas h

theorem callHyp_dispatch {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    (m.pc = readRequestsPc kind ↔ h.isUser = false) ∧
      (m.pc = userPathPc kind ↔ h.isUser = true) ∧
      m.stack = [] := by
  have g := caller_gate kind h.caller h.gas h.gas_ge hrun
  constructor
  · rw [g.1, h.isSystem_iff]
  constructor
  · rw [g.2.1, h.caller_class]
  · exact g.2.2

/-! ## Opening opcodes (F3 re-export, both runtimes) -/

theorem deposit_opening_opcodes :
    opcodeAt depositOpening 0 = some (.CALLER, none) ∧
      opcodeAt depositOpening 1 =
        some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) ∧
      opcodeAt depositOpening 22 = some (.EQ, none) ∧
      opcodeAt depositOpening 23 =
        some (.PUSH2, some (UInt256.ofNat Deposit.read_requests, 2)) ∧
      opcodeAt depositOpening 26 = some (.JUMPI, none) ∧
      opcodeAt depositOpening 27 = some (.PUSH0, none) ∧
      opcodeAt depositOpening 28 = some (.SLOAD, none) :=
  ⟨deposit_opcode_CALLER, deposit_opcode_PUSH20, deposit_opcode_EQ,
    deposit_opcode_PUSH2, deposit_opcode_JUMPI,
    deposit_opcode_user_PUSH0, deposit_opcode_user_SLOAD⟩

theorem exit_opening_opcodes :
    opcodeAt exitOpening 0 = some (.CALLER, none) ∧
      opcodeAt exitOpening 1 =
        some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) ∧
      opcodeAt exitOpening 22 = some (.EQ, none) ∧
      opcodeAt exitOpening 23 =
        some (.PUSH1, some (UInt256.ofNat Exit.read_requests, 1)) ∧
      opcodeAt exitOpening 25 = some (.JUMPI, none) ∧
      opcodeAt exitOpening 26 = some (.PUSH0, none) ∧
      opcodeAt exitOpening 27 = some (.SLOAD, none) :=
  ⟨exit_opcode_CALLER, exit_opcode_PUSH20, exit_opcode_EQ,
    exit_opcode_PUSH1, exit_opcode_JUMPI,
    exit_opcode_user_PUSH0, exit_opcode_user_SLOAD⟩

/-- `DUP1` of the inhibitor check sits in F3's 32-byte opening. -/
theorem deposit_opcode_user_DUP1 :
    opcodeAt depositOpening 29 = some (.DUP1, none) :=
  rfl

theorem exit_opcode_user_DUP1 :
    opcodeAt exitOpening 28 = some (.DUP1, none) :=
  rfl

/-! ## Inhibitor-check CFG (user path after the gate)

`PUSH0; SLOAD; DUP1; PUSH32 INHIBITOR; EQ; PUSH @revert; JUMPI`.
F3's `cfgStep` does not handle `PUSH0` / `SLOAD` / `DUP1`. The longer
prefix is the first 68 (deposit) / 67 (exit) runtime bytes — still a
`fromHex` of a closed string, not the full runtime.
-/

def depositInhibitorHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff" ++
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14" ++
    "61027057"

def exitInhibitorHex : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff" ++
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1461" ++
    "01c657"

def depositInhibitorPrefix : ByteArray := fromHex depositInhibitorHex
def exitInhibitorPrefix : ByteArray := fromHex exitInhibitorHex

def inhibitorPrefix : Kind → ByteArray
  | .deposit => depositInhibitorPrefix
  | .exit => exitInhibitorPrefix

@[simp] def depositInhibitorJumpiPc : Nat := 67
@[simp] def exitInhibitorJumpiPc : Nat := 66

/-- Gate + inhibitor-check gas. `SLOAD` is charged `Gcoldsload`. -/
def inhibitorGasBound : Nat :=
  prefixGasBound + Gbase + Gcoldsload + 4 * Gverylow + Ghigh

theorem inhibitorGasBound_le_campaign : inhibitorGasBound ≤ campaignGasBound := by
  decide

theorem inhibitorGasBound_ge_prefix : prefixGasBound ≤ inhibitorGasBound := by
  decide

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

/-- Extended tick: `PUSH0` / `SLOAD` / `DUP1` plus F3's Push/EQ/JUMPI.
Handled in one match so a `PUSH32` step does not re-enter `cfgStep` and
re-decode the 32-byte immediate (that overflows the kernel recursor). -/
def cfgStepExt (code : ByteArray) (_caller : UInt256)
    (validJumps : Array UInt256) (σ : Storage) (m : CfgState) :
    Except CfgError CfgState :=
  match opcodeAt code m.pc with
  | some (.Push .PUSH0, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := UInt256.ofNat 0 :: m.stack,
              gas := m.gas - Gbase }
  | some (.StackMemFlow .SLOAD, none) =>
      match m.stack with
      | key :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok { pc := m.pc + 1,
                  stack := σ.getD key (UInt256.ofNat 0) :: rest,
                  gas := m.gas - Gcoldsload }
      | _ => .error .stackUnderflow
  | some (.Dup .DUP1, none) =>
      match m.stack with
      | top :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := top :: top :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
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

/-- Seven ticks of the user-path inhibitor check. -/
def runInhibitorCheck (code : ByteArray) (caller : UInt256)
    (validJumps : Array UInt256) (σ : Storage) (m : CfgState) :
    Except CfgError CfgState :=
  match cfgStepExt code caller validJumps σ m with
  | .error e => .error e
  | .ok m1 =>
    match cfgStepExt code caller validJumps σ m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStepExt code caller validJumps σ m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStepExt code caller validJumps σ m3 with
        | .error e => .error e
        | .ok m4 =>
          match cfgStepExt code caller validJumps σ m4 with
          | .error e => .error e
          | .ok m5 =>
            match cfgStepExt code caller validJumps σ m5 with
            | .error e => .error e
            | .ok m6 => cfgStepExt code caller validJumps σ m6

private theorem eq_one_of_eq {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem bne_one_zero :
    (UInt256.ofNat 1 != UInt256.ofNat 0) = true := by
  decide

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
    (UInt256.ofNat Deposit.revert).toNat = Deposit.revert :=
  rfl

theorem toNat_exit_revert :
    (UInt256.ofNat Exit.revert).toNat = Exit.revert :=
  rfl

theorem sload_slot0 (σ : Storage) :
    σ.getD (UInt256.ofNat 0) (UInt256.ofNat 0) = loadU256 σ 0 :=
  rfl

theorem eq_of_toNat_eq {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk va =>
    cases b with
    | mk vb =>
      simp [UInt256.toNat] at h
      exact congrArg UInt256.mk (Fin.eq_of_val_eq h)

theorem toNat_ofNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size :=
  rfl

theorem uint256_ofNat_toNat (u : UInt256) : UInt256.ofNat u.toNat = u := by
  apply eq_of_toNat_eq
  rw [toNat_ofNat]
  exact Nat.mod_eq_of_lt (show u.toNat < UInt256.size from u.val.isLt)

theorem loadU256_of_excess_eq_inhibitor {σ : Storage}
    (h : slotExcess σ = inhibitor) :
    loadU256 σ 0 = UInt256.ofNat inhibitor := by
  have : (loadU256 σ 0).toNat = inhibitor := h
  rw [← this, uint256_ofNat_toNat]

/-! ### Deposit inhibitor opcodes -/

theorem deposit_inh_opcode_PUSH0 :
    opcodeAt depositInhibitorPrefix 27 = some (.PUSH0, none) :=
  rfl

theorem deposit_inh_opcode_SLOAD :
    opcodeAt depositInhibitorPrefix 28 = some (.SLOAD, none) :=
  rfl

theorem deposit_inh_opcode_DUP1 :
    opcodeAt depositInhibitorPrefix 29 = some (.DUP1, none) :=
  rfl

set_option maxHeartbeats 4000000 in
theorem deposit_inh_opcode_PUSH32 :
    opcodeAt depositInhibitorPrefix 30 =
      some (.PUSH32, some (UInt256.ofNat inhibitor, 32)) :=
  rfl

theorem deposit_inh_opcode_EQ :
    opcodeAt depositInhibitorPrefix 63 = some (.EQ, none) :=
  rfl

theorem deposit_inh_opcode_PUSH2 :
    opcodeAt depositInhibitorPrefix 64 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) :=
  rfl

theorem deposit_inh_opcode_JUMPI :
    opcodeAt depositInhibitorPrefix 67 = some (.JUMPI, none) :=
  rfl

/-! ### Exit inhibitor opcodes -/

theorem exit_inh_opcode_PUSH0 :
    opcodeAt exitInhibitorPrefix 26 = some (.PUSH0, none) :=
  rfl

theorem exit_inh_opcode_SLOAD :
    opcodeAt exitInhibitorPrefix 27 = some (.SLOAD, none) :=
  rfl

theorem exit_inh_opcode_DUP1 :
    opcodeAt exitInhibitorPrefix 28 = some (.DUP1, none) :=
  rfl

set_option maxHeartbeats 4000000 in
theorem exit_inh_opcode_PUSH32 :
    opcodeAt exitInhibitorPrefix 29 =
      some (.PUSH32, some (UInt256.ofNat inhibitor, 32)) :=
  rfl

theorem exit_inh_opcode_EQ :
    opcodeAt exitInhibitorPrefix 62 = some (.EQ, none) :=
  rfl

theorem exit_inh_opcode_PUSH2 :
    opcodeAt exitInhibitorPrefix 63 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) :=
  rfl

theorem exit_inh_opcode_JUMPI :
    opcodeAt exitInhibitorPrefix 66 = some (.JUMPI, none) :=
  rfl

/-! ### Deposit inhibitor CFG steps -/

private theorem remaining_after_gate_ge (gas : Nat)
    (hgas : gas ≥ campaignGasBound) :
    gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh ≥
      Gbase + Gcoldsload + 4 * Gverylow + Ghigh := by
  simp [campaignGasBound, Gbase, Gverylow, Ghigh, Gcoldsload] at hgas ⊢
  omega

private theorem inh_gas_parts {g : Nat}
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    ¬ g < Gbase ∧
      ¬ g - Gbase < Gcoldsload ∧
      ¬ g - Gbase - Gcoldsload < Gverylow ∧
      ¬ g - Gbase - Gcoldsload - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow - Gverylow <
          Ghigh := by
  simp [Gbase, Gcoldsload, Gverylow, Ghigh] at hg ⊢
  omega

theorem deposit_cfg_inh_PUSH0 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 27, stack := [], gas := g } =
      .ok { pc := 28, stack := [UInt256.ofNat 0], gas := g - Gbase } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_PUSH0]
  simp [(inh_gas_parts hg).1]

theorem deposit_cfg_inh_SLOAD (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh)
    (hinh : slotExcess σ = inhibitor) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 28, stack := [UInt256.ofNat 0], gas := g - Gbase } =
      .ok { pc := 29, stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_SLOAD]
  simp [(inh_gas_parts hg).2.1, sload_slot0,
    loadU256_of_excess_eq_inhibitor hinh]

theorem deposit_cfg_inh_DUP1 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 29, stack := [UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload } =
      .ok { pc := 30,
            stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_DUP1]
  simp [(inh_gas_parts hg).2.2.1]

theorem deposit_cfg_inh_PUSH32 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 30,
          stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow } =
      .ok { pc := 63,
            stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor,
                      UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_PUSH32]
  simp [(inh_gas_parts hg).2.2.2.1]

theorem deposit_cfg_inh_EQ (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 63,
          stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor,
                    UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow } =
      .ok { pc := 64,
            stack := [UInt256.ofNat 1, UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_EQ]
  have heq : UInt256.eq (UInt256.ofNat inhibitor) (UInt256.ofNat inhibitor) =
      UInt256.ofNat 1 := eq_one_of_eq rfl
  simp [(inh_gas_parts hg).2.2.2.2.1, heq]

theorem deposit_cfg_inh_PUSH2 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 64,
          stack := [UInt256.ofNat 1, UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 67,
            stack := [UInt256.ofNat Deposit.revert, UInt256.ofNat 1,
                      UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_PUSH2]
  simp [(inh_gas_parts hg).2.2.2.2.2.1]

theorem deposit_cfg_inh_JUMPI (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt depositInhibitorPrefix caller depositJumpdests σ
        { pc := 67,
          stack := [UInt256.ofNat Deposit.revert, UInt256.ofNat 1,
                    UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                   - Gverylow } =
      .ok { pc := Deposit.revert,
            stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow - Ghigh } := by
  unfold cfgStepExt
  rw [deposit_inh_opcode_JUMPI]
  simp [(inh_gas_parts hg).2.2.2.2.2.2, bne_one_zero, deposit_revert_contains,
    toNat_deposit_revert]

theorem deposit_runInhibitorCheck (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh)
    (hinh : slotExcess σ = inhibitor) :
    runInhibitorCheck depositInhibitorPrefix caller depositJumpdests σ
        { pc := depositUserPc, stack := [], gas := g } =
      .ok { pc := Deposit.revert,
            stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow - Ghigh } := by
  simp [runInhibitorCheck, depositUserPc,
        deposit_cfg_inh_PUSH0 caller σ g hg,
        deposit_cfg_inh_SLOAD caller σ g hg hinh,
        deposit_cfg_inh_DUP1 caller σ g hg,
        deposit_cfg_inh_PUSH32 caller σ g hg,
        deposit_cfg_inh_EQ caller σ g hg,
        deposit_cfg_inh_PUSH2 caller σ g hg,
        deposit_cfg_inh_JUMPI caller σ g hg]

/-- Inhibited user path: after the F3 gate, the inhibitor JUMPI lands on
deposit `revert` (624). CFG-level; not a reduction of `X`. -/
theorem deposit_inhibited_user_to_revert (caller : UInt256) (σ : Storage)
    (gas : Nat) (hgas : gas ≥ campaignGasBound)
    (huser : isUserCaller caller) (hinh : slotExcess σ = inhibitor)
    {mGate : CfgState}
    (hGate : runGatePrefix depositOpening caller depositJumpdests gas = .ok mGate) :
    mGate.pc = depositUserPc ∧
      runInhibitorCheck depositInhibitorPrefix caller depositJumpdests σ mGate =
        .ok { pc := Deposit.revert,
              stack := [UInt256.ofNat inhibitor],
              gas := mGate.gas - Gbase - Gcoldsload - Gverylow - Gverylow
                       - Gverylow - Gverylow - Ghigh } := by
  have hpre : gas ≥ prefixGasBound := Nat.le_trans prefixGasBound_le_campaign hgas
  have hrem := remaining_after_gate_ge gas hgas
  rw [deposit_runGatePrefix caller gas hpre] at hGate
  have hnsys : ¬ isSystemCaller caller := (isUserCaller_iff caller).mp huser
  simp [hnsys] at hGate
  cases hGate
  constructor
  · rfl
  · exact deposit_runInhibitorCheck caller σ _ hrem hinh

/-! ### Exit inhibitor CFG steps -/

theorem exit_cfg_inh_PUSH0 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 26, stack := [], gas := g } =
      .ok { pc := 27, stack := [UInt256.ofNat 0], gas := g - Gbase } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_PUSH0]
  simp [(inh_gas_parts hg).1]

theorem exit_cfg_inh_SLOAD (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh)
    (hinh : slotExcess σ = inhibitor) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 27, stack := [UInt256.ofNat 0], gas := g - Gbase } =
      .ok { pc := 28, stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_SLOAD]
  simp [(inh_gas_parts hg).2.1, sload_slot0,
    loadU256_of_excess_eq_inhibitor hinh]

theorem exit_cfg_inh_DUP1 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 28, stack := [UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload } =
      .ok { pc := 29,
            stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_DUP1]
  simp [(inh_gas_parts hg).2.2.1]

theorem exit_cfg_inh_PUSH32 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 29,
          stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow } =
      .ok { pc := 62,
            stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor,
                      UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_PUSH32]
  simp [(inh_gas_parts hg).2.2.2.1]

theorem exit_cfg_inh_EQ (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 62,
          stack := [UInt256.ofNat inhibitor, UInt256.ofNat inhibitor,
                    UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow } =
      .ok { pc := 63,
            stack := [UInt256.ofNat 1, UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_EQ]
  have heq : UInt256.eq (UInt256.ofNat inhibitor) (UInt256.ofNat inhibitor) =
      UInt256.ofNat 1 := eq_one_of_eq rfl
  simp [(inh_gas_parts hg).2.2.2.2.1, heq]

theorem exit_cfg_inh_PUSH2 (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 63,
          stack := [UInt256.ofNat 1, UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 66,
            stack := [UInt256.ofNat Exit.revert, UInt256.ofNat 1,
                      UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_PUSH2]
  simp [(inh_gas_parts hg).2.2.2.2.2.1]

theorem exit_cfg_inh_JUMPI (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh) :
    cfgStepExt exitInhibitorPrefix caller exitJumpdests σ
        { pc := 66,
          stack := [UInt256.ofNat Exit.revert, UInt256.ofNat 1,
                    UInt256.ofNat inhibitor],
          gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                   - Gverylow } =
      .ok { pc := Exit.revert,
            stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow - Ghigh } := by
  unfold cfgStepExt
  rw [exit_inh_opcode_JUMPI]
  simp [(inh_gas_parts hg).2.2.2.2.2.2, bne_one_zero, exit_revert_contains,
    toNat_exit_revert]

theorem exit_runInhibitorCheck (caller : UInt256) (σ : Storage) (g : Nat)
    (hg : g ≥ Gbase + Gcoldsload + 4 * Gverylow + Ghigh)
    (hinh : slotExcess σ = inhibitor) :
    runInhibitorCheck exitInhibitorPrefix caller exitJumpdests σ
        { pc := exitUserPc, stack := [], gas := g } =
      .ok { pc := Exit.revert,
            stack := [UInt256.ofNat inhibitor],
            gas := g - Gbase - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - Gverylow - Ghigh } := by
  simp [runInhibitorCheck, exitUserPc,
        exit_cfg_inh_PUSH0 caller σ g hg,
        exit_cfg_inh_SLOAD caller σ g hg hinh,
        exit_cfg_inh_DUP1 caller σ g hg,
        exit_cfg_inh_PUSH32 caller σ g hg,
        exit_cfg_inh_EQ caller σ g hg,
        exit_cfg_inh_PUSH2 caller σ g hg,
        exit_cfg_inh_JUMPI caller σ g hg]

/-- Inhibited user path: after the F3 gate, the inhibitor JUMPI lands on
exit `revert` (454). CFG-level; not a reduction of `X`. -/
theorem exit_inhibited_user_to_revert (caller : UInt256) (σ : Storage)
    (gas : Nat) (hgas : gas ≥ campaignGasBound)
    (huser : isUserCaller caller) (hinh : slotExcess σ = inhibitor)
    {mGate : CfgState}
    (hGate : runGatePrefix exitOpening caller exitJumpdests gas = .ok mGate) :
    mGate.pc = exitUserPc ∧
      runInhibitorCheck exitInhibitorPrefix caller exitJumpdests σ mGate =
        .ok { pc := Exit.revert,
              stack := [UInt256.ofNat inhibitor],
              gas := mGate.gas - Gbase - Gcoldsload - Gverylow - Gverylow
                       - Gverylow - Gverylow - Ghigh } := by
  have hpre : gas ≥ prefixGasBound := Nat.le_trans prefixGasBound_le_campaign hgas
  have hrem := remaining_after_gate_ge gas hgas
  rw [exit_runGatePrefix caller gas hpre] at hGate
  have hnsys : ¬ isSystemCaller caller := (isUserCaller_iff caller).mp huser
  simp [hnsys] at hGate
  cases hGate
  constructor
  · rfl
  · exact exit_runInhibitorCheck caller σ _ hrem hinh

/-- Both kinds: inhibited + user → inhibitor JUMPI dest is `*.revert`. -/
theorem inhibited_user_to_revert (kind : Kind) (caller : UInt256) (σ : Storage)
    (gas : Nat) (hgas : gas ≥ campaignGasBound)
    (huser : isUserCaller caller) (hinh : slotExcess σ = inhibitor)
    {mGate m : CfgState}
    (hGate : runGatePrefix (openingCode kind) caller (openingJumps kind) gas =
      .ok mGate)
    (hInh : runInhibitorCheck (inhibitorPrefix kind) caller (openingJumps kind)
        σ mGate = .ok m) :
    mGate.pc = userPathPc kind ∧ m.pc = revertPc kind := by
  cases kind with
  | deposit =>
      have ⟨hpc, hrun⟩ :=
        deposit_inhibited_user_to_revert caller σ gas hgas huser hinh hGate
      constructor
      · exact hpc
      · dsimp [inhibitorPrefix, openingJumps] at hInh
        rw [hrun] at hInh
        cases hInh
        rfl
  | exit =>
      have ⟨hpc, hrun⟩ :=
        exit_inhibited_user_to_revert caller σ gas hgas huser hinh hGate
      constructor
      · exact hpc
      · dsimp [inhibitorPrefix, openingJumps] at hInh
        rw [hrun] at hInh
        cases hInh
        rfl

end Eip8282.Audit.Correspondence
