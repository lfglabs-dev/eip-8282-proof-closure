import Eip8282.Audit.Step
import Eip8282.Audit.WellFormed
import Eip8282.Audit.Model

/-!
Init-bytecode constructors (`depositInit` / `exitInit`) on a CFG prefix.

C4: close `initial_gating` on bytes. The abstract fact is
`inhibited initialDeposit = false ∧ inhibited initialExit = true`. This
module proves the matching storage effect of the two **init** programs:

* Deposit ctor: `PUSH2 size; DUP1; PUSH1 0x0a; PUSH0; CODECOPY; PUSH0; RETURN`.
  No `SSTORE`. Copied payload starts at F1's `depositInitPreamble` (10).
* Exit ctor: `PUSH32 INHIBITOR; PUSH0; SSTORE` then the same copy/return
  with `PUSH1 0x2d` (`exitInitPreamble` = 45). First (and only) `SSTORE`
  is slot 0 `:= 2^256-1`.

`fromHex` of the full init blobs times out in the kernel. Opcode facts are
`rfl` on the first `++` chunk of `depositInitHex` and the first two chunks
of `exitInitHex` — enough for the whole preamble plus the opening `CALLER`
of the copied runtime. This is the F3 opening-chunk method, not a `Ξ`
trace. No `native_decide`. JUMPDEST tables are unused: the preamble has
no jump.
-/

namespace Eip8282.Audit.Guarantees.PControl1.Ctor

open EvmYul (UInt256 Storage)
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Model (inhibitor inhibited initialDeposit initialExit Kind)
open GasConstants

set_option maxRecDepth 20000

/-! ## Pinned ctor openings (first `++` chunks, not the full init hex) -/

/-- First `++` chunk of `depositInitHex` (64 hex chars = 32 bytes). Covers
the 10-byte preamble and `CALLER; PUSH20 SYSTEM_ADDR`. -/
def depositCtorHex : String :=
  "61027480600a5f395ff33373fffffffffffffffffffffffffffffffffffffffe"

/-- First two `++` chunks of `exitInitHex` (128 hex chars = 64 bytes).
Covers the 45-byte preamble (`PUSH32 INHIBITOR; SSTORE` then copy/return)
and the copied runtime's opening `CALLER`. -/
def exitCtorHex : String :=
  "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
    "ff5f556101ca80602d5f395ff33373ffffffffffffffffffffffffffffffffff"

def depositCtorPrefix : ByteArray := fromHex depositCtorHex
def exitCtorPrefix : ByteArray := fromHex exitCtorHex

/-- `PUSH2` length of the deposit runtime copy (`0x0274`). -/
@[simp] def depositRuntimeLen : Nat := 0x0274

/-- `PUSH2` length of the exit runtime copy (`0x01ca`). -/
@[simp] def exitRuntimeLen : Nat := 0x01ca

theorem depositCtorHex_first_chunk :
    depositCtorHex =
      "61027480600a5f395ff33373fffffffffffffffffffffffffffffffffffffffe" :=
  rfl

theorem exitCtorHex_first_two_chunks :
    exitCtorHex =
      "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
        "ff5f556101ca80602d5f395ff33373ffffffffffffffffffffffffffffffffff" :=
  rfl

theorem depositInitPreamble_eq : depositInitPreamble = 10 := rfl
theorem exitInitPreamble_eq : exitInitPreamble = 45 := rfl

/-! ## Deposit ctor opcodes

`PUSH2 0x0274; DUP1; PUSH1 0x0a; PUSH0; CODECOPY; PUSH0; RETURN`.
-/

theorem deposit_ctor_opcode_PUSH2 :
    opcodeAt depositCtorPrefix 0 =
      some (.PUSH2, some (UInt256.ofNat depositRuntimeLen, 2)) :=
  rfl

theorem deposit_ctor_opcode_DUP1 :
    opcodeAt depositCtorPrefix 3 = some (.DUP1, none) :=
  rfl

theorem deposit_ctor_opcode_PUSH1 :
    opcodeAt depositCtorPrefix 4 =
      some (.PUSH1, some (UInt256.ofNat depositInitPreamble, 1)) :=
  rfl

theorem deposit_ctor_opcode_PUSH0 :
    opcodeAt depositCtorPrefix 6 = some (.PUSH0, none) :=
  rfl

theorem deposit_ctor_opcode_CODECOPY :
    opcodeAt depositCtorPrefix 7 = some (.CODECOPY, none) :=
  rfl

theorem deposit_ctor_opcode_PUSH0_ret :
    opcodeAt depositCtorPrefix 8 = some (.PUSH0, none) :=
  rfl

theorem deposit_ctor_opcode_RETURN :
    opcodeAt depositCtorPrefix 9 = some (.RETURN, none) :=
  rfl

/-- Copied payload starts at `@code` = 10. Same opening as the runtime. -/
theorem deposit_payload_at_preamble :
    opcodeAt depositCtorPrefix depositInitPreamble = some (.CALLER, none) :=
  rfl

theorem deposit_payload_PUSH20 :
    opcodeAt depositCtorPrefix (depositInitPreamble + 1) =
      some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) :=
  rfl

/-! ## Exit ctor opcodes

`PUSH32 INHIBITOR; PUSH0; SSTORE; PUSH2 0x01ca; DUP1; PUSH1 0x2d; PUSH0;
CODECOPY; PUSH0; RETURN`.
-/

set_option maxHeartbeats 4000000 in
theorem exit_ctor_opcode_PUSH32 :
    opcodeAt exitCtorPrefix 0 =
      some (.PUSH32, some (UInt256.ofNat inhibitor, 32)) :=
  rfl

theorem exit_ctor_opcode_PUSH0_slot :
    opcodeAt exitCtorPrefix 33 = some (.PUSH0, none) :=
  rfl

theorem exit_ctor_opcode_SSTORE :
    opcodeAt exitCtorPrefix 34 = some (.SSTORE, none) :=
  rfl

theorem exit_ctor_opcode_PUSH2 :
    opcodeAt exitCtorPrefix 35 =
      some (.PUSH2, some (UInt256.ofNat exitRuntimeLen, 2)) :=
  rfl

theorem exit_ctor_opcode_DUP1 :
    opcodeAt exitCtorPrefix 38 = some (.DUP1, none) :=
  rfl

theorem exit_ctor_opcode_PUSH1 :
    opcodeAt exitCtorPrefix 39 =
      some (.PUSH1, some (UInt256.ofNat exitInitPreamble, 1)) :=
  rfl

theorem exit_ctor_opcode_PUSH0 :
    opcodeAt exitCtorPrefix 41 = some (.PUSH0, none) :=
  rfl

theorem exit_ctor_opcode_CODECOPY :
    opcodeAt exitCtorPrefix 42 = some (.CODECOPY, none) :=
  rfl

theorem exit_ctor_opcode_PUSH0_ret :
    opcodeAt exitCtorPrefix 43 = some (.PUSH0, none) :=
  rfl

theorem exit_ctor_opcode_RETURN :
    opcodeAt exitCtorPrefix 44 = some (.RETURN, none) :=
  rfl

/-- Copied payload starts at `@code` = 45. -/
theorem exit_payload_at_preamble :
    opcodeAt exitCtorPrefix exitInitPreamble = some (.CALLER, none) :=
  rfl

/-! ## Ctor CFG stepper (storage + CODECOPY offset; no jumps) -/

/-- Yellow-paper copy cost without memory expansion. Campaign gas (30M)
covers expansion; F3's prefix stepper likewise omits it. -/
def codecopyCost (size : UInt256) : Nat :=
  Gverylow + Gcopy * ((size.toNat + 31) / 32)

def depositCodecopyGas : Nat :=
  Gverylow + Gcopy * ((depositRuntimeLen + 31) / 32)

def exitCodecopyGas : Nat :=
  Gverylow + Gcopy * ((exitRuntimeLen + 31) / 32)

theorem depositCodecopyGas_eq : depositCodecopyGas = 63 := by
  simp [depositCodecopyGas, Gverylow, Gcopy]
  decide

theorem exitCodecopyGas_eq : exitCodecopyGas = 48 := by
  simp [exitCodecopyGas, Gverylow, Gcopy]
  decide

structure CtorState where
  pc : Nat
  stack : List UInt256
  gas : Nat
  storage : Storage
  codecopyOffset : UInt256 := UInt256.ofNat 0
  deriving Inhabited

structure CtorPost where
  storage : Storage
  retOffset : UInt256
  retSize : UInt256
  codecopyOffset : UInt256
  deriving Inhabited

inductive CtorOutcome where
  | running (m : CtorState)
  | returned (post : CtorPost)
  | error (e : CfgError)

/-- One ctor tick. `PUSH32` is the generic Push arm so the 32-byte immediate
is not re-decoded. `CODECOPY` does not write storage. `SSTORE` charges
`Gsset` (cold set; a conservative bound). `RETURN` halts. -/
def ctorStep (code : ByteArray) (m : CtorState) : CtorOutcome :=
  match opcodeAt code m.pc with
  | some (.Push .PUSH0, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .running { m with pc := m.pc + 1,
          stack := UInt256.ofNat 0 :: m.stack, gas := m.gas - Gbase }
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .running { m with pc := m.pc + 1 + width,
          stack := imm :: m.stack, gas := m.gas - Gverylow }
  | some (.Dup .DUP1, none) =>
      match m.stack with
      | top :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .running { m with pc := m.pc + 1,
              stack := top :: top :: rest, gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.Env .CODECOPY, none) =>
      match m.stack with
      | _dest :: offset :: size :: rest =>
          let cost := codecopyCost size
          if m.gas < cost then .error .outOfGas
          else
            .running { m with pc := m.pc + 1, stack := rest,
              gas := m.gas - cost, codecopyOffset := offset }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .SSTORE, none) =>
      match m.stack with
      | key :: value :: rest =>
          if m.gas < Gsset then .error .outOfGas
          else
            .running { m with pc := m.pc + 1, stack := rest,
              gas := m.gas - Gsset,
              storage := m.storage.insert key value }
      | _ => .error .stackUnderflow
  | some (.System .RETURN, none) =>
      match m.stack with
      | offset :: size :: _ =>
          .returned { storage := m.storage, retOffset := offset,
            retSize := size, codecopyOffset := m.codecopyOffset }
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

/-- Deposit preamble: 7 ticks through `RETURN`. -/
def runDepositCtor (gas : Nat) (σ : Storage) : CtorOutcome :=
  let m0 : CtorState := { pc := 0, stack := [], gas, storage := σ }
  match ctorStep depositCtorPrefix m0 with
  | .error e => .error e
  | .returned p => .returned p
  | .running m1 =>
    match ctorStep depositCtorPrefix m1 with
    | .error e => .error e
    | .returned p => .returned p
    | .running m2 =>
      match ctorStep depositCtorPrefix m2 with
      | .error e => .error e
      | .returned p => .returned p
      | .running m3 =>
        match ctorStep depositCtorPrefix m3 with
        | .error e => .error e
        | .returned p => .returned p
        | .running m4 =>
          match ctorStep depositCtorPrefix m4 with
          | .error e => .error e
          | .returned p => .returned p
          | .running m5 =>
            match ctorStep depositCtorPrefix m5 with
            | .error e => .error e
            | .returned p => .returned p
            | .running m6 => ctorStep depositCtorPrefix m6

/-- Exit `PUSH32; PUSH0; SSTORE` then the copy/return. -/
def runExitCtor (gas : Nat) (σ : Storage) : CtorOutcome :=
  let m0 : CtorState := { pc := 0, stack := [], gas, storage := σ }
  match ctorStep exitCtorPrefix m0 with
  | .error e => .error e
  | .returned p => .returned p
  | .running m1 =>
    match ctorStep exitCtorPrefix m1 with
    | .error e => .error e
    | .returned p => .returned p
    | .running m2 =>
      match ctorStep exitCtorPrefix m2 with
      | .error e => .error e
      | .returned p => .returned p
      | .running m3 =>
        match ctorStep exitCtorPrefix m3 with
        | .error e => .error e
        | .returned p => .returned p
        | .running m4 =>
          match ctorStep exitCtorPrefix m4 with
          | .error e => .error e
          | .returned p => .returned p
          | .running m5 =>
            match ctorStep exitCtorPrefix m5 with
            | .error e => .error e
            | .returned p => .returned p
            | .running m6 =>
              match ctorStep exitCtorPrefix m6 with
              | .error e => .error e
              | .returned p => .returned p
              | .running m7 =>
                match ctorStep exitCtorPrefix m7 with
                | .error e => .error e
                | .returned p => .returned p
                | .running m8 =>
                  match ctorStep exitCtorPrefix m8 with
                  | .error e => .error e
                  | .returned p => .returned p
                  | .running m9 => ctorStep exitCtorPrefix m9

/-- Post-image of the deposit ctor: storage is not written. -/
def depositPost (σ : Storage) : Storage := σ

/-- Post-image of the exit ctor: slot 0 holds `INHIBITOR`. -/
def exitPost (σ : Storage) : Storage :=
  σ.insert (UInt256.ofNat 0) (UInt256.ofNat inhibitor)

/-! ## Gas leftovers -/

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

private theorem deposit_gas_parts {g : Nat} (hg : g ≥ campaignGasBound) :
    ¬ g < Gverylow ∧
      ¬ g - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow < Gbase ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gbase < depositCodecopyGas ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gbase - depositCodecopyGas <
          Gbase := by
  simp [campaignGasBound, Gverylow, Gbase, depositCodecopyGas, Gcopy] at hg ⊢
  omega

private theorem exit_gas_parts {g : Nat} (hg : g ≥ campaignGasBound) :
    ¬ g < Gverylow ∧
      ¬ g - Gverylow < Gbase ∧
      ¬ g - Gverylow - Gbase < Gsset ∧
      ¬ g - Gverylow - Gbase - Gsset < Gverylow ∧
      ¬ g - Gverylow - Gbase - Gsset - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gbase - Gsset - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow <
          Gbase ∧
      ¬ g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow - Gbase <
          exitCodecopyGas ∧
      ¬ g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow - Gbase -
            exitCodecopyGas < Gbase := by
  simp [campaignGasBound, Gverylow, Gbase, Gsset, exitCodecopyGas, Gcopy]
    at hg ⊢
  omega

theorem toNat_ofNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size :=
  rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem runtimeLen_lt_size :
    depositRuntimeLen < UInt256.size ∧ exitRuntimeLen < UInt256.size := by
  simp [UInt256.size]
  decide

theorem deposit_codecopyCost :
    codecopyCost (UInt256.ofNat depositRuntimeLen) = depositCodecopyGas := by
  simp [codecopyCost, depositCodecopyGas,
    toNat_ofNat_lt runtimeLen_lt_size.1]

theorem exit_codecopyCost :
    codecopyCost (UInt256.ofNat exitRuntimeLen) = exitCodecopyGas := by
  simp [codecopyCost, exitCodecopyGas,
    toNat_ofNat_lt runtimeLen_lt_size.2]

/-! ## Deposit CFG steps -/

theorem deposit_cfg_PUSH2 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 0, stack := [], gas := g, storage := σ } =
      .running { pc := 3, stack := [UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow, storage := σ } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_PUSH2]
  simp [(deposit_gas_parts hg).1]

theorem deposit_cfg_DUP1 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 3, stack := [UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow, storage := σ } =
      .running { pc := 4,
        stack := [UInt256.ofNat depositRuntimeLen,
          UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow - Gverylow, storage := σ } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_DUP1]
  simp [(deposit_gas_parts hg).2.1]

theorem deposit_cfg_PUSH1 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 4,
          stack := [UInt256.ofNat depositRuntimeLen,
            UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow - Gverylow, storage := σ } =
      .running { pc := 6,
        stack := [UInt256.ofNat depositInitPreamble,
          UInt256.ofNat depositRuntimeLen, UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow - Gverylow - Gverylow, storage := σ } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_PUSH1]
  simp [(deposit_gas_parts hg).2.2.1]

theorem deposit_cfg_PUSH0 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 6,
          stack := [UInt256.ofNat depositInitPreamble,
            UInt256.ofNat depositRuntimeLen, UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow - Gverylow - Gverylow, storage := σ } =
      .running { pc := 7,
        stack := [UInt256.ofNat 0, UInt256.ofNat depositInitPreamble,
          UInt256.ofNat depositRuntimeLen, UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow - Gverylow - Gverylow - Gbase, storage := σ } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_PUSH0]
  simp [(deposit_gas_parts hg).2.2.2.1]

theorem deposit_cfg_CODECOPY (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 7,
          stack := [UInt256.ofNat 0, UInt256.ofNat depositInitPreamble,
            UInt256.ofNat depositRuntimeLen, UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow - Gverylow - Gverylow - Gbase, storage := σ } =
      .running { pc := 8, stack := [UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow - Gverylow - Gverylow - Gbase - depositCodecopyGas,
        storage := σ, codecopyOffset := UInt256.ofNat depositInitPreamble } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_CODECOPY]
  simp [(deposit_gas_parts hg).2.2.2.2.1, deposit_codecopyCost]

theorem deposit_cfg_PUSH0_ret (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 8, stack := [UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow - Gverylow - Gverylow - Gbase - depositCodecopyGas,
          storage := σ, codecopyOffset := UInt256.ofNat depositInitPreamble } =
      .running { pc := 9,
        stack := [UInt256.ofNat 0, UInt256.ofNat depositRuntimeLen],
        gas := g - Gverylow - Gverylow - Gverylow - Gbase - depositCodecopyGas -
          Gbase,
        storage := σ, codecopyOffset := UInt256.ofNat depositInitPreamble } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_PUSH0_ret]
  simp [(deposit_gas_parts hg).2.2.2.2.2]

theorem deposit_cfg_RETURN (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep depositCtorPrefix
        { pc := 9,
          stack := [UInt256.ofNat 0, UInt256.ofNat depositRuntimeLen],
          gas := g - Gverylow - Gverylow - Gverylow - Gbase - depositCodecopyGas -
            Gbase,
          storage := σ, codecopyOffset := UInt256.ofNat depositInitPreamble } =
      .returned { storage := σ, retOffset := UInt256.ofNat 0,
        retSize := UInt256.ofNat depositRuntimeLen,
        codecopyOffset := UInt256.ofNat depositInitPreamble } := by
  unfold ctorStep
  rw [deposit_ctor_opcode_RETURN]
  simp

/-- Deposit init does not `SSTORE`. Storage is unchanged; `CODECOPY` source
is the 10-byte `@code` prefix; `RETURN` size is the PUSH2 runtime length. -/
theorem deposit_ctor_storage_zero (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    runDepositCtor g σ =
      .returned { storage := depositPost σ, retOffset := UInt256.ofNat 0,
        retSize := UInt256.ofNat depositRuntimeLen,
        codecopyOffset := UInt256.ofNat depositInitPreamble } := by
  simp [runDepositCtor, depositPost,
    deposit_cfg_PUSH2 g σ hg,
    deposit_cfg_DUP1 g σ hg,
    deposit_cfg_PUSH1 g σ hg,
    deposit_cfg_PUSH0 g σ hg,
    deposit_cfg_CODECOPY g σ hg,
    deposit_cfg_PUSH0_ret g σ hg,
    deposit_cfg_RETURN g σ hg]

/-! ## Exit CFG steps -/

theorem exit_cfg_PUSH32 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 0, stack := [], gas := g, storage := σ } =
      .running { pc := 33, stack := [UInt256.ofNat inhibitor],
        gas := g - Gverylow, storage := σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH32]
  simp [(exit_gas_parts hg).1]

theorem exit_cfg_PUSH0_slot (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 33, stack := [UInt256.ofNat inhibitor],
          gas := g - Gverylow, storage := σ } =
      .running { pc := 34,
        stack := [UInt256.ofNat 0, UInt256.ofNat inhibitor],
        gas := g - Gverylow - Gbase, storage := σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH0_slot]
  simp [(exit_gas_parts hg).2.1]

theorem exit_cfg_SSTORE (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 34,
          stack := [UInt256.ofNat 0, UInt256.ofNat inhibitor],
          gas := g - Gverylow - Gbase, storage := σ } =
      .running { pc := 35, stack := [],
        gas := g - Gverylow - Gbase - Gsset,
        storage := exitPost σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_SSTORE]
  simp [(exit_gas_parts hg).2.2.1, exitPost]

/-- First `SSTORE` of the exit ctor is slot 0 `:= INHIBITOR`. No prior
storage write. -/
theorem exit_ctor_first_sstore (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 34, stack := [UInt256.ofNat 0, UInt256.ofNat inhibitor],
          gas := g - Gverylow - Gbase, storage := σ } =
      .running { pc := 35, stack := [],
        gas := g - Gverylow - Gbase - Gsset, storage := exitPost σ } :=
  exit_cfg_SSTORE g σ hg

theorem exit_cfg_PUSH2 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 35, stack := [],
          gas := g - Gverylow - Gbase - Gsset, storage := exitPost σ } =
      .running { pc := 38, stack := [UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow,
        storage := exitPost σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH2]
  simp [(exit_gas_parts hg).2.2.2.1]

theorem exit_cfg_DUP1 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 38, stack := [UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow,
          storage := exitPost σ } =
      .running { pc := 39,
        stack := [UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow,
        storage := exitPost σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_DUP1]
  simp [(exit_gas_parts hg).2.2.2.2.1]

theorem exit_cfg_PUSH1 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 39,
          stack := [UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow,
          storage := exitPost σ } =
      .running { pc := 41,
        stack := [UInt256.ofNat exitInitPreamble,
          UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow,
        storage := exitPost σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH1]
  simp [(exit_gas_parts hg).2.2.2.2.2.1]

theorem exit_cfg_PUSH0 (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 41,
          stack := [UInt256.ofNat exitInitPreamble,
            UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow,
          storage := exitPost σ } =
      .running { pc := 42,
        stack := [UInt256.ofNat 0, UInt256.ofNat exitInitPreamble,
          UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
          Gbase,
        storage := exitPost σ } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH0]
  simp [(exit_gas_parts hg).2.2.2.2.2.2.1]

theorem exit_cfg_CODECOPY (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 42,
          stack := [UInt256.ofNat 0, UInt256.ofNat exitInitPreamble,
            UInt256.ofNat exitRuntimeLen, UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
            Gbase,
          storage := exitPost σ } =
      .running { pc := 43, stack := [UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
          Gbase - exitCodecopyGas,
        storage := exitPost σ,
        codecopyOffset := UInt256.ofNat exitInitPreamble } := by
  unfold ctorStep
  rw [exit_ctor_opcode_CODECOPY]
  simp [(exit_gas_parts hg).2.2.2.2.2.2.2.1, exit_codecopyCost]

theorem exit_cfg_PUSH0_ret (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 43, stack := [UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
            Gbase - exitCodecopyGas,
          storage := exitPost σ,
          codecopyOffset := UInt256.ofNat exitInitPreamble } =
      .running { pc := 44,
        stack := [UInt256.ofNat 0, UInt256.ofNat exitRuntimeLen],
        gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
          Gbase - exitCodecopyGas - Gbase,
        storage := exitPost σ,
        codecopyOffset := UInt256.ofNat exitInitPreamble } := by
  unfold ctorStep
  rw [exit_ctor_opcode_PUSH0_ret]
  simp [(exit_gas_parts hg).2.2.2.2.2.2.2.2]

theorem exit_cfg_RETURN (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    ctorStep exitCtorPrefix
        { pc := 44,
          stack := [UInt256.ofNat 0, UInt256.ofNat exitRuntimeLen],
          gas := g - Gverylow - Gbase - Gsset - Gverylow - Gverylow - Gverylow -
            Gbase - exitCodecopyGas - Gbase,
          storage := exitPost σ,
          codecopyOffset := UInt256.ofNat exitInitPreamble } =
      .returned { storage := exitPost σ, retOffset := UInt256.ofNat 0,
        retSize := UInt256.ofNat exitRuntimeLen,
        codecopyOffset := UInt256.ofNat exitInitPreamble } := by
  unfold ctorStep
  rw [exit_ctor_opcode_RETURN]
  simp

/-- Exit init: first `SSTORE` is slot 0 `:= INHIBITOR`, then `CODECOPY` from
offset 45 and `RETURN` of the runtime length. No further storage write. -/
theorem exit_ctor_stores_inhibitor (g : Nat) (σ : Storage)
    (hg : g ≥ campaignGasBound) :
    runExitCtor g σ =
      .returned { storage := exitPost σ, retOffset := UInt256.ofNat 0,
        retSize := UInt256.ofNat exitRuntimeLen,
        codecopyOffset := UInt256.ofNat exitInitPreamble } := by
  simp [runExitCtor,
    exit_cfg_PUSH32 g σ hg,
    exit_cfg_PUSH0_slot g σ hg,
    exit_cfg_SSTORE g σ hg,
    exit_cfg_PUSH2 g σ hg,
    exit_cfg_DUP1 g σ hg,
    exit_cfg_PUSH1 g σ hg,
    exit_cfg_PUSH0 g σ hg,
    exit_cfg_CODECOPY g σ hg,
    exit_cfg_PUSH0_ret g σ hg,
    exit_cfg_RETURN g σ hg]

/-! ## `initial_gating` on the ctor post-images -/

theorem storage_default_eq_empty :
    (default : Storage) = (∅ : Storage) :=
  rfl

theorem slotExcess_default :
    slotExcess (default : Storage) = 0 := by
  simp [slotExcess, loadNat, loadU256, storage_default_eq_empty,
    Std.TreeMap.getD_emptyc, toNat_ofNat]
  decide

private theorem inhibitor_lt_size : inhibitor < UInt256.size := by
  simp [inhibitor, UInt256.size]
  omega

theorem slotExcess_exitPost (σ : Storage) :
    slotExcess (exitPost σ) = inhibitor := by
  simp [slotExcess, loadNat, loadU256, exitPost, Std.TreeMap.getD_insert_self,
    toNat_ofNat_lt inhibitor_lt_size]

theorem depositPost_not_inhibited :
    inhibited (toModel .deposit (depositPost default)) = false := by
  simp [depositPost, inhibited, toModel_excess, slotExcess_default, inhibitor]
  decide

theorem exitPost_inhibited :
    inhibited (toModel .exit (exitPost default)) = true := by
  simp [inhibited, toModel_excess, slotExcess_exitPost]

/-- After ctor, deposit excess is not the inhibitor and exit excess is.
Bytecode analogue of `PControl1.initial_gating`. -/
theorem initial_gating_bytes :
    inhibited (toModel .deposit (depositPost default)) = false ∧
      inhibited (toModel .exit (exitPost default)) = true :=
  ⟨depositPost_not_inhibited, exitPost_inhibited⟩

/-- Same conjunction as the abstract `initial_gating`, transported through
the ctor post-images. -/
theorem initial_gating_bytes_matches_model :
    inhibited (toModel .deposit (depositPost default)) =
        inhibited initialDeposit ∧
      inhibited (toModel .exit (exitPost default)) =
        inhibited initialExit := by
  simp [initial_gating_bytes]
  constructor <;> rfl

/-- Deployed-from-empty: the CFG post-images are the CREATE storage
the abstract constructors describe. -/
theorem ctor_posts_from_empty (g : Nat) (hg : g ≥ campaignGasBound) :
    (runDepositCtor g default =
      .returned { storage := depositPost default, retOffset := UInt256.ofNat 0,
        retSize := UInt256.ofNat depositRuntimeLen,
        codecopyOffset := UInt256.ofNat depositInitPreamble }) ∧
      (runExitCtor g default =
        .returned { storage := exitPost default, retOffset := UInt256.ofNat 0,
          retSize := UInt256.ofNat exitRuntimeLen,
          codecopyOffset := UInt256.ofNat exitInitPreamble }) :=
  ⟨deposit_ctor_storage_zero g default hg,
    exit_ctor_stores_inhibitor g default hg⟩

end Eip8282.Audit.Guarantees.PControl1.Ctor
