import Eip8282.Audit.Correspondence

/-!
P-SUBMIT-1 user-path revert: every `JUMPI @revert` sits before the first
`SSTORE` / `LOG0`.

CFG-direct `∀` (F4 left `A-ABSTRACT-TX` open). Opcode facts are `rfl` on
`fromHex` of a **user-path prefix**, not the full runtime. `fake_expo` is
not simulated: later fragments start at the post-`fake_expo` fee-dispatch
PC with the quoted word already on the stack (numeric `fake_expo` is S4).

User path = `isUserCaller`. System path is out of scope.
-/

namespace Eip8282.Audit.Guarantees.PSubmit1.Revert

open EvmYul (UInt256 Storage)
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model (Kind inhibitor)
open GasConstants

set_option maxRecDepth 20000

/-! ## Named PCs (runtime offsets; disassembly of the pinned hex) -/

/-- First user-path `SSTORE` (`SLOT_COUNT += 1` after the stake check). -/
@[simp] def depositFirstSstorePc : Nat := 213
/-- First user-path `LOG0` (after the six queue `SSTORE`s). -/
@[simp] def depositFirstLog0Pc : Nat := 276

@[simp] def exitFirstSstorePc : Nat := 173
@[simp] def exitFirstLog0Pc : Nat := 217

/-- `CALLDATASIZE` immediately after `fake_expo` cleanup. Stack: `[req_fee]`. -/
@[simp] def depositFeeDispatchPc : Nat := 136
@[simp] def exitFeeDispatchPc : Nat := 135

/-- User-path `JUMPI` PCs whose pushed destination is `Deposit.revert` (624). -/
def depositUserRevertJumpiPcs : List Nat := [67, 147, 152, 166, 190, 204]

/-- User-path `JUMPI` PCs whose pushed destination is `Exit.revert` (454). -/
def exitUserRevertJumpiPcs : List Nat := [66, 146, 151, 164]

@[simp] def depositInhibitorJumpiPc : Nat := 67
@[simp] def depositBadCdsJumpiPc : Nat := 147
@[simp] def depositValueGetterJumpiPc : Nat := 152
@[simp] def depositUnderpayJumpiPc : Nat := 166
@[simp] def depositMinAmountJumpiPc : Nat := 190
@[simp] def depositStakeJumpiPc : Nat := 204

@[simp] def exitInhibitorJumpiPc : Nat := 66
@[simp] def exitBadCdsJumpiPc : Nat := 146
@[simp] def exitValueGetterJumpiPc : Nat := 151
@[simp] def exitUnderpayJumpiPc : Nat := 164

def MIN_AMOUNT : Nat := 1000000000
def GWEI : Nat := 1000000000
def UINT64_MASK : Nat := 0xffffffffffffffff

/-! ## User-path prefixes

Each 32-byte `fromHex` matches one `++` chunk of the pinned hex. A single
`fromHex` of the concatenated string times out in the kernel; appending
closed 32-byte arrays does not.
-/

def depositChunk0 : ByteArray := fromHex "3373fffffffffffffffffffffffffffffffffffffffe1461011c575f54807fff"
def depositChunk1 : ByteArray := fromHex "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14"
def depositChunk2 : ByteArray := fromHex "6102705760015460088111605257506058565b60089003015b60119060018202"
def depositChunk3 : ByteArray := fromHex "6001905f5b5f821115607f57810190830284830290049160010191906064565b"
def depositChunk4 : ByteArray := fromHex "90939004925050503660b814609f57366102705734610270575f5260205ff35b"
def depositChunk5 : ByteArray := fromHex "8034106102705760383567ffffffffffffffff1680633b9aca00116102705763"
def depositChunk6 : ByteArray := fromHex "3b9aca0002903403106102705760015460010160015560035480600602600401"

/-- First 224 runtime bytes: every user-path revert `JUMPI` and first `SSTORE`. -/
def depositUserPrefix : ByteArray :=
  depositChunk0 ++ depositChunk1 ++ depositChunk2 ++ depositChunk3 ++
    depositChunk4 ++ depositChunk5 ++ depositChunk6

def exitChunk0 : ByteArray := fromHex "3373fffffffffffffffffffffffffffffffffffffffe1460e1575f54807fffff"
def exitChunk1 : ByteArray := fromHex "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1461"
def exitChunk2 : ByteArray := fromHex "01c65760015460028111605157506057565b60029003015b6011906001820260"
def exitChunk3 : ByteArray := fromHex "01905f5b5f821115607e57810190830284830290049160010191906063565b90"
def exitChunk4 : ByteArray := fromHex "9390049250505036603014609e57366101c657346101c6575f5260205ff35b34"
def exitChunk5 : ByteArray := fromHex "106101c657600154600101600155600354806003026004013381556001015f35"
def exitChunk6 : ByteArray := fromHex "815560010160203590553360601b5f5260305f60143760445fa0600101600355"

/-- First 224 runtime bytes: revert `JUMPI`s, first `SSTORE`, first `LOG0`. -/
def exitUserPrefix : ByteArray :=
  exitChunk0 ++ exitChunk1 ++ exitChunk2 ++ exitChunk3 ++
    exitChunk4 ++ exitChunk5 ++ exitChunk6

/-! ## Static: revert `JUMPI`s before first write -/

theorem deposit_first_sstore_lt_log0 :
    depositFirstSstorePc < depositFirstLog0Pc := by
  decide

theorem exit_first_sstore_lt_log0 :
    exitFirstSstorePc < exitFirstLog0Pc := by
  decide

theorem deposit_revert_jumpis_before_writes :
    ∀ pc, pc ∈ depositUserRevertJumpiPcs →
      pc < depositFirstSstorePc ∧ pc < depositFirstLog0Pc := by
  intro pc h
  simp [depositUserRevertJumpiPcs] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem exit_revert_jumpis_before_writes :
    ∀ pc, pc ∈ exitUserRevertJumpiPcs →
      pc < exitFirstSstorePc ∧ pc < exitFirstLog0Pc := by
  intro pc h
  simp [exitUserRevertJumpiPcs] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-! ## Opcode-at-PC (ground `decode` of the user prefix) -/

set_option maxHeartbeats 4000000

theorem deposit_opcode_jumpi_67 :
    opcodeAt depositUserPrefix 67 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_64 :
    opcodeAt depositUserPrefix 64 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_jumpi_147 :
    opcodeAt depositUserPrefix 147 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_144 :
    opcodeAt depositUserPrefix 144 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_jumpi_152 :
    opcodeAt depositUserPrefix 152 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_149 :
    opcodeAt depositUserPrefix 149 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_jumpi_166 :
    opcodeAt depositUserPrefix 166 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_163 :
    opcodeAt depositUserPrefix 163 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_jumpi_190 :
    opcodeAt depositUserPrefix 190 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_187 :
    opcodeAt depositUserPrefix 187 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_jumpi_204 :
    opcodeAt depositUserPrefix 204 = some (.JUMPI, none) := rfl

theorem deposit_opcode_push_revert_201 :
    opcodeAt depositUserPrefix 201 =
      some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) := rfl

theorem deposit_opcode_first_sstore :
    opcodeAt depositUserPrefix depositFirstSstorePc = some (.SSTORE, none) :=
  rfl

theorem deposit_opcode_cds_136 :
    opcodeAt depositUserPrefix 136 = some (.CALLDATASIZE, none) := rfl

theorem deposit_opcode_push184_137 :
    opcodeAt depositUserPrefix 137 =
      some (.PUSH1, some (UInt256.ofNat 184, 1)) := rfl

theorem deposit_opcode_eq_139 :
    opcodeAt depositUserPrefix 139 = some (.EQ, none) := rfl

theorem deposit_opcode_push_handle_140 :
    opcodeAt depositUserPrefix 140 =
      some (.PUSH1, some (UInt256.ofNat Deposit.handle_input, 1)) := rfl

theorem deposit_opcode_jumpi_142 :
    opcodeAt depositUserPrefix 142 = some (.JUMPI, none) := rfl

theorem deposit_opcode_cds_143 :
    opcodeAt depositUserPrefix 143 = some (.CALLDATASIZE, none) := rfl

theorem deposit_opcode_callvalue_148 :
    opcodeAt depositUserPrefix 148 = some (.CALLVALUE, none) := rfl

theorem deposit_opcode_jumpdest_159 :
    opcodeAt depositUserPrefix 159 = some (.JUMPDEST, none) := rfl

theorem deposit_opcode_dup1_160 :
    opcodeAt depositUserPrefix 160 = some (.DUP1, none) := rfl

theorem deposit_opcode_callvalue_161 :
    opcodeAt depositUserPrefix 161 = some (.CALLVALUE, none) := rfl

theorem deposit_opcode_lt_162 :
    opcodeAt depositUserPrefix 162 = some (.LT, none) := rfl

theorem deposit_opcode_push56_167 :
    opcodeAt depositUserPrefix 167 =
      some (.PUSH1, some (UInt256.ofNat 56, 1)) := rfl

theorem deposit_opcode_calldataload_169 :
    opcodeAt depositUserPrefix 169 = some (.CALLDATALOAD, none) := rfl

theorem deposit_opcode_push_mask_170 :
    opcodeAt depositUserPrefix 170 =
      some (.PUSH8, some (UInt256.ofNat UINT64_MASK, 8)) := rfl

theorem deposit_opcode_and_179 :
    opcodeAt depositUserPrefix 179 = some (.AND, none) := rfl

theorem deposit_opcode_dup1_180 :
    opcodeAt depositUserPrefix 180 = some (.DUP1, none) := rfl

theorem deposit_opcode_push_min_181 :
    opcodeAt depositUserPrefix 181 =
      some (.PUSH4, some (UInt256.ofNat MIN_AMOUNT, 4)) := rfl

theorem deposit_opcode_gt_186 :
    opcodeAt depositUserPrefix 186 = some (.GT, none) := rfl

theorem deposit_opcode_push_gwei_191 :
    opcodeAt depositUserPrefix 191 =
      some (.PUSH4, some (UInt256.ofNat GWEI, 4)) := rfl

theorem deposit_opcode_mul_196 :
    opcodeAt depositUserPrefix 196 = some (.MUL, none) := rfl

theorem deposit_opcode_swap1_197 :
    opcodeAt depositUserPrefix 197 = some (.SWAP1, none) := rfl

theorem deposit_opcode_callvalue_198 :
    opcodeAt depositUserPrefix 198 = some (.CALLVALUE, none) := rfl

theorem deposit_opcode_sub_199 :
    opcodeAt depositUserPrefix 199 = some (.SUB, none) := rfl

theorem deposit_opcode_lt_200 :
    opcodeAt depositUserPrefix 200 = some (.LT, none) := rfl

theorem exit_opcode_jumpi_66 :
    opcodeAt exitUserPrefix 66 = some (.JUMPI, none) := rfl

theorem exit_opcode_push_revert_63 :
    opcodeAt exitUserPrefix 63 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_opcode_jumpi_146 :
    opcodeAt exitUserPrefix 146 = some (.JUMPI, none) := rfl

theorem exit_opcode_push_revert_143 :
    opcodeAt exitUserPrefix 143 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_opcode_jumpi_151 :
    opcodeAt exitUserPrefix 151 = some (.JUMPI, none) := rfl

theorem exit_opcode_push_revert_148 :
    opcodeAt exitUserPrefix 148 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_opcode_jumpi_164 :
    opcodeAt exitUserPrefix 164 = some (.JUMPI, none) := rfl

theorem exit_opcode_push_revert_161 :
    opcodeAt exitUserPrefix 161 =
      some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) := rfl

theorem exit_opcode_first_sstore :
    opcodeAt exitUserPrefix exitFirstSstorePc = some (.SSTORE, none) :=
  rfl

theorem exit_opcode_first_log0 :
    opcodeAt exitUserPrefix exitFirstLog0Pc = some (.LOG0, none) :=
  rfl

theorem exit_opcode_cds_135 :
    opcodeAt exitUserPrefix 135 = some (.CALLDATASIZE, none) := rfl

theorem exit_opcode_push48_136 :
    opcodeAt exitUserPrefix 136 =
      some (.PUSH1, some (UInt256.ofNat 48, 1)) := rfl

theorem exit_opcode_eq_138 :
    opcodeAt exitUserPrefix 138 = some (.EQ, none) := rfl

theorem exit_opcode_push_handle_139 :
    opcodeAt exitUserPrefix 139 =
      some (.PUSH1, some (UInt256.ofNat Exit.handle_input, 1)) := rfl

theorem exit_opcode_jumpi_141 :
    opcodeAt exitUserPrefix 141 = some (.JUMPI, none) := rfl

theorem exit_opcode_cds_142 :
    opcodeAt exitUserPrefix 142 = some (.CALLDATASIZE, none) := rfl

theorem exit_opcode_callvalue_147 :
    opcodeAt exitUserPrefix 147 = some (.CALLVALUE, none) := rfl

theorem exit_opcode_jumpdest_158 :
    opcodeAt exitUserPrefix 158 = some (.JUMPDEST, none) := rfl

theorem exit_opcode_callvalue_159 :
    opcodeAt exitUserPrefix 159 = some (.CALLVALUE, none) := rfl

theorem exit_opcode_lt_160 :
    opcodeAt exitUserPrefix 160 = some (.LT, none) := rfl

/-! ## Every listed `JUMPI` really is `JUMPI`, dest really is `*.revert` -/

theorem deposit_user_revert_jumpi_opcode {pc : Nat}
    (h : pc ∈ depositUserRevertJumpiPcs) :
    opcodeAt depositUserPrefix pc = some (.JUMPI, none) := by
  simp [depositUserRevertJumpiPcs] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact deposit_opcode_jumpi_67
  · exact deposit_opcode_jumpi_147
  · exact deposit_opcode_jumpi_152
  · exact deposit_opcode_jumpi_166
  · exact deposit_opcode_jumpi_190
  · exact deposit_opcode_jumpi_204

theorem exit_user_revert_jumpi_opcode {pc : Nat}
    (h : pc ∈ exitUserRevertJumpiPcs) :
    opcodeAt exitUserPrefix pc = some (.JUMPI, none) := by
  simp [exitUserRevertJumpiPcs] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact exit_opcode_jumpi_66
  · exact exit_opcode_jumpi_146
  · exact exit_opcode_jumpi_151
  · exact exit_opcode_jumpi_164

/-- Combined static claim: each user-path revert `JUMPI` is a `JUMPI`
whose dest-push is `Deposit.revert`, and it occurs before the first write. -/
theorem deposit_every_user_revert_jumpi_before_writes :
    (∀ pc, pc ∈ depositUserRevertJumpiPcs →
      opcodeAt depositUserPrefix pc = some (.JUMPI, none) ∧
        pc < depositFirstSstorePc ∧ pc < depositFirstLog0Pc) ∧
      opcodeAt depositUserPrefix depositFirstSstorePc = some (.SSTORE, none) ∧
      opcodeAt depositUserPrefix 64 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) ∧
      opcodeAt depositUserPrefix 144 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) ∧
      opcodeAt depositUserPrefix 149 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) ∧
      opcodeAt depositUserPrefix 163 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) ∧
      opcodeAt depositUserPrefix 187 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) ∧
      opcodeAt depositUserPrefix 201 =
        some (.PUSH2, some (UInt256.ofNat Deposit.revert, 2)) :=
  ⟨fun _ h =>
      ⟨deposit_user_revert_jumpi_opcode h,
        deposit_revert_jumpis_before_writes _ h⟩,
    deposit_opcode_first_sstore,
    deposit_opcode_push_revert_64, deposit_opcode_push_revert_144,
    deposit_opcode_push_revert_149, deposit_opcode_push_revert_163,
    deposit_opcode_push_revert_187, deposit_opcode_push_revert_201⟩

theorem exit_every_user_revert_jumpi_before_writes :
    (∀ pc, pc ∈ exitUserRevertJumpiPcs →
      opcodeAt exitUserPrefix pc = some (.JUMPI, none) ∧
        pc < exitFirstSstorePc ∧ pc < exitFirstLog0Pc) ∧
      opcodeAt exitUserPrefix exitFirstSstorePc = some (.SSTORE, none) ∧
      opcodeAt exitUserPrefix exitFirstLog0Pc = some (.LOG0, none) ∧
      opcodeAt exitUserPrefix 63 =
        some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) ∧
      opcodeAt exitUserPrefix 143 =
        some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) ∧
      opcodeAt exitUserPrefix 148 =
        some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) ∧
      opcodeAt exitUserPrefix 161 =
        some (.PUSH2, some (UInt256.ofNat Exit.revert, 2)) :=
  ⟨fun _ h =>
      ⟨exit_user_revert_jumpi_opcode h, exit_revert_jumpis_before_writes _ h⟩,
    exit_opcode_first_sstore, exit_opcode_first_log0,
    exit_opcode_push_revert_63, exit_opcode_push_revert_143,
    exit_opcode_push_revert_148, exit_opcode_push_revert_161⟩

/-! ## Tx env and user-path CFG tick

`fake_expo` is skipped: fragments below start at fee-dispatch / `handle_input`
with the quoted word already on the stack. `CALLDATALOAD` is only needed at
offset 56 (deposit amount).
-/

structure TxEnv where
  calldatasize : UInt256
  callvalue : UInt256
  word56 : UInt256 := UInt256.ofNat 0

/-- Enough gas for any revert fragment below (≪ 30M campaign bound). -/
def fragmentGas : Nat := 200

theorem fragmentGas_le_campaign : fragmentGas ≤ campaignGasBound := by
  decide

theorem fragmentGas_ge_Gbase : fragmentGas ≥ Gbase := by decide
theorem fragmentGas_ge_Gverylow : fragmentGas ≥ Gverylow := by decide
theorem fragmentGas_ge_Ghigh : fragmentGas ≥ Ghigh := by decide
theorem fragmentGas_ge_Glow : fragmentGas ≥ Glow := by decide
theorem fragmentGas_ge_Gjumpdest : fragmentGas ≥ Gjumpdest := by decide

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

/-- One user-path tick. `JUMPI` uses `≠ 0` (Prop) so `∀` calldata/value
does not need `BEq` on open `UInt256` terms. -/
def cfgStepUser (code : ByteArray) (env : TxEnv)
    (validJumps : Array UInt256) (m : CfgState) : Except CfgError CfgState :=
  match opcodeAt code m.pc with
  | some (.Push .PUSH0, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := UInt256.ofNat 0 :: m.stack,
              gas := m.gas - Gbase }
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1 + width, stack := imm :: m.stack,
              gas := m.gas - Gverylow }
  | some (.Env .CALLDATASIZE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := env.calldatasize :: m.stack,
              gas := m.gas - Gbase }
  | some (.Env .CALLVALUE, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := env.callvalue :: m.stack,
              gas := m.gas - Gbase }
  | some (.Env .CALLDATALOAD, none) =>
      match m.stack with
      | off :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            let word :=
              if off = UInt256.ofNat 56 then env.word56
              else UInt256.ofNat 0
            .ok { pc := m.pc + 1, stack := word :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.CompBit .EQ, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.eq a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.CompBit .LT, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.lt a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.CompBit .GT, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.gt a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.CompBit .AND, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.land a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.StopArith .MUL, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Glow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.mul a b :: rest,
                  gas := m.gas - Glow }
      | _ => .error .stackUnderflow
  | some (.StopArith .SUB, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := UInt256.sub a b :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.Dup .DUP1, none) =>
      match m.stack with
      | top :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := top :: top :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.Exchange .SWAP1, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := b :: a :: rest,
                  gas := m.gas - Gverylow }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPDEST, none) =>
      if m.gas < Gjumpdest then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := m.stack, gas := m.gas - Gjumpdest }
  | some (.StackMemFlow .JUMPI, none) =>
      match m.stack with
      | dest :: cond :: rest =>
          if m.gas < Ghigh then .error .outOfGas
          else if cond ≠ UInt256.ofNat 0 then
            if validJumps.contains dest then
              .ok { pc := dest.toNat, stack := rest, gas := m.gas - Ghigh }
            else
              .error .badJump
          else
            .ok { pc := m.pc + 1, stack := rest, gas := m.gas - Ghigh }
      | _ => .error .stackUnderflow
  | _ => .error .unexpectedOpcode

/-- `n` ticks of `cfgStepUser`. Composition lemmas unfold this rather than
using `Except.bind` (`simp` does not chain open `do` notation). -/
def runSteps : Nat → ByteArray → TxEnv → Array UInt256 → CfgState →
    Except CfgError CfgState
  | 0, _, _, _, m => .ok m
  | n + 1, code, env, jumps, m =>
      match cfgStepUser code env jumps m with
      | .error e => .error e
      | .ok m' => runSteps n code env jumps m'

theorem runSteps_succ_ok {n : Nat} {code : ByteArray} {env : TxEnv}
    {jumps : Array UInt256} {m m' : CfgState}
    (h : cfgStepUser code env jumps m = .ok m') :
    runSteps (n + 1) code env jumps m = runSteps n code env jumps m' := by
  simp [runSteps, h]

private theorem eq_one_of_eq {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

private theorem lt_one_of_lt {a b : UInt256} (h : a < b) :
    UInt256.lt a b = UInt256.ofNat 1 := by
  simp [UInt256.lt, UInt256.fromBool, Bool.toUInt256, h]

private theorem gt_one_of_gt {a b : UInt256} (h : a > b) :
    UInt256.gt a b = UInt256.ofNat 1 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

private theorem ne_zero_of_one :
    UInt256.ofNat 1 ≠ UInt256.ofNat 0 := by
  decide

/-! ### Shared remaining-gas facts for the fee-dispatch fragment (8 ticks) -/

private theorem fee_gas_parts {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g < Gbase ∧
      ¬ g - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow < Ghigh ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh < Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase <
          Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase -
          Gverylow < Ghigh := by
  simp [fragmentGas, Gbase, Gverylow, Ghigh] at hg ⊢
  omega

/-! ## 1. Inhibitor → `*.revert`, no write before the `JUMPI`

Reuses F4 `deposit_inhibited_user_to_revert` / `exit_inhibited_user_to_revert`.
The `JUMPI` itself is PC 67 / 66, before first `SSTORE`.
-/

theorem deposit_inhibitor_reverts_before_writes
    {σ : Storage} (h : CallHyp .deposit σ)
    (hU : h.isUser = true) (hI : slotExcess σ = inhibitor)
    {mGate : CfgState}
    (hGate : runGatePrefix depositOpening h.caller depositJumpdests h.gas =
      .ok mGate) :
    mGate.pc = depositUserPc ∧
      runInhibitorCheck depositInhibitorPrefix h.caller depositJumpdests σ
          mGate =
        .ok { pc := Deposit.revert,
              stack := [UInt256.ofNat inhibitor],
              gas := mGate.gas - Gbase - Gcoldsload - Gverylow - Gverylow
                       - Gverylow - Gverylow - Ghigh } ∧
      depositInhibitorJumpiPc < depositFirstSstorePc ∧
      depositInhibitorJumpiPc < depositFirstLog0Pc := by
  have huser : isUserCaller h.caller := h.caller_class.mp hU
  have ⟨hpc, hrun⟩ :=
    deposit_inhibited_user_to_revert h.caller σ h.gas h.gas_ge huser hI hGate
  exact ⟨hpc, hrun, by decide, by decide⟩

theorem exit_inhibitor_reverts_before_writes
    {σ : Storage} (h : CallHyp .exit σ)
    (hU : h.isUser = true) (hI : slotExcess σ = inhibitor)
    {mGate : CfgState}
    (hGate : runGatePrefix exitOpening h.caller exitJumpdests h.gas =
      .ok mGate) :
    mGate.pc = exitUserPc ∧
      runInhibitorCheck exitInhibitorPrefix h.caller exitJumpdests σ mGate =
        .ok { pc := Exit.revert,
              stack := [UInt256.ofNat inhibitor],
              gas := mGate.gas - Gbase - Gcoldsload - Gverylow - Gverylow
                       - Gverylow - Gverylow - Ghigh } ∧
      exitInhibitorJumpiPc < exitFirstSstorePc ∧
      exitInhibitorJumpiPc < exitFirstLog0Pc := by
  have huser : isUserCaller h.caller := h.caller_class.mp hU
  have ⟨hpc, hrun⟩ :=
    exit_inhibited_user_to_revert h.caller σ h.gas h.gas_ge huser hI hGate
  exact ⟨hpc, hrun, by decide, by decide⟩

/-- Kind-indexed inhibitor: user + `SLOT_EXCESS = INHIBITOR` → revert dest,
and that `JUMPI` is before the first write. -/
theorem inhibitor_reverts_before_writes
    (kind : Kind) {σ : Storage} (h : CallHyp kind σ)
    (hU : h.isUser = true) (hI : slotExcess σ = inhibitor)
    {mGate m : CfgState}
    (hGate : runGatePrefix (openingCode kind) h.caller (openingJumps kind)
        h.gas = .ok mGate)
    (hInh : runInhibitorCheck (inhibitorPrefix kind) h.caller
        (openingJumps kind) σ mGate = .ok m) :
    mGate.pc = userPathPc kind ∧ m.pc = revertPc kind ∧
      depositInhibitorJumpiPc < depositFirstSstorePc ∧
      exitInhibitorJumpiPc < exitFirstSstorePc := by
  have ⟨hpc, hrev⟩ :=
    inhibited_user_to_revert kind h.caller σ h.gas h.gas_ge
      (h.caller_class.mp hU) hI hGate hInh
  exact ⟨hpc, hrev, by decide, by decide⟩

/-! ## Fee-dispatch CFG (post-`fake_expo`, stack `[quotedFee]`) -/

section QuotedFee
variable (quotedFee : UInt256)

theorem deposit_cfg_cds_136 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 136, stack := [quotedFee], gas := g } =
      .ok { pc := 137, stack := [env.calldatasize, quotedFee],
            gas := g - Gbase } := by
  unfold cfgStepUser
  rw [deposit_opcode_cds_136]
  simp [(fee_gas_parts hg).1]

theorem deposit_cfg_push184 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 137, stack := [env.calldatasize, quotedFee],
          gas := g - Gbase } =
      .ok { pc := 139,
            stack := [UInt256.ofNat 184, env.calldatasize, quotedFee],
            gas := g - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push184_137]
  simp [(fee_gas_parts hg).2.1]

theorem deposit_cfg_eq_139 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 139,
          stack := [UInt256.ofNat 184, env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow } =
      .ok { pc := 140,
            stack := [UInt256.eq (UInt256.ofNat 184) env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_eq_139]
  simp [(fee_gas_parts hg).2.2.1]

theorem deposit_cfg_push_handle (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 140,
          stack := [UInt256.eq (UInt256.ofNat 184) env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow } =
      .ok { pc := 142,
            stack := [UInt256.ofNat Deposit.handle_input,
                      UInt256.eq (UInt256.ofNat 184) env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_handle_140]
  simp [(fee_gas_parts hg).2.2.2.1]

theorem deposit_cfg_jumpi_not_handle (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas)
    (hne : env.calldatasize ≠ UInt256.ofNat 184) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 142,
          stack := [UInt256.ofNat Deposit.handle_input,
                    UInt256.eq (UInt256.ofNat 184) env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 143, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_142]
  have heq : UInt256.eq (UInt256.ofNat 184) env.calldatasize =
      UInt256.ofNat 0 := eq_zero_of_ne (Ne.symm hne)
  simp [(fee_gas_parts hg).2.2.2.2.1, heq]

theorem deposit_cfg_cds_143 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 143, stack := [quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } =
      .ok { pc := 144, stack := [env.calldatasize, quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase } := by
  unfold cfgStepUser
  rw [deposit_opcode_cds_143]
  simp [(fee_gas_parts hg).2.2.2.2.2.1]

theorem deposit_cfg_push_revert_144 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 144, stack := [env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase } =
      .ok { pc := 147,
            stack := [UInt256.ofNat Deposit.revert, env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_revert_144]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.1]

theorem deposit_cfg_jumpi_bad_cds (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hne0 : env.calldatasize ≠ UInt256.ofNat 0) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 147,
          stack := [UInt256.ofNat Deposit.revert, env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_147]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.2, hne0, deposit_revert_contains,
    toNat_deposit_revert]

/-- `calldatasize` not 0 and not 184 → `JUMPI @revert` at 147, before writes.
`quotedFee` is the stack word after `fake_expo` (S4 owns its numeric value). -/
theorem deposit_bad_calldatasize_reverts_before_writes
    {σ : Storage} (_h : CallHyp .deposit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hbad : env.calldatasize ≠ UInt256.ofNat 0 ∧
      env.calldatasize ≠ UInt256.ofNat 184) :
    runSteps 8 depositUserPrefix env depositJumpdests
        { pc := 136, stack := [quotedFee], gas := g } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } ∧
      depositBadCdsJumpiPc < depositFirstSstorePc ∧
      depositBadCdsJumpiPc < depositFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (deposit_cfg_cds_136 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push184 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_eq_139 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_handle quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_not_handle quotedFee env g hg hbad.2)]
    rw [runSteps_succ_ok (deposit_cfg_cds_143 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_144 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_bad_cds quotedFee env g hg hbad.1)]
    rfl
  · exact ⟨by decide, by decide⟩

/-! ### Getter (`calldatasize = 0`) + `value ≠ 0` -/

theorem deposit_cfg_jumpi_cds_zero (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (h0 : env.calldatasize = UInt256.ofNat 0) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 147,
          stack := [UInt256.ofNat Deposit.revert, env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow } =
      .ok { pc := 148, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_147]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.2, h0]

private theorem getter_gas_tail {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase -
          Gverylow - Ghigh < Gbase ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase -
          Gverylow - Ghigh - Gbase < Gverylow ∧
      ¬ g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh - Gbase -
          Gverylow - Ghigh - Gbase - Gverylow < Ghigh := by
  simp [fragmentGas, Gbase, Gverylow, Ghigh] at hg ⊢
  omega

theorem deposit_cfg_callvalue_148 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 148, stack := [quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh } =
      .ok { pc := 149, stack := [env.callvalue, quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase } := by
  unfold cfgStepUser
  rw [deposit_opcode_callvalue_148]
  simp [(getter_gas_tail hg).1]

theorem deposit_cfg_push_revert_149 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 149, stack := [env.callvalue, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh - Gbase } =
      .ok { pc := 152,
            stack := [UInt256.ofNat Deposit.revert, env.callvalue,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_revert_149]
  simp [(getter_gas_tail hg).2.1]

theorem deposit_cfg_jumpi_value_getter (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hv : env.callvalue ≠ UInt256.ofNat 0) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 152,
          stack := [UInt256.ofNat Deposit.revert, env.callvalue,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh - Gbase - Gverylow } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow
                     - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_152]
  simp [(getter_gas_tail hg).2.2, hv, deposit_revert_contains,
    toNat_deposit_revert]

/-- Empty calldata and `value ≠ 0` → revert `JUMPI` at 152, before writes. -/
theorem deposit_value_on_getter_reverts_before_writes
    {σ : Storage} (_h : CallHyp .deposit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (h0 : env.calldatasize = UInt256.ofNat 0)
    (hv : env.callvalue ≠ UInt256.ofNat 0) :
    runSteps 11 depositUserPrefix env depositJumpdests
        { pc := 136, stack := [quotedFee], gas := g } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow
                     - Ghigh } ∧
      depositValueGetterJumpiPc < depositFirstSstorePc ∧
      depositValueGetterJumpiPc < depositFirstLog0Pc := by
  have hne184 : env.calldatasize ≠ UInt256.ofNat 184 := by
    rw [h0]; decide
  constructor
  · rw [runSteps_succ_ok (deposit_cfg_cds_136 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push184 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_eq_139 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_handle quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_not_handle quotedFee env g hg hne184)]
    rw [runSteps_succ_ok (deposit_cfg_cds_143 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_144 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_cds_zero quotedFee env g hg h0)]
    rw [runSteps_succ_ok (deposit_cfg_callvalue_148 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_149 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_value_getter quotedFee env g hg hv)]
    rfl
  · exact ⟨by decide, by decide⟩

/-! ## Exit fee-dispatch (same shape; input size 48) -/

theorem exit_cfg_cds_135 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 135, stack := [quotedFee], gas := g } =
      .ok { pc := 136, stack := [env.calldatasize, quotedFee],
            gas := g - Gbase } := by
  unfold cfgStepUser
  rw [exit_opcode_cds_135]
  simp [(fee_gas_parts hg).1]

theorem exit_cfg_push48 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 136, stack := [env.calldatasize, quotedFee],
          gas := g - Gbase } =
      .ok { pc := 138,
            stack := [UInt256.ofNat 48, env.calldatasize, quotedFee],
            gas := g - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_push48_136]
  simp [(fee_gas_parts hg).2.1]

theorem exit_cfg_eq_138 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 138,
          stack := [UInt256.ofNat 48, env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow } =
      .ok { pc := 139,
            stack := [UInt256.eq (UInt256.ofNat 48) env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_eq_138]
  simp [(fee_gas_parts hg).2.2.1]

theorem exit_cfg_push_handle (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 139,
          stack := [UInt256.eq (UInt256.ofNat 48) env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow } =
      .ok { pc := 141,
            stack := [UInt256.ofNat Exit.handle_input,
                      UInt256.eq (UInt256.ofNat 48) env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_push_handle_139]
  simp [(fee_gas_parts hg).2.2.2.1]

theorem exit_cfg_jumpi_not_handle (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hne : env.calldatasize ≠ UInt256.ofNat 48) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 141,
          stack := [UInt256.ofNat Exit.handle_input,
                    UInt256.eq (UInt256.ofNat 48) env.calldatasize,
                    quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 142, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpi_141]
  have heq : UInt256.eq (UInt256.ofNat 48) env.calldatasize =
      UInt256.ofNat 0 := eq_zero_of_ne (Ne.symm hne)
  simp [(fee_gas_parts hg).2.2.2.2.1, heq]

theorem exit_cfg_cds_142 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 142, stack := [quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } =
      .ok { pc := 143, stack := [env.calldatasize, quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase } := by
  unfold cfgStepUser
  rw [exit_opcode_cds_142]
  simp [(fee_gas_parts hg).2.2.2.2.2.1]

theorem exit_cfg_push_revert_143 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 143, stack := [env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase } =
      .ok { pc := 146,
            stack := [UInt256.ofNat Exit.revert, env.calldatasize,
                      quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_push_revert_143]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.1]

theorem exit_cfg_jumpi_bad_cds (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hne0 : env.calldatasize ≠ UInt256.ofNat 0) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 146,
          stack := [UInt256.ofNat Exit.revert, env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow } =
      .ok { pc := Exit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpi_146]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.2, hne0, exit_revert_contains,
    toNat_exit_revert]

theorem exit_bad_calldatasize_reverts_before_writes
    {σ : Storage} (_h : CallHyp .exit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hbad : env.calldatasize ≠ UInt256.ofNat 0 ∧
      env.calldatasize ≠ UInt256.ofNat 48) :
    runSteps 8 exitUserPrefix env exitJumpdests
        { pc := 135, stack := [quotedFee], gas := g } =
      .ok { pc := Exit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } ∧
      exitBadCdsJumpiPc < exitFirstSstorePc ∧
      exitBadCdsJumpiPc < exitFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (exit_cfg_cds_135 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push48 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_eq_138 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_handle quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_not_handle quotedFee env g hg hbad.2)]
    rw [runSteps_succ_ok (exit_cfg_cds_142 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_revert_143 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_bad_cds quotedFee env g hg hbad.1)]
    rfl
  · exact ⟨by decide, by decide⟩

theorem exit_cfg_jumpi_cds_zero (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (h0 : env.calldatasize = UInt256.ofNat 0) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 146,
          stack := [UInt256.ofNat Exit.revert, env.calldatasize, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow } =
      .ok { pc := 147, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpi_146]
  simp [(fee_gas_parts hg).2.2.2.2.2.2.2, h0]

theorem exit_cfg_callvalue_147 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 147, stack := [quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh } =
      .ok { pc := 148, stack := [env.callvalue, quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase } := by
  unfold cfgStepUser
  rw [exit_opcode_callvalue_147]
  simp [(getter_gas_tail hg).1]

theorem exit_cfg_push_revert_148 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 148, stack := [env.callvalue, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh - Gbase } =
      .ok { pc := 151,
            stack := [UInt256.ofNat Exit.revert, env.callvalue, quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_push_revert_148]
  simp [(getter_gas_tail hg).2.1]

theorem exit_cfg_jumpi_value_getter (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hv : env.callvalue ≠ UInt256.ofNat 0) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 151,
          stack := [UInt256.ofNat Exit.revert, env.callvalue, quotedFee],
          gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                   - Gbase - Gverylow - Ghigh - Gbase - Gverylow } =
      .ok { pc := Exit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow
                     - Ghigh } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpi_151]
  simp [(getter_gas_tail hg).2.2, hv, exit_revert_contains, toNat_exit_revert]

theorem exit_value_on_getter_reverts_before_writes
    {σ : Storage} (_h : CallHyp .exit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (h0 : env.calldatasize = UInt256.ofNat 0)
    (hv : env.callvalue ≠ UInt256.ofNat 0) :
    runSteps 11 exitUserPrefix env exitJumpdests
        { pc := 135, stack := [quotedFee], gas := g } =
      .ok { pc := Exit.revert, stack := [quotedFee],
            gas := g - Gbase - Gverylow - Gverylow - Gverylow - Ghigh
                     - Gbase - Gverylow - Ghigh - Gbase - Gverylow
                     - Ghigh } ∧
      exitValueGetterJumpiPc < exitFirstSstorePc ∧
      exitValueGetterJumpiPc < exitFirstLog0Pc := by
  have hne48 : env.calldatasize ≠ UInt256.ofNat 48 := by
    rw [h0]; decide
  constructor
  · rw [runSteps_succ_ok (exit_cfg_cds_135 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push48 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_eq_138 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_handle quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_not_handle quotedFee env g hg hne48)]
    rw [runSteps_succ_ok (exit_cfg_cds_142 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_revert_143 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_cds_zero quotedFee env g hg h0)]
    rw [runSteps_succ_ok (exit_cfg_callvalue_147 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_revert_148 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_value_getter quotedFee env g hg hv)]
    rfl
  · exact ⟨by decide, by decide⟩

/-! ## `handle_input`: underpay (`value < quotedFee`)

Starts at `handle_input` with `[quotedFee]` on the stack — the CFG state
after a taken `JUMPI` from fee-dispatch when `calldatasize` is well-formed.
Numeric equality of `quotedFee` with `fake_expo` is S4.
-/

private theorem underpay_gas_parts {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g < Gjumpdest ∧
      ¬ g - Gjumpdest < Gverylow ∧
      ¬ g - Gjumpdest - Gverylow < Gbase ∧
      ¬ g - Gjumpdest - Gverylow - Gbase < Gverylow ∧
      ¬ g - Gjumpdest - Gverylow - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gjumpdest - Gverylow - Gbase - Gverylow - Gverylow < Ghigh := by
  simp [fragmentGas, Gjumpdest, Gverylow, Gbase, Ghigh] at hg ⊢
  omega

private theorem exit_underpay_gas_parts {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g < Gjumpdest ∧
      ¬ g - Gjumpdest < Gbase ∧
      ¬ g - Gjumpdest - Gbase < Gverylow ∧
      ¬ g - Gjumpdest - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gjumpdest - Gbase - Gverylow - Gverylow < Ghigh := by
  simp [fragmentGas, Gjumpdest, Gbase, Gverylow, Ghigh] at hg ⊢
  omega

theorem deposit_cfg_jumpdest_159 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 159, stack := [quotedFee], gas := g } =
      .ok { pc := 160, stack := [quotedFee], gas := g - Gjumpdest } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpdest_159]
  simp [(underpay_gas_parts hg).1]

theorem deposit_cfg_dup1_160 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 160, stack := [quotedFee], gas := g - Gjumpdest } =
      .ok { pc := 161, stack := [quotedFee, quotedFee],
            gas := g - Gjumpdest - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_dup1_160]
  simp [(underpay_gas_parts hg).2.1]

theorem deposit_cfg_callvalue_161 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 161, stack := [quotedFee, quotedFee],
          gas := g - Gjumpdest - Gverylow } =
      .ok { pc := 162, stack := [env.callvalue, quotedFee, quotedFee],
            gas := g - Gjumpdest - Gverylow - Gbase } := by
  unfold cfgStepUser
  rw [deposit_opcode_callvalue_161]
  simp [(underpay_gas_parts hg).2.2.1]

theorem deposit_cfg_lt_162 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 162, stack := [env.callvalue, quotedFee, quotedFee],
          gas := g - Gjumpdest - Gverylow - Gbase } =
      .ok { pc := 163,
            stack := [UInt256.lt env.callvalue quotedFee, quotedFee],
            gas := g - Gjumpdest - Gverylow - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_lt_162]
  simp [(underpay_gas_parts hg).2.2.2.1]

theorem deposit_cfg_push_revert_163 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 163,
          stack := [UInt256.lt env.callvalue quotedFee, quotedFee],
          gas := g - Gjumpdest - Gverylow - Gbase - Gverylow } =
      .ok { pc := 166,
            stack := [UInt256.ofNat Deposit.revert,
                      UInt256.lt env.callvalue quotedFee, quotedFee],
            gas := g - Gjumpdest - Gverylow - Gbase - Gverylow
                     - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_revert_163]
  simp [(underpay_gas_parts hg).2.2.2.2.1]

theorem deposit_cfg_jumpi_underpay (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hlt : env.callvalue < quotedFee) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 166,
          stack := [UInt256.ofNat Deposit.revert,
                    UInt256.lt env.callvalue quotedFee, quotedFee],
          gas := g - Gjumpdest - Gverylow - Gbase - Gverylow - Gverylow } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gjumpdest - Gverylow - Gbase - Gverylow - Gverylow
                     - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_166]
  have h1 : UInt256.lt env.callvalue quotedFee = UInt256.ofNat 1 :=
    lt_one_of_lt hlt
  simp [(underpay_gas_parts hg).2.2.2.2.2, h1, ne_zero_of_one,
    deposit_revert_contains, toNat_deposit_revert]

/-- Well-formed length, `value < quotedFee` → revert at 166, before writes.
`∀` in the quoted word (and thus in excess/count that the quote uses);
numeric `fake_expo` is S4. -/
theorem deposit_underpay_reverts_before_writes
    {σ : Storage} (_h : CallHyp .deposit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hlt : env.callvalue < quotedFee) :
    runSteps 6 depositUserPrefix env depositJumpdests
        { pc := 159, stack := [quotedFee], gas := g } =
      .ok { pc := Deposit.revert, stack := [quotedFee],
            gas := g - Gjumpdest - Gverylow - Gbase - Gverylow
                     - Gverylow - Ghigh } ∧
      depositUnderpayJumpiPc < depositFirstSstorePc ∧
      depositUnderpayJumpiPc < depositFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (deposit_cfg_jumpdest_159 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_dup1_160 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_callvalue_161 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_lt_162 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_163 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_underpay quotedFee env g hg hlt)]
    rfl
  · exact ⟨by decide, by decide⟩

theorem exit_cfg_jumpdest_158 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 158, stack := [quotedFee], gas := g } =
      .ok { pc := 159, stack := [quotedFee], gas := g - Gjumpdest } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpdest_158]
  simp [(exit_underpay_gas_parts hg).1]

theorem exit_cfg_callvalue_159 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 159, stack := [quotedFee], gas := g - Gjumpdest } =
      .ok { pc := 160, stack := [env.callvalue, quotedFee],
            gas := g - Gjumpdest - Gbase } := by
  unfold cfgStepUser
  rw [exit_opcode_callvalue_159]
  simp [(exit_underpay_gas_parts hg).2.1]

theorem exit_cfg_lt_160 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 160, stack := [env.callvalue, quotedFee],
          gas := g - Gjumpdest - Gbase } =
      .ok { pc := 161, stack := [UInt256.lt env.callvalue quotedFee],
            gas := g - Gjumpdest - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_lt_160]
  simp [(exit_underpay_gas_parts hg).2.2.1]

theorem exit_cfg_push_revert_161 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 161, stack := [UInt256.lt env.callvalue quotedFee],
          gas := g - Gjumpdest - Gbase - Gverylow } =
      .ok { pc := 164,
            stack := [UInt256.ofNat Exit.revert,
                      UInt256.lt env.callvalue quotedFee],
            gas := g - Gjumpdest - Gbase - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [exit_opcode_push_revert_161]
  simp [(exit_underpay_gas_parts hg).2.2.2.1]

theorem exit_cfg_jumpi_underpay (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hlt : env.callvalue < quotedFee) :
    cfgStepUser exitUserPrefix env exitJumpdests
        { pc := 164,
          stack := [UInt256.ofNat Exit.revert,
                    UInt256.lt env.callvalue quotedFee],
          gas := g - Gjumpdest - Gbase - Gverylow - Gverylow } =
      .ok { pc := Exit.revert, stack := [],
            gas := g - Gjumpdest - Gbase - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [exit_opcode_jumpi_164]
  have h1 : UInt256.lt env.callvalue quotedFee = UInt256.ofNat 1 :=
    lt_one_of_lt hlt
  simp [(exit_underpay_gas_parts hg).2.2.2.2, h1, ne_zero_of_one,
    exit_revert_contains, toNat_exit_revert]

theorem exit_underpay_reverts_before_writes
    {σ : Storage} (_h : CallHyp .exit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hlt : env.callvalue < quotedFee) :
    runSteps 5 exitUserPrefix env exitJumpdests
        { pc := 158, stack := [quotedFee], gas := g } =
      .ok { pc := Exit.revert, stack := [],
            gas := g - Gjumpdest - Gbase - Gverylow - Gverylow - Ghigh } ∧
      exitUnderpayJumpiPc < exitFirstSstorePc ∧
      exitUnderpayJumpiPc < exitFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (exit_cfg_jumpdest_158 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_callvalue_159 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_lt_160 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_push_revert_161 quotedFee env g hg)]
    rw [runSteps_succ_ok (exit_cfg_jumpi_underpay quotedFee env g hg hlt)]
    rfl
  · exact ⟨by decide, by decide⟩

/-! ## Deposit min-amount and stake

After a *failing* underpay `JUMPI` (`value ≥ quotedFee`), stack is `[quotedFee]`.
Amount is `CALLDATALOAD(56) ∧ uint64_mask`.
-/

/-- Stack at `AND` is `[mask, word56, fee]`, so the result is `mask.land word56`. -/
def amountOf (env : TxEnv) : UInt256 :=
  UInt256.land (UInt256.ofNat UINT64_MASK) env.word56

private theorem min_gas_parts {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g < Gverylow ∧
      ¬ g - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow <
          Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow -
          Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow -
          Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow -
          Gverylow - Gverylow - Gverylow < Ghigh := by
  simp [fragmentGas, Gverylow, Ghigh] at hg ⊢
  omega

/-- Remaining gas after a not-taken underpay `JUMPI`. -/
def afterUnderpayGas (g : Nat) : Nat :=
  g - Gjumpdest - Gverylow - Gbase - Gverylow - Gverylow - Ghigh

theorem deposit_cfg_jumpi_underpay_fallthrough (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) (hge : ¬ env.callvalue < quotedFee) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 166,
          stack := [UInt256.ofNat Deposit.revert,
                    UInt256.lt env.callvalue quotedFee, quotedFee],
          gas := g - Gjumpdest - Gverylow - Gbase - Gverylow - Gverylow } =
      .ok { pc := 167, stack := [quotedFee],
            gas := afterUnderpayGas g } := by
  unfold cfgStepUser afterUnderpayGas
  rw [deposit_opcode_jumpi_166]
  have hz : UInt256.lt env.callvalue quotedFee = UInt256.ofNat 0 := by
    simp [UInt256.lt, UInt256.fromBool, Bool.toUInt256, hge]
  simp [(underpay_gas_parts hg).2.2.2.2.2, hz]

private theorem after_underpay_ge {g : Nat} (hg : g ≥ fragmentGas) :
    afterUnderpayGas g ≥ fragmentGas - (Gjumpdest + Gverylow + Gbase +
      Gverylow + Gverylow + Ghigh) := by
  simp [afterUnderpayGas, fragmentGas, Gjumpdest, Gverylow, Gbase, Ghigh] at hg ⊢
  omega

private theorem min_gas_from_after {g : Nat} (hg : g ≥ fragmentGas) :
    afterUnderpayGas g ≥ fragmentGas - 30 := by
  simp [afterUnderpayGas, fragmentGas, Gjumpdest, Gverylow, Gbase, Ghigh] at hg ⊢
  omega

/-- Restart min-amount/stake fragments with a fresh `≥ fragmentGas` budget
so we do not thread the underpay subtraction. Honest: campaign gas is 30M. -/
theorem deposit_cfg_push56 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 167, stack := [quotedFee], gas := g } =
      .ok { pc := 169, stack := [UInt256.ofNat 56, quotedFee],
            gas := g - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push56_167]
  simp [(min_gas_parts hg).1]

theorem deposit_cfg_calldataload_169 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 169, stack := [UInt256.ofNat 56, quotedFee],
          gas := g - Gverylow } =
      .ok { pc := 170, stack := [env.word56, quotedFee],
            gas := g - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_calldataload_169]
  simp [(min_gas_parts hg).2.1]

theorem deposit_cfg_push_mask (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 170, stack := [env.word56, quotedFee],
          gas := g - Gverylow - Gverylow } =
      .ok { pc := 179,
            stack := [UInt256.ofNat UINT64_MASK, env.word56, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_mask_170]
  simp [(min_gas_parts hg).2.2.1]

theorem deposit_cfg_and_179 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 179,
          stack := [UInt256.ofNat UINT64_MASK, env.word56, quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 180, stack := [amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser amountOf
  rw [deposit_opcode_and_179]
  simp [(min_gas_parts hg).2.2.2.1]

theorem deposit_cfg_dup1_180 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 180, stack := [amountOf env, quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 181, stack := [amountOf env, amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_dup1_180]
  simp [(min_gas_parts hg).2.2.2.2.1]

theorem deposit_cfg_push_min (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 181, stack := [amountOf env, amountOf env, quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 186,
            stack := [UInt256.ofNat MIN_AMOUNT, amountOf env, amountOf env,
                      quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_min_181]
  simp [(min_gas_parts hg).2.2.2.2.2.1]

theorem deposit_cfg_gt_186 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 186,
          stack := [UInt256.ofNat MIN_AMOUNT, amountOf env, amountOf env,
                    quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                   - Gverylow - Gverylow } =
      .ok { pc := 187,
            stack := [UInt256.gt (UInt256.ofNat MIN_AMOUNT) (amountOf env),
                      amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_gt_186]
  simp [(min_gas_parts hg).2.2.2.2.2.2.1]

theorem deposit_cfg_push_revert_187 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 187,
          stack := [UInt256.gt (UInt256.ofNat MIN_AMOUNT) (amountOf env),
                    amountOf env, quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                   - Gverylow - Gverylow - Gverylow } =
      .ok { pc := 190,
            stack := [UInt256.ofNat Deposit.revert,
                      UInt256.gt (UInt256.ofNat MIN_AMOUNT) (amountOf env),
                      amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow - Gverylow - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_revert_187]
  simp [(min_gas_parts hg).2.2.2.2.2.2.2.1]

theorem deposit_cfg_jumpi_min_amount (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas)
    (hmin : UInt256.ofNat MIN_AMOUNT > amountOf env) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 190,
          stack := [UInt256.ofNat Deposit.revert,
                    UInt256.gt (UInt256.ofNat MIN_AMOUNT) (amountOf env),
                    amountOf env, quotedFee],
          gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                   - Gverylow - Gverylow - Gverylow - Gverylow } =
      .ok { pc := Deposit.revert, stack := [amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow - Gverylow - Gverylow - Gverylow
                     - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_190]
  have h1 : UInt256.gt (UInt256.ofNat MIN_AMOUNT) (amountOf env) =
      UInt256.ofNat 1 := gt_one_of_gt hmin
  simp [(min_gas_parts hg).2.2.2.2.2.2.2.2, h1, ne_zero_of_one,
    deposit_revert_contains, toNat_deposit_revert]

/-- `MIN_AMOUNT > amount` → revert at 190, before writes. Amount is the
low 64 bits of `CALLDATALOAD(56)`. -/
theorem deposit_min_amount_reverts_before_writes
    {σ : Storage} (_h : CallHyp .deposit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hmin : UInt256.ofNat MIN_AMOUNT > amountOf env) :
    runSteps 9 depositUserPrefix env depositJumpdests
        { pc := 167, stack := [quotedFee], gas := g } =
      .ok { pc := Deposit.revert, stack := [amountOf env, quotedFee],
            gas := g - Gverylow - Gverylow - Gverylow - Gverylow
                     - Gverylow - Gverylow - Gverylow - Gverylow
                     - Ghigh } ∧
      depositMinAmountJumpiPc < depositFirstSstorePc ∧
      depositMinAmountJumpiPc < depositFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (deposit_cfg_push56 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_calldataload_169 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_mask quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_and_179 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_dup1_180 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_min quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_gt_186 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_187 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_min_amount quotedFee env g hg hmin)]
    rfl
  · exact ⟨by decide, by decide⟩

/-! ### Stake: `(callvalue - fee) < amount * GWEI` -/

private theorem stake_gas_parts {g : Nat} (hg : g ≥ fragmentGas) :
    ¬ g < Gverylow ∧
      ¬ g - Gverylow < Glow ∧
      ¬ g - Gverylow - Glow < Gverylow ∧
      ¬ g - Gverylow - Glow - Gverylow < Gbase ∧
      ¬ g - Gverylow - Glow - Gverylow - Gbase < Gverylow ∧
      ¬ g - Gverylow - Glow - Gverylow - Gbase - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Glow - Gverylow - Gbase - Gverylow - Gverylow <
          Gverylow ∧
      ¬ g - Gverylow - Glow - Gverylow - Gbase - Gverylow - Gverylow -
          Gverylow < Ghigh := by
  simp [fragmentGas, Gverylow, Glow, Gbase, Ghigh] at hg ⊢
  omega

/-- Start of the stake check: after a not-taken min-amount `JUMPI`.
Stack: `[amount, quotedFee]`. -/
theorem deposit_cfg_push_gwei (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 191, stack := [amountOf env, quotedFee], gas := g } =
      .ok { pc := 196,
            stack := [UInt256.ofNat GWEI, amountOf env, quotedFee],
            gas := g - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_gwei_191]
  simp [(stake_gas_parts hg).1]

theorem deposit_cfg_mul_196 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 196,
          stack := [UInt256.ofNat GWEI, amountOf env, quotedFee],
          gas := g - Gverylow } =
      .ok { pc := 197,
            stack := [UInt256.mul (UInt256.ofNat GWEI) (amountOf env),
                      quotedFee],
            gas := g - Gverylow - Glow } := by
  unfold cfgStepUser
  rw [deposit_opcode_mul_196]
  simp [(stake_gas_parts hg).2.1]

theorem deposit_cfg_swap1_197 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 197,
          stack := [UInt256.mul (UInt256.ofNat GWEI) (amountOf env),
                    quotedFee],
          gas := g - Gverylow - Glow } =
      .ok { pc := 198,
            stack := [quotedFee,
                      UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
            gas := g - Gverylow - Glow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_swap1_197]
  simp [(stake_gas_parts hg).2.2.1]

theorem deposit_cfg_callvalue_198 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 198,
          stack := [quotedFee,
                    UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
          gas := g - Gverylow - Glow - Gverylow } =
      .ok { pc := 199,
            stack := [env.callvalue, quotedFee,
                      UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
            gas := g - Gverylow - Glow - Gverylow - Gbase } := by
  unfold cfgStepUser
  rw [deposit_opcode_callvalue_198]
  simp [(stake_gas_parts hg).2.2.2.1]

theorem deposit_cfg_sub_199 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 199,
          stack := [env.callvalue, quotedFee,
                    UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
          gas := g - Gverylow - Glow - Gverylow - Gbase } =
      .ok { pc := 200,
            stack := [UInt256.sub env.callvalue quotedFee,
                      UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
            gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_sub_199]
  simp [(stake_gas_parts hg).2.2.2.2.1]

theorem deposit_cfg_lt_200 (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 200,
          stack := [UInt256.sub env.callvalue quotedFee,
                    UInt256.mul (UInt256.ofNat GWEI) (amountOf env)],
          gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow } =
      .ok { pc := 201,
            stack := [UInt256.lt (UInt256.sub env.callvalue quotedFee)
                        (UInt256.mul (UInt256.ofNat GWEI) (amountOf env))],
            gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                     - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_lt_200]
  simp [(stake_gas_parts hg).2.2.2.2.2.1]

theorem deposit_cfg_push_revert_201 (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 201,
          stack := [UInt256.lt (UInt256.sub env.callvalue quotedFee)
                      (UInt256.mul (UInt256.ofNat GWEI) (amountOf env))],
          gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                   - Gverylow } =
      .ok { pc := 204,
            stack := [UInt256.ofNat Deposit.revert,
                      UInt256.lt (UInt256.sub env.callvalue quotedFee)
                        (UInt256.mul (UInt256.ofNat GWEI) (amountOf env))],
            gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                     - Gverylow - Gverylow } := by
  unfold cfgStepUser
  rw [deposit_opcode_push_revert_201]
  simp [(stake_gas_parts hg).2.2.2.2.2.2.1]

theorem deposit_cfg_jumpi_stake (env : TxEnv) (g : Nat)
    (hg : g ≥ fragmentGas)
    (hst : UInt256.sub env.callvalue quotedFee <
        UInt256.mul (UInt256.ofNat GWEI) (amountOf env)) :
    cfgStepUser depositUserPrefix env depositJumpdests
        { pc := 204,
          stack := [UInt256.ofNat Deposit.revert,
                    UInt256.lt (UInt256.sub env.callvalue quotedFee)
                      (UInt256.mul (UInt256.ofNat GWEI) (amountOf env))],
          gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                   - Gverylow - Gverylow } =
      .ok { pc := Deposit.revert, stack := [],
            gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                     - Gverylow - Gverylow - Ghigh } := by
  unfold cfgStepUser
  rw [deposit_opcode_jumpi_204]
  have h1 :
      UInt256.lt (UInt256.sub env.callvalue quotedFee)
          (UInt256.mul (UInt256.ofNat GWEI) (amountOf env)) =
        UInt256.ofNat 1 := lt_one_of_lt hst
  simp [(stake_gas_parts hg).2.2.2.2.2.2.2, h1, ne_zero_of_one,
    deposit_revert_contains, toNat_deposit_revert]

/-- Stake shortfall `(value − fee) < amount * 1 gwei` → revert at 204,
before writes. Assumes the underpay and min-amount `JUMPI`s were not taken. -/
theorem deposit_stake_reverts_before_writes
    {σ : Storage} (_h : CallHyp .deposit σ)
    (env : TxEnv) (g : Nat) (hg : g ≥ fragmentGas)
    (hst : UInt256.sub env.callvalue quotedFee <
        UInt256.mul (UInt256.ofNat GWEI) (amountOf env)) :
    runSteps 8 depositUserPrefix env depositJumpdests
        { pc := 191, stack := [amountOf env, quotedFee], gas := g } =
      .ok { pc := Deposit.revert, stack := [],
            gas := g - Gverylow - Glow - Gverylow - Gbase - Gverylow
                     - Gverylow - Gverylow - Ghigh } ∧
      depositStakeJumpiPc < depositFirstSstorePc ∧
      depositStakeJumpiPc < depositFirstLog0Pc := by
  constructor
  · rw [runSteps_succ_ok (deposit_cfg_push_gwei quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_mul_196 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_swap1_197 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_callvalue_198 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_sub_199 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_lt_200 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_push_revert_201 quotedFee env g hg)]
    rw [runSteps_succ_ok (deposit_cfg_jumpi_stake quotedFee env g hg hst)]
    rfl
  · exact ⟨by decide, by decide⟩

end QuotedFee

/-! ## Packaging: campaign gas on `CallHyp` -/

theorem callHyp_fragmentGas {kind : Kind} {σ : Storage}
    (h : CallHyp kind σ) : h.gas ≥ fragmentGas :=
  Nat.le_trans fragmentGas_le_campaign h.gas_ge

/-- `CallHyp` form of the deposit bad-`calldatasize` revert. -/
theorem deposit_bad_calldatasize_of_callHyp
    {σ : Storage} (h : CallHyp .deposit σ)
    (quotedFee : UInt256) (env : TxEnv)
    (hbad : env.calldatasize ≠ UInt256.ofNat 0 ∧
      env.calldatasize ≠ UInt256.ofNat 184) :
    ∃ m, runSteps 8 depositUserPrefix env depositJumpdests
        { pc := depositFeeDispatchPc, stack := [quotedFee], gas := h.gas } = .ok m ∧
      m.pc = Deposit.revert := by
  have hrun := deposit_bad_calldatasize_reverts_before_writes quotedFee h env
    h.gas (callHyp_fragmentGas h) hbad
  simp [depositFeeDispatchPc]
  exact ⟨_, hrun.1, rfl⟩

end Eip8282.Audit.Guarantees.PSubmit1.Revert
