import Std.Data.TreeMap.Lemmas
import Eip8282.Audit.Correspondence
import Eip8282.Audit.WellFormed

/-!
P-CONTROL-1 count: paid user increments `SLOT_COUNT` (wrap mod 2^256) and
does not `SSTORE` slot 0; system `store_excess` stores `SLOT_COUNT := 0`.

CFG-direct on the pinned `SSTORE` sites. Excess fold is C2; FIFO is D2;
`fake_expo` is S4. F4 left `A-ABSTRACT-TX` open, so these lemmas are not a
reduction of `Ξ`.
-/

namespace Eip8282.Audit.Guarantees.PControl1.Count

open Std
open EvmYul (UInt256 Storage)
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model (Kind inhibitor)
open GasConstants

/-! ## UInt256 order (TreeMap `getD_insert`) and wrapping add -/

/-- Derived `Ord` is `(compare val).then eq`, which equals `compare val`. -/
theorem compare_val (a b : UInt256) :
    compare a b = compare a.val b.val := by
  cases a with
  | mk va =>
    cases b with
    | mk vb =>
      change (compare va vb).then Ordering.eq = compare va vb
      cases (compare va vb) <;> rfl

instance : OrientedOrd UInt256 where
  eq_swap {a b} := by
    rw [compare_val a b, compare_val b a]
    exact OrientedOrd.eq_swap (α := Fin UInt256.size)

instance : TransOrd UInt256 where
  isLE_trans {a b c} h₁ h₂ := by
    rw [compare_val a b] at h₁
    rw [compare_val b c] at h₂
    rw [compare_val a c]
    exact TransOrd.isLE_trans (α := Fin UInt256.size) h₁ h₂

instance : LawfulEqOrd UInt256 where
  eq_of_compare {a b} h := by
    have hval : compare a.val b.val = .eq := by
      rwa [← compare_val]
    exact congrArg UInt256.mk (LawfulEqOrd.eq_of_compare (α := Fin UInt256.size) hval)

theorem uint256_add_comm (a b : UInt256) : a + b = b + a := by
  cases a; cases b
  exact congrArg UInt256.mk (add_comm _ _)

theorem toNat_add (a b : UInt256) :
    (a + b).toNat = (a.toNat + b.toNat) % UInt256.size :=
  Fin.val_add a.val b.val

theorem toNat_ofNat_one : (UInt256.ofNat 1).toNat = 1 := by
  rw [Correspondence.toNat_ofNat]
  decide

theorem toNat_ofNat_zero : (UInt256.ofNat 0).toNat = 0 := by
  rw [Correspondence.toNat_ofNat]
  decide

/-- Wrapping `+ 1` on a storage word. -/
theorem toNat_add_one (c : UInt256) :
    (c + UInt256.ofNat 1).toNat = (c.toNat + 1) % UInt256.size := by
  rw [toNat_add, toNat_ofNat_one]

theorem ofNat_zero_ne_one : UInt256.ofNat 0 ≠ UInt256.ofNat 1 := by
  intro h
  have h0 := toNat_ofNat_zero
  have h1 := toNat_ofNat_one
  rw [h] at h0
  rw [h1] at h0
  cases h0

theorem slot0_ne_slot1 :
    UInt256.ofNat SLOT_EXCESS ≠ UInt256.ofNat SLOT_COUNT := by
  unfold SLOT_EXCESS SLOT_COUNT
  exact ofNat_zero_ne_one

theorem loadU256_insert_self (σ : Storage) (k v : UInt256) :
    (σ.insert k v).getD k (UInt256.ofNat 0) = v :=
  TreeMap.getD_insert_self

theorem loadU256_insert_ne (σ : Storage) (k a v : UInt256)
    (hne : k ≠ a) :
    (σ.insert k v).getD a (UInt256.ofNat 0) = σ.getD a (UInt256.ofNat 0) := by
  rw [TreeMap.getD_insert]
  split
  · rename_i heq
    have : k = a := LawfulEqOrd.compare_eq_iff_eq.mp heq
    exact (hne this).elim
  · rfl

theorem loadU256_sstore_count (σ : Storage) (v : UInt256) :
    loadU256 (σ.insert (UInt256.ofNat SLOT_COUNT) v) SLOT_COUNT = v := by
  unfold loadU256
  exact loadU256_insert_self σ _ v

theorem loadU256_sstore_count_preserves_excess (σ : Storage) (v : UInt256) :
    loadU256 (σ.insert (UInt256.ofNat SLOT_COUNT) v) SLOT_EXCESS =
      loadU256 σ SLOT_EXCESS := by
  unfold loadU256
  exact loadU256_insert_ne σ _ _ v slot0_ne_slot1.symm

theorem loadU256_sstore_excess_then_count_zero (σ : Storage) (ex : UInt256) :
    loadU256
        ((σ.insert (UInt256.ofNat SLOT_EXCESS) ex).insert
          (UInt256.ofNat SLOT_COUNT) (UInt256.ofNat 0))
        SLOT_COUNT =
      UInt256.ofNat 0 := by
  unfold loadU256
  exact loadU256_insert_self _ _ _

/-! ## Pinned hex at the count / `store_excess` SSTORE sites

`fromHex` of a full runtime is kernel-opaque (F3). These fragments are the
bytes at the named PCs; they are the same in both runtimes.
-/

/-- `PUSH1 1; SLOAD; PUSH1 1; ADD; PUSH1 1; SSTORE` — both runtimes. -/
def countIncHex : String := "600154600101600155"

/-- `JUMPDEST; PUSH0; SSTORE; PUSH0; PUSH1 1; SSTORE` at `store_excess`. -/
def storeExcessHex : String := "5b5f555f600155"

def countIncCode : ByteArray := fromHex countIncHex
def storeExcessCode : ByteArray := fromHex storeExcessHex

/-- Deposit bytes 192–223 contain the user count increment at offset 13. -/
def depositChunk192 : String :=
  "3b9aca0002903403106102705760015460010160015560035480600602600401"

/-- Exit bytes 160–191 contain the user count increment at offset 5. -/
def exitChunk160 : String :=
  "106101c657600154600101600155600354806003026004013381556001015f35"

/-- Deposit tail containing `store_excess`. -/
def depositStoreExcessTail : String :=
  "ffffffff5b5f555f60015560b8025ff35b5f5ffd"

/-- Exit tail containing `store_excess`. -/
def exitStoreExcessTail : String :=
  "5b5f555f6001556044025ff35b5f5ffd"

theorem countIncHex_eq : countIncHex = "600154600101600155" := rfl
theorem storeExcessHex_eq : storeExcessHex = "5b5f555f600155" := rfl

/-! ## Absolute PCs (runtime image) -/

/-- First byte of the user `PUSH1 SLOT_COUNT` after `handle_input` admission. -/
def countIncPc : Kind → Nat
  | .deposit => 205
  | .exit => 165

/-- User `SSTORE SLOT_COUNT` (the increment). -/
def countSstorePc : Kind → Nat
  | .deposit => 213
  | .exit => 173

def storeExcessPc : Kind → Nat
  | .deposit => Deposit.store_excess
  | .exit => Exit.store_excess

/-- System `SSTORE SLOT_COUNT := 0`. -/
def countResetSstorePc : Kind → Nat
  | .deposit => Deposit.store_excess + 6
  | .exit => Exit.store_excess + 6

theorem deposit_countIncPc : countIncPc .deposit = 205 := rfl
theorem exit_countIncPc : countIncPc .exit = 165 := rfl
theorem deposit_countSstorePc : countSstorePc .deposit = 213 := rfl
theorem exit_countSstorePc : countSstorePc .exit = 173 := rfl

theorem deposit_storeExcessPc :
    storeExcessPc .deposit = Deposit.store_excess :=
  rfl

theorem exit_storeExcessPc :
    storeExcessPc .exit = Exit.store_excess :=
  rfl

theorem deposit_countResetSstorePc :
    countResetSstorePc .deposit = 618 :=
  rfl

theorem exit_countResetSstorePc :
    countResetSstorePc .exit = 448 :=
  rfl

theorem deposit_countInc_after_handle_input :
    Deposit.handle_input = 159 ∧ countIncPc .deposit = 205 := by
  decide

theorem exit_countInc_after_handle_input :
    Exit.handle_input = 158 ∧ countIncPc .exit = 165 := by
  decide

/-! ## Opcode-at-PC on the fragments -/

theorem countInc_opcode_PUSH1_slot :
    opcodeAt countIncCode 0 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem countInc_opcode_SLOAD :
    opcodeAt countIncCode 2 = some (.SLOAD, none) :=
  rfl

theorem countInc_opcode_PUSH1_one :
    opcodeAt countIncCode 3 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem countInc_opcode_ADD :
    opcodeAt countIncCode 5 = some (.ADD, none) :=
  rfl

theorem countInc_opcode_PUSH1_slot' :
    opcodeAt countIncCode 6 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem countInc_opcode_SSTORE :
    opcodeAt countIncCode 8 = some (.SSTORE, none) :=
  rfl

theorem storeExcess_opcode_JUMPDEST :
    opcodeAt storeExcessCode 0 = some (.JUMPDEST, none) :=
  rfl

theorem storeExcess_opcode_PUSH0_excess :
    opcodeAt storeExcessCode 1 = some (.PUSH0, none) :=
  rfl

theorem storeExcess_opcode_SSTORE_excess :
    opcodeAt storeExcessCode 2 = some (.SSTORE, none) :=
  rfl

theorem storeExcess_opcode_PUSH0_zero :
    opcodeAt storeExcessCode 3 = some (.PUSH0, none) :=
  rfl

theorem storeExcess_opcode_PUSH1_count :
    opcodeAt storeExcessCode 4 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem storeExcess_opcode_SSTORE_count :
    opcodeAt storeExcessCode 6 = some (.SSTORE, none) :=
  rfl

/-! ## CFG stepper with storage -/

/-- Cold `SSTORE` upper bound (`Gcoldsload + Gsset`). Enough-gas hyp only. -/
def sstoreGasBound : Nat := Gcoldsload + Gsset

/-- `PUSH1; SLOAD; PUSH1; ADD; PUSH1; SSTORE`. -/
def countIncGasBound : Nat :=
  4 * Gverylow + Gcoldsload + sstoreGasBound

/-- `JUMPDEST; PUSH0; SSTORE; PUSH0; PUSH1; SSTORE`. -/
def storeExcessGasBound : Nat :=
  Gjumpdest + 2 * Gbase + Gverylow + 2 * sstoreGasBound

theorem countIncGasBound_le_campaign :
    countIncGasBound ≤ campaignGasBound := by
  decide

theorem storeExcessGasBound_le_campaign :
    storeExcessGasBound ≤ campaignGasBound := by
  decide

structure CountCfg where
  pc : Nat
  stack : List UInt256
  gas : Nat
  storage : Storage
  deriving Inhabited

/-- One tick: the count / `store_excess` opcodes only.
`Push` with an immediate is matched before `PUSH0` so simp can discriminate
on `Option` (`some imm` vs `none`), as F3 does. -/
def cfgStepCount (code : ByteArray) (m : CountCfg) :
    Except CfgError CountCfg :=
  match opcodeAt code m.pc with
  | some (.Push _, some (imm, width)) =>
      if m.gas < Gverylow then .error .outOfGas
      else
        .ok { pc := m.pc + 1 + width, stack := imm :: m.stack,
              gas := m.gas - Gverylow, storage := m.storage }
  | some (.Push .PUSH0, none) =>
      if m.gas < Gbase then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := UInt256.ofNat 0 :: m.stack,
              gas := m.gas - Gbase, storage := m.storage }
  | some (.StackMemFlow .SLOAD, none) =>
      match m.stack with
      | key :: rest =>
          if m.gas < Gcoldsload then .error .outOfGas
          else
            .ok { pc := m.pc + 1,
                  stack := m.storage.getD key (UInt256.ofNat 0) :: rest,
                  gas := m.gas - Gcoldsload, storage := m.storage }
      | _ => .error .stackUnderflow
  | some (.StopArith .ADD, none) =>
      match m.stack with
      | a :: b :: rest =>
          if m.gas < Gverylow then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := (a + b) :: rest,
                  gas := m.gas - Gverylow, storage := m.storage }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .SSTORE, none) =>
      match m.stack with
      | key :: val :: rest =>
          if m.gas < sstoreGasBound then .error .outOfGas
          else
            .ok { pc := m.pc + 1, stack := rest,
                  gas := m.gas - sstoreGasBound,
                  storage := m.storage.insert key val }
      | _ => .error .stackUnderflow
  | some (.StackMemFlow .JUMPDEST, none) =>
      if m.gas < Gjumpdest then .error .outOfGas
      else
        .ok { pc := m.pc + 1, stack := m.stack, gas := m.gas - Gjumpdest,
              storage := m.storage }
  | _ => .error .unexpectedOpcode

private theorem count_gas_parts {g : Nat} (hg : g ≥ countIncGasBound) :
    ¬ g < Gverylow ∧
      ¬ g - Gverylow < Gcoldsload ∧
      ¬ g - Gverylow - Gcoldsload < Gverylow ∧
      ¬ g - Gverylow - Gcoldsload - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gcoldsload - Gverylow - Gverylow < Gverylow ∧
      ¬ g - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow <
          sstoreGasBound := by
  simp [countIncGasBound, sstoreGasBound, Gverylow, Gcoldsload, Gsset] at hg ⊢
  omega

private theorem store_gas_parts {g : Nat} (hg : g ≥ storeExcessGasBound) :
    ¬ g < Gjumpdest ∧
      ¬ g - Gjumpdest < Gbase ∧
      ¬ g - Gjumpdest - Gbase < sstoreGasBound ∧
      ¬ g - Gjumpdest - Gbase - sstoreGasBound < Gbase ∧
      ¬ g - Gjumpdest - Gbase - sstoreGasBound - Gbase < Gverylow ∧
      ¬ g - Gjumpdest - Gbase - sstoreGasBound - Gbase - Gverylow <
          sstoreGasBound := by
  simp [storeExcessGasBound, sstoreGasBound, Gjumpdest, Gbase, Gverylow,
    Gcoldsload, Gsset] at hg ⊢
  omega

/-! ### User count-increment steps -/

theorem count_cfg_PUSH1_slot (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 0, stack := [], gas := g, storage := σ } =
      .ok { pc := 2, stack := [UInt256.ofNat 1],
            gas := g - Gverylow, storage := σ } := by
  unfold cfgStepCount
  simp only [countInc_opcode_PUSH1_slot]
  simp [(count_gas_parts hg).1]

theorem count_cfg_SLOAD (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 2, stack := [UInt256.ofNat 1],
          gas := g - Gverylow, storage := σ } =
      .ok { pc := 3, stack := [loadU256 σ SLOT_COUNT],
            gas := g - Gverylow - Gcoldsload, storage := σ } := by
  unfold cfgStepCount
  simp only [countInc_opcode_SLOAD]
  simp [(count_gas_parts hg).2.1]
  rfl

theorem count_cfg_PUSH1_one (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 3, stack := [loadU256 σ SLOT_COUNT],
          gas := g - Gverylow - Gcoldsload, storage := σ } =
      .ok { pc := 5,
            stack := [UInt256.ofNat 1, loadU256 σ SLOT_COUNT],
            gas := g - Gverylow - Gcoldsload - Gverylow, storage := σ } := by
  unfold cfgStepCount
  simp only [countInc_opcode_PUSH1_one]
  simp [(count_gas_parts hg).2.2.1]

theorem count_cfg_ADD (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 5, stack := [UInt256.ofNat 1, loadU256 σ SLOT_COUNT],
          gas := g - Gverylow - Gcoldsload - Gverylow, storage := σ } =
      .ok { pc := 6,
            stack := [UInt256.ofNat 1 + loadU256 σ SLOT_COUNT],
            gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow,
            storage := σ } := by
  unfold cfgStepCount
  simp only [countInc_opcode_ADD]
  simp [(count_gas_parts hg).2.2.2.1]

theorem count_cfg_PUSH1_slot' (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 6, stack := [UInt256.ofNat 1 + loadU256 σ SLOT_COUNT],
          gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow,
          storage := σ } =
      .ok { pc := 8,
            stack := [UInt256.ofNat 1,
                      UInt256.ofNat 1 + loadU256 σ SLOT_COUNT],
            gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow,
            storage := σ } := by
  unfold cfgStepCount
  simp only [countInc_opcode_PUSH1_slot']
  simp [(count_gas_parts hg).2.2.2.2.1]

theorem count_cfg_SSTORE (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    cfgStepCount countIncCode
        { pc := 8,
          stack := [UInt256.ofNat 1,
                    UInt256.ofNat 1 + loadU256 σ SLOT_COUNT],
          gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow,
          storage := σ } =
      .ok { pc := 9, stack := [],
            gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - sstoreGasBound,
            storage :=
              σ.insert (UInt256.ofNat 1)
                (UInt256.ofNat 1 + loadU256 σ SLOT_COUNT) } := by
  unfold cfgStepCount
  simp only [countInc_opcode_SSTORE]
  simp [(count_gas_parts hg).2.2.2.2.2]

def runCountInc (σ : Storage) (gas : Nat) : Except CfgError CountCfg :=
  let m0 : CountCfg := { pc := 0, stack := [], gas, storage := σ }
  match cfgStepCount countIncCode m0 with
  | .error e => .error e
  | .ok m1 =>
    match cfgStepCount countIncCode m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStepCount countIncCode m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStepCount countIncCode m3 with
        | .error e => .error e
        | .ok m4 =>
          match cfgStepCount countIncCode m4 with
          | .error e => .error e
          | .ok m5 => cfgStepCount countIncCode m5

/-- `∀` prior `SLOT_COUNT`: wrapping `+1`, no `SSTORE` of slot 0. -/
theorem runCountInc_ok (σ : Storage) (g : Nat)
    (hg : g ≥ countIncGasBound) :
    runCountInc σ g =
      .ok { pc := 9, stack := [],
            gas := g - Gverylow - Gcoldsload - Gverylow - Gverylow - Gverylow
                     - sstoreGasBound,
            storage :=
              σ.insert (UInt256.ofNat SLOT_COUNT)
                (loadU256 σ SLOT_COUNT + UInt256.ofNat 1) } := by
  have h1 := count_cfg_PUSH1_slot σ g hg
  have h2 := count_cfg_SLOAD σ g hg
  have h3 := count_cfg_PUSH1_one σ g hg
  have h4 := count_cfg_ADD σ g hg
  have h5 := count_cfg_PUSH1_slot' σ g hg
  have h6 := count_cfg_SSTORE σ g hg
  have hcomm :
      UInt256.ofNat 1 + loadU256 σ SLOT_COUNT =
        loadU256 σ SLOT_COUNT + UInt256.ofNat 1 :=
    uint256_add_comm _ _
  simp [runCountInc, h1, h2, h3, h4, h5, h6]
  rw [hcomm]
  rfl

/-! ### System `store_excess` steps -/

theorem store_cfg_JUMPDEST (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 0, stack := [ex, cnt], gas := g, storage := σ } =
      .ok { pc := 1, stack := [ex, cnt],
            gas := g - Gjumpdest, storage := σ } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_JUMPDEST]
  simp [(store_gas_parts hg).1]

theorem store_cfg_PUSH0_excess (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 1, stack := [ex, cnt],
          gas := g - Gjumpdest, storage := σ } =
      .ok { pc := 2, stack := [UInt256.ofNat 0, ex, cnt],
            gas := g - Gjumpdest - Gbase, storage := σ } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_PUSH0_excess]
  simp [(store_gas_parts hg).2.1]

theorem store_cfg_SSTORE_excess (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 2, stack := [UInt256.ofNat 0, ex, cnt],
          gas := g - Gjumpdest - Gbase, storage := σ } =
      .ok { pc := 3, stack := [cnt],
            gas := g - Gjumpdest - Gbase - sstoreGasBound,
            storage := σ.insert (UInt256.ofNat 0) ex } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_SSTORE_excess]
  simp [(store_gas_parts hg).2.2.1]

theorem store_cfg_PUSH0_zero (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 3, stack := [cnt],
          gas := g - Gjumpdest - Gbase - sstoreGasBound,
          storage := σ.insert (UInt256.ofNat 0) ex } =
      .ok { pc := 4, stack := [UInt256.ofNat 0, cnt],
            gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase,
            storage := σ.insert (UInt256.ofNat 0) ex } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_PUSH0_zero]
  simp [(store_gas_parts hg).2.2.2.1]

theorem store_cfg_PUSH1_count (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 4, stack := [UInt256.ofNat 0, cnt],
          gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase,
          storage := σ.insert (UInt256.ofNat 0) ex } =
      .ok { pc := 6, stack := [UInt256.ofNat 1, UInt256.ofNat 0, cnt],
            gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase - Gverylow,
            storage := σ.insert (UInt256.ofNat 0) ex } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_PUSH1_count]
  simp [(store_gas_parts hg).2.2.2.2.1]

theorem store_cfg_SSTORE_count (σ : Storage) (ex cnt : UInt256) (g : Nat)
    (hg : g ≥ storeExcessGasBound) :
    cfgStepCount storeExcessCode
        { pc := 6, stack := [UInt256.ofNat 1, UInt256.ofNat 0, cnt],
          gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase - Gverylow,
          storage := σ.insert (UInt256.ofNat 0) ex } =
      .ok { pc := 7, stack := [cnt],
            gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase - Gverylow
                     - sstoreGasBound,
            storage :=
              (σ.insert (UInt256.ofNat 0) ex).insert
                (UInt256.ofNat 1) (UInt256.ofNat 0) } := by
  unfold cfgStepCount
  simp only [storeExcess_opcode_SSTORE_count]
  simp [(store_gas_parts hg).2.2.2.2.2]

def runStoreExcess (σ : Storage) (newExcess drainCount : UInt256)
    (gas : Nat) : Except CfgError CountCfg :=
  let m0 : CountCfg :=
    { pc := 0, stack := [newExcess, drainCount], gas, storage := σ }
  match cfgStepCount storeExcessCode m0 with
  | .error e => .error e
  | .ok m1 =>
    match cfgStepCount storeExcessCode m1 with
    | .error e => .error e
    | .ok m2 =>
      match cfgStepCount storeExcessCode m2 with
      | .error e => .error e
      | .ok m3 =>
        match cfgStepCount storeExcessCode m3 with
        | .error e => .error e
        | .ok m4 =>
          match cfgStepCount storeExcessCode m4 with
          | .error e => .error e
          | .ok m5 => cfgStepCount storeExcessCode m5

/-- `∀` prior `SLOT_COUNT`: `store_excess` writes `0` to slot 1.
`newExcess` is C2's stack value; `drainCount` is the leftover return-size
word, not `SLOT_COUNT`. -/
theorem runStoreExcess_ok (σ : Storage) (newExcess drainCount : UInt256)
    (g : Nat) (hg : g ≥ storeExcessGasBound) :
    runStoreExcess σ newExcess drainCount g =
      .ok { pc := 7, stack := [drainCount],
            gas := g - Gjumpdest - Gbase - sstoreGasBound - Gbase - Gverylow
                     - sstoreGasBound,
            storage :=
              (σ.insert (UInt256.ofNat SLOT_EXCESS) newExcess).insert
                (UInt256.ofNat SLOT_COUNT) (UInt256.ofNat 0) } := by
  have h1 := store_cfg_JUMPDEST σ newExcess drainCount g hg
  have h2 := store_cfg_PUSH0_excess σ newExcess drainCount g hg
  have h3 := store_cfg_SSTORE_excess σ newExcess drainCount g hg
  have h4 := store_cfg_PUSH0_zero σ newExcess drainCount g hg
  have h5 := store_cfg_PUSH1_count σ newExcess drainCount g hg
  have h6 := store_cfg_SSTORE_count σ newExcess drainCount g hg
  simp [runStoreExcess, h1, h2, h3, h4, h5, h6]
  rfl

/-! ## Campaign hypotheses

Paid user: not inhibited, `calldatasize` 184/48, `value ≥ fee` (S4 owns
the quote). After `handle_input` admission the stack is empty and PC is
`countIncPc`. System: `CallHyp.isUser = false`; C2 owns `newExcess`.
-/

structure PaidUser (kind : Kind) (σ : Storage) where
  call : CallHyp kind σ
  isUser : call.isUser = true
  notInhibited : slotExcess σ ≠ inhibitor
  calldatasize : Nat
  calldatasize_eq : calldatasize = itemBytes kind
  value : UInt256
  fee : UInt256
  value_ge_fee : fee.toNat ≤ value.toNat

theorem PaidUser.gas_ge_countInc {kind : Kind} {σ : Storage}
    (p : PaidUser kind σ) :
    p.call.gas ≥ countIncGasBound :=
  Nat.le_trans countIncGasBound_le_campaign p.call.gas_ge

/-! ## Parent theorems (both predeploys) -/

/-- Paid user, not inhibited, well-formed paying input: post count is
pre+1 (mod 2^256) and post excess is unchanged. Both runtimes share the
count-increment bytes; PCs are `countIncPc` / `countSstorePc`. -/
theorem paid_user_count_inc
    {kind : Kind} {σ : Storage} (p : PaidUser kind σ)
    {m : CountCfg}
    (hrun : runCountInc σ p.call.gas = .ok m) :
    loadU256 m.storage SLOT_COUNT =
        loadU256 σ SLOT_COUNT + UInt256.ofNat 1 ∧
      loadU256 m.storage SLOT_EXCESS = loadU256 σ SLOT_EXCESS ∧
      slotCount m.storage =
        (slotCount σ + 1) % UInt256.size ∧
      slotExcess m.storage = slotExcess σ := by
  have hg := p.gas_ge_countInc
  have hok := runCountInc_ok σ p.call.gas hg
  rw [hok] at hrun
  cases hrun
  refine ⟨?count, ?excess, ?countNat, ?excessNat⟩
  · exact loadU256_sstore_count σ _
  · exact loadU256_sstore_count_preserves_excess σ _
  · unfold slotCount loadNat
    rw [loadU256_sstore_count σ _]
    exact toNat_add_one (loadU256 σ SLOT_COUNT)
  · unfold slotExcess loadNat
    rw [loadU256_sstore_count_preserves_excess σ _]

/-- Both predeploys: the same wrapping increment and unchanged excess. -/
theorem paid_user_count_inc_both
    {σ : Storage}
    (pd : PaidUser .deposit σ) (pe : PaidUser .exit σ)
    {md me : CountCfg}
    (hd : runCountInc σ pd.call.gas = .ok md)
    (he : runCountInc σ pe.call.gas = .ok me) :
    loadU256 md.storage SLOT_COUNT =
        loadU256 σ SLOT_COUNT + UInt256.ofNat 1 ∧
      loadU256 md.storage SLOT_EXCESS = loadU256 σ SLOT_EXCESS ∧
      loadU256 me.storage SLOT_COUNT =
        loadU256 σ SLOT_COUNT + UInt256.ofNat 1 ∧
      loadU256 me.storage SLOT_EXCESS = loadU256 σ SLOT_EXCESS :=
  let ⟨h1, h2, _, _⟩ := paid_user_count_inc pd hd
  let ⟨h3, h4, _, _⟩ := paid_user_count_inc pe he
  ⟨h1, h2, h3, h4⟩

/-- System caller: `store_excess` sets `SLOT_COUNT := 0` for any prior
count (the leftover stack word is drain size, not slot 1). Both
predeploys; PCs `storeExcessPc` / `countResetSstorePc`. -/
theorem system_count_reset
    {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    (_hsys : h.isUser = false)
    (newExcess drainCount : UInt256)
    {m : CountCfg}
    (hg : h.gas ≥ storeExcessGasBound)
    (hrun : runStoreExcess σ newExcess drainCount h.gas = .ok m) :
    loadU256 m.storage SLOT_COUNT = UInt256.ofNat 0 ∧
      slotCount m.storage = 0 := by
  have hok := runStoreExcess_ok σ newExcess drainCount h.gas hg
  rw [hok] at hrun
  cases hrun
  refine ⟨?u, ?n⟩
  · exact loadU256_sstore_excess_then_count_zero σ newExcess
  · unfold slotCount loadNat
    rw [loadU256_sstore_excess_then_count_zero σ newExcess]
    exact toNat_ofNat_zero

theorem system_count_reset_both
    {σ : Storage}
    (hd : CallHyp .deposit σ) (he : CallHyp .exit σ)
    (hsd : hd.isUser = false) (hse : he.isUser = false)
    (newExcess drainCount : UInt256)
    {md me : CountCfg}
    (hgd : hd.gas ≥ storeExcessGasBound)
    (hge : he.gas ≥ storeExcessGasBound)
    (rd : runStoreExcess σ newExcess drainCount hd.gas = .ok md)
    (re : runStoreExcess σ newExcess drainCount he.gas = .ok me) :
    loadU256 md.storage SLOT_COUNT = UInt256.ofNat 0 ∧
      loadU256 me.storage SLOT_COUNT = UInt256.ofNat 0 :=
  ⟨(system_count_reset hd hsd newExcess drainCount hgd rd).1,
    (system_count_reset he hse newExcess drainCount hge re).1⟩

/-- Reachability: enough gas implies the user increment CFG succeeds. -/
theorem paid_user_count_inc_runs
    {kind : Kind} {σ : Storage} (p : PaidUser kind σ) :
    ∃ m, runCountInc σ p.call.gas = .ok m ∧
      loadU256 m.storage SLOT_COUNT =
        loadU256 σ SLOT_COUNT + UInt256.ofNat 1 ∧
      loadU256 m.storage SLOT_EXCESS = loadU256 σ SLOT_EXCESS := by
  refine ⟨_, runCountInc_ok σ p.call.gas p.gas_ge_countInc, ?_⟩
  constructor
  · exact loadU256_sstore_count σ _
  · exact loadU256_sstore_count_preserves_excess σ _

/-- Reachability: enough gas implies the system reset CFG succeeds. -/
theorem system_count_reset_runs
    {kind : Kind} {σ : Storage} (h : CallHyp kind σ)
    (_hsys : h.isUser = false)
    (newExcess drainCount : UInt256)
    (hg : h.gas ≥ storeExcessGasBound) :
    ∃ m, runStoreExcess σ newExcess drainCount h.gas = .ok m ∧
      loadU256 m.storage SLOT_COUNT = UInt256.ofNat 0 := by
  refine ⟨_, runStoreExcess_ok σ newExcess drainCount h.gas hg, ?_⟩
  exact loadU256_sstore_excess_then_count_zero σ newExcess

end Eip8282.Audit.Guarantees.PControl1.Count
